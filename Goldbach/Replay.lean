import Lean.Replay
import Lean.Util.ForEachExpr

/-!
Audit command run with lake env lean --run Goldbach/Replay.lean.

The command loads .olean proof bodies the same way as leanchecker --fresh, then
replays the dependency closure of selected results into an empty environment.
It is an executable audit and is not imported by any Goldbach proof module.
-/

open Lean

private def kernelReferences (expr : Expr) : StateRefT NameSet IO Unit :=
  expr.forEach fun
    | .const name _ | .proj name _ _ => modify (·.insert name)
    | .lit (.natVal _) => modify (·.insert `Nat)
    | .lit (.strVal _) => modify (·.insert `String)
    | _ => pure ()

private def dependencies (info : ConstantInfo) : IO NameSet := (do
  kernelReferences info.type
  if let some body := info.value? (allowOpaque := true) then
    kernelReferences body
  match info with
  | .inductInfo induct =>
    modify (· ++ .ofList (induct.all ++ induct.ctors))
  | .ctorInfo ctor =>
    modify (·.insert ctor.induct)
  | .recInfo recursor =>
    modify (· ++ .ofList recursor.all)
    for rule in recursor.rules do
      modify (·.insert rule.ctor)
      kernelReferences rule.rhs
  | .quotInfo _ =>
    modify (·.insert `Eq)
  | _ => pure ()
  get : StateRefT NameSet IO NameSet).run' {}

private def closure (env : Environment) (roots : Array Name) :
    IO (Std.HashMap Name ConstantInfo) := do
  let mut work := roots
  let mut declarations := {}
  while let some name := work.back? do
    work := work.pop
    if !declarations.contains name then
      let some info := env.checked.get.find? name
        | throw (IO.userError s!"Missing dependency {name}")
      if info.isUnsafe || info.isPartial then
        throw (IO.userError s!"Unexpected unsafe or partial dependency {name}")
      declarations := declarations.insert name info
      for dependency in (← dependencies info) do
        unless declarations.contains dependency do
          work := work.push dependency
  return declarations

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let defaultRoots := #[`goldbach_short_interval_of_psi, `GoldbachConcrete.Target,
    `GoldbachConcrete.firstMomentInput, `GoldbachZeros.weil_explicit_on_line,
    `GoldbachZeros.scaled_positive_window_tendsto, `GoldbachZeros.row_summable_and_bound,
    `GoldbachZeros.row_even, `GoldbachSpectrum.integral_profile_zero,
    `GoldbachSpectrum.local_mean_square_of_ae_limit, `GoldbachSpectrum.coefficient_sq_scale,
    `GoldbachSpectrum.profile_sub_le, `GoldbachSpectrum.diagonalEnergy_summable,
    `GoldbachLogIntegral.integral_normalized_error, `GoldbachLogIntegral.ae_avoids_natural_endpoints,
    `GoldbachArithmetic.trivialZeroTerm_sub_le, `GoldbachArithmetic.sqrt_le_pow_gap,
    `GoldbachConcrete.logWidth_scale_tendsto_one,
    `GoldbachSpectrum.eventually_partialSum_sub_mean_square_le,
    `GoldbachZeros.integral_gammaBracket_shift_div_log]
  let stdout ← IO.getStdout
  let parseName (input : String) := (input.splitOn ".").foldl Name.str Name.anonymous
  let (inputModule, roots) := match args with
    | [] => (`Goldbach, defaultRoots)
    | moduleName :: theoremNames => (parseName moduleName, theoremNames.toArray.map parseName)
  if roots.isEmpty then
    throw (IO.userError "Supply at least one declaration to replay.")
  Lean.withImportModules #[{ module := inputModule }] {} fun source => do
    let declarations ← closure source roots
    let mut axiomNames : Array Name := #[]
    for (name, info) in declarations do
      if let .axiomInfo _ := info then
        axiomNames := axiomNames.push name
    let axioms := axiomNames.qsort Name.lt
    let expected := #[`propext, `Classical.choice, `Quot.sound].qsort Name.lt
    stdout.putStrLn s!"Roots: {roots}"
    stdout.putStrLn s!"Dependency declarations: {declarations.size}"
    stdout.putStrLn s!"Axioms: {axioms}"
    stdout.flush
    unless axioms == expected do
      throw (IO.userError "Unexpected set of axioms")
    let checked ← (← mkEmptyEnvironment).replay declarations
    for root in roots do
      unless (checked.checked.get.find? root).isSome do
        throw (IO.userError s!"Replay did not produce {root}")
    stdout.putStrLn "Fresh kernel replay of the dependency closure passed."
