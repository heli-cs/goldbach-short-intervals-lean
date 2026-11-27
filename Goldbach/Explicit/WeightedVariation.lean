import Goldbach.Explicit.Reflection
import Goldbach.Explicit.Variation

/-! The L¹ translation bound for the actual reflected weight. -/

open MeasureTheory Set
noncomputable section

namespace GoldbachExplicit

def trimmedLogWeight (V x A : ℝ) (s : ℝ) : ℝ :=
  (Icc A (x - A)).indicator (reflectedWeight V x) (Real.exp s)

private theorem upperWeight_mono {V x y z : ℝ} (hV : 0 < V) (hy : 0 < y)
    (hyz : y ≤ z) (hz : z ≤ x) :
    upperWeight V x y ≤ upperWeight V x z := by
  have hz₀ := hy.trans_le hyz
  have hx₀ := hz₀.trans_le hz
  let p := Real.log (x / z)
  let q := Real.log (x / y)
  have h₀ : 0 ≤ p := Real.log_nonneg ((one_le_div hz₀).mpr hz)
  have hpq : p ≤ q :=
    Real.log_le_log (div_pos hx₀ hz₀) (div_le_div_of_nonneg_left hx₀.le hy hyz)
  change cosineWeight V q ≤ cosineWeight V p
  by_cases hq : q ≤ V
  · exact cosineWeight_antitoneOn hV ⟨h₀, hpq.trans hq⟩ ⟨h₀.trans hpq, hq⟩ hpq
  · have h : V < |q| := by rw [abs_of_nonneg (h₀.trans hpq)]; exact lt_of_not_ge hq
    rw [cosineWeight_zero_of_lt_abs h]
    exact cosineWeight_nonneg hV _

/-- The exact log-coordinate weight in the explicit lower bound has
translation cost at most twice the shift length. -/
theorem trimmed_log_weight_translation_le {V x A lam : ℝ} (hV : 0 < V)
    (hA : 0 < A) (hAx : A ≤ x / 2) (hlam : 0 ≤ lam) :
    Integrable (fun s => |trimmedLogWeight V x A (s - lam) - trimmedLogWeight V x A s|) ∧
    (∫ s, |trimmedLogWeight V x A (s - lam) - trimmedLogWeight V x A s|) ≤ 2 * lam := by
  let q := trimmedLogWeight V x A
  let c := Real.log (x / 2)
  let a := Real.log A - 1
  let b := Real.log (x - A) + 1
  let I := Icc A (x - A)
  have hx₂ : 0 < x / 2 := hA.trans_le hAx
  have hxA : 0 < x - A := by linarith
  have hca : a ≤ c := by
    dsimp [a, c]
    linarith [Real.log_le_log hA hAx]
  have hcb : c ≤ b := by
    dsimp [b, c]
    linarith [Real.log_le_log hx₂ (show x / 2 ≤ x - A by linarith)]
  have hq₀ (s : ℝ) : 0 ≤ q s := by
    apply indicator_nonneg
    intro y _
    exact cosineWeight_nonneg hV _
  have hq₁ (s : ℝ) : q s ≤ 1 := by
    by_cases hs : Real.exp s ∈ I
    · exact (indicator_of_mem hs (reflectedWeight V x)).trans_le (cosineWeight_le_one hV _)
    · exact (indicator_of_notMem hs (reflectedWeight V x)).trans_le zero_le_one
  have hlo (s : ℝ) (hs : s ≤ a) : q s = 0 := by
    apply indicator_of_notMem
    show Real.exp s ∉ I
    have h := Real.exp_lt_exp.mpr (show s < Real.log A by dsimp [a] at hs; linarith)
    rw [Real.exp_log hA] at h
    exact fun hs => (not_lt_of_ge hs.1) h
  have hhi (s : ℝ) (hs : b ≤ s) : q s = 0 := by
    apply indicator_of_notMem
    show Real.exp s ∉ I
    have h := Real.exp_lt_exp.mpr (show Real.log (x - A) < s by dsimp [b] at hs; linarith)
    rw [Real.exp_log hxA] at h
    exact fun hs => (not_lt_of_ge hs.2) h
  have hleft : MonotoneOn q (Iic c) := by
    intro u _ v hv huv
    have hv' : Real.exp v ≤ x / 2 := by
      have he := Real.exp_le_exp.mpr (mem_Iic.mp hv)
      rwa [show Real.exp c = x / 2 from Real.exp_log hx₂] at he
    have huv' := Real.exp_le_exp.mpr huv
    by_cases hu : Real.exp u ∈ I
    · have hvI : Real.exp v ∈ I := ⟨hu.1.trans huv', by linarith⟩
      change I.indicator (reflectedWeight V x) (Real.exp u) ≤
        I.indicator (reflectedWeight V x) (Real.exp v)
      rw [indicator_of_mem hu, indicator_of_mem hvI, reflectedWeight, reflectedWeight,
        min_eq_left (by linarith : Real.exp u ≤ x - Real.exp u),
        min_eq_left (by linarith : Real.exp v ≤ x - Real.exp v)]
      exact upperWeight_mono hV (Real.exp_pos _) huv' (by linarith)
    · change I.indicator (reflectedWeight V x) (Real.exp u) ≤ q v
      rw [indicator_of_notMem hu]
      exact hq₀ v
  have hright : AntitoneOn q (Ici c) := by
    intro u hu v _ huv
    have hu' : x / 2 ≤ Real.exp u := by
      have he := Real.exp_le_exp.mpr (mem_Ici.mp hu)
      rwa [show Real.exp c = x / 2 from Real.exp_log hx₂] at he
    have huv' := Real.exp_le_exp.mpr huv
    by_cases hv : Real.exp v ∈ I
    · have huI : Real.exp u ∈ I := ⟨hAx.trans hu', huv'.trans hv.2⟩
      change I.indicator (reflectedWeight V x) (Real.exp v) ≤
        I.indicator (reflectedWeight V x) (Real.exp u)
      rw [indicator_of_mem huI, indicator_of_mem hv, reflectedWeight, reflectedWeight,
        min_eq_right (by linarith : x - Real.exp u ≤ Real.exp u),
        min_eq_right (by linarith : x - Real.exp v ≤ Real.exp v)]
      exact upperWeight_mono hV (by linarith [hv.2]) (by linarith) (by linarith [Real.exp_pos u])
    · change I.indicator (reflectedWeight V x) (Real.exp v) ≤ q u
      rw [indicator_of_notMem hv]
      exact hq₀ u
  exact integral_abs_sub_translate_le hca hcb hlam hleft hright hlo hhi (hq₁ c)

end GoldbachExplicit
