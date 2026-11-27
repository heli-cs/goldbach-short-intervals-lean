import Goldbach.GammaBracket
import Goldbach.Zeros
import Zeta23.ExplicitFormula.Bridge

open Filter MeasureTheory Set
open scoped BigOperators Topology FourierTransform
noncomputable section

namespace GoldbachZeros

open Zeta23

private def gammaPoint (r : ℝ) : ℂ := 1 / 4 + Complex.I * (r : ℂ) / 2

private theorem gammaPoint_re (r : ℝ) : (gammaPoint r).re = 1 / 4 := by
  norm_num [gammaPoint, Complex.div_re, Complex.mul_re]

private theorem gammaPoint_mem (r : ℝ) : gammaPoint r ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have h := congrArg Complex.re hn
  simp only [Complex.intCast_re, gammaPoint_re] at h
  have h₀ : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < (n : ℝ) by linarith)
  have h₁ : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
  omega

private def resolvent (n : ℕ) (r : ℝ) : ℝ := ((gammaPoint r + (n : ℂ))⁻¹).re

private def gammaSummand (n : ℕ) (r : ℝ) : ℝ := resolvent n 0 - resolvent n r

private theorem resolvent_eq (n : ℕ) (r : ℝ) :
    resolvent n r = ((n : ℝ) + 1 / 4) / (((n : ℝ) + 1 / 4)^2 + (r / 2)^2) := by
  have h : gammaPoint r + (n : ℂ) =
      ((((n : ℝ) + 1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I) := by
    unfold gammaPoint
    push_cast
    ring
  rw [resolvent, h, Complex.inv_re, Complex.normSq_add_mul_I]
  simp

private theorem resolvent_zero (n : ℕ) : resolvent n 0 = (((n : ℝ) + 1 / 4))⁻¹ := by
  rw [resolvent_eq]
  have h : 0 < (n : ℝ) + 1 / 4 := by positivity
  field_simp [h.ne']
  <;> ring

private theorem gammaSummand_nonneg (n : ℕ) (r : ℝ) : 0 ≤ gammaSummand n r := by
  unfold gammaSummand
  rw [resolvent_zero, resolvent_eq, sub_nonneg]
  have h : 0 < (n : ℝ) + 1 / 4 := by positivity
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) h]
  nlinarith [sq_nonneg (r / 2)]

private theorem hasSum_gammaSummand (r : ℝ) :
    HasSum (fun n : ℕ => gammaSummand n r) (EF.gammaBracket r - EF.gammaBracket 0) := by
  let z := gammaPoint r
  let z₀ := gammaPoint 0
  let c := (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z -
    (Complex.digamma z₀ + (Real.eulerMascheroniConstant : ℂ) + 1 / z₀)).re
  have hs :
      HasSum (fun n : ℕ => gammaSummand (n + 1) r) c := by
    have h := Complex.reCLM.hasSum
      ((DigammaSeries.hasSum_digamma_series (gammaPoint_mem r)).sub
        (DigammaSeries.hasSum_digamma_series (gammaPoint_mem 0)))
    have hf : (fun n : ℕ => gammaSummand (n + 1) r) =
        fun n : ℕ => Complex.reCLM ((1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) -
          (1 / ((n : ℂ) + 1) - 1 / (z₀ + n + 1))) := by
      funext n
      symm
      change ((1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) -
        (1 / ((n : ℂ) + 1) - 1 / (z₀ + n + 1))).re = _
      rw [gammaSummand, resolvent, resolvent, ← Complex.sub_re]
      congr 1
      push_cast
      rw [← add_assoc z₀, ← add_assoc z]
      ring
    rw [hf]
    exact h
  have he : EF.gammaBracket r - EF.gammaBracket 0 =
      c + ∑ n ∈ Finset.range 1, gammaSummand n r := by
    simp only [Finset.sum_range_one, c, EF.gammaBracket, gammaSummand, resolvent,
      Nat.cast_zero, add_zero, one_div, Complex.sub_re, Complex.add_re,
      Complex.ofReal_re, z, z₀, gammaPoint]
    ring
  rw [he]
  exact (hasSum_nat_add_iff (f := fun n : ℕ => gammaSummand n r) 1).mp hs

private def expWeight (A v : ℝ) : ℂ := (Real.exp (-2 * A * |v|) : ℂ)

private theorem expWeight_integrable {A : ℝ} (hA : 0 < A) : Integrable (expWeight A) := by
  let c := 4 * A
  have hc : 0 < c := by dsimp [c]; positivity
  apply (EF.integrable_exp_neg_abs_half.comp_mul_left' hc.ne').congr
  filter_upwards with v
  simp only [Function.comp_apply, expWeight, abs_mul, abs_of_pos hc, c]
  congr 2
  ring

private theorem expWeight_transform {A : ℝ} (hA : 0 < A) (r : ℝ) :
    (∫ v : ℝ, expWeight A v * Complex.exp (-Complex.I * (r : ℂ) * (v : ℂ))) =
      (A / (A^2 + (r / 2)^2) : ℝ) := by
  let c := 4 * A
  have hc : 0 < c := by dsimp [c]; positivity
  have he (v : ℝ) :
      expWeight A v * Complex.exp (-Complex.I * (r : ℂ) * (v : ℂ)) =
        ((Real.exp (-|c*v| / 2) : ℂ) *
          Complex.exp (-Complex.I * ((r/c : ℝ) : ℂ) * ((c*v : ℝ) : ℂ))) := by
    unfold expWeight
    rw [abs_mul, abs_of_pos hc]
    congr 2
    · dsimp [c]; ring
    · push_cast; field_simp [show (c : ℂ) ≠ 0 by exact_mod_cast hc.ne']
  simp_rw [he]
  rw [Measure.integral_comp_mul_left (fun v : ℝ => (Real.exp (-|v| / 2) : ℂ) *
    Complex.exp (-Complex.I * ((r/c : ℝ) : ℂ) * (v : ℂ))) c,
    EF.integral_exp_neg_abs_half, Complex.real_smul, abs_of_pos (inv_pos.mpr hc)]
  have h : c⁻¹ * (1 / ((1 / 4 : ℝ) + (r / c)^2)) = A / (A^2 + (r / 2)^2) := by
    dsimp [c]
    field_simp [hA.ne', show A^2 + (r / 2)^2 ≠ 0 by positivity,
      show 1 / 4 + (r / (4 * A))^2 ≠ 0 by positivity]
    ring
  have h' := congrArg Complex.ofReal h
  push_cast at h' ⊢
  exact h'

private theorem integrable_gammaBracket_mul {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hs : HasCompactSupport k) :
    Integrable (fun r : ℝ => paperFT k (r : ℂ) * (EF.gammaBracket r : ℂ)) := by
  have he (r : ℝ) : EF.gammaBracket r = (2 * Real.pi) * mu r := by
    unfold EF.gammaBracket mu
    field_simp [Real.pi_pos.ne']
  have h := (EF.integrable_paperFT_mul_mu hk hs gammaFacts).const_mul (2 * (Real.pi : ℂ))
  refine h.congr (Eventually.of_forall fun r => ?_)
  dsimp only
  rw [he]
  push_cast
  ring

/-- The Archimedean Weil term on tests supported away from the origin on
the positive half-line. The kernel includes the entire trivial-zero series. -/
theorem archimedean_positive_test {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {a : ℝ} (ha : 0 < a) (hpos : ∀ v ≤ a, k v = 0) :
    (1 / (2 * Real.pi) : ℂ) * (∫ r : ℝ, paperFT k (r : ℂ) * (EF.gammaBracket r : ℂ)) =
      -(∫ v in Ioi (0 : ℝ), k v * (Real.exp (-v / 2) / (1 - Real.exp (-2 * v)) : ℝ)) := by
  let F (r : ℝ) := paperFT k (r : ℂ)
  let c : ℂ := 1 / (2 * Real.pi)
  have hkI : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  have hFourier := EF.integrable_fourier_of_contDiff_two hk hkc
  have hFI : Integrable F := EF.integrable_paperFT_ofReal hFourier
  have hInv : c * (∫ r, F r) = 0 := by
    have h := EF.paper_inversion hk.continuous hkI hFourier 0
    simpa only [hpos 0 ha.le, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, c, F]
      using h.symm
  have hOne (n : ℕ) :
      c * (∫ r, F r * (gammaSummand n r : ℂ)) =
        -(∫ v in Ioi (0 : ℝ), k v * (Real.exp (-2 * ((n : ℝ) + 1 / 4) * v) : ℝ)) := by
    let A := (n : ℝ) + 1 / 4
    have hA : 0 < A := by dsimp [A]; positivity
    have hE := expWeight_integrable hA
    have hW := EF.integral_k_mul_weight hk.continuous hkI hFourier hE
    have hFi := EF.integrable_paperFT_mul_weightFT hFourier hE
    have htransform (r : ℝ) :
        (∫ v : ℝ, expWeight A v * Complex.exp (-Complex.I * (r : ℂ) * (v : ℂ))) =
          (resolvent n r : ℂ) := by rw [expWeight_transform hA, resolvent_eq]
    simp_rw [htransform] at hW hFi
    have hconst : c * (∫ r, F r * (resolvent n 0 : ℂ)) = 0 := by
      rw [EF.cintegral_mul_const, ← mul_assoc, hInv, zero_mul]
    have hhalf : (∫ v, k v * expWeight A v) =
        ∫ v in Ioi (0 : ℝ), k v * (Real.exp (-2 * A * v) : ℝ) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with v
      by_cases hv : 0 < v
      · rw [indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv), expWeight, abs_of_pos hv]
      · rw [indicator_of_notMem (show v ∉ Ioi (0 : ℝ) from hv), hpos v ((le_of_not_gt hv).trans ha.le), zero_mul]
    unfold gammaSummand
    simp_rw [Complex.ofReal_sub, mul_sub]
    rw [integral_sub (hFI.mul_const _) hFi, mul_sub, hconst, zero_sub]
    congr 1
    exact hW.symm.trans hhalf
  let G (N : ℕ) (r : ℝ) := ∑ n ∈ Finset.range N, gammaSummand n r
  have hGlim (r : ℝ) := (hasSum_gammaSummand r).tendsto_sum_nat
  have hG₀ (N : ℕ) (r : ℝ) : 0 ≤ G N r :=
    Finset.sum_nonneg (fun n _ => gammaSummand_nonneg n r)
  have hGle (N : ℕ) (r : ℝ) : G N r ≤ EF.gammaBracket r - EF.gammaBracket 0 := by
    have h := hasSum_gammaSummand r
    rw [← h.tsum_eq]
    exact h.summable.sum_le_tsum _ (fun n _ => gammaSummand_nonneg n r)
  have hFΓ : Integrable (fun r => F r * ((EF.gammaBracket r - EF.gammaBracket 0 : ℝ) : ℂ)) := by
    convert (integrable_gammaBracket_mul hk hkc).sub (hFI.mul_const (EF.gammaBracket 0 : ℂ)) using 1
    funext r
    simp only [F, Pi.sub_apply, Complex.ofReal_sub, mul_sub]
  have hInt₁ : Tendsto (fun N : ℕ => c * ∫ r, F r * (G N r : ℂ)) atTop
      (𝓝 (c * ∫ r, F r * ((EF.gammaBracket r - EF.gammaBracket 0 : ℝ) : ℂ))) := by
    apply Tendsto.const_mul
    apply tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (fun r => ‖F r * ((EF.gammaBracket r - EF.gammaBracket 0 : ℝ) : ℂ)‖)
    · apply Eventually.of_forall
      intro N
      apply hFI.aestronglyMeasurable.mul
      have hc : Continuous (G N) := by
        unfold G gammaSummand resolvent
        apply continuous_finsetSum
        intro n _
        apply continuous_const.sub
        apply Complex.continuous_re.comp
        apply Continuous.inv₀ (by unfold gammaPoint; fun_prop)
        intro r h
        have h' := congrArg Complex.re h
        simp only [Complex.add_re, gammaPoint_re, Complex.natCast_re, Complex.zero_re] at h'
        linarith [Nat.cast_nonneg (α := ℝ) n]
      exact (Complex.continuous_ofReal.comp hc).aestronglyMeasurable
    · exact Eventually.of_forall fun N => Eventually.of_forall fun r => by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (hG₀ N r), abs_of_nonneg ((hG₀ N r).trans (hGle N r))]
        exact mul_le_mul_of_nonneg_left (hGle N r) (norm_nonneg _)
    · exact hFΓ.norm
    · exact Eventually.of_forall fun r =>
        (Complex.continuous_ofReal.continuousAt.tendsto.comp (hGlim r)).const_mul (F r)
  have hGamma : c * (∫ r, F r * ((EF.gammaBracket r - EF.gammaBracket 0 : ℝ) : ℂ)) =
      c * ∫ r, F r * (EF.gammaBracket r : ℂ) := by
    simp_rw [Complex.ofReal_sub, mul_sub]
    rw [integral_sub (integrable_gammaBracket_mul hk hkc) (hFI.mul_const _),
      mul_sub, EF.cintegral_mul_const, ← mul_assoc, hInv, zero_mul, sub_zero]
  rw [hGamma] at hInt₁
  let P (N : ℕ) (v : ℝ) := ∑ n ∈ Finset.range N, Real.exp (-2 * ((n : ℝ) + 1 / 4) * v)
  let L (v : ℝ) := Real.exp (-v / 2) / (1 - Real.exp (-2 * v))
  have hgeom (v : ℝ) (hv : 0 < v) :
      HasSum (fun n : ℕ => Real.exp (-2 * ((n : ℝ) + 1 / 4) * v)) (L v) := by
    have he (n : ℕ) : Real.exp (-2 * ((n : ℝ) + 1 / 4) * v) =
        Real.exp (-v / 2) * (Real.exp (-2 * v))^n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    simp_rw [he]
    have h₀ : 0 ≤ Real.exp (-2 * v) := (Real.exp_pos _).le
    have h₁ : Real.exp (-2 * v) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    simpa only [L, div_eq_mul_inv] using (hasSum_geometric_of_lt_one h₀ h₁).mul_left (Real.exp (-v / 2))
  have hInt₂ : Tendsto (fun N : ℕ => -(∫ v in Ioi (0 : ℝ), k v * (P N v : ℂ))) atTop
      (𝓝 (-(∫ v in Ioi (0 : ℝ), k v * (L v : ℂ)))) := by
    apply Tendsto.neg
    apply tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ))) (fun v => (1 - Real.exp (-2 * a))⁻¹ * ‖k v‖)
    · apply Eventually.of_forall
      intro N
      apply (hk.continuous.mul ?_).aestronglyMeasurable
      apply Complex.continuous_ofReal.comp
      unfold P
      exact continuous_finsetSum _ (fun n _ => by fun_prop)
    · apply Eventually.of_forall
      intro N
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi] with v hv
      by_cases h : v ≤ a
      · simp [hpos v h]
      have hvp : 0 < v := hv
      have hP : 0 ≤ P N v := Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
      have hLP : P N v ≤ L v := by
        rw [← (hgeom v hvp).tsum_eq]
        exact (hgeom v hvp).summable.sum_le_tsum _ (fun _ _ => (Real.exp_pos _).le)
      have hD : 0 < 1 - Real.exp (-2 * a) :=
        sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
      have hcap : L v ≤ (1 - Real.exp (-2 * a))⁻¹ := by
        unfold L
        rw [inv_eq_one_div]
        apply div_le_div₀ (by norm_num) (Real.exp_le_one_iff.mpr (by linarith)) hD
        exact sub_le_sub_left (Real.exp_le_exp.mpr (by linarith)) 1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP,
        mul_comm ((1 - Real.exp (-2 * a))⁻¹) _]
      exact mul_le_mul_of_nonneg_left (hLP.trans hcap) (norm_nonneg _)
    · exact (hkI.norm.const_mul _).integrableOn
    · filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi] with v hv
      exact (Complex.continuous_ofReal.continuousAt.tendsto.comp (hgeom v hv).tendsto_sum_nat).const_mul (k v)
  have heq (N : ℕ) : c * (∫ r, F r * (G N r : ℂ)) =
      -(∫ v in Ioi (0 : ℝ), k v * (P N v : ℂ)) := by
    unfold G P
    simp_rw [Complex.ofReal_sum, Finset.mul_sum]
    have hif (n : ℕ) : Integrable (fun r => F r * (gammaSummand n r : ℂ)) := by
      let A := (n : ℝ) + 1 / 4
      have hh : 0 < A := by dsimp [A]; positivity
      have h := EF.integrable_paperFT_mul_weightFT hFourier (expWeight_integrable hh)
      have htransform (r : ℝ) :
          (∫ v : ℝ, expWeight A v * Complex.exp (-Complex.I * (r : ℂ) * (v : ℂ))) =
            (resolvent n r : ℂ) := by rw [expWeight_transform hh, resolvent_eq]
      simp_rw [htransform] at h
      refine ((hFI.mul_const (resolvent n 0 : ℂ)).sub h).congr
        (Eventually.of_forall fun r => ?_)
      simp only [Pi.sub_apply, gammaSummand, Complex.ofReal_sub, mul_sub, F]
    have hiw (n : ℕ) :
        IntegrableOn (fun v : ℝ => k v * (Real.exp (-2 * ((n : ℝ) + 1 / 4) * v) : ℝ)) (Ioi 0) := by
      refine hkI.integrableOn.mul_bdd (c := 1) (by fun_prop) ?_
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi] with v hv
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
          (show 0 < v from hv).le)
    rw [integral_finsetSum _ (fun n _ => hif n), Finset.mul_sum,
      integral_finsetSum _ (fun n _ => hiw n), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun n _ => hOne n)
  exact tendsto_nhds_unique (hInt₁.congr heq) hInt₂

end GoldbachZeros
