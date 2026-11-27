import Goldbach.GammaKernel
import Goldbach.ArithmeticError

open MeasureTheory Set
open scoped Interval BigOperators
noncomputable section

namespace GoldbachSpectrum

open Zeta23 GoldbachZeros

/-- Poles and the entire gamma contribution to the Weil formula, on the positive half-line. -/
def positiveWeilKernel (v : ℝ) : ℝ :=
  Real.exp (-v / 2) + Real.exp (v / 2) - Real.exp (-v / 2) / (1 - Real.exp (-2 * v))

private theorem gammaDenom_pos {v : ℝ} (hv : 0 < v) : 0 < 1 - Real.exp (-2 * v) :=
  sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))

private theorem continuousOn_gammaKernel {a B : ℝ} (ha : 0 < a) :
    ContinuousOn (fun v : ℝ => Real.exp (-v / 2) / (1 - Real.exp (-2 * v))) (Icc a B) :=
  (by fun_prop : Continuous (fun v : ℝ => Real.exp (-v / 2))).continuousOn.div
    (by fun_prop) (fun v hv => (gammaDenom_pos (ha.trans_le hv.1)).ne')

theorem continuousOn_positiveWeilKernel {a B : ℝ} (ha : 0 < a) :
    ContinuousOn positiveWeilKernel (Icc a B) := by
  unfold positiveWeilKernel
  exact (by fun_prop : Continuous (fun v : ℝ => Real.exp (-v / 2) + Real.exp (v / 2))).continuousOn.sub
    (continuousOn_gammaKernel ha)

private theorem pole_eval (k : ℝ → ℂ) (e : ℝ) :
    paperFT k (-(e : ℂ) * Complex.I) = ∫ v, k v * (Real.exp (e * v) : ℝ) := by
  unfold paperFT
  apply integral_congr_ae
  filter_upwards with v
  rw [Complex.ofReal_exp]
  congr 2
  push_cast
  linear_combination -((e : ℂ) * (v : ℂ)) * Complex.I_sq

/-- Positive-support form of the smooth von Mangoldt explicit formula. -/
theorem smooth_vonMangoldt_positive (hRH : RiemannHypothesis) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {a B : ℝ} (ha : 0 < a) (haB : a ≤ B)
    (hbelow : ∀ v ≤ a, k v = 0) (habove : ∀ v, B < v → k v = 0) :
    (∑' ρ : Zeros, (multiplicity ρ : ℂ) * paperFT k (ordinate ρ)) =
      (∫ v in Icc a B, k v * (positiveWeilKernel v : ℂ)) -
        ∑ n ∈ Finset.Ioc 0 ⌊Real.exp B⌋₊,
          ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
  let S := Finset.Ioc 0 ⌊Real.exp B⌋₊
  have hcut (v : ℝ) (hv : v ∉ Icc a B) : k v = 0 := by
    by_cases hb : v ≤ a
    · exact hbelow v hb
    · exact habove v (lt_of_not_ge fun h => hv ⟨(lt_of_not_ge hb).le, h⟩)
  have hts : tsupport k ⊆ Icc (-B) B := by
    apply closure_minimal _ isClosed_Icc
    intro v hv
    have hm : v ∈ Icc a B := by by_contra h; exact hv (hcut v h)
    exact ⟨by linarith [hm.1], hm.2⟩
  have hrestr (f : ℝ → ℂ) : (∫ v, k v * f v) = ∫ v in Icc a B, k v * f v := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hcut v hv, zero_mul]
  have hrestr' (f : ℝ → ℂ) :
      (∫ v in Ioi (0 : ℝ), k v * f v) = ∫ v in Icc a B, k v * f v := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with v
    by_cases h : v ∈ Icc a B
    · rw [indicator_of_mem (show v ∈ Ioi (0 : ℝ) from ha.trans_le h.1), indicator_of_mem h]
    · rw [indicator_of_notMem h]
      by_cases hv : v ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hv, hcut v h, zero_mul]
      · rw [indicator_of_notMem hv]
  let g₁ : ℝ → ℂ := fun v => (Real.exp (-v / 2) : ℂ)
  let g₂ : ℝ → ℂ := fun v => (Real.exp (v / 2) : ℂ)
  let g₃ : ℝ → ℂ := fun v => (Real.exp (-v / 2) / (1 - Real.exp (-2 * v)) : ℝ)
  have h₁ : paperFT k (Complex.I / 2) = ∫ v in Icc a B, k v * g₁ v := by
    rw [show Complex.I / 2 = -((-1 / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring, pole_eval]
    simpa only [g₁, neg_div, neg_mul, one_mul, div_mul_eq_mul_div] using hrestr g₁
  have h₂ : paperFT k (-Complex.I / 2) = ∫ v in Icc a B, k v * g₂ v := by
    rw [show -Complex.I / 2 = -((1 / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring, pole_eval]
    simpa only [g₂, one_mul, div_mul_eq_mul_div] using hrestr g₂
  have h₃ := archimedean_positive_test hk hkc ha hbelow
  rw [hrestr' g₃] at h₃
  have hprime (n : ℕ) (hn : n ∈ S) : k (-Real.log n) = 0 := by
    apply hbelow
    have hn₁ : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
    have hn₁' : (1 : ℝ) ≤ n := by exact_mod_cast hn₁
    linarith [Real.log_nonneg hn₁']
  have hp :
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))) =
        ∑ n ∈ S, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
    rw [tsum_eq_sum (s := S) (fun n hn => EF.prime_summand_eq_zero hts hn)]
    exact Finset.sum_congr rfl (fun n hn => by rw [hprime n hn, add_zero])
  have hi (f : ℝ → ℂ) (hf : ContinuousOn f (Icc a B)) : IntegrableOn (fun v => k v * f v) (Icc a B) :=
    (hk.continuous.continuousOn.mul hf).integrableOn_compact isCompact_Icc
  have hi₁ := hi g₁ (by unfold g₁; fun_prop)
  have hi₂ := hi g₂ (by unfold g₂; fun_prop)
  have hi₃ := hi g₃ (Complex.continuous_ofReal.comp_continuousOn (continuousOn_gammaKernel ha))
  rw [(weil_explicit_on_line hRH k hk hkc).2, EF.literatureRHS, h₁, h₂, hp, h₃]
  change _ + _ - _ + -_ = _ - _
  rw [show ∀ (A B P C : ℂ), A + B - P + -C = (A + B - C) - P by intros; ring]
  have hi₁₂ : IntegrableOn (fun v => k v * g₁ v + k v * g₂ v) (Icc a B) := hi₁.add hi₂
  rw [← integral_add hi₁ hi₂, ← integral_sub hi₁₂ hi₃]
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  simp only [positiveWeilKernel, Complex.ofReal_add, Complex.ofReal_sub,
    g₁, g₂, g₃]
  ring

private theorem sharpPrimitive_deriv {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun v : ℝ => Real.exp v - 1 / 2 * Real.log (1 - Real.exp (-2 * v)))
      (Real.exp v - Real.exp (-2 * v) / (1 - Real.exp (-2 * v))) v := by
  have h0 : HasDerivAt (fun v : ℝ => -2 * v) (-2 : ℝ) v := by simpa using (hasDerivAt_id v).const_mul (-2)
  have h := (Real.hasDerivAt_exp v).sub
    ((((h0.exp).const_sub 1).log (gammaDenom_pos hv).ne').const_mul (1 / 2))
  convert h using 1 <;> first | rfl | field_simp [(gammaDenom_pos hv).ne']

theorem sharpWeilMoment {a u lam B : ℝ} (ha : 0 < a) (hau : a ≤ u) (hlam : 0 < lam)
    (hB : u + lam ≤ B) :
    (∫ v in Icc a B, ((Ioc 0 lam).indicator (fun s => (Real.exp (s / 2) : ℂ)) (v - u)) *
      (positiveWeilKernel v : ℂ)) =
      (Real.exp (-u / 2) * (Real.exp (u + lam) - Real.exp u +
        (GoldbachArithmetic.trivialZeroTerm (Real.exp (u + lam)) -
         GoldbachArithmetic.trivialZeroTerm (Real.exp u))) : ℝ) := by
  let D (v : ℝ) := Real.exp v - Real.exp (-2 * v) / (1 - Real.exp (-2 * v))
  have hs : Ioc u (u + lam) ⊆ Icc a B := fun v hv => ⟨hau.trans hv.1.le, hv.2.trans hB⟩
  have he (v : ℝ) :
      ((Ioc 0 lam).indicator (fun s => (Real.exp (s / 2) : ℂ)) (v - u)) *
        (positiveWeilKernel v : ℂ) =
      (Ioc u (u + lam)).indicator (fun v => (Real.exp (-u / 2) * D v : ℝ)) v := by
    have hm : v - u ∈ Ioc 0 lam ↔ v ∈ Ioc u (u + lam) := by
      simp only [mem_Ioc, lt_sub_iff_add_lt, sub_le_iff_le_add, zero_add, add_comm lam u]
    by_cases hv : v ∈ Ioc u (u + lam)
    · rw [indicator_of_mem hv, indicator_of_mem (hm.mpr hv), ← Complex.ofReal_mul]
      apply congrArg Complex.ofReal
      have e₁ : Real.exp ((v - u) / 2) * Real.exp (-v / 2) = Real.exp (-u / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      have e₂ : Real.exp ((v - u) / 2) * Real.exp (v / 2) =
          Real.exp (-u / 2) * Real.exp v := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      unfold positiveWeilKernel D
      rw [mul_sub, mul_add, e₁, e₂, ← mul_div_assoc, e₁]
      have hD : 1 - 1 / (1 - Real.exp (-2 * v)) =
          -(Real.exp (-2 * v) / (1 - Real.exp (-2 * v))) := by
        let Q := 1 - Real.exp (-2 * v)
        have hQ : Q ≠ 0 := (gammaDenom_pos (ha.trans_le (hau.trans hv.1.le))).ne'
        change 1 - 1 / Q = -(Real.exp (-2 * v) / Q)
        calc
          _ = Q / Q - 1 / Q := by rw [div_self hQ]
          _ = (Q - 1) / Q := (sub_div _ _ _).symm
          _ = _ := by rw [← neg_div]; congr 1; unfold Q; ring
      linear_combination Real.exp (-u / 2) * hD
    · rw [indicator_of_notMem hv, indicator_of_notMem (hm.not.mpr hv), zero_mul, Complex.ofReal_zero]
  simp_rw [he]
  rw [integral_complex_ofReal, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr hs, integral_const_mul]
  have hFTC :
      (∫ v in u..(u + lam), D v) =
        (Real.exp (u + lam) - 1 / 2 * Real.log (1 - Real.exp (-2 * (u + lam)))) -
          (Real.exp u - 1 / 2 * Real.log (1 - Real.exp (-2 * u))) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun v : ℝ => Real.exp v - 1 / 2 * Real.log (1 - Real.exp (-2 * v)))
      (f' := D) (fun v hv => ?_) ?_
    · rw [uIcc_of_le (by linarith : u ≤ u + lam)] at hv
      exact sharpPrimitive_deriv (ha.trans_le (hau.trans hv.1))
    · have hD : ContinuousOn D (Icc u (u + lam)) := by
        apply Real.continuous_exp.continuousOn.sub
        apply (by fun_prop : Continuous (fun v : ℝ => Real.exp (-2 * v))).continuousOn.div (by fun_prop)
        exact fun v hv => (gammaDenom_pos (ha.trans_le (hau.trans hv.1))).ne'
      apply hD.intervalIntegrable_of_Icc (by linarith)
  rw [intervalIntegral.integral_of_le (by linarith : u ≤ u + lam)] at hFTC
  rw [hFTC]
  apply congrArg Complex.ofReal
  have htr (v : ℝ) : GoldbachArithmetic.trivialZeroTerm (Real.exp v) =
      -(1 / 2 : ℝ) * Real.log (1 - Real.exp (-2 * v)) := by
    unfold GoldbachArithmetic.trivialZeroTerm
    rw [show -2 * v = -(2 * v) by ring, Real.exp_neg, two_mul, Real.exp_add, pow_two]
  rw [htr, htr]
  ring

end GoldbachSpectrum
