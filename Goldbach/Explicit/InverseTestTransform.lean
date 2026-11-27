import Goldbach.Explicit.PrimeDiagonal
import Goldbach.SmoothBox
import Zeta23.ExplicitFormula

/-! Identification of the inverse test with the squared sharp coefficient. -/

open MeasureTheory Set Complex
open scoped FourierTransform Convolution Interval ComplexConjugate

noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum Zeta23

private theorem tilde_logBox_eq (lam s : ℝ) : EF.tilde (logBox lam) s = logBox lam (-s) := by
  by_cases h : -s ∈ Ioc 0 lam
  · simp only [EF.tilde, logBox, indicator_of_mem h, Complex.conj_ofReal]
  · simp only [EF.tilde, logBox, indicator_of_notMem h, map_zero]

private theorem tilde_logBox_integrable (lam : ℝ) : Integrable (EF.tilde (logBox lam)) := by
  refine (logBox_integrable lam).comp_neg.congr ?_
  exact Filter.Eventually.of_forall (fun s => (tilde_logBox_eq lam s).symm)

private theorem convolution_logBox_apply (lam u : ℝ) :
    (logBox lam ⋆[ContinuousLinearMap.mul ℂ ℂ] EF.tilde (logBox lam)) u =
      ∫ v in Ioc (max 0 u) (min lam (u + lam)), (Real.exp (v - u / 2) : ℂ) := by
  rw [convolution_def, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with v
  rw [ContinuousLinearMap.mul_apply', tilde_logBox_eq, neg_sub]
  have hm : v ∈ Ioc (max (0 : ℝ) u) (min lam (u + lam)) ↔
      v ∈ Ioc 0 lam ∧ v - u ∈ Ioc 0 lam := by
    simp only [mem_Ioc, max_lt_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h₀, hu⟩, hv, hvu⟩
      exact ⟨⟨h₀, hv⟩, ⟨by linarith, by linarith⟩⟩
    · rintro ⟨⟨h₀, hv⟩, hu, hvu⟩
      exact ⟨⟨h₀, by linarith⟩, hv, by linarith⟩
  by_cases h : v ∈ Ioc (0 : ℝ) lam <;> by_cases h' : v - u ∈ Ioc (0 : ℝ) lam
  · simp only [logBox, indicator_of_mem h, indicator_of_mem h', indicator_of_mem (hm.mpr ⟨h, h'⟩)]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · simp [logBox, hm, h, h']
  · simp [logBox, hm, h, h']
  · simp [logBox, hm, h, h']

private theorem integral_exp_shift_on_Ioc {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    (∫ v in Ioc a b, (Real.exp (v - c) : ℂ)) =
      (Real.exp (b - c) - Real.exp (a - c) : ℝ) := by
  rw [integral_complex_ofReal, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_sub_right Real.exp c, integral_exp]

private theorem logBox_convolution {lam : ℝ} :
    logBox lam ⋆[ContinuousLinearMap.mul ℂ ℂ] EF.tilde (logBox lam) =
      fun u => (inverseTest lam u : ℂ) := by
  funext u
  rw [convolution_logBox_apply]
  by_cases h : |u| ≤ lam
  · rw [inverseTest, if_pos h]
    rcases le_total 0 u with hu | hu
    · have huL : u ≤ lam := le_abs_self u |>.trans h
      rw [max_eq_right hu, min_eq_left (by linarith : lam ≤ u + lam), integral_exp_shift_on_Ioc huL,
        abs_of_nonneg hu]
      apply congrArg Complex.ofReal
      rw [mul_sub, ← Real.exp_add, mul_one]
      congr 1 <;> congr 1 <;> ring
    · have huL : 0 ≤ u + lam := by linarith [neg_le_abs u]
      rw [max_eq_left hu, min_eq_right (by linarith : u + lam ≤ lam),
        integral_exp_shift_on_Ioc huL, abs_of_nonpos hu]
      apply congrArg Complex.ofReal
      rw [mul_sub, ← Real.exp_add, mul_one]
      congr 1 <;> congr 1 <;> ring
  · rw [inverseTest, if_neg h, Complex.ofReal_zero, Ioc_eq_empty (by
      by_contra! hd
      apply h
      apply abs_le.mpr
      have h₁ := lt_of_le_of_lt (le_max_right 0 u) hd
      have h₂ := lt_of_le_of_lt (le_max_left 0 u) hd
      have h₃ : min lam (u + lam) ≤ lam := min_le_left _ _
      have h₄ : min lam (u + lam) ≤ u + lam := min_le_right _ _
      constructor <;> linarith), Measure.restrict_empty, integral_zero_measure]

/-- The explicit compact triangular test has exactly the squared
sharp-window coefficient as its angular-frequency Fourier transform. -/
theorem inverseTest_paperFT {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) :
    paperFT (fun u => (inverseTest lam u : ℂ)) (t : ℂ) =
      (‖coefficient lam t‖^2 : ℝ) := by
  let r := -t / (2 * Real.pi)
  calc
    _ = 𝓕 (logBox lam ⋆[ContinuousLinearMap.mul ℂ ℂ] EF.tilde (logBox lam)) r := by
      rw [logBox_convolution, EF.paperFT_ofReal_eq_fourier]
    _ = (𝓕 (logBox lam) r) * (𝓕 (EF.tilde (logBox lam)) r) :=
      Real.fourier_mul_convolution_eq (logBox_integrable lam) (tilde_logBox_integrable lam) r
    _ = _ := by
      dsimp only [r]
      rw [← EF.paperFT_ofReal_eq_fourier, ← EF.paperFT_ofReal_eq_fourier,
        EF.paperFT_tilde, Complex.conj_ofReal, paperFT_logBox hlam, Complex.mul_conj']
      simp only [Complex.ofReal_pow]

end GoldbachExplicit
