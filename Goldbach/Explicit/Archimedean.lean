import Goldbach.GammaBracket
import Zeta23.GammaFacts.Complete

/-! The archimedean convolution estimate in Section 8.4. The logarithmic
envelope uses the verified vertical Stirling bound and monotonicity. -/

open MeasureTheory Set
noncomputable section
namespace GoldbachExplicit

open Zeta23

private theorem gammaBracket_eq_mul_mu (t : ℝ) :
    EF.gammaBracket t = (2 * Real.pi) * mu t := by
  unfold EF.gammaBracket mu
  field_simp [Real.pi_ne_zero]

private theorem gammaBracket_abs (t : ℝ) : EF.gammaBracket |t| = EF.gammaBracket t := by
  rw [gammaBracket_eq_mul_mu, gammaBracket_eq_mul_mu]
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, mu_even]

private theorem log_two_pi_gt :
    (179 / 100 : ℝ) < Real.log (2 * Real.pi) := by
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h := Real.log_le_log (show (0 : ℝ) < 6 by norm_num)
    (show (6 : ℝ) ≤ 2 * Real.pi by linarith [Real.pi_gt_three])
  rw [hlog6] at h
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

private theorem log_five_halves_gt :
    (9 / 10 : ℝ) < Real.log (5 / 2) := by
  have h := Real.sum_range_le_log_div (x := (3 / 7 : ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The global digamma bound sufficient for the cosine-kernel convolution. -/
theorem gammaBracket_le_log_abs_add (t : ℝ) :
    EF.gammaBracket t ≤ Real.log (|t| + 5 / 2) := by
  rw [← gammaBracket_abs t]
  by_cases ht : 4 ≤ |t|
  · have hst := (abs_le.mp (GoldbachZeros.gammaBracket_sub_log_le (by linarith : 1 ≤ |t|))).2
    have hsq : (16 : ℝ) ≤ |t|^2 := by nlinarith [sq_nonneg (|t| - 4)]
    have htail : 20 / |t|^2 ≤ 5 / 4 := by
      apply (div_le_iff₀ (show 0 < |t|^2 by positivity)).mpr
      linarith
    have h := Real.log_le_log (show 0 < |t| by linarith) (by linarith : |t| ≤ |t| + 5 / 2)
    linarith [log_two_pi_gt]
  · have hmono := MuFields.mu_monotoneOn (show |t| ∈ Ici (0 : ℝ) from mem_Ici.mpr (abs_nonneg t))
      (show (4 : ℝ) ∈ Ici 0 by simp) (le_of_not_ge ht)
    have hmono' : EF.gammaBracket |t| ≤ EF.gammaBracket 4 := by
      rw [gammaBracket_eq_mul_mu, gammaBracket_eq_mul_mu]
      exact mul_le_mul_of_nonneg_left hmono (by positivity)
    have hst := (abs_le.mp (GoldbachZeros.gammaBracket_sub_log_le (by norm_num : (1 : ℝ) ≤ 4))).2
    have hlog : Real.log 4 < (14 / 10 : ℝ) := by
      rw [Real.log_four_eq]
      linarith [Real.log_two_lt_d9]
    have hmin := Real.log_le_log (show (0 : ℝ) < 5 / 2 by norm_num)
      (show (5 / 2 : ℝ) ≤ |t| + 5 / 2 by linarith [abs_nonneg t])
    norm_num at hst
    linarith [log_two_pi_gt, log_five_halves_gt]

private theorem gammaBracket_tangent (t s : ℝ) :
    EF.gammaBracket (t + s) ≤ Real.log (|t| + 3) +
      (s^2 - 1 / 4) / (|t| + 3) := by
  let D := |t| + 3
  let P := |t + s| + 5 / 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hP hD)
  rw [Real.log_div hP.ne' hD.ne'] at hlog
  have hs : |s| ≤ s^2 + 1 / 4 := by
    nlinarith only [sq_nonneg (|s| - 1 / 2), sq_abs s]
  have htriangle : P - D ≤ s^2 - 1 / 4 := by
    dsimp [P, D]
    linarith [abs_add_le t s]
  have hdiv := div_le_div_of_nonneg_right htriangle hD.le
  have he : (P - D) / D = P / D - 1 := by rw [sub_div, div_self hD.ne']
  rw [he] at hdiv
  have hΓ : EF.gammaBracket (t + s) ≤ Real.log P := gammaBracket_le_log_abs_add (t + s)
  change _ ≤ Real.log D + (s^2 - 1 / 4) / D
  linarith

/-- Logarithmic convolution bound for probability densities with second
moment at most one quarter. In the application the density is the
normalized Fourier transform of the compact cosine-bump weight. -/
theorem gamma_average_le_log_add_three {p : ℝ → ℝ} (t : ℝ)
    (hp : ∀ s : ℝ, 0 ≤ p s) (hI : Integrable p volume) (hnorm : (∫ s, p s) = 1)
    (h2I : Integrable (fun s => p s * s^2) volume)
    (h2 : (∫ s, p s * s^2) ≤ 1 / 4)
    (hΓ : Integrable (fun s => p s * EF.gammaBracket (t + s)) volume) :
    (∫ s, p s * EF.gammaBracket (t + s)) ≤ Real.log (|t| + 3) := by
  let D := |t| + 3
  let C := Real.log D - (1 / 4) / D
  have hD : 0 < D := by dsimp [D]; positivity
  have h₁ : Integrable (fun s => p s * C) := hI.mul_const C
  have h₂ : Integrable (fun s => (p s * s^2) * D⁻¹) := h2I.mul_const D⁻¹
  calc
    _ ≤ ∫ s, p s * C + (p s * s^2) * D⁻¹ := by
      refine integral_mono hΓ (h₁.add h₂) fun s => ?_
      have h := mul_le_mul_of_nonneg_left (gammaBracket_tangent t s) (hp s)
      refine h.trans_eq ?_
      dsimp [C, D]
      rw [sub_div, div_eq_mul_inv, div_eq_mul_inv]
      ring
    _ = C + (∫ s, p s * s^2) * D⁻¹ := by
      rw [integral_add h₁ h₂, integral_mul_const, integral_mul_const, hnorm, one_mul]
    _ ≤ Real.log D := by
      have h := mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hD.le)
      dsimp [C]
      rw [div_eq_mul_inv]
      linarith

end GoldbachExplicit
