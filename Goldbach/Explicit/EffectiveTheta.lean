import Goldbach.Explicit.AveragedPsi
import Goldbach.Explicit.ChebyshevBounds

/-! An effective theta estimate for the first moment on the trimmed interval. -/

open MeasureTheory Set
open scoped Interval
noncomputable section

namespace GoldbachExplicit

open GoldbachArithmetic

private theorem trivialZeroTerm_mem_Icc {t : ℝ} (ht : 2 ≤ t) :
    trivialZeroTerm t ∈ Icc (0 : ℝ) 1 := by
  have ht₂ : 2 ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 2)]
  have hi : (t ^ 2)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) ht₂
  have hp : 0 < 1 - (t ^ 2)⁻¹ := by linarith
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2)
    (show 1 / 2 ≤ 1 - (t ^ 2)⁻¹ by linarith)
  have hhi := Real.log_nonpos hp.le
    (sub_le_self _ (inv_nonneg.mpr (sq_nonneg t)))
  rw [one_div, Real.log_inv] at hlo
  unfold trivialZeroTerm
  exact ⟨by linarith, by linarith [Real.log_two_lt_d9]⟩

private theorem exp_one_lower : (27 / 10 : ℝ) < Real.exp 1 := by
  linarith [Real.exp_one_gt_d9]

private theorem exp_nat_lower {n : ℕ} (hn : n ≠ 0) : (27 / 10 : ℝ)^n < Real.exp n := by
  rw [show (n : ℝ) = (n : ℝ) * 1 by ring, Real.exp_nat_mul]
  exact pow_lt_pow_left₀ exp_one_lower (by norm_num) hn

private theorem exp_two_lt_nine : Real.exp 2 < 9 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1, sq_nonneg (Real.exp 1 - 3)]

private theorem averagedLogPsiError_anchor_abs_le {eps : ℝ} (heps : 0 ≤ eps)
    (heps₁ : eps ≤ 1) : |averagedLogPsiError eps 1| ≤ 64 * eps := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s => logPsiError (1 + s)) (a := 0) (b := eps) (C := 64) (by
      intro s hs
      rw [uIoc_of_le heps] at hs
      have ht : 2 ≤ Real.exp (1 + s) :=
        (by linarith [exp_one_lower] : 2 ≤ Real.exp 1).trans
          (Real.exp_le_exp.mpr (by linarith [hs.1]))
      have ht' : Real.exp (1 + s) ≤ 9 :=
        (Real.exp_le_exp.mpr (by linarith [hs.2] : 1 + s ≤ 2)).trans exp_two_lt_nine.le
      obtain ⟨hz₀, hz₁⟩ := trivialZeroTerm_mem_Icc ht
      have hpsi := Chebyshev.psi_le_const_mul_self (Real.exp_pos (1 + s)).le
      have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      have hpsi' : Chebyshev.psi (Real.exp (1 + s)) ≤ 63 := by
        calc
          _ ≤ _ := hpsi
          _ ≤ 7 * Real.exp (1 + s) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
          _ ≤ 63 := by linarith
      rw [Real.norm_eq_abs, abs_le]
      unfold logPsiError
      constructor <;> linarith [Chebyshev.psi_nonneg (Real.exp (1 + s))])
  simpa only [averagedLogPsiError, Real.norm_eq_abs, sub_zero, abs_of_nonneg heps] using h

private theorem averagedLogPsiError_abs_le (hRH : RiemannHypothesis) {eps v : ℝ}
    (heps : 0 ≤ eps) (heps₁ : eps ≤ 1) (hv : 1 ≤ v) :
    |averagedLogPsiError eps v| ≤ (3 / 10 : ℝ) * Real.exp (v / 2) + 64 * eps := by
  have h := averagedLogPsiError_sub_abs_le hRH heps heps₁ (by norm_num : (0 : ℝ) < 1) hv
  have hmono := Real.exp_le_exp.mpr (show (1 : ℝ) / 2 ≤ v / 2 by linarith)
  rw [show averagedLogPsiError eps v = (averagedLogPsiError eps v -
    averagedLogPsiError eps 1) + averagedLogPsiError eps 1 by ring]
  exact (abs_add_le _ _).trans (by linarith [averagedLogPsiError_anchor_abs_le heps heps₁])

private theorem averaged_integrable {eps v : ℝ} (heps : 0 ≤ eps) (hv : 0 < v) :
    IntervalIntegrable (fun s => logPsiError (v + s)) volume 0 eps := by
  have h := (logPsiError_intervalIntegrable hv (show v ≤ v + eps by linarith)).comp_add_right v
  simpa only [sub_self, add_sub_cancel_left, add_comm _ v] using h

private theorem psi_exp_error_le (hRH : RiemannHypothesis) {u : ℝ} (hu : 16 ≤ u) :
    |Chebyshev.psi (Real.exp u) - Real.exp u| ≤ (6 / 5 : ℝ) * Real.exp (3 * u / 4) := by
  let eps := Real.exp (-(u / 4)) / 2
  let M := Real.exp (3 * u / 4)
  let S := Real.exp (u / 2)
  have heps : 0 < eps := by unfold eps; positivity
  have heps₂ : eps ≤ 1 / 20 := by
    have he := exp_nat_lower (n := 4) (by decide)
    have hh : Real.exp (-4) ≤ 1 / 10 := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by norm_num) (by norm_num at he ⊢; linarith)
    have hexp := (Real.exp_le_exp.mpr (show -(u / 4) ≤ -4 by linarith)).trans hh
    unfold eps
    linarith
  have heps₁ : eps ≤ 1 := by linarith
  have hv : 1 ≤ u - eps := by linarith
  have hu₁ : 1 ≤ u := by linarith
  have hM : eps * Real.exp u = M / 2 := by
    unfold eps M
    rw [div_mul_eq_mul_div, ← Real.exp_add, show -(u / 4) + u = 3 * u / 4 by ring]
  have hS : S = 2 * (M * eps) := by
    have he : M * Real.exp (-(u / 4)) = S := by
      unfold M S
      rw [← Real.exp_add]
      congr 1
      ring
    change S = 2 * (M * (Real.exp (-(u / 4)) / 2))
    rw [← mul_div_assoc, he]
    ring
  have hplus : Real.exp (u + eps) - Real.exp u ≤ (11 / 20) * M := by
    have he : Real.exp eps ≤ 1 + (11 / 10) * eps :=
      (Real.exp_bound_div_one_sub_of_interval heps.le (by linarith)).trans
        ((div_le_iff₀ (by linarith : 0 < 1 - eps)).2 (by
          nlinarith [mul_nonneg heps.le (show 0 ≤ 1 - 11 * eps by linarith)]))
    rw [Real.exp_add]
    nlinarith only [hM, mul_le_mul_of_nonneg_left he (Real.exp_pos u).le]
  have hminus : Real.exp u - Real.exp (u - eps) ≤ M / 2 := by
    rw [sub_eq_add_neg u eps, Real.exp_add]
    nlinarith only [hM, mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-eps)) (Real.exp_pos u).le]
  have hforward :
      averagedLogPsiError eps u ≤ eps * (Real.exp (u + eps) + 1 - Chebyshev.psi (Real.exp u)) := by
    unfold averagedLogPsiError
    rw [← sub_zero eps, ← smul_eq_mul, ← intervalIntegral.integral_const]
    simp only [sub_zero]
    refine intervalIntegral.integral_mono_on heps.le
      (averaged_integrable (v := u) heps.le (by linarith)) intervalIntegrable_const ?_
    intro s hs
    have ht₀ : Real.exp u ≤ Real.exp (u + s) := Real.exp_le_exp.mpr (by linarith [hs.1])
    have ht₁ : Real.exp (u + s) ≤ Real.exp (u + eps) := Real.exp_le_exp.mpr (by linarith [hs.2])
    have ht : 2 ≤ Real.exp (u + s) := (by linarith [exp_one_lower] : 2 ≤ Real.exp 1).trans
      (Real.exp_le_exp.mpr (by linarith [hs.1]))
    unfold logPsiError
    linarith only [ht₁, (trivialZeroTerm_mem_Icc ht).2, Chebyshev.psi_mono ht₀]
  have hbackward :
      eps * (Real.exp (u - eps) - Chebyshev.psi (Real.exp u)) ≤ averagedLogPsiError eps (u - eps) := by
    unfold averagedLogPsiError
    rw [← sub_zero eps, ← smul_eq_mul, ← intervalIntegral.integral_const]
    simp only [sub_zero]
    refine intervalIntegral.integral_mono_on heps.le intervalIntegrable_const
      (averaged_integrable (v := u - eps) heps.le (by linarith)) ?_
    intro s hs
    have ht₀ : Real.exp (u - eps) ≤ Real.exp (u - eps + s) :=
      Real.exp_le_exp.mpr (by linarith [hs.1])
    have ht₁ : Real.exp (u - eps + s) ≤ Real.exp u :=
      Real.exp_le_exp.mpr (by linarith [hs.2])
    have ht : 2 ≤ Real.exp (u - eps + s) := (by linarith [exp_one_lower] : 2 ≤ Real.exp 1).trans
      (Real.exp_le_exp.mpr (by linarith [hs.1]))
    unfold logPsiError
    linarith only [ht₀, (trivialZeroTerm_mem_Icc ht).1, Chebyshev.psi_mono ht₁]
  have hf := (abs_le.mp (averagedLogPsiError_abs_le hRH heps.le heps₁ hu₁)).1
  have hb := (abs_le.mp (averagedLogPsiError_abs_le hRH heps.le heps₁ hv)).2
  change -((3 / 10 : ℝ) * S + 64 * eps) ≤ _ at hf
  have hb' : averagedLogPsiError eps (u - eps) ≤ (3 / 10 : ℝ) * S + 64 * eps := by
    have hm : Real.exp ((u - eps) / 2) ≤ S := Real.exp_le_exp.mpr (by linarith)
    linarith only [hb, hm]
  rw [hS] at hf hb'
  have hbig : 65 ≤ (1 / 20 : ℝ) * M := by
    have hmon : Real.exp 12 ≤ M := Real.exp_le_exp.mpr (by linarith)
    have he := exp_nat_lower (n := 12) (by norm_num)
    norm_num at he
    linarith
  have hupper : Chebyshev.psi (Real.exp u) - Real.exp u ≤ (23 / 20 : ℝ) * M + 65 := by
    apply (mul_le_mul_iff_left₀ heps).mp
    nlinarith only [hf, hforward, mul_le_mul_of_nonneg_left hplus heps.le]
  have hlower : Real.exp u - Chebyshev.psi (Real.exp u) ≤ (11 / 10 : ℝ) * M + 64 := by
    apply (mul_le_mul_iff_left₀ heps).mp
    nlinarith only [hb', hbackward, mul_le_mul_of_nonneg_left hminus heps.le]
  have hM₀ : 0 ≤ M := (Real.exp_pos _).le
  change |Chebyshev.psi (Real.exp u) - Real.exp u| ≤ (6 / 5 : ℝ) * M
  exact abs_le.mpr ⟨by linarith only [hlower, hbig, hM₀], by linarith only [hupper, hbig]⟩

/-- For `u ≥ 16`, RH implies an effective pointwise error for theta
by averaging the common-height sharp spectral formula. -/
theorem theta_exp_error_le_three_halves (hRH : RiemannHypothesis) {u : ℝ} (hu : 16 ≤ u) :
    |Chebyshev.theta (Real.exp u) - Real.exp u| ≤ (3 / 2) * Real.exp (3 * u / 4) := by
  have he₄ : 40 ≤ Real.exp 4 := by
    have h := exp_nat_lower (n := 4) (by norm_num)
    norm_num at h
    linarith
  have he : 40 ≤ Real.exp (u / 4) := he₄.trans (Real.exp_le_exp.mpr (by linarith))
  have hs : √(Real.exp u) = Real.exp (u / 2) := by
    have hsq : Real.exp (u / 2) ^ 2 = Real.exp u := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [← hsq, Real.sqrt_sq (Real.exp_pos _).le]
  have hp : Chebyshev.psi (Real.exp u) - Chebyshev.theta (Real.exp u) ≤
      (1 / 10) * Real.exp (3 * u / 4) := by
    have h := psi_sub_theta_le_four_sqrt (Real.one_le_exp_iff.mpr (by linarith : 0 ≤ u))
      (by simpa only [Real.log_exp] using hu)
    rw [hs] at h
    refine h.trans ?_
    rw [show 3 * u / 4 = u / 4 + u / 2 by ring, Real.exp_add]
    nlinarith only [mul_le_mul_of_nonneg_right he (Real.exp_pos (u / 2)).le]
  have hψ := psi_exp_error_le hRH hu
  have hθ := Chebyshev.theta_le_psi (Real.exp u)
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hψ).1, Real.exp_pos (3 * u / 4)],
    by linarith [(abs_le.mp hψ).2, Real.exp_pos (3 * u / 4)]⟩

theorem theta_exp_error_le (hRH : RiemannHypothesis) {u : ℝ} (hu : 16 ≤ u) :
    |Chebyshev.theta (Real.exp u) - Real.exp u| ≤ 4 * Real.exp (3 * u / 4) :=
  (theta_exp_error_le_three_halves hRH hu).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le)

end GoldbachExplicit
