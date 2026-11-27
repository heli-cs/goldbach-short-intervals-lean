import Mathlib

/-! Explicit Chebyshev bounds for the weighted prime and prime-power errors. -/

namespace GoldbachExplicit

theorem psi_le_log_envelope (t : ℝ) (ht : 1 ≤ t) :
    Chebyshev.psi t ≤ t * (Real.log 4 + 2 * (Real.log t * Real.exp (-Real.log t / 2))) := by
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  have hsqrt : Real.sqrt t = t * Real.exp (-Real.log t / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht₀, ← Real.exp_log ht₀, ← Real.exp_add]
    rw [Real.log_exp]
    congr 1
    ring
  have h := Chebyshev.psi_le ht
  rw [hsqrt] at h
  nlinarith only [h]

theorem psi_le_three_mul (t : ℝ) (ht : 1 ≤ t) : Chebyshev.psi t ≤ 3 * t := by
  let u := Real.log t / 2
  have h : u ≤ Real.exp (u - 1) := by linarith [Real.add_one_le_exp (u - 1)]
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (-u)).le
  rw [← Real.exp_add, show u - 1 + -u = -1 by ring] at hmul
  have he : Real.exp (-1) ≤ (10 / 27 : ℝ) := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    linarith [Real.exp_one_gt_d9]
  have hlog : Real.log 4 ≤ 3 / 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hcoef : Real.log 4 + 2 * (Real.log t * Real.exp (-Real.log t / 2)) ≤ 3 := by
    have hu : 4 * (u * Real.exp (-u)) = 2 * (Real.log t * Real.exp (-Real.log t / 2)) := by
      dsimp [u]
      rw [neg_div]
      ring
    linarith only [hmul, he, hlog, hu]
  exact (psi_le_log_envelope t ht).trans
    ((mul_le_mul_of_nonneg_left hcoef (zero_le_one.trans ht)).trans_eq (mul_comm t 3))

/-- The Costa-Pereira upper inequality and the elementary linear psi
bound control the total weight of higher prime powers. -/
theorem psi_sub_theta_le_four_sqrt {t : ℝ} (ht : 1 ≤ t) (hlog : 16 ≤ Real.log t) :
    Chebyshev.psi t - Chebyshev.theta t ≤ 4 * Real.sqrt t := by
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  have hs : Real.sqrt t = Real.exp (Real.log t / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht₀]
    ring_nf
  have he₂ : (27 / 10 : ℝ)^2 ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 2
  have hE : 10 ≤ Real.exp (Real.log t / 6) := calc
    _ ≤ (27 / 10 : ℝ)^2 * (1 + 2 / 3) := by norm_num
    _ ≤ Real.exp 2 * Real.exp (2 / 3) :=
      mul_le_mul he₂ (by simpa only [add_comm] using Real.add_one_le_exp (2 / 3))
        (by norm_num) (by positivity)
    _ = Real.exp (2 + 2 / 3) := by rw [Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hsmall (r : ℝ) (hr : r ≤ 1 / 3) : t^r ≤ Real.sqrt t / 10 := by
    have hr' : Real.log t * r ≤ Real.log t / 3 := by
      linarith only [mul_le_mul_of_nonneg_left hr (Real.log_nonneg ht)]
    rw [Real.rpow_def_of_pos ht₀, hs]
    calc
      _ ≤ Real.exp (Real.log t / 3) := Real.exp_le_exp.mpr hr'
      _ = Real.exp (Real.log t / 2) / Real.exp (Real.log t / 6) := by
        rw [← Real.exp_sub]
        ring_nf
      _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hE
  have h₂ := psi_le_three_mul (t ^ (2 : ℝ)⁻¹) (Real.one_le_rpow ht (by norm_num))
  have h₃ := psi_le_three_mul (t ^ (3 : ℝ)⁻¹) (Real.one_le_rpow ht (by norm_num))
  have h₅ := psi_le_three_mul (t ^ (5 : ℝ)⁻¹) (Real.one_le_rpow ht (by norm_num))
  linarith only [Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi t,
    show t ^ (2 : ℝ)⁻¹ = Real.sqrt t by rw [Real.sqrt_eq_rpow, one_div],
    h₂, h₃, h₅, hsmall ((3 : ℝ)⁻¹) (by norm_num), hsmall ((5 : ℝ)⁻¹) (by norm_num),
    Real.sqrt_nonneg t]

end GoldbachExplicit
