import Goldbach.Explicit.NumericalBounds

/-! Numerical margins for the explicit variance comparison. -/

noncomputable section

namespace GoldbachExplicit

/-- The larger upper allowance from the elementary logarithmic moments
and Mathlib's Chebyshev bound still gives a strict contradiction. -/
theorem alternative_upper_lt_lower {L : ℝ} (hL : 42 ≤ L) :
    (L - 2 * Real.log L)^2 + 4 * L + 105 < L^2 - 7 * L := by
  let a := Real.log 42
  let a₀ : ℝ := 37375 / 10000
  have ha₀ : a₀ ≤ a := log_forty_two_bounds.1.le
  have ha : a ≤ 4 := log_forty_two_bounds.2.le
  have hlog : a ≤ Real.log L := Real.log_le_log (by norm_num) hL
  have hB : 0 ≤ L - 2 * Real.log L := by
    linarith [log_le_sixth_of_ge_28 (show 28 ≤ L by linarith)]
  have hSq : (L - 2 * Real.log L)^2 ≤ (L - 2 * a)^2 :=
    pow_le_pow_left₀ hB (by linarith) _
  have hcompare := mul_nonneg (sub_nonneg.mpr ha₀)
    (show 0 ≤ 4 * L - 4 * (a + a₀) by dsimp [a₀]; linarith)
  have hbase := mul_nonneg (show 0 ≤ L - 42 by linarith)
    (show 0 ≤ 4 * a₀ - 11 by norm_num [a₀])
  unfold a₀ at hcompare hbase
  nlinarith only [hSq, hcompare, hbase]

/-- The tightened upper and lower allowances remain separated at L = 28. -/
theorem alternative_upper_lt_lower_of_ge_28 {L : ℝ} (hL : 28 ≤ L) :
    (L - 2 * Real.log L)^2 + (21 / 4) * L - 7 < L^2 - (53 / 8) * L := by
  have hLog := log_twenty_eight_lower.trans (Real.log_le_log (by norm_num) hL)
  have hB : 0 ≤ L - 2 * Real.log L := by linarith [log_le_sixth_of_ge_28 hL]
  have hSq := pow_le_pow_left₀ hB
    (show L - 2 * Real.log L ≤ L - 2 * (83 / 25) by linarith) 2
  have hlinear := mul_nonneg (sub_nonneg.mpr hL)
    (show 0 ≤ 4 * (83 / 25 : ℝ) - (21 / 4 + 53 / 8) by norm_num)
  nlinarith only [hSq, hlinear]

/-- Main integral and counting allowances, expressed in the original
large-range parameters. -/
theorem archimedean_expression_le_of_ge_28 {L : ℝ} (hL : 28 ≤ L) :
    let lam := logWidth L
    let B := -Real.log lam
    (Real.exp lam - 1) * B^2 + lam * Real.exp lam * (8 * B + 10) / Real.pi +
        50000 * lam^2 * (B + 1)^2 ≤
      delta L * ((L - 2 * Real.log L)^2 + (8 / 3) * L - 12) := by
  let d := delta L
  let lam := logWidth L
  let B := -Real.log lam
  let C := L - 2 * Real.log L
  change (Real.exp lam - 1) * B^2 + lam * Real.exp lam * (8 * B + 10) / Real.pi +
      50000 * lam^2 * (B + 1)^2 ≤ d * (C^2 + (8 / 3) * L - 12)
  have hL₀ : 0 < L := by linarith
  have hd : 0 < d := delta_pos_of_pos hL₀
  have hd₁ : d ≤ 1 := (delta_lt_of_ge_28 hL).le.trans (by norm_num)
  have hlam : 0 < lam := logWidth_pos_of_pos hL₀
  have hdlam : lam ≤ d := logWidth_le_delta_of_pos hL₀
  have h1d : 0 < 1 + d := by linarith
  have he : Real.exp lam = 1 + d := Real.exp_log h1d
  have hlog := log_twenty_eight_lower.trans (Real.log_le_log (by norm_num) hL)
  have hC : 0 ≤ C := by unfold C; linarith [log_le_sixth_of_ge_28 hL]
  have hC' : C ≤ L := by unfold C; linarith
  have hB : 0 ≤ B := neg_nonneg.mpr (Real.log_nonpos hlam.le (hdlam.trans hd₁))
  have hCL : C = -Real.log d := by
    unfold C d delta
    rw [Real.log_mul (sq_pos_of_pos hL₀).ne' (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
    norm_num
    ring
  have hlow : d / (1 + d) ≤ lam := by
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr h1d)
    rw [Real.log_inv, show Real.log (1 + d) = lam from rfl] at hh
    have hq : (1 + d)⁻¹ - 1 = -(d / (1 + d)) := by field_simp [h1d.ne']; ring
    rw [hq] at hh
    linarith
  have hBC : B ≤ C + d := by
    have hl := Real.log_le_log (div_pos hd h1d) hlow
    rw [Real.log_div hd.ne' h1d.ne', show Real.log (1 + d) = lam from rfl] at hl
    unfold B
    linarith only [hl, hCL, hdlam]
  have hBL : B ≤ L - 6 := by
    unfold C at hBC
    have hdsmall : d < 1 / 10^8 := delta_lt_of_ge_28 hL
    linarith only [hBC, hlog, hdsmall]
  have hBsq := pow_le_pow_left₀ hB hBC 2
  have hmain : d * B^2 ≤ d * C^2 + d^2 * (2 * L + 1) := by
    have hu := mul_le_mul_of_nonneg_left hBsq hd.le
    have hz := mul_le_mul_of_nonneg_left hC' (sq_nonneg d)
    have hz' := mul_le_mul_of_nonneg_left hd₁ (sq_nonneg d)
    nlinarith only [hu, hz, hz']
  have hlogpart : lam * Real.exp lam * (8 * B + 10) / Real.pi ≤
      d * (1 + d) * ((8 / 3) * L - 38 / 3) := by
    rw [he, mul_div_assoc]
    refine mul_le_mul (mul_le_mul_of_nonneg_right hdlam h1d.le) ?_ (by positivity) (by positivity)
    calc
      _ ≤ (8 * B + 10) / 3 := div_le_div_of_nonneg_left (by positivity) (by norm_num)
        Real.pi_gt_three.le
      _ ≤ _ := by linarith
  have hsmall := (delta_mul_square_le_of_ge_28 hL).le
  change d * (L + 1)^2 ≤ 1 / 10^6 at hsmall
  have he2 : (2 * L + 1) + ((8 / 3) * L - 38 / 3) ≤ 5 * (L + 1)^2 := by
    nlinarith [sq_nonneg L]
  have hder : 50000 * lam^2 * (B + 1)^2 ≤ 50000 * d^2 * (L + 1)^2 := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlam.le hdlam _) (by norm_num))
      (pow_le_pow_left₀ (by linarith) (by linarith) _) (by positivity) (by positivity)
  rw [he] at hlogpart
  rw [he, add_sub_cancel_left]
  have hbudget := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 50005 * d by positivity)
  nlinarith only [hmain, hlogpart, hder, hbudget, mul_le_mul_of_nonneg_left he2 (sq_nonneg d), hd]

theorem archimedean_expression_le {L : ℝ} (hL : 42 ≤ L) :
    let lam := logWidth L
    let B := -Real.log lam
    (Real.exp lam - 1) * B^2 + lam * Real.exp lam * (8 * B + 10) / Real.pi +
        50000 * lam^2 * (B + 1)^2 ≤
      delta L * ((L - 2 * Real.log L)^2 + (8 / 3) * L + 5) :=
  (archimedean_expression_le_of_ge_28 (by linarith : 28 ≤ L)).trans
    (mul_le_mul_of_nonneg_left (by linarith) (delta_pos hL).le)

end GoldbachExplicit
