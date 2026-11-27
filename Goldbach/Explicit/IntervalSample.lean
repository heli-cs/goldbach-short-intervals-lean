import Goldbach.Explicit.IntervalSampleData

/-! A representative interval near 10¹⁸ and the cover from reusing its prime ladder. -/

open GoldbachExplicit

private theorem high_width_le_log_sq : (1600 : ℝ) ≤ (Real.log 1000000000000000000)^2 := by
  have hr := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 5 by norm_num)
  have hratio : (1 / 5 : ℝ) ≤ Real.log (5 / 4) := by
    rw [show (5 / 4 : ℝ) = (4 / 5)⁻¹ by norm_num, Real.log_inv]
    linarith
  have hlog10 : Real.log 10 = Real.log (5 / 4) + 3 * Real.log 2 := by
    calc
      Real.log 10 = Real.log ((5 / 4 : ℝ) * 2 ^ (3 : ℕ)) := by norm_num
      _ = _ := by rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
  have h40 : (40 : ℝ) ≤ Real.log 1000000000000000000 := by
    rw [show (1000000000000000000 : ℝ) = 10 ^ (18 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_gt_d9]
  calc
    (1600 : ℝ) = (40 : ℝ)^2 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h40 2

private theorem sample_prime_cover :
    ∀ y : ℝ, 999999999999999997 ≤ y → y < 1000000000000399997 →
      HasOddPrime y 1600 := by
  simpa only [Nat.cast_ofNat] using goldbach_high_prime_ladder_0

private theorem sample_fixed_width :
    ∀ x : ℝ, 1000000000000000000 ≤ x → x < 1000000000000400000 →
      GoldbachConcrete.HasGoldbach x 1600 := by
  have h := goldbach_interval_of_prime_shift (p := 3) (by decide) (by decide) sample_prime_cover
  simpa only [Nat.cast_ofNat,
    show (999999999999999997 : ℝ) + 3 = 1000000000000000000 by norm_num,
    show (1000000000000399997 : ℝ) + 3 = 1000000000000400000 by norm_num] using h

/-- Every real input in the measured single-ladder block has the exact width. -/
theorem goldbach_short_interval_high_sample :
    ∀ x : ℝ, 1000000000000000000 ≤ x → x < 1000000000000400000 →
      GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
  log_sq_cover_of_width (by norm_num) high_width_le_log_sq sample_fixed_width

private theorem two_ladders_fixed_width :
    ∀ x : ℝ, 1000000000000400000 ≤ x → x < 1000000000102800000 →
      GoldbachConcrete.HasGoldbach x 1600 := by
  have hout := goldbach_high_prime_ladder_1
  simp only [Nat.cast_ofNat] at hout
  have hout' : ∀ z : ℝ, 3 ≤ z → z < 102400003 →
      HasOddPrime z (1000000000000399997 - 999999999999999997) := by
    simpa only [show (1000000000000399997 : ℝ) - 999999999999999997 = 400000 by norm_num]
      using hout
  have h := goldbach_interval_of_two_prime_covers sample_prime_cover hout'
  simpa only [show (1000000000000399997 : ℝ) + 3 = 1000000000000400000 by norm_num,
    show (1000000000000399997 : ℝ) + 102400003 = 1000000000102800000 by norm_num] using h

/-- Certified adjacent blocks, with the larger block using two prime ladders. -/
theorem goldbach_short_interval_high_two_ladders :
    ∀ x : ℝ, 1000000000000000000 ≤ x → x < 1000000000102800000 →
      GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
  log_sq_cover_of_width (by norm_num) high_width_le_log_sq
    (join_goldbach_interval_covers (H := fun _ => 1600) sample_fixed_width two_ladders_fixed_width)
