import Goldbach.Explicit.IntervalContinuation
import Goldbach.Explicit.IntervalExtendedInnerData
import Goldbach.Explicit.IntervalExtendedOuterData

/-! The continuation of the checked prefix using modular Pratt checks. -/

open GoldbachExplicit

private theorem extended_width_le : (330 : ℝ) ≤ (Real.log 100000000)^2 := by
  have hratio : (1 / 5 : ℝ) ≤ Real.log (5 / 4) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 5 by norm_num)
    rw [show (4 / 5 : ℝ) = (5 / 4)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  have hlog : (182 / 10 : ℝ) ≤ Real.log 100000000 := by
    rw [show (100000000 : ℝ) = ((5 / 4 : ℝ) * 2^3)^8 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
    linarith [Real.log_two_gt_d9]
  exact (show (330 : ℝ) ≤ (182 / 10)^2 by norm_num).trans
    (pow_le_pow_left₀ (by norm_num) hlog _)

/-- The checked real interval certified by the two compact prime ladders. -/
theorem goldbach_short_interval_certified_middle :
    ∀ x : ℝ, 100000000 ≤ x → x < 10000000000 →
      GoldbachConcrete.HasGoldbach x ((Real.log x)^2) := by
  have inner : ∀ y : ℝ, 3 ≤ y → y < 1800003 → HasOddPrime y 330 := by
    simpa only [Nat.cast_ofNat] using goldbach_extended_inner_ladder
  have outer : ∀ z : ℝ, 98199997 ≤ z → z < 9998199997 → HasOddPrime z (1800003 - 3) := by
    simpa only [Nat.cast_ofNat, show (1800003 : ℝ) - 3 = 1800000 by norm_num]
      using goldbach_extended_outer_ladder
  exact log_sq_cover_of_width (by norm_num) extended_width_le
    (by simpa only [show (1800003 : ℝ) + 98199997 = 100000000 by norm_num,
      show (1800003 : ℝ) + 9998199997 = 10000000000 by norm_num]
      using goldbach_interval_of_two_prime_covers inner outer)

/-- Unconditional coefficient-one coverage for every real input in the enlarged prefix. -/
theorem goldbach_short_interval_certified_prefix_to_ten_billion :
    ∀ x : ℝ, 5 ≤ x → x < 10000000000 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
  join_goldbach_interval_covers goldbach_short_interval_certified_extended_prefix
    goldbach_short_interval_certified_middle
