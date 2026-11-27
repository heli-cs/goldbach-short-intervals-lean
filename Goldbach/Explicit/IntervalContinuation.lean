import Goldbach.Explicit.IntervalContinuationData
import Goldbach.Explicit.IntervalPrefix

/-! The next certified coefficient-one block, adjacent to the original prefix. -/

open GoldbachExplicit

private theorem continuation_width_le : (250 : ℝ) ≤ (Real.log 10000000)^2 := by
  have hratio : (1 / 5 : ℝ) ≤ Real.log (5 / 4) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 5 by norm_num)
    rw [show (5 / 4 : ℝ) = (4 / 5)⁻¹ by norm_num, Real.log_inv]
    linarith
  have hlog : (159 / 10 : ℝ) ≤ Real.log 10000000 := by
    rw [show (10000000 : ℝ) = ((5 / 4 : ℝ) * 2^3)^7 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
    linarith [Real.log_two_gt_d9]
  exact (show (250 : ℝ) ≤ (159 / 10)^2 by norm_num).trans
    (pow_le_pow_left₀ (by norm_num) hlog _)

/-- The two certified prime ladders cover every real argument in the block,
including the left endpoint. -/
theorem goldbach_short_interval_certified_next :
    ∀ x : ℝ, 10000000 ≤ x → x < 100000000 →
      GoldbachConcrete.HasGoldbach x ((Real.log x)^2) := by
  have inner : ∀ y : ℝ, 3 ≤ y → y < 151003 → HasOddPrime y 250 := by
    simpa only [Nat.cast_ofNat] using goldbach_continuation_prime_ladder_0
  have outer : ∀ z : ℝ, 9848997 ≤ z → z < 99848997 → HasOddPrime z (151003 - 3) := by
    simpa only [Nat.cast_ofNat, show (151003 : ℝ) - 3 = 151000 by norm_num]
      using goldbach_continuation_prime_ladder_1
  exact log_sq_cover_of_width (by norm_num) continuation_width_le
    (by simpa only [show (151003 : ℝ) + 9848997 = 10000000 by norm_num,
      show (151003 : ℝ) + 99848997 = 100000000 by norm_num]
      using goldbach_interval_of_two_prime_covers inner outer)

/-- The contiguous checked prefix after joining at ten million. -/
theorem goldbach_short_interval_certified_extended_prefix :
    ∀ x : ℝ, 5 ≤ x → x < 100000000 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
  join_goldbach_interval_covers goldbach_short_interval_certified_prefix
    goldbach_short_interval_certified_next
