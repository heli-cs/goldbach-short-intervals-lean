import Goldbach.Explicit.IntervalExtended
import Goldbach.Explicit.CutoffData.Inner0
import Goldbach.Explicit.CutoffData.Inner1
import Goldbach.Explicit.CutoffData.Inner2
import Goldbach.Explicit.CutoffData.Inner3
import Goldbach.Explicit.CutoffData.Inner4
import Goldbach.Explicit.CutoffData.Inner5
import Goldbach.Explicit.CutoffData.Inner6
import Goldbach.Explicit.CutoffData.Inner7
import Goldbach.Explicit.CutoffData.Outer0
import Goldbach.Explicit.CutoffData.Outer1
import Goldbach.Explicit.CutoffData.Outer2
import Goldbach.Explicit.CutoffData.Outer3
import Goldbach.Explicit.CutoffData.Outer4
import Goldbach.Explicit.CutoffData.Outer5
import Goldbach.Explicit.CutoffData.Outer6
import Goldbach.Explicit.CutoffData.Outer7

/-! A two-ladder certificate from ten billion to the analytic range. -/

open GoldbachExplicit

private theorem cutoff_first_inner :
    ∀ y : ℝ, (3 : ℕ) ≤ y → y < (1800003 : ℕ) → HasOddPrime y (510 : ℕ) := by
  intro y hy hy'
  obtain ⟨p, hp, hpo, hlo, hhi⟩ := goldbach_extended_inner_ladder y hy hy'
  have hw : ((330 : ℕ) : ℝ) ≤ (510 : ℕ) := by norm_num
  exact ⟨p, hp, hpo, hlo, hhi.trans (add_le_add_right hw y)⟩

private theorem cutoff_inner :
    ∀ y : ℝ, (3 : ℕ) ≤ y → y < (27500003 : ℕ) → HasOddPrime y (510 : ℕ) :=
  (join_prime_interval_covers
    (join_prime_interval_covers
      (join_prime_interval_covers
        cutoff_first_inner
        cutoff_inner_0)
      (join_prime_interval_covers
        cutoff_inner_1
        cutoff_inner_2))
    (join_prime_interval_covers
      (join_prime_interval_covers
        cutoff_inner_3
        cutoff_inner_4)
      (join_prime_interval_covers
        cutoff_inner_5
        (join_prime_interval_covers
          cutoff_inner_6
          cutoff_inner_7))))

private theorem cutoff_outer :
    ∀ z : ℝ, (9972499997 : ℕ) ≤ z → z < (1499972499997 : ℕ) →
      HasOddPrime z (27500000 : ℕ) :=
  (join_prime_interval_covers
    (join_prime_interval_covers
      (join_prime_interval_covers
        cutoff_outer_0
        cutoff_outer_1)
      (join_prime_interval_covers
        cutoff_outer_2
        cutoff_outer_3))
    (join_prime_interval_covers
      (join_prime_interval_covers
        cutoff_outer_4
        cutoff_outer_5)
      (join_prime_interval_covers
        cutoff_outer_6
        cutoff_outer_7)))

private theorem cutoff_width_le : (510 : ℝ) ≤ (Real.log 10000000000)^2 := by
  have hratio : (1 / 5 : ℝ) ≤ Real.log (5 / 4) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 5 by norm_num)
    rw [show (4 / 5 : ℝ) = (5 / 4)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  have hlog : (227 / 10 : ℝ) ≤ Real.log 10000000000 := by
    rw [show (10000000000 : ℝ) = ((5 / 4 : ℝ) * 2^3)^10 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
    linarith [Real.log_two_gt_d9]
  exact (show (510 : ℝ) ≤ (227 / 10)^2 by norm_num).trans
    (pow_le_pow_left₀ (by norm_num) hlog _)

/-- This block has a checked odd-prime representation in every real window. -/
theorem goldbach_short_interval_certified_to_cutoff :
    ∀ x : ℝ, 10000000000 ≤ x → x < 1500000000000 →
      GoldbachConcrete.HasGoldbach x ((Real.log x)^2) := by
  have inner : ∀ y : ℝ, 3 ≤ y → y < 27500003 → HasOddPrime y 510 := by
    simpa only [Nat.cast_ofNat] using cutoff_inner
  have outer : ∀ z : ℝ, 9972499997 ≤ z → z < 1499972499997 →
      HasOddPrime z (27500003 - 3) := by
    simpa only [Nat.cast_ofNat, show (27500003 : ℝ) - 3 = 27500000 by norm_num] using cutoff_outer
  exact log_sq_cover_of_width (by norm_num) cutoff_width_le
    (by simpa only [show (27500003 : ℝ) + 9972499997 = 10000000000 by norm_num,
      show (27500003 : ℝ) + 1499972499997 = 1500000000000 by norm_num]
      using goldbach_interval_of_two_prime_covers inner outer)

/-- The checked finite prefix overlaps the earlier analytic range. -/
theorem goldbach_short_interval_certified_prefix_to_cutoff :
    ∀ x : ℝ, 5 ≤ x → x < 1500000000000 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
  join_goldbach_interval_covers goldbach_short_interval_certified_prefix_to_ten_billion
    goldbach_short_interval_certified_to_cutoff
