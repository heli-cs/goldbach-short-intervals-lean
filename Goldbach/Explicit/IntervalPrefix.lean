import Goldbach.Explicit.IntervalPrefixData
import Goldbach.Explicit.IntervalPrefixLadderData

/-! A continuous checked prefix from five, with dyadic width bounds. -/

open GoldbachExplicit

private theorem log_five_lower : (3 / 2 : ℝ) ≤ Real.log 5 := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ)^2) := by norm_num
      _ = _ := by rw [Real.log_pow]; norm_num
  have hr := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 5 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), hlog4] at hr
  linarith [Real.log_two_gt_d9]

private theorem prefix_bucket {a b width : ℝ} (k : ℕ) (ha : a = 5 * 2^k)
    (hw : width ≤ (3 / 2 + 69 / 100 * (k : ℝ))^2)
    (hraw : ∀ x : ℝ, a ≤ x → x < b → GoldbachConcrete.HasGoldbach x width) :
    ∀ x : ℝ, a ≤ x → x < b → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) := by
  have ha' : 1 ≤ a := by
    rw [ha]
    have hpow : (1 : ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
    linarith
  have hlog : (3 / 2 + 69 / 100 * (k : ℝ)) ≤ Real.log a := by
    rw [ha, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have hlog2 : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith [log_five_lower]
  exact log_sq_cover_of_width ha' (hw.trans (pow_le_pow_left₀ (by positivity) hlog 2)) hraw

/-- The result from the direct dyadic certificate blocks. -/
private theorem initial_prefix :
    ∀ x : ℝ, 5 ≤ x → x < 81920 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) := by
  have cover0 : ∀ x : ℝ, 5 ≤ x → x < 10 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
    prefix_bucket 0 (width := 2) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_ofNat] using goldbach_prefix_fixed_width_0)
  have cover1 : ∀ x : ℝ, 10 ≤ x → x < 20 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
    prefix_bucket 1 (width := 4) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_ofNat] using goldbach_prefix_fixed_width_1)
  have cover2 : ∀ x : ℝ, 20 ≤ x → x < 40 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
    prefix_bucket 2 (width := 8) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_ofNat] using goldbach_prefix_fixed_width_2)
  have cover3 : ∀ x : ℝ, 40 ≤ x → x < 80 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
    prefix_bucket 3 (width := 12) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_ofNat] using goldbach_prefix_fixed_width_3)
  have cover4 : ∀ x : ℝ, 80 ≤ x → x < 160 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
    prefix_bucket 4 (width := 18) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_ofNat] using goldbach_prefix_fixed_width_4)
  have cover5 : ∀ x : ℝ, 160 ≤ x → x < 320 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
    prefix_bucket 5 (width := 24) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_ofNat] using goldbach_prefix_fixed_width_5)
  have cover6 : ∀ x : ℝ, 320 ≤ x → x < 640 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
    prefix_bucket 6 (width := 31) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_ofNat] using goldbach_prefix_fixed_width_6)
  have cover7 : ∀ x : ℝ, 640 ≤ x → x < 1280 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
    prefix_bucket 7 (width := 40) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_ofNat] using goldbach_prefix_fixed_width_7)
  have cover8 : ∀ x : ℝ, 1280 ≤ x → x < 2560 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
    prefix_bucket 8 (width := 49) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_ofNat] using goldbach_prefix_fixed_width_8)
  have cover9 : ∀ x : ℝ, 2560 ≤ x → x < 5120 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
    prefix_bucket 9 (width := 59) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_ofNat] using goldbach_prefix_fixed_width_9)
  have cover10 : ∀ x : ℝ, 5120 ≤ x → x < 10240 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
    prefix_bucket 10 (width := 70) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_ofNat] using goldbach_prefix_fixed_width_10)
  have cover11 : ∀ x : ℝ, 10240 ≤ x → x < 20480 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
    prefix_bucket 11 (width := 82) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_ofNat] using goldbach_prefix_fixed_width_11)
  have cover12 : ∀ x : ℝ, 20480 ≤ x → x < 40960 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
    prefix_bucket 12 (width := 95) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_ofNat] using goldbach_prefix_fixed_width_12)
  have cover13 : ∀ x : ℝ, 40960 ≤ x → x < 81920 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
    prefix_bucket 13 (width := 109) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_ofNat] using goldbach_prefix_fixed_width_13)
  exact (join_goldbach_interval_covers (H := fun x => (Real.log x)^2)
    (join_goldbach_interval_covers (H := fun x => (Real.log x)^2)
      (join_goldbach_interval_covers (H := fun x => (Real.log x)^2)
        cover0
        (join_goldbach_interval_covers (H := fun x => (Real.log x)^2)
          cover1
          cover2))
      (join_goldbach_interval_covers (H := fun x => (Real.log x)^2)
        (join_goldbach_interval_covers (H := fun x => (Real.log x)^2)
          cover3
          cover4)
        (join_goldbach_interval_covers (H := fun x => (Real.log x)^2)
          cover5
          cover6)))
    (join_goldbach_interval_covers (H := fun x => (Real.log x)^2)
      (join_goldbach_interval_covers (H := fun x => (Real.log x)^2)
        cover7
        (join_goldbach_interval_covers (H := fun x => (Real.log x)^2)
          cover8
          cover9))
      (join_goldbach_interval_covers (H := fun x => (Real.log x)^2)
        (join_goldbach_interval_covers (H := fun x => (Real.log x)^2)
          cover10
          cover11)
        (join_goldbach_interval_covers (H := fun x => (Real.log x)^2)
          cover12
          cover13))))

private theorem prefix_extension :
    ∀ x : ℝ, 81920 ≤ x → x < 10000000 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) := by
  have inner : ∀ y : ℝ, 3 ≤ y → y < 35003 → HasOddPrime y 124 := by
    simpa only [Nat.cast_ofNat] using goldbach_prefix_prime_ladder_0
  have outer : ∀ z : ℝ, 46917 ≤ z → z < 9964997 → HasOddPrime z (35003 - 3) := by
    simpa only [Nat.cast_ofNat, show (35003 : ℝ) - 3 = 35000 by norm_num]
      using goldbach_prefix_prime_ladder_1
  have h := goldbach_interval_of_two_prime_covers inner outer
  exact prefix_bucket 14 (width := 124) (by norm_num) (by norm_num)
    (by simpa only [show (35003 : ℝ) + 46917 = 81920 by norm_num,
      show (35003 : ℝ) + 9964997 = 10000000 by norm_num] using h)

/-- The exact interval statement for the contiguous certified prefix. -/
theorem goldbach_short_interval_certified_prefix :
    ∀ x : ℝ, 5 ≤ x → x < 10000000 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
  join_goldbach_interval_covers initial_prefix prefix_extension
