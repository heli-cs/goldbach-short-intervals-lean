import Goldbach.Explicit.IntervalCoverage
import Goldbach.Explicit.IntervalCutoff
import Goldbach.Explicit.IntervalPrefix
import Goldbach.Explicit.IntervalSample
import Goldbach.Explicit.OptimalCoefficient

/-! Glue the certified blocks to the two remaining intervals and the analytic range. -/

open GoldbachConcrete GoldbachExplicit

/-- Coverage still needed after the certified prefix and the high block. -/
def RemainingGoldbachIntervalCoverage : Prop :=
  (∀ x : ℝ, 10000000 ≤ x → x < 1000000000000000000 →
    HasGoldbach x ((Real.log x)^2)) ∧
  (∀ x : ℝ, 1000000000102800000 ≤ x → x < Real.exp 42 →
    HasGoldbach x ((Real.log x)^2))

theorem finiteGoldbachIntervalCoverage_of_remaining
    (h : RemainingGoldbachIntervalCoverage) : FiniteGoldbachIntervalCoverage :=
  join_goldbach_interval_covers
    (join_goldbach_interval_covers goldbach_short_interval_certified_prefix h.1)
    (join_goldbach_interval_covers goldbach_short_interval_high_two_ladders h.2)

theorem goldbach_short_interval_explicit_of_remaining_intervals
    (hRH : RiemannHypothesis) (h : RemainingGoldbachIntervalCoverage) :
    ∀ x : ℝ, 5 ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + (Real.log x)^2 :=
  goldbach_short_interval_explicit_of_interval_coverage hRH
    (finiteGoldbachIntervalCoverage_of_remaining h)

theorem goldbach_short_interval_max_of_remaining_intervals
    (hRH : RiemannHypothesis) (h : RemainingGoldbachIntervalCoverage) :
    ∀ x : ℝ, 4 ≤ x → HasGoldbach x (max 2 ((Real.log x)^2)) :=
  goldbach_short_interval_max_of_explicit
    (goldbach_short_interval_explicit_of_remaining_intervals hRH h)

theorem goldbach_log_sq_optimal_of_remaining_intervals
    (hRH : RiemannHypothesis) (h : RemainingGoldbachIntervalCoverage) :
    IsLeast {C : ℝ | ∀ x : ℝ, 4 ≤ x → HasGoldbach x (C * (Real.log x)^2)}
      (2 / (Real.log 4)^2) :=
  goldbach_log_sq_optimal_of_explicit
    (goldbach_short_interval_explicit_of_remaining_intervals hRH h)

private theorem earlier_cutoff_lt_certificate_end : Real.exp 28 < (1500000000000 : ℝ) := by
  have hbase : Real.exp 1 ≤ (2719 / 1000 : ℝ) := by linarith [Real.exp_one_lt_d9]
  calc
    Real.exp 28 = (Real.exp 1)^28 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (2719 / 1000 : ℝ)^28 := pow_le_pow_left₀ (Real.exp_pos _).le hbase 28
    _ < _ := by norm_num

/-- The completed finite and analytic overlap discharges the exact two gaps. -/
theorem remainingGoldbachIntervalCoverage (hRH : RiemannHypothesis) :
    RemainingGoldbachIntervalCoverage := by
  have cover (x : ℝ) (hx : 5 ≤ x) : HasGoldbach x ((Real.log x)^2) := by
    by_cases hx' : x < 1500000000000
    · exact goldbach_short_interval_certified_prefix_to_cutoff x hx hx'
    · exact goldbach_short_interval_explicit_of_exp28 hRH x
        (earlier_cutoff_lt_certificate_end.le.trans (le_of_not_gt hx'))
  exact ⟨fun x hx _ => cover x (le_trans (by norm_num) hx),
    fun x hx _ => cover x (le_trans (by norm_num) hx)⟩

/-- The coefficient-one Goldbach short-interval theorem from RH. -/
theorem goldbach_short_interval_explicit (hRH : RiemannHypothesis) :
    ∀ x : ℝ, 5 ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + (Real.log x)^2 :=
  goldbach_short_interval_explicit_of_remaining_intervals hRH
    (remainingGoldbachIntervalCoverage hRH)

/-- The max-width Goldbach short-interval theorem from RH. -/
theorem goldbach_short_interval_max (hRH : RiemannHypothesis) :
    ∀ x : ℝ, 4 ≤ x → HasGoldbach x (max 2 ((Real.log x)^2)) :=
  goldbach_short_interval_max_of_remaining_intervals hRH (remainingGoldbachIntervalCoverage hRH)

/-- The least coefficient for the real range starting at four, from RH. -/
theorem goldbach_log_sq_optimal (hRH : RiemannHypothesis) :
    IsLeast {C : ℝ | ∀ x : ℝ, 4 ≤ x → HasGoldbach x (C * (Real.log x)^2)}
      (2 / (Real.log 4)^2) :=
  goldbach_log_sq_optimal_of_remaining_intervals hRH (remainingGoldbachIntervalCoverage hRH)
