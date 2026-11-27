import Goldbach.Explicit.RemainingCoverage

/-! The coefficient-two interval on the verified ranges and its finite-range bridge. -/

open GoldbachConcrete GoldbachExplicit

private theorem goldbach_two_widen {x w : ℝ} (h : HasGoldbach x w)
    (hw : w ≤ 2 * (Real.log x)^2) : HasGoldbach x (2 * (Real.log x)^2) := by
  obtain ⟨p, q, hp, hq, hpo, hqo, hlo, hhi⟩ := h
  exact ⟨p, q, hp, hq, hpo, hqo, hlo, hhi.trans (add_le_add_right hw x)⟩

private theorem goldbach_two_of_one {x : ℝ} (h : HasGoldbach x ((Real.log x)^2)) :
    HasGoldbach x (2 * (Real.log x)^2) :=
  goldbach_two_widen h (by linarith [sq_nonneg (Real.log x)])

private theorem two_le_two_log_sq {x : ℝ} (hx : 4 ≤ x) :
    (2 : ℝ) ≤ 2 * (Real.log x)^2 := by
  have hl : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hs : (1 : ℝ)^2 ≤ (Real.log x)^2 := pow_le_pow_left₀ (by norm_num) hl 2
  rw [show (1 : ℝ)^2 = 1 by norm_num] at hs
  linarith only [hs]

/-- The certificate at the start of the coefficient-two range. -/
theorem goldbach_short_interval_two_certified_prefix :
    ∀ x : ℝ, 4 ≤ x → x < 10000000 → HasGoldbach x (2 * (Real.log x)^2) := by
  intro x hx hx'
  by_cases hx5 : 5 ≤ x
  · exact goldbach_two_of_one (goldbach_short_interval_certified_prefix x hx5 hx')
  · have hw := two_le_two_log_sq hx
    refine ⟨3, 3, by decide, by decide, by decide, by decide, ?_, ?_⟩
    · norm_num
      linarith [lt_of_not_ge hx5]
    · norm_num
      linarith

theorem goldbach_short_interval_two_certified_high :
    ∀ x : ℝ, 1000000000000000000 ≤ x → x < 1000000000102800000 →
      HasGoldbach x (2 * (Real.log x)^2) :=
  fun x hx hx' => goldbach_two_of_one (goldbach_short_interval_high_two_ladders x hx hx')

theorem goldbach_short_interval_two_large (hRH : RiemannHypothesis) :
    ∀ x : ℝ, Real.exp 42 ≤ x → HasGoldbach x (2 * (Real.log x)^2) :=
  fun x hx => goldbach_two_of_one (goldbach_short_interval_explicit_large hRH x hx)

/-- Coverage at the coefficient-two width on the two finite gaps. -/
def RemainingGoldbachTwoIntervalCoverage : Prop :=
  (∀ x : ℝ, 10000000 ≤ x → x < 1000000000000000000 →
    HasGoldbach x (2 * (Real.log x)^2)) ∧
  (∀ x : ℝ, 1000000000102800000 ≤ x → x < Real.exp 42 →
    HasGoldbach x (2 * (Real.log x)^2))

theorem goldbach_short_interval_two_of_remaining_intervals
    (hRH : RiemannHypothesis) (h : RemainingGoldbachTwoIntervalCoverage) :
    ∀ x : ℝ, 4 ≤ x → HasGoldbach x (2 * (Real.log x)^2) := by
  have hsmall : ∀ x : ℝ, 4 ≤ x → x < Real.exp 42 →
      HasGoldbach x (2 * (Real.log x)^2) :=
    join_goldbach_interval_covers
      (join_goldbach_interval_covers goldbach_short_interval_two_certified_prefix h.1)
      (join_goldbach_interval_covers goldbach_short_interval_two_certified_high h.2)
  intro x hx
  by_cases hcut : x < Real.exp 42
  · exact hsmall x hx hcut
  · exact goldbach_short_interval_two_large hRH x (le_of_not_gt hcut)

theorem goldbach_short_interval_two_of_finite
    (hRH : RiemannHypothesis) (hfin : FiniteGoldbachExplicitRange) :
    ∀ x : ℝ, 4 ≤ x → HasGoldbach x (2 * (Real.log x)^2) := by
  intro x hx
  exact goldbach_two_widen (goldbach_short_interval_max_of_finite hRH hfin x hx)
    (max_le (two_le_two_log_sq hx) (by linarith [sq_nonneg (Real.log x)]))
