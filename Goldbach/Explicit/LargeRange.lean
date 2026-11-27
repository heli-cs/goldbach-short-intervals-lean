import Goldbach.Explicit.VarianceUpper

/-! The RH-only explicit Goldbach theorem in the analytic range. -/

/-- For every real x at least e^42, the interval (x, x + (log x)^2]
contains a sum of two odd primes under the Riemann hypothesis. -/
theorem goldbach_short_interval_explicit_large
    (hRH : RiemannHypothesis) :
    ∀ x : ℝ, Real.exp 42 ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + (Real.log x)^2 := by
  intro x hx
  let L := Real.log x
  have hx₀ := (Real.exp_pos 42).trans_le hx
  have hxL : Real.exp L = x := Real.exp_log hx₀
  have hL : 42 ≤ L := Real.exp_le_exp.mp (hxL.symm ▸ hx)
  have hPair : GoldbachConcrete.HasGoldbach (Real.exp L) (L^2) := by
    by_contra hn
    have hLo := GoldbachExplicit.explicit_variance_gt_of_no_goldbach hRH hL hn
    have hHi := GoldbachExplicit.explicit_variance_lt hRH hL
    have hDiff := mul_lt_mul_of_pos_left (GoldbachExplicit.alternative_upper_lt_lower hL)
      (GoldbachExplicit.delta_pos hL)
    exact lt_irrefl _ (hLo.trans (hHi.trans hDiff))
  simpa only [GoldbachConcrete.HasGoldbach, hxL, L] using hPair

/-- The coefficient-one interval theorem at the earlier analytic cutoff. -/
theorem goldbach_short_interval_explicit_of_exp28 (hRH : RiemannHypothesis) :
    ∀ x : ℝ, Real.exp 28 ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + (Real.log x)^2 := by
  intro x hx
  let L := Real.log x
  have hx₀ := (Real.exp_pos 28).trans_le hx
  have hxL : Real.exp L = x := Real.exp_log hx₀
  have hL : 28 ≤ L := Real.exp_le_exp.mp (hxL.symm ▸ hx)
  have hPair : GoldbachConcrete.HasGoldbach (Real.exp L) (L^2) := by
    by_contra hn
    have hLo := GoldbachExplicit.explicit_variance_gt_of_no_goldbach_of_ge_28 hRH hL hn
    have hHi := GoldbachExplicit.explicit_variance_lt_of_ge_28 hRH hL
    have hDiff := mul_lt_mul_of_pos_left
      (GoldbachExplicit.alternative_upper_lt_lower_of_ge_28 hL)
      (GoldbachExplicit.delta_pos_of_pos (show 0 < L by linarith))
    exact lt_irrefl _ (hLo.trans (hHi.trans hDiff))
  simpa only [GoldbachConcrete.HasGoldbach, hxL, L] using hPair
