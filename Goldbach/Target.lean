import Goldbach.ChebyshevTransfer

/-- Conditional composition of the checked reduction with the outstanding
sharp estimate. The exact Goldbach conclusion and the analytic premise
are both visible in the type. -/
theorem goldbach_short_interval_of_gaussian
    (hGaussian : RiemannHypothesis → GoldbachConcrete.GaussianSecondMoment)
    (hRH : RiemannHypothesis) :
    ∀ c : ℝ, 1 < c → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + c * (Real.log x)^2 :=
  GoldbachConcrete.conditional_target GoldbachConcrete.firstMomentInput
    (fun rh => GoldbachConcrete.secondMomentInput_of_gaussian (hGaussian rh)) hRH

/-- The sharp local estimate for Chebyshev's ψ is sufficient for the exact target. -/
theorem goldbach_short_interval_of_psi
    (hGaussianPsi : RiemannHypothesis → GoldbachConcrete.GaussianPsiSecondMoment) :
    GoldbachConcrete.Target :=
  fun rh => goldbach_short_interval_of_gaussian
    (fun h => GoldbachConcrete.gaussianSecondMoment_of_psi (hGaussianPsi h)) rh
