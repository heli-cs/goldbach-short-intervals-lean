import Goldbach

/-! This independent file restates the exact target and checks the
conditional composition separately. Its axiom output is transitive. -/

open Filter MeasureTheory
open scoped Topology

example : GoldbachConcrete.Target ↔
    (RiemannHypothesis → ∀ c : ℝ, 1 < c → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + c * (Real.log x)^2) :=
  Iff.rfl

example (analytic : RiemannHypothesis → GoldbachConcrete.GaussianSecondMoment)
    (rh : RiemannHypothesis) :
    ∀ c : ℝ, 1 < c → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + c * (Real.log x)^2 :=
  goldbach_short_interval_of_gaussian analytic rh

example (analytic : RiemannHypothesis → GoldbachConcrete.GaussianPsiSecondMoment) :
    RiemannHypothesis → ∀ c : ℝ, 1 < c → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + c * (Real.log x)^2 :=
  goldbach_short_interval_of_psi analytic

#print RiemannHypothesis
#print GoldbachConcrete.Target
#print GoldbachConcrete.GaussianSecondMoment
#print Zeta23.IsNontrivialZero
#print Zeta23.zeroMult
#print Zeta23.RiemannVonMangoldt
#print Zeta23.EF.EF_lit
#check MediumPNT
#check Zeta23.gammaFacts
#check Zeta23.RvM.riemannVonMangoldt
#check Zeta23.WeilEF.EF_lit_zetaZeroConfig
#check GoldbachConcrete.density_eq_theta_sub
#check GoldbachConcrete.firstMomentInput
#check GoldbachConcrete.secondMomentInput_of_gaussian
#check GoldbachZeros.weil_explicit_on_line
#check GoldbachZeros.row_summable_and_bound
#check GoldbachZeros.cumulative_count_tendsto
#check GoldbachZeros.scaled_positive_window_tendsto
#check GoldbachZeros.row_even
#check GoldbachSpectrum.profile_sub_le
#check GoldbachSpectrum.integral_profile_zero
#check GoldbachSpectrum.diagonalEnergy_summable
#check GoldbachSpectrum.local_mean_square_of_ae_limit
#check goldbach_short_interval_of_gaussian
#print axioms RiemannHypothesis
#print axioms MediumPNT
#print axioms Zeta23.zetaSeam
#print axioms Zeta23.gammaFacts
#print axioms Zeta23.RvM.riemannVonMangoldt
#print axioms Zeta23.WeilEF.EF_lit_zetaZeroConfig
#print axioms Zeta23.WeilEF.zero_sum_inv_sq
#print axioms GoldbachConcrete.theta_div_tendsto_one
#print axioms GoldbachConcrete.density_eq_theta_sub
#print axioms GoldbachConcrete.firstMomentInput
#print axioms GoldbachConcrete.secondMomentInput_of_gaussian
#print axioms GoldbachSchur.finite_schur_weighted
#print axioms GoldbachGaussian.integral_kernel
#print axioms GoldbachGaussian.integral_norm_sq_le_schur
#print axioms GoldbachZeros.riemannVonMangoldt
#print axioms GoldbachZeros.weil_explicit_on_line
#print axioms GoldbachZeros.row_summable_and_bound
#print axioms GoldbachZeros.cumulative_count_tendsto
#print axioms GoldbachZeros.scaled_positive_window_tendsto
#print axioms GoldbachSpectrum.integral_profile_zero
#print axioms GoldbachArithmetic.trivialZeroTerm_sub_le
#print axioms GoldbachArithmetic.sqrt_le_pow_gap
#print axioms GoldbachZeros.row_even
#print axioms GoldbachSpectrum.profile_sub_le
#print axioms GoldbachSpectrum.coefficient_sq_scale
#print axioms GoldbachSpectrum.diagonalEnergy_summable
#print axioms GoldbachSpectrum.local_mean_square_of_ae_limit
#print axioms GoldbachLogIntegral.integral_normalized_error
#print axioms GoldbachLogIntegral.ae_avoids_natural_endpoints
#print axioms goldbach_short_interval_of_gaussian

#print GoldbachConcrete.GaussianPsiSecondMoment
#check GoldbachArithmetic.primePowerError_bound
#check GoldbachArithmetic.primePowerError_isLittleO
#check GoldbachConcrete.logWidth_scale_tendsto_one
#check GoldbachSpectrum.eventually_partialSum_sub_mean_square_le
#check GoldbachConcrete.gaussianSecondMoment_of_psi
#check goldbach_short_interval_of_psi
#print axioms GoldbachArithmetic.primePowerError_bound
#print axioms GoldbachArithmetic.primePowerError_isLittleO
#print axioms GoldbachConcrete.logWidth_scale_tendsto_one
#print axioms GoldbachSpectrum.eventually_partialSum_sub_mean_square_le
#print axioms GoldbachConcrete.gaussianSecondMoment_of_psi
#print axioms goldbach_short_interval_of_psi
#check GoldbachZeros.gammaBracket_sub_log_le
#check GoldbachZeros.integral_gammaBracket_shift_div_log
#print axioms GoldbachZeros.integral_gammaBracket_shift_div_log
#print axioms Zeta23.StirlingVert.re_digamma_stirling'

/-! The two endpoints below independently use the complete, expanded type. -/

example (hRH : RiemannHypothesis) :
    ∀ c : ℝ, 1 < c → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + c * (Real.log x)^2 :=
  goldbach_short_interval hRH

example :
    GoldbachConcrete.Target :=
  goldbach_short_interval

#check @GoldbachZeros.translated_cell_tsum_bound
#check @GoldbachZeros.gaussian_cell_tail_bound
#check @GoldbachZeros.translated_window_count_tendsto
#check @GoldbachZeros.row_div_log_abs_tendsto_one
#check @GoldbachSpectrum.scaledWindowTest_tendsto
#check @GoldbachSpectrum.scaledEnergy_small_bound
#check @GoldbachSpectrum.scaledEnergy_dyadic_tail_bound
#check @GoldbachSpectrum.scaledWindowEnergy_tendsto
#check @GoldbachSpectrum.weighted_spectral_asymptotic
#check @GoldbachZeros.archimedean_positive_test
#check @GoldbachSpectrum.smooth_vonMangoldt_positive
#check @GoldbachSpectrum.sharpWeilMoment
#check @GoldbachSpectrum.paperFT_smoothLogBox
#check @GoldbachSpectrum.local_weighted_spectral_tail
#check @GoldbachSpectrum.smoothedSum_tendsto_sharp
#check @GoldbachSpectrum.local_sharp_spectral_tail
#check @GoldbachSpectrum.local_sharp_spectral_mean_square
#check @GoldbachSpectrum.sharp_spectral_identification
#check @GoldbachConcrete.gaussianPsiSecondMoment_of_RH
#check @goldbach_short_interval
#print axioms GoldbachZeros.translated_cell_tsum_bound
#print axioms GoldbachZeros.gaussian_cell_tail_bound
#print axioms GoldbachZeros.translated_window_count_tendsto
#print axioms GoldbachZeros.row_div_log_abs_tendsto_one
#print axioms GoldbachSpectrum.scaledWindowTest_tendsto
#print axioms GoldbachSpectrum.scaledEnergy_small_bound
#print axioms GoldbachSpectrum.scaledEnergy_dyadic_tail_bound
#print axioms GoldbachSpectrum.scaledWindowEnergy_tendsto
#print axioms GoldbachSpectrum.weighted_spectral_asymptotic
#print axioms GoldbachZeros.archimedean_positive_test
#print axioms GoldbachSpectrum.smooth_vonMangoldt_positive
#print axioms GoldbachSpectrum.sharpWeilMoment
#print axioms GoldbachSpectrum.paperFT_smoothLogBox
#print axioms GoldbachSpectrum.local_weighted_spectral_tail
#print axioms GoldbachSpectrum.smoothedSum_tendsto_sharp
#print axioms GoldbachSpectrum.local_sharp_spectral_tail
#print axioms GoldbachSpectrum.local_sharp_spectral_mean_square
#print axioms GoldbachSpectrum.sharp_spectral_identification
#print axioms GoldbachConcrete.gaussianPsiSecondMoment_of_RH
#print axioms goldbach_short_interval
