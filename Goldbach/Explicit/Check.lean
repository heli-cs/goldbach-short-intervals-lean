import Goldbach.Explicit
import Goldbach.Target

open MeasureTheory Set
open GoldbachExplicit GoldbachZeros GoldbachConcrete

example (hRH : RiemannHypothesis) :
    Summable reciprocalZeroTerm ∧
      (∑' ρ : Zeros, reciprocalZeroTerm ρ) =
        2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) :=
  reciprocal_zero_sum hRH

example (hRH : RiemannHypothesis) :
    Summable (fun ρ : Zeros => multiplicity ρ / ordinate ρ^2) ∧
      (∑' ρ : Zeros, multiplicity ρ / ordinate ρ^2) < (48 / 1000 : ℝ) :=
  inverse_square_zero_sum_lt hRH

example (t : ℝ) : Zeta23.EF.gammaBracket t ≤ Real.log (|t| + 5 / 2) :=
  gammaBracket_le_log_abs_add t

example {L : ℝ} (hL : 42 ≤ L) :
    (L - 2 * Real.log L)^2 + 3 * L + 7 < L^2 - 7 * L :=
  upper_expression_lt_lower_expression hL

example {V x A d : ℝ} (hV : 0 < V) (hA : 0 < A) (hd : 0 < d)
    (hn : ¬ HasGoldbach x (d * x)) :
    2 * (∫ y in Icc A (x - A), reflectedWeight V x y * density d y) -
      (∫ y in Icc A (x - A), reflectedWeight V x y) ≤
      ∫ y in Icc A (x - A), upperWeight V x y * (density d y - 1)^2 :=
  weighted_reflection_of_no_goldbach hV hA hd hn


example {V : ℝ} (hV : 0 < V) :
    Integrable (fun t : ℝ => (cosineTransform V (t : ℂ)).re * t^2) ∧
      (∫ t : ℝ, (cosineTransform V (t : ℂ)).re * t^2) =
        (2 * Real.pi) * (Real.pi^2 / V^2) :=
  cosineTransform_second_moment hV

example {V : ℝ} (hV : 2 * Real.pi ≤ V) (t : ℝ) :
    Integrable (fun s : ℝ =>
      (cosineTransform V (s : ℂ)).re / (2 * Real.pi) * Zeta23.EF.gammaBracket (t + s)) ∧
    (∫ s : ℝ, (cosineTransform V (s : ℂ)).re / (2 * Real.pi) * Zeta23.EF.gammaBracket (t + s)) ≤
      Real.log (|t| + 3) :=
  cosine_gamma_average_le hV t

example (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) :
    |(Zeta23.Ncount 0 T : ℝ) - zeroCountMain T| ≤ 250 * Real.log (T + 2) :=
  cumulative_zero_count_le hRH hT

example (hRH : RiemannHypothesis) {L : ℝ} (hL : 42 ≤ L) :
    Summable (poleTerm L) ∧ (∑' ρ : Zeros, poleTerm L ρ) < delta L :=
  pole_contribution_lt_delta hRH hL

example {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) :
    Zeta23.paperFT (fun u => (inverseTest lam u : ℂ)) (t : ℂ) =
      (‖GoldbachSpectrum.coefficient lam t‖^2 : ℝ) :=
  inverseTest_paperFT hlam t


#check @cosineWeight_even
#check @cosineWeight_hasCompactSupport
#check @cosineWeight_antitoneOn
#check @cosineWeight_nonneg
#check @cosineWeight_le_one
#check @cosineWeight_quadratic
#check @continuous_cosineWeight
#check @weighted_reflection_of_no_goldbach
#check @gammaBracket_le_log_abs_add
#check @gamma_average_le_log_add_three
#check @reciprocal_zero_sum
#check @reciprocal_zero_sum_lt
#check @ordinate_abs_gt_nine_halves
#check @inverse_square_zero_sum_lt
#check @margin_at_forty_two
#check @margin_strictMonoOn
#check @upper_expression_lt_lower_expression
#check @cosine_loss_constant_lt
#check @delta_lt
#check @delta_exp_bandwidth_lt
#check @delta_exp_half_bandwidth_lt

#print axioms cosineWeight_even
#print axioms cosineWeight_hasCompactSupport
#print axioms cosineWeight_antitoneOn
#print axioms cosineWeight_nonneg
#print axioms cosineWeight_le_one
#print axioms cosineWeight_quadratic
#print axioms continuous_cosineWeight
#print axioms weighted_reflection_of_no_goldbach
#print axioms gammaBracket_le_log_abs_add
#print axioms gamma_average_le_log_add_three
#print axioms reciprocal_zero_sum
#print axioms reciprocal_zero_sum_lt
#print axioms ordinate_abs_gt_nine_halves
#print axioms inverse_square_zero_sum_lt
#print axioms margin_at_forty_two
#print axioms margin_strictMonoOn
#print axioms upper_expression_lt_lower_expression
#print axioms cosine_loss_constant_lt
#print axioms delta_lt
#print axioms delta_exp_bandwidth_lt
#print axioms delta_exp_half_bandwidth_lt

#check @cosineBump_hasCompactSupport
#check @continuous_cosineBump
#check @cosineWeight_eq_autocorr
#check @cosineTransform_eq
#check @cosineTransform_ofReal_nonneg
#check @norm_cosineTransform_pole_le
#check @cosineTransform_real_integral
#check @cosineTransform_second_moment
#check @cosine_gamma_average_le
#check @pole_contribution_lt_delta
#check @cumulative_zero_count_le
#check @compact_weight_spectral_identification
#check @integral_cosine_norm_sq_le_schur
#check @translated_inverseTest_diagonal
#check @inverseTest_paperFT
#check @psi_sub_eq_vonMangoldt
#check @zero_window_integration_by_parts
#check @spectral_discrepancy_boundary_tendsto
#check @prime_coefficient_lt
#check @rational_tail_integral_coefficient_lt

#print axioms cosineBump_hasCompactSupport
#print axioms continuous_cosineBump
#print axioms cosineWeight_eq_autocorr
#print axioms cosineTransform_eq
#print axioms cosineTransform_ofReal_nonneg
#print axioms norm_cosineTransform_pole_le
#print axioms cosineTransform_real_integral
#print axioms cosineTransform_second_moment
#print axioms cosine_gamma_average_le
#print axioms pole_contribution_lt_delta
#print axioms cumulative_zero_count_le
#print axioms compact_weight_spectral_identification
#print axioms integral_cosine_norm_sq_le_schur
#print axioms translated_inverseTest_diagonal
#print axioms inverseTest_paperFT
#print axioms psi_sub_eq_vonMangoldt
#print axioms zero_window_integration_by_parts
#print axioms spectral_discrepancy_boundary_tendsto
#print axioms prime_coefficient_lt
#print axioms rational_tail_integral_coefficient_lt

example {V x A lam : ℝ} (hV : 0 < V) (hA : 0 < A) (hAx : A ≤ x / 2) (hlam : 0 ≤ lam) :
    Integrable (fun s => |trimmedLogWeight V x A (s - lam) - trimmedLogWeight V x A s|) ∧
      (∫ s, |trimmedLogWeight V x A (s - lam) - trimmedLogWeight V x A s|) ≤ 2 * lam :=
  trimmed_log_weight_translation_le hV hA hAx hlam

#check @integral_abs_sub_translate_le
#check @trimmed_log_weight_translation_le
#print axioms integral_abs_sub_translate_le
#print axioms trimmed_log_weight_translation_le

#check @reflected_weight_mass_ge
#check @weighted_firstMoment_abs_le
#check @sharpSpectralValue_memLp
#check @sharp_spectral_integral_eq_tsum
#check @coefficient_norm_le_inv_ordinate
#check @averagedLogPsiError_sub_abs_le
#check @theta_exp_error_le
#check @first_moment_error_lt_trimmed_endpoint
#check @explicit_firstMoment_abs_lt
#check @explicit_variance_gt_of_no_goldbach

#print axioms reflected_weight_mass_ge
#print axioms weighted_firstMoment_abs_le
#print axioms sharpSpectralValue_memLp
#print axioms sharp_spectral_integral_eq_tsum
#print axioms coefficient_norm_le_inv_ordinate
#print axioms averagedLogPsiError_sub_abs_le
#print axioms theta_exp_error_le
#print axioms first_moment_error_lt_trimmed_endpoint
#print axioms explicit_firstMoment_abs_lt
#print axioms explicit_variance_gt_of_no_goldbach

#check @contDiff_two_cosineWeight
#check @cosineWeight_hasDerivAt_on
#check @cosine_row_formula
#check @prime_trace_lower
#check @cosine_sharp_meanSquare_le
#check @cosine_energy_le
#check @coefficient_sq_integral
#check @coefficient_sq_integral_positive
#check @log_pow_div_sq_integral
#check @log_sq_integral_near_zero
#check @integral_log_sq_le_of_envelope
#check @coefficient_log_square_integral_le

#print axioms contDiff_two_cosineWeight
#print axioms cosineWeight_hasDerivAt_on
#print axioms cosine_row_formula
#print axioms prime_trace_lower
#print axioms cosine_sharp_meanSquare_le
#print axioms cosine_energy_le
#print axioms coefficient_sq_integral
#print axioms coefficient_sq_integral_positive
#print axioms log_pow_div_sq_integral
#print axioms log_sq_integral_near_zero
#print axioms integral_log_sq_le_of_envelope
#print axioms coefficient_log_square_integral_le

example (hRH : RiemannHypothesis) (x : ℝ) (hx : Real.exp 42 ≤ x) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
      x < (p : ℝ) + (q : ℝ) ∧
      (p : ℝ) + (q : ℝ) ≤ x + (Real.log x)^2 :=
  goldbach_short_interval_explicit_large hRH x hx

#check @coefficient_sq_eq_quotient
#check @contDiff_coefficient_sq
#check @coefficient_sq_tail_le
#check @coefficient_sq_tail_deriv_le
#check @coefficient_sq_uniform_le
#check @coefficient_sq_uniform_deriv_le
#check @counting_derivative_integral_le
#check @zeroCountMain_hasDerivAt
#check @log_mul_clippedZeroDensity_le
#check @finite_logarithmic_zero_sum_le
#check @alternative_upper_lt_lower
#check @archimedean_expression_le
#check @integral_cosineWeight_first_moment
#check @integral_cosineAbelWeight_le
#check @weightedMangoldtSquares_le
#check @twice_weightedMangoldtSquares_le
#check @archimedeanZeroSum_log_le
#check @archimedeanZeroSum_explicit_le
#check @cosine_energy_explicit_le
#check @sq_lt_sqrt_trimmedEndpoint
#check @explicit_interval_endpoints
#check @explicit_primePowerIncrement_le
#check @primePowerIncrement_integral_div_sq_le
#check @reciprocal_higherPrimePowerWeight_le
#check @explicit_primePower_error_lt
#check @explicit_trivialZero_error_lt
#check @explicit_spectral_variance_lt
#check @explicit_variance_lt
#check @goldbach_short_interval_explicit_large

#print axioms coefficient_sq_eq_quotient
#print axioms contDiff_coefficient_sq
#print axioms coefficient_sq_tail_le
#print axioms coefficient_sq_tail_deriv_le
#print axioms coefficient_sq_uniform_le
#print axioms coefficient_sq_uniform_deriv_le
#print axioms counting_derivative_integral_le
#print axioms zeroCountMain_hasDerivAt
#print axioms log_mul_clippedZeroDensity_le
#print axioms finite_logarithmic_zero_sum_le
#print axioms alternative_upper_lt_lower
#print axioms archimedean_expression_le
#print axioms integral_cosineWeight_first_moment
#print axioms integral_cosineAbelWeight_le
#print axioms weightedMangoldtSquares_le
#print axioms twice_weightedMangoldtSquares_le
#print axioms archimedeanZeroSum_log_le
#print axioms archimedeanZeroSum_explicit_le
#print axioms cosine_energy_explicit_le
#print axioms sq_lt_sqrt_trimmedEndpoint
#print axioms explicit_interval_endpoints
#print axioms explicit_primePowerIncrement_le
#print axioms primePowerIncrement_integral_div_sq_le
#print axioms reciprocal_higherPrimePowerWeight_le
#print axioms explicit_primePower_error_lt
#print axioms explicit_trivialZero_error_lt
#print axioms explicit_spectral_variance_lt
#print axioms explicit_variance_lt
#print axioms goldbach_short_interval_explicit_large

example : FiniteGoldbachExplicitRange ↔
    ∀ n : ℕ, 6 ≤ n → (n : ℝ) < Real.exp 42 + 2 → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧ p + q = n :=
  Iff.rfl

example (hRH : RiemannHypothesis) (hfin : FiniteGoldbachExplicitRange)
    (x : ℝ) (hx : 5 ≤ x) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
      x < (p : ℝ) + (q : ℝ) ∧
      (p : ℝ) + (q : ℝ) ≤ x + (Real.log x)^2 :=
  goldbach_short_interval_explicit_of_finite hRH hfin x hx

#print FiniteGoldbachExplicitRange
#check @goldbach_short_interval_finite_of_finite
#check @finiteGoldbachExplicitRange_of_prime_representations
#check @goldbach_short_interval_explicit_of_finite

#print axioms goldbach_short_interval_finite_of_finite
#print axioms finiteGoldbachExplicitRange_of_prime_representations
#print axioms goldbach_short_interval_explicit_of_finite

example (h : RiemannHypothesis → GaussianPsiSecondMoment) : GoldbachConcrete.Target :=
  goldbach_short_interval_of_psi h

example (hRH : RiemannHypothesis) (hfin : FiniteGoldbachExplicitRange) :
    IsLeast {C : ℝ | ∀ x : ℝ, 4 ≤ x →
      GoldbachConcrete.HasGoldbach x (C * (Real.log x)^2)} (2 / (Real.log 4)^2) :=
  goldbach_log_sq_optimal_of_finite hRH hfin

example (hRH : RiemannHypothesis) (hfin : FiniteGoldbachExplicitRange) :
    ∀ x : ℝ, 4 ≤ x → GoldbachConcrete.HasGoldbach x (max 2 ((Real.log x)^2)) :=
  goldbach_short_interval_max_of_finite hRH hfin

#check @goldbach_short_interval_of_psi
#check @goldbach_log_sq_coefficient_lower_bound
#check @goldbach_short_interval_max_of_explicit
#check @goldbach_log_sq_optimal_of_explicit
#check @goldbach_short_interval_max_of_finite
#check @goldbach_log_sq_optimal_of_finite

#print axioms goldbach_short_interval_of_psi
#print axioms goldbach_log_sq_coefficient_lower_bound
#print axioms goldbach_short_interval_max_of_explicit
#print axioms goldbach_log_sq_optimal_of_explicit
#print axioms goldbach_short_interval_max_of_finite
#print axioms goldbach_log_sq_optimal_of_finite

example : RemainingGoldbachIntervalCoverage ↔
    (∀ x : ℝ, 10000000 ≤ x → x < 1000000000000000000 →
      GoldbachConcrete.HasGoldbach x ((Real.log x)^2)) ∧
    (∀ x : ℝ, 1000000000102800000 ≤ x → x < Real.exp 42 →
      GoldbachConcrete.HasGoldbach x ((Real.log x)^2)) :=
  Iff.rfl

example (hRH : RiemannHypothesis) (h : RemainingGoldbachIntervalCoverage)
    (x : ℝ) (hx : 5 ≤ x) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
      x < (p : ℝ) + (q : ℝ) ∧
      (p : ℝ) + (q : ℝ) ≤ x + (Real.log x)^2 :=
  goldbach_short_interval_explicit_of_remaining_intervals hRH h x hx

example (hRH : RiemannHypothesis) (h : RemainingGoldbachIntervalCoverage) :
    IsLeast {C : ℝ | ∀ x : ℝ, 4 ≤ x → GoldbachConcrete.HasGoldbach x (C * (Real.log x)^2)}
      (2 / (Real.log 4)^2) :=
  goldbach_log_sq_optimal_of_remaining_intervals hRH h

example (hRH : RiemannHypothesis) (h : RemainingGoldbachIntervalCoverage) :
    ∀ x : ℝ, 4 ≤ x → GoldbachConcrete.HasGoldbach x (max 2 ((Real.log x)^2)) :=
  goldbach_short_interval_max_of_remaining_intervals hRH h

example :
    ∀ x : ℝ, 5 ≤ x → x < 10000000 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
  goldbach_short_interval_certified_prefix

example :
    ∀ x : ℝ, 1000000000000000000 ≤ x → x < 1000000000102800000 →
      GoldbachConcrete.HasGoldbach x ((Real.log x)^2) :=
  goldbach_short_interval_high_two_ladders

#check @prime_of_lucas_factorization
#check @interval_cover_of_check
#check @prime_interval_cover_of_check
#check @goldbach_interval_of_two_prime_covers
#check @goldbach_short_interval_certified_prefix
#check @goldbach_short_interval_high_sample
#check @goldbach_short_interval_high_two_ladders
#check @goldbach_short_interval_explicit_of_interval_coverage
#print RemainingGoldbachIntervalCoverage
#check @finiteGoldbachIntervalCoverage_of_remaining
#check @goldbach_short_interval_explicit_of_remaining_intervals
#check @goldbach_short_interval_max_of_remaining_intervals
#check @goldbach_log_sq_optimal_of_remaining_intervals

#print axioms prime_of_lucas_factorization
#print axioms interval_cover_of_check
#print axioms prime_interval_cover_of_check
#print axioms goldbach_interval_of_two_prime_covers
#print axioms goldbach_short_interval_certified_prefix
#print axioms goldbach_short_interval_high_sample
#print axioms goldbach_short_interval_high_two_ladders
#print axioms goldbach_short_interval_explicit_of_interval_coverage
#print axioms finiteGoldbachIntervalCoverage_of_remaining
#print axioms goldbach_short_interval_explicit_of_remaining_intervals
#print axioms goldbach_short_interval_max_of_remaining_intervals
#print axioms goldbach_log_sq_optimal_of_remaining_intervals

example : (1000000000102800000 : ℝ) < Real.exp 42 := by
  have hbase : (27 / 10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc
    (1000000000102800000 : ℝ) < (27 / 10 : ℝ)^42 := by norm_num
    _ < (Real.exp 1)^42 := pow_lt_pow_left₀ hbase (by norm_num) (by decide)
    _ = Real.exp 42 := by rw [← Real.exp_nat_mul]; norm_num

example : (30 : ℝ)^2 - 7 * 30 < (30 - 2 * Real.log 30)^2 + 4 * 30 + 105 := by
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    calc
      Real.log 32 = Real.log ((2 : ℝ)^5) := by norm_num
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlog : Real.log 30 ≤ (7 / 2 : ℝ) := calc
    Real.log 30 ≤ Real.log 32 := Real.log_le_log (by norm_num) (by norm_num)
    _ = 5 * Real.log 2 := h32
    _ ≤ _ := by linarith [Real.log_two_lt_d9]
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 23)
      (show (23 : ℝ) ≤ 30 - 2 * Real.log 30 by linarith) 2
  linarith only [hsq]

example (hRH : RiemannHypothesis)
    (hcomputed : ∀ n : ℕ, 6 ≤ n → n < 4000000000000000000 → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) :
    (∀ x : ℝ, 4 ≤ x → GoldbachConcrete.HasGoldbach x (max 2 ((Real.log x)^2))) ∧
      IsLeast {C : ℝ | ∀ x : ℝ, 4 ≤ x →
        GoldbachConcrete.HasGoldbach x (C * (Real.log x)^2)} (2 / (Real.log 4)^2) := by
  have hfin := finiteGoldbachExplicitRange_of_prime_representations hcomputed
  exact ⟨goldbach_short_interval_max_of_finite hRH hfin,
    goldbach_log_sq_optimal_of_finite hRH hfin⟩

example (hRH : RiemannHypothesis) (h : RemainingGoldbachTwoIntervalCoverage) :
    ∀ x : ℝ, 4 ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + 2 * (Real.log x)^2 :=
  goldbach_short_interval_two_of_remaining_intervals hRH h

example (hRH : RiemannHypothesis) (hfin : FiniteGoldbachExplicitRange) :
    ∀ x : ℝ, 4 ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + 2 * (Real.log x)^2 :=
  goldbach_short_interval_two_of_finite hRH hfin

#print RemainingGoldbachTwoIntervalCoverage
#check @goldbach_short_interval_two_certified_prefix
#check @goldbach_short_interval_two_certified_high
#check @goldbach_short_interval_two_large
#check @goldbach_short_interval_two_of_remaining_intervals
#check @goldbach_short_interval_two_of_finite

#print axioms goldbach_short_interval_two_certified_prefix
#print axioms goldbach_short_interval_two_certified_high
#print axioms goldbach_short_interval_two_large
#print axioms goldbach_short_interval_two_of_remaining_intervals
#print axioms goldbach_short_interval_two_of_finite

example : RiemannHypothesis → RemainingGoldbachIntervalCoverage :=
  remainingGoldbachIntervalCoverage

example (hRH : RiemannHypothesis) :
    ∀ x : ℝ, 5 ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + (Real.log x)^2 :=
  goldbach_short_interval_explicit hRH

example (hRH : RiemannHypothesis) :
    ∀ x : ℝ, 4 ≤ x → GoldbachConcrete.HasGoldbach x (max 2 ((Real.log x)^2)) :=
  goldbach_short_interval_max hRH

example (hRH : RiemannHypothesis) :
    IsLeast {C : ℝ | ∀ x : ℝ, 4 ≤ x → GoldbachConcrete.HasGoldbach x (C * (Real.log x)^2)}
      (2 / (Real.log 4)^2) :=
  goldbach_log_sq_optimal hRH

#check @goldbach_log_sq_real_cover_iff_even
#check @goldbach_short_interval_certified_prefix_to_cutoff
#check @goldbach_short_interval_explicit_of_exp28
#check @remainingGoldbachIntervalCoverage
#check @goldbach_short_interval_explicit
#check @goldbach_short_interval_max
#check @goldbach_log_sq_optimal

#print axioms GoldbachExplicit.prattModPow_eq
#print axioms GoldbachExplicit.prime_of_pratt_modular
#print axioms goldbach_log_sq_real_cover_iff_even
#print axioms goldbach_short_interval_certified_prefix_to_cutoff
#print axioms goldbach_short_interval_explicit_of_exp28
#print axioms remainingGoldbachIntervalCoverage
#print axioms goldbach_short_interval_explicit
#print axioms goldbach_short_interval_max
#print axioms goldbach_log_sq_optimal
