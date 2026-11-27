import Goldbach.Explicit.FiniteRange

/-! Sharp coefficients and the endpoint at four. -/

open GoldbachConcrete

private theorem hasGoldbach_mono_width {x H₁ H₂ : ℝ} (h : H₁ ≤ H₂)
    (hG : HasGoldbach x H₁) : HasGoldbach x H₂ := by
  obtain ⟨p, q, hp, hq, hpo, hqo, hlo, hhi⟩ := hG
  exact ⟨p, q, hp, hq, hpo, hqo, hlo, hhi.trans (add_le_add_right h x)⟩

private theorem log_four_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)

private theorem log_four_sq_lt_two : (Real.log 4)^2 < 2 := by
  have hlog : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ)^2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hlt : Real.log 4 < (7 / 5 : ℝ) := by
    linarith [Real.log_two_lt_d9]
  calc
    (Real.log 4)^2 < (7 / 5 : ℝ)^2 :=
      pow_lt_pow_left₀ hlt log_four_pos.le (by decide)
    _ < 2 := by norm_num

/-- The argument at four gives a necessary lower bound for every uniform coefficient. -/
theorem goldbach_log_sq_coefficient_lower_bound {C : ℝ}
    (h : ∀ x : ℝ, 4 ≤ x → HasGoldbach x (C * (Real.log x)^2)) :
    2 / (Real.log 4)^2 ≤ C := by
  obtain ⟨p, q, hp, hq, hpo, hqo, _, hhi⟩ := h 4 le_rfl
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    obtain ⟨k, hk⟩ := hpo
    omega
  have hq3 : 3 ≤ q := by
    have hq2 := hq.two_le
    obtain ⟨k, hk⟩ := hqo
    omega
  have hp3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hq3' : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  apply (div_le_iff₀ (sq_pos_of_pos log_four_pos)).2
  linarith

/-- Extend the coefficient-one theorem to four using the width
`max 2 ((Real.log x)^2)`. -/
theorem goldbach_short_interval_max_of_explicit
    (h : ∀ x : ℝ, 5 ≤ x → HasGoldbach x ((Real.log x)^2)) :
    ∀ x : ℝ, 4 ≤ x → HasGoldbach x (max 2 ((Real.log x)^2)) := by
  intro x hx
  by_cases hx5 : 5 ≤ x
  · exact hasGoldbach_mono_width (le_max_right _ _) (h x hx5)
  · have hwidth : (2 : ℝ) ≤ max 2 ((Real.log x)^2) := le_max_left _ _
    refine ⟨3, 3, by decide, by decide, by decide, by decide, ?_, ?_⟩
    · norm_num
      linarith [lt_of_not_ge hx5]
    · norm_num
      linarith

/-- The coefficient fixed by the argument at four is feasible if the
coefficient-one theorem is known from five onwards. -/
theorem goldbach_log_sq_optimal_of_explicit
    (h : ∀ x : ℝ, 5 ≤ x → HasGoldbach x ((Real.log x)^2)) :
    IsLeast {C : ℝ | ∀ x : ℝ, 4 ≤ x → HasGoldbach x (C * (Real.log x)^2)}
      (2 / (Real.log 4)^2) := by
  refine ⟨?_, fun C hC => goldbach_log_sq_coefficient_lower_bound hC⟩
  intro x hx
  have hC : 1 < 2 / (Real.log 4)^2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos log_four_pos)).2
    simpa only [one_mul] using log_four_sq_lt_two
  have hxlog : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hsquare := pow_le_pow_left₀ log_four_pos.le hxlog 2
  have hwidth : (2 : ℝ) ≤ (2 / (Real.log 4)^2) * (Real.log x)^2 := calc
    (2 : ℝ) = (2 / (Real.log 4)^2) * (Real.log 4)^2 :=
      (div_mul_cancel₀ _ (sq_pos_of_pos log_four_pos).ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsquare (by linarith)
  have hlogwidth : (Real.log x)^2 ≤ (2 / (Real.log 4)^2) * (Real.log x)^2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC.le (sq_nonneg (Real.log x))
  exact hasGoldbach_mono_width (max_le hwidth hlogwidth)
    (goldbach_short_interval_max_of_explicit h x hx)

theorem goldbach_short_interval_max_of_finite
    (hRH : RiemannHypothesis) (hfin : FiniteGoldbachExplicitRange) :
    ∀ x : ℝ, 4 ≤ x → HasGoldbach x (max 2 ((Real.log x)^2)) :=
  goldbach_short_interval_max_of_explicit (goldbach_short_interval_explicit_of_finite hRH hfin)

theorem goldbach_log_sq_optimal_of_finite
    (hRH : RiemannHypothesis) (hfin : FiniteGoldbachExplicitRange) :
    IsLeast {C : ℝ | ∀ x : ℝ, 4 ≤ x → HasGoldbach x (C * (Real.log x)^2)}
      (2 / (Real.log 4)^2) :=
  goldbach_log_sq_optimal_of_explicit (goldbach_short_interval_explicit_of_finite hRH hfin)
