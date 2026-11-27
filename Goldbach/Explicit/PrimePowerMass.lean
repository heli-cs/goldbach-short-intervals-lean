import Goldbach.Explicit.PrimePowerPointwise

/-! Weighted mass of the higher-prime-power increments on a moving interval. -/

open MeasureTheory Set
open scoped Interval
noncomputable section

namespace GoldbachExplicit

open GoldbachArithmetic

private theorem integral_div_sq_on_support {d : ℝ} (hd : 0 ≤ d) {n : ℕ} (hn : 0 < (n : ℝ)) :
    IntegrableOn (fun y : ℝ => (higherPrimePowerWeight n) / y^2)
        (Ico ((n : ℝ) / (1 + d)) (n : ℝ)) ∧
      (∫ y in Ico ((n : ℝ) / (1 + d)) (n : ℝ), higherPrimePowerWeight n / y^2) =
        d * (higherPrimePowerWeight n / n) := by
  let a := (n : ℝ) / (1 + d)
  let w := higherPrimePowerWeight n
  have hd₁ : 0 < 1 + d := by linarith
  have ha : 0 < a := div_pos hn hd₁
  have hab : a ≤ (n : ℝ) := div_le_self hn.le (by linarith)
  have hh : ContinuousOn (fun y : ℝ => w / y^2) (Icc a (n : ℝ)) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun y hy => pow_ne_zero _ (ha.trans_le hy.1).ne')
  have hi := hh.integrableOn_compact (μ := volume) isCompact_Icc
  refine ⟨hi.mono_set Ico_subset_Icc_self, ?_⟩
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hdiff (t : ℝ) (ht : t ∈ uIcc a (n : ℝ)) : HasDerivAt (fun y : ℝ => -w / y) (w / t^2) t := by
    rw [uIcc_of_le hab] at ht
    have ht₀ := ha.trans_le ht.1
    have h := (hasDerivAt_const t (-w)).div (hasDerivAt_id t) ht₀.ne'
    convert h using 1 <;> first | rfl | (simp only [id_eq, zero_mul, mul_one]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hdiff (hh.intervalIntegrable_of_Icc hab)]
  unfold w a
  field_simp [hd₁.ne', hn.ne']
  ring

/-- Integrating the reciprocal-square weighted increment reduces to a
finite reciprocal sum over the integer prime-power locations. -/
theorem primePowerIncrement_integral_div_sq_le {d a b x : ℝ}
    (hd : 0 ≤ d) (ha : 0 < a) (hbx : (1 + d) * b ≤ x) :
    IntegrableOn (fun y => primePowerIncrement d y / y^2) (Icc a b) ∧
      (∫ y in Icc a b, primePowerIncrement d y / y^2) ≤
        d * ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊, higherPrimePowerWeight n / n := by
  classical
  let J := Icc a b
  let S := Finset.Ioc ⌊a⌋₊ ⌊x⌋₊
  let U (n : ℕ) := Ico ((n : ℝ) / (1 + d)) (n : ℝ)
  let f (n : ℕ) := (U n).indicator (fun y => higherPrimePowerWeight n / y^2)
  have hd₁ : 0 < 1 + d := by linarith
  have hpos (n : ℕ) (hn : n ∈ S) : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hn).1
  have hfi (n : ℕ) (hn : n ∈ S) : Integrable (f n) :=
    (integrable_indicator_iff measurableSet_Ico).2 (integral_div_sq_on_support hd (hpos n hn)).1
  have he (y : ℝ) (hy : y ∈ J) : (∑ n ∈ S, f n y) = primePowerIncrement d y / y^2 := by
    have hy₀ := ha.trans_le hy.1
    have hDy₀ : 0 ≤ (1 + d) * y := mul_nonneg hd₁.le hy₀.le
    have hY : (1 + d) * y ≤ x := (mul_le_mul_of_nonneg_left hy.2 hd₁.le).trans hbx
    rw [primePowerIncrement_eq_sum hd hy₀.le, Finset.sum_div]
    have ht : Finset.Ioc ⌊y⌋₊ ⌊(1 + d) * y⌋₊ = S.filter (fun n => y ∈ U n) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ioc, S, U, mem_Ico]
      rw [Nat.floor_lt hy₀.le, Nat.le_floor_iff hDy₀, Nat.floor_lt ha.le,
        Nat.le_floor_iff (hDy₀.trans hY), div_le_iff₀ hd₁, mul_comm y (1 + d)]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨⟨hy.1.trans_lt h₁, h₂.trans hY⟩, ⟨h₂, h₁⟩⟩
      · rintro ⟨_, h₂, h₁⟩
        exact ⟨h₁, h₂⟩
    rw [ht, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun n _ => by
      by_cases hn : y ∈ U n <;> simp [f, hn])
  have hae := (ae_restrict_mem (μ := volume) (s := J) measurableSet_Icc).mono he
  have hi : IntegrableOn (fun y => ∑ n ∈ S, f n y) J :=
    integrable_finsetSum _ (fun n hn => (hfi n hn).integrableOn)
  refine ⟨hi.congr hae, ?_⟩
  calc
    _ = ∑ n ∈ S, ∫ y in J, f n y := by
      rw [← integral_congr_ae hae, integral_finsetSum _ (fun n hn => (hfi n hn).integrableOn)]
    _ ≤ ∑ n ∈ S, d * (higherPrimePowerWeight n / n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnon (y : ℝ) : 0 ≤ f n y := by
        apply indicator_nonneg
        exact fun _ _ => div_nonneg (higherPrimePowerWeight_nonneg n) (sq_nonneg _)
      calc
        _ ≤ ∫ y, f n y := integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall hnon) (hfi n hn)
        _ = _ := by
          unfold f
          rw [integral_indicator measurableSet_Ico]
          exact (integral_div_sq_on_support hd (hpos n hn)).2
    _ = _ := by rw [Finset.mul_sum]

private theorem integral_sqrt_div_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in Ioc a b, Real.sqrt t / t^2) = 2 / Real.sqrt a - 2 / Real.sqrt b := by
  rw [← intervalIntegral.integral_of_le hab]
  have he : (∫ t in a..b, Real.sqrt t / t^2) = ∫ t in a..b, t ^ (-(3 / 2) : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht₀ := ha.trans_le ht.1
    change Real.sqrt t / t^2 = t ^ (-(3 / 2) : ℝ)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_sub ht₀]
    norm_num
  rw [he, integral_rpow (Or.inr ⟨by norm_num, by
    rw [uIcc_of_le hab]
    exact fun h => ha.not_ge h.1⟩)]
  norm_num
  rw [Real.rpow_neg ha.le, Real.rpow_neg (ha.trans_le hab).le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  ring

/-- Abel summation of the remaining reciprocal sum, using the elementary
bound on the total von Mangoldt weight of higher prime powers. -/
private theorem reciprocal_higherPrimePowerWeight_le_of_bound {a b M : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hM : 0 ≤ M)
    (hK : ∀ t ∈ Icc a b, Chebyshev.psi t - Chebyshev.theta t ≤ M * Real.sqrt t) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, higherPrimePowerWeight n / n) ≤
      2 * M / Real.sqrt a := by
  let f (t : ℝ) := t⁻¹
  let K (t : ℝ) := Chebyshev.psi t - Chebyshev.theta t
  have ha₀ : 0 < a := zero_lt_one.trans_le ha
  have hb₀ : 0 < b := ha₀.trans_le hab
  have hf (t : ℝ) (ht : 0 < t) : HasDerivAt f (- (t^2)⁻¹) t := by
    change HasDerivAt (id⁻¹ : ℝ → ℝ) (-(t^2)⁻¹) t
    simpa only [id_eq, one_div, neg_div] using (hasDerivAt_id t).inv ht.ne'
  have hcont : ContinuousOn (deriv f) (Icc a b) := by
    apply ((continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero _ (ha₀.trans_le ht.1).ne')).neg.congr
    exact fun t ht => (hf t (ha₀.trans_le ht.1)).deriv
  have hAbel := sum_mul_eq_sub_sub_integral_mul (f := f) higherPrimePowerWeight ha₀.le hab
    (fun t ht => (hf t (ha₀.trans_le ht.1)).differentiableAt)
    (hcont.integrableOn_compact (μ := volume) isCompact_Icc)
  have hsum (t : ℝ) : (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, higherPrimePowerWeight n) = K t := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons,
      show higherPrimePowerWeight 0 = 0 from by
        rw [higherPrimePowerWeight_eq_vonMangoldt (by decide)]
        simp, zero_add, sum_higherPrimePowerWeight]
  have hAbelI : (∫ t in Ioc a b, deriv f t * K t) = -(∫ t in Ioc a b, K t / t^2) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change deriv f t * K t = -(K t / t^2)
    rw [(hf t (ha₀.trans ht.1)).deriv]
    ring
  simp_rw [hsum] at hAbel
  rw [hAbelI] at hAbel
  have hAbel' : (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, higherPrimePowerWeight n / n) =
      K b / b - K a / a + ∫ t in Ioc a b, K t / t^2 := by
    have he : (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, higherPrimePowerWeight n / n) =
        ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * higherPrimePowerWeight n :=
      Finset.sum_congr rfl (fun n _ => by unfold f; ring)
    rw [he, hAbel]
    unfold f
    ring
  have hK₀ (t : ℝ) : 0 ≤ K t := sub_nonneg.mpr (Chebyshev.theta_le_psi t)
  have hKi : IntegrableOn K (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      (Chebyshev.psi_mono.intervalIntegrable.sub Chebyshev.theta_mono.intervalIntegrable)
  have hin : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Icc a b) :=
    (continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero _ (ha₀.trans_le ht.1).ne')
  have hI : IntegrableOn (fun t => K t / t^2) (Ioc a b) := by
    simp_rw [div_eq_mul_inv]
    exact (hKi.mul_continuousOn hin isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hIs : IntegrableOn (fun t => Real.sqrt t / t^2) (Ioc a b) := by
    simp_rw [div_eq_mul_inv]
    exact ((Real.continuous_sqrt.continuousOn.mul hin).integrableOn_compact
      (μ := volume) isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hIb : (∫ t in Ioc a b, K t / t^2) ≤ M * (2 / Real.sqrt a - 2 / Real.sqrt b) := by
    rw [← integral_sqrt_div_sq ha₀ hab, ← integral_const_mul]
    refine integral_mono_ae hI (hIs.const_mul M) ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc a b) measurableSet_Ioc] with t ht
    have hh := div_le_div_of_nonneg_right (hK t ⟨ht.1.le, ht.2⟩) (sq_nonneg t)
    simpa only [mul_div_assoc] using hh
  have hKb : K b / b ≤ M / Real.sqrt b := by
    calc
      _ ≤ (M * Real.sqrt b) / b :=
        div_le_div_of_nonneg_right (hK b ⟨hab, le_rfl⟩) hb₀.le
      _ = _ := by rw [mul_div_assoc, Real.sqrt_div_self']; ring
  rw [hAbel']
  have hKa : 0 ≤ K a / a := div_nonneg (hK₀ a) ha₀.le
  change _ ≤ 2 * M / Real.sqrt a
  simp only [div_eq_mul_inv] at hKb hIb hKa ⊢
  have hpositivity : 0 ≤ M * (Real.sqrt b)⁻¹ := by positivity
  nlinarith only [hKb, hIb, hKa, hpositivity]

theorem reciprocal_higherPrimePowerWeight_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, higherPrimePowerWeight n / n) ≤
      4 * Real.log b / Real.sqrt a := by
  have hM := Real.log_nonneg (ha.trans hab)
  have h := reciprocal_higherPrimePowerWeight_le_of_bound ha hab (M := 2 * Real.log b)
    (by positivity) (fun t ht => (Chebyshev.psi_sub_theta_le (ha.trans ht.1)).trans
      (by
        have hlog := Real.log_le_log (zero_lt_one.trans_le (ha.trans ht.1)) ht.2
        nlinarith only [mul_le_mul_of_nonneg_right hlog
          (show 0 ≤ 2 * Real.sqrt t by positivity)]))
  simpa only [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using h

theorem reciprocal_higherPrimePowerWeight_le_of_log_ge_16 {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hlog : 16 ≤ Real.log a) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, higherPrimePowerWeight n / n) ≤ 8 / Real.sqrt a := by
  simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using
    reciprocal_higherPrimePowerWeight_le_of_bound ha hab (M := 4) (by norm_num)
      (fun t ht => psi_sub_theta_le_four_sqrt (ha.trans ht.1)
        (hlog.trans (Real.log_le_log (zero_lt_one.trans_le ha) ht.1)))

end GoldbachExplicit
