import Mathlib

/-! Logarithmic moments for the envelopes used in the main spectral integral. -/

open MeasureTheory Set
noncomputable section

namespace GoldbachExplicit

private theorem exp_neg_pow_moment (k : ℕ) :
    IntegrableOn (fun s : ℝ => s^k * Real.exp (-s)) (Ioi (0 : ℝ)) ∧
      (∫ s in Ioi (0 : ℝ), s^k * Real.exp (-s)) = (k.factorial : ℝ) := by
  constructor
  · have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := 1)
      (show -1 < (k : ℝ) by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]) (by norm_num) (by norm_num)
    simpa only [Real.rpow_natCast, Real.rpow_one, one_mul, neg_mul, neg_one_mul] using h
  · have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := 1)
      (by positivity) (by norm_num)
    simpa only [add_sub_cancel_right, Real.rpow_natCast, one_mul, div_one, Real.one_rpow,
      Real.Gamma_nat_eq_factorial] using h

/-- The kth moment of the decaying exponential on the positive half-line. -/
theorem exponential_moment (k : ℕ) :
    IntegrableOn (fun s : ℝ => s^k * Real.exp (-s)) (Ioi (0 : ℝ)) ∧
      (∫ s in Ioi (0 : ℝ), s^k * Real.exp (-s)) = (k.factorial : ℝ) :=
  exp_neg_pow_moment k

/-- The inverse-square tail of the kth logarithmic moment equals k factorial. -/
theorem log_pow_div_sq_integral (k : ℕ) :
    IntegrableOn (fun t : ℝ => (Real.log t)^k / t^2) (Ioi (1 : ℝ)) ∧
      (∫ t in Ioi (1 : ℝ), (Real.log t)^k / t^2) = (k.factorial : ℝ) := by
  let f (t : ℝ) := (Real.log t)^k / t^2
  have hf (s : ℝ) : Real.exp s • f (Real.exp s) = s^k * Real.exp (-s) := by
    simp only [smul_eq_mul, f, Real.log_exp, Real.exp_neg]
    field_simp [(Real.exp_pos s).ne']
  have hI := integrableOn_comp_exp_Ioi f 0
  have h := integral_comp_exp_Ioi f 0
  simp only [hf, Real.exp_zero] at hI h
  exact ⟨hI.mp (exp_neg_pow_moment k).1, h.symm.trans (exp_neg_pow_moment k).2⟩

/-- The second logarithmic moment on the interval from zero to one. -/
theorem log_sq_integral_near_zero :
    IntegrableOn (fun t : ℝ => (Real.log t)^2) (Ioc (0 : ℝ) 1) ∧
      (∫ t in Ioc (0 : ℝ) 1, (Real.log t)^2) = 2 := by
  let e (s : ℝ) := Real.exp (-s)
  have himage : e '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs)⟩
    · intro ht
      refine ⟨-Real.log t, neg_pos.mpr (Real.log_neg ht.1 ht.2), ?_⟩
      exact by simp only [e, neg_neg, Real.exp_log ht.1]
  have he : InjOn e (Ioi (0 : ℝ)) := by
    intro s _ t _ h
    exact neg_injective (Real.exp_injective h)
  have hd (s : ℝ) (_ : s ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt e (-Real.exp (-s)) (Ioi (0 : ℝ)) s := by
    simpa only [e, Pi.neg_apply, id_eq, mul_neg, mul_one] using
      ((hasDerivAt_id s).neg.exp).hasDerivWithinAt (s := Ioi (0 : ℝ))
  have hf (s : ℝ) :
      |-Real.exp (-s)| • (Real.log (e s))^2 = s^2 * Real.exp (-s) := by
    simp only [e, abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul, Real.log_exp, neg_sq]
    ring
  have hI := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd he
    (fun t => (Real.log t)^2)
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd he
    (fun t => (Real.log t)^2)
  simp only [himage, hf] at hI h
  refine ⟨(integrableOn_Ioc_iff_integrableOn_Ioo (μ := volume)).mpr (hI.mpr (exp_neg_pow_moment 2).1), ?_⟩
  rw [integral_Ioc_eq_integral_Ioo, h]
  simpa [Nat.factorial] using (exp_neg_pow_moment 2).2

/-- The normalized profile's leading term depends only on its exact mass.
The logarithmic errors follow from the constant and reciprocal-square envelopes. -/
theorem integral_log_sq_le_of_envelope {f : ℝ → ℝ} (hf : Measurable f)
    (hfi : IntegrableOn f (Ioi (0 : ℝ))) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf₀ : ∀ t > 0, 0 ≤ f t) (hf₁ : ∀ t > 0, f t ≤ C)
    (hf₂ : ∀ t > 0, f t ≤ 4 * C / t^2) :
    IntegrableOn (fun t => f t * (B + Real.log t)^2) (Ioi (0 : ℝ)) ∧
      (∫ t in Ioi (0 : ℝ), f t * (B + Real.log t)^2) ≤
        B^2 * (∫ t in Ioi (0 : ℝ), f t) + C * (8 * B + 10) := by
  let J := Ioc (0 : ℝ) 1
  let K := Ioi (1 : ℝ)
  let F (t : ℝ) := f t * (B + Real.log t)^2
  let P (t : ℝ) := B^2 * f t
  let Q (t : ℝ) := (8 * B * C) * (Real.log t / t^2)
  let R (t : ℝ) := (4 * C) * ((Real.log t)^2 / t^2)
  let U (t : ℝ) := C * (Real.log t)^2
  have hjk : J ∪ K = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi (by norm_num)
  have hd : Disjoint J K := Set.disjoint_left.mpr (fun _ ht₁ ht₂ => ht₂.not_ge ht₁.2)
  have hfj : IntegrableOn f J := hfi.mono_set (fun _ ht => ht.1)
  have hfk : IntegrableOn f K := hfi.mono_set (fun _ ht => mem_Ioi.mpr ((zero_lt_one : (0 : ℝ) < 1).trans (mem_Ioi.mp ht)))
  have hpj : IntegrableOn P J := hfj.const_mul _
  have hpk : IntegrableOn P K := hfk.const_mul _
  have hQ : IntegrableOn Q K := by
    change Integrable (fun t : ℝ => (8 * B * C) * (Real.log t / t^2)) (volume.restrict (Ioi 1))
    simpa only [pow_one] using (log_pow_div_sq_integral 1).1.const_mul (8 * B * C)
  have hR : IntegrableOn R K := (log_pow_div_sq_integral 2).1.const_mul (4 * C)
  have hU : IntegrableOn U J := log_sq_integral_near_zero.1.const_mul C
  have hF : Measurable F := hf.mul ((measurable_const.add Real.measurable_log).pow_const 2)
  have hleJ (t : ℝ) (ht : t ∈ J) : F t ≤ P t + U t := by
    have hl := Real.log_nonpos ht.1.le ht.2
    have hc := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hB (hf₀ t ht.1)) hl
    have hh := mul_le_mul_of_nonneg_right (hf₁ t ht.1) (sq_nonneg (Real.log t))
    dsimp [F, P, U]
    nlinarith only [hc, hh]
  have hleK (t : ℝ) (ht : t ∈ K) : F t ≤ P t + Q t + R t := by
    have hp : 0 < t := zero_lt_one.trans ht
    have hl := Real.log_nonneg ht.le
    have hq := mul_le_mul_of_nonneg_right (hf₂ t hp)
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB) hl)
    have hr := mul_le_mul_of_nonneg_right (hf₂ t hp) (sq_nonneg (Real.log t))
    dsimp [F, P, Q, R]
    simp only [div_eq_mul_inv] at hq hr ⊢
    nlinarith only [hq, hr]
  have hFj : IntegrableOn F J := by
    refine (hpj.add hU).mono' hF.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    have hn : 0 ≤ F t := mul_nonneg (hf₀ t ht.1) (sq_nonneg _)
    simpa only [Real.norm_of_nonneg hn, Pi.add_apply] using hleJ t ht
  have hFk : IntegrableOn F K := by
    refine ((hpk.add hQ).add hR).mono' hF.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    have hn : 0 ≤ F t := mul_nonneg (hf₀ t (zero_lt_one.trans ht)) (sq_nonneg _)
    simpa only [Real.norm_of_nonneg hn, Pi.add_apply] using hleK t ht
  refine ⟨by rw [← hjk]; exact hFj.union hFk, ?_⟩
  change (∫ t in Ioi (0 : ℝ), F t) ≤ _
  rw [← hjk, setIntegral_union hd measurableSet_Ioi hFj hFk,
    setIntegral_union hd measurableSet_Ioi hfj hfk]
  have hJle := integral_mono_ae hFj (hpj.add hU)
    ((ae_restrict_mem (μ := volume) (s := J) measurableSet_Ioc).mono hleJ)
  have hKle := integral_mono_ae hFk ((hpk.add hQ).add hR)
    ((ae_restrict_mem (μ := volume) (s := K) measurableSet_Ioi).mono hleK)
  simp only [Pi.add_apply] at hJle hKle
  rw [integral_add hpj hU] at hJle
  have hPK : IntegrableOn (fun t => P t + Q t) K := hpk.add hQ
  rw [integral_add hPK hR, integral_add hpk hQ] at hKle
  have hq : (∫ t in K, Q t) = 8 * B * C := by
    rw [show (∫ t in K, Q t) = (8 * B * C) * ∫ t in Ioi (1 : ℝ), Real.log t / t^2
      from integral_const_mul _ _]
    have h := (log_pow_div_sq_integral 1).2
    norm_num [Nat.factorial] at h
    rw [h, mul_one]
  have hr : (∫ t in K, R t) = 4 * C * 2 := by
    unfold R K
    rw [integral_const_mul, (log_pow_div_sq_integral 2).2]
    norm_num [Nat.factorial]
  have hu : (∫ t in J, U t) = C * 2 := by
    unfold U J
    rw [integral_const_mul, log_sq_integral_near_zero.2]
  rw [hq, hr] at hKle
  rw [hu] at hJle
  simp only [P, integral_const_mul] at hJle hKle
  nlinarith only [hJle, hKle]

end GoldbachExplicit
