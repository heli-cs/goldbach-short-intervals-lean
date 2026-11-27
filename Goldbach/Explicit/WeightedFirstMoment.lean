import Goldbach.Explicit.WeightedVariation
import Goldbach.LogIntegral
import Goldbach.PrimeIntegral

/-! The passage from a pointwise error for theta to the weighted first moment. -/

open MeasureTheory Set
noncomputable section

namespace GoldbachExplicit

/-- Translation of the zero-extended reflected weight bounds the first moment
by twice a uniform error for theta over the union of the two windows. -/
theorem weighted_firstMoment_abs_le {V x A d E : ℝ}
    (hV : 0 < V) (hA : 2 ≤ A) (hAx : A ≤ x / 2) (hd : 0 < d) (hE : 0 ≤ E)
    (hθ : ∀ t ∈ Icc A ((1 + d) * (x - A)), |Chebyshev.theta t - t| ≤ E) :
    |∫ y in Icc A (x - A), reflectedWeight V x y * (GoldbachConcrete.density d y - 1)| ≤ 2 * E := by
  let a := Real.log A
  let b := Real.log (x - A)
  let lam := Real.log (1 + d)
  let J := Icc a b
  let w := reflectedWeight V x
  let q := trimmedLogWeight V x A
  let D (s : ℝ) := Chebyshev.theta (Real.exp s) - Real.exp s
  have hA₀ : 0 < A := by linarith
  have hB₀ : 0 < x - A := by linarith
  have hd₁ : 0 < 1 + d := by linarith
  have hlam : 0 ≤ lam := Real.log_nonneg (by linarith)
  have hlamd : lam ≤ d := by
    simpa only [lam, add_sub_cancel_left] using Real.log_le_sub_one_of_pos hd₁
  have hexp (s : ℝ) : Real.exp (s + lam) = (1 + d) * Real.exp s := by
    rw [Real.exp_add, show Real.exp lam = 1 + d from Real.exp_log hd₁, mul_comm]
  have hmem (s : ℝ) : Real.exp s ∈ Icc A (x - A) ↔ s ∈ J := by
    have ha : Real.exp a = A := Real.exp_log hA₀
    have hb : Real.exp b = x - A := Real.exp_log hB₀
    exact ⟨fun h => ⟨Real.exp_le_exp.mp (ha.symm ▸ h.1), Real.exp_le_exp.mp (hb.symm ▸ h.2)⟩,
      fun h => ⟨ha ▸ Real.exp_le_exp.mpr h.1, hb ▸ Real.exp_le_exp.mpr h.2⟩⟩
  have hq (s : ℝ) : q s = J.indicator (fun t => w (Real.exp t)) s := by
    change (Icc A (x - A)).indicator w (Real.exp s) = _
    by_cases hs : s ∈ J
    · rw [indicator_of_mem ((hmem s).2 hs), indicator_of_mem hs]
    · rw [indicator_of_notMem (fun ht => hs ((hmem s).1 ht)), indicator_of_notMem hs]
  have hqj (s : ℝ) (hs : s ∈ J) : q s = w (Real.exp s) := by
    rw [hq, indicator_of_mem hs]
  have hq₀ (s : ℝ) (hs : s ∉ J) : q s = 0 := by
    rw [hq, indicator_of_notMem hs]
  have hw : Measurable w := by
    have hlog : Measurable (fun y : ℝ => Real.log (x / min y (x - y))) :=
      (measurable_const.div (measurable_id.min (measurable_const.sub measurable_id))).log
    exact (continuous_cosineWeight hV).measurable.comp hlog
  have hD : Measurable D :=
    (Chebyshev.theta_mono.measurable.comp Real.continuous_exp.measurable).sub Real.continuous_exp.measurable
  have hD₀ (s : ℝ) (hs : s ∈ J) : |D s| ≤ E := by
    have ht := (hmem s).2 hs
    exact hθ _ ⟨ht.1, ht.2.trans (by nlinarith [mul_nonneg hd.le hB₀.le])⟩
  have hD₁ (s : ℝ) (hs : s ∈ J) : |D (s + lam)| ≤ E := by
    have ht := (hmem s).2 hs
    apply hθ
    rw [hexp]
    exact ⟨ht.1.trans (by nlinarith [mul_nonneg hd.le (Real.exp_pos s).le]),
      mul_le_mul_of_nonneg_left ht.2 hd₁.le⟩
  have hqi (f : ℝ → ℝ) (hf : Measurable f) (hfE : ∀ s ∈ J, |f s| ≤ E) :
      Integrable (fun s => q s * f s) := by
    have he : (fun s => q s * f s) = J.indicator (fun s => w (Real.exp s) * f s) := by
      funext s
      by_cases hs : s ∈ J
      · rw [hqj s hs, indicator_of_mem hs]
      · rw [hq₀ s hs, zero_mul, indicator_of_notMem hs]
    rw [he, integrable_indicator_iff measurableSet_Icc]
    have hc : IntegrableOn (fun _ : ℝ => E) J := integrableOn_const measure_Icc_lt_top.ne
    refine hc.mono' ((hw.comp Real.continuous_exp.measurable).mul hf).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := J) measurableSet_Icc] with s hs
    have hw₀ : 0 ≤ w (Real.exp s) := cosineWeight_nonneg hV _
    rw [norm_mul, Real.norm_eq_abs (w (Real.exp s)), Real.norm_eq_abs (f s),
      abs_of_nonneg hw₀]
    exact (mul_le_of_le_one_left (abs_nonneg _) (cosineWeight_le_one hV _)).trans (hfE s hs)
  have hi₀ := hqi D hD hD₀
  have hi₁ := hqi (fun s => D (s + lam)) (hD.comp (measurable_id.add_const _)) hD₁
  have hsweep : (∫ s, q s * D (s + lam)) = ∫ s, q (s - lam) * D s := by
    simpa only [add_sub_cancel_right] using
      integral_add_right_eq_self (fun s => q (s - lam) * D s) lam
  have hi_shift : Integrable (fun s => q (s - lam) * D s) := by
    convert hi₁.comp_sub_right lam using 1
    funext s
    simp
  have hform :
      (∫ y in Icc A (x - A), w y * (GoldbachConcrete.density d y - 1)) =
      (∫ s, (q (s - lam) - q s) * D s) / d := by
    calc
      _ = ∫ y in Icc A (x - A),
          (q (Real.log y) * (D (Real.log y + lam) - D (Real.log y)) / d) / y := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro y hy
        have hy₀ : 0 < y := hA₀.trans_le hy.1
        have hyJ : Real.log y ∈ J := (hmem _).1 (by simpa only [Real.exp_log hy₀] using hy)
        change w y * (GoldbachConcrete.density d y - 1) =
          q (Real.log y) * (D (Real.log y + lam) - D (Real.log y)) / d / y
        rw [GoldbachConcrete.density_eq_theta_sub hd (hA.trans hy.1), hqj _ hyJ]
        dsimp [D]
        rw [hexp, Real.exp_log hy₀]
        field_simp <;> ring
      _ = ∫ s in J, q s * (D (s + lam) - D s) / d :=
        GoldbachLogIntegral.integral_log_change hA₀ hB₀
          (fun s => q s * (D (s + lam) - D s) / d)
      _ = (∫ s, q s * (D (s + lam) - D s)) / d := by
        rw [integral_div]
        congr 1
        exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun s hs => by rw [hq₀ _ hs, zero_mul])
      _ = (∫ s, (q (s - lam) - q s) * D s) / d := by
        simp_rw [mul_sub, sub_mul]
        rw [integral_sub hi₁ hi₀, integral_sub hi_shift hi₀, hsweep]
  obtain ⟨hvarI, hvar⟩ := trimmed_log_weight_translation_le hV hA₀ hAx hlam
  have hdom (s : ℝ) : |(q (s - lam) - q s) * D s| ≤ |q (s - lam) - q s| * E := by
    rw [abs_mul]
    by_cases hs : s ∈ J
    · exact mul_le_mul_of_nonneg_left (hD₀ s hs) (abs_nonneg _)
    by_cases ht : s - lam ∈ J
    · have h := hD₁ _ ht
      rw [sub_add_cancel] at h
      exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    rw [hq₀ _ hs, hq₀ _ ht]
    simp
  have hI : Integrable (fun s => (q (s - lam) - q s) * D s) := by
    simpa only [sub_mul, Pi.sub_def] using hi_shift.sub hi₀
  rw [hform, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  calc
    _ ≤ ∫ s, |(q (s - lam) - q s) * D s| := abs_integral_le_integral_abs
    _ ≤ ∫ s, |q (s - lam) - q s| * E := integral_mono hI.abs (hvarI.mul_const E) hdom
    _ ≤ 2 * E * d := by
      rw [integral_mul_const]
      calc
        _ ≤ (2 * lam) * E := mul_le_mul_of_nonneg_right hvar hE
        _ = (2 * E) * lam := by ring
        _ ≤ (2 * E) * d := mul_le_mul_of_nonneg_left hlamd (by positivity)

end GoldbachExplicit
