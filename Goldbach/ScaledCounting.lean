import Goldbach.LocalDensity
import Goldbach.CumulativeZeros

open Filter MeasureTheory Set
open scoped BigOperators Topology Interval
noncomputable section

namespace GoldbachSpectrum

open GoldbachZeros Zeta23

/-- Mass on a positive half-open interval after scaling the ordinates by the height. -/
def scaledCount (T a b : ℝ) : ℝ := (Ncount (a * T) (b * T) : ℝ) / (T * Real.log T)

/-- Integral of a test against the normalized zero masses on a positive compact window. -/
def scaledWindowTest (T a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∑ ρ ∈ zeroWindow (a * T) (b * T), multiplicity ρ * f (ordinate ρ / T)) /
    (T * Real.log T)

private theorem scaledWindowTest_by_parts {T a b : ℝ} (hT : 0 < T)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    scaledWindowTest T a b f =
      f b * scaledCount T a b - ∫ u in Ioc a b, deriv f u * scaledCount T a u := by
  classical
  let W := zeroWindow (a * T) (b * T)
  let Q (u : ℝ) : ℝ := Ncount (a * T) (u * T)
  let H (ρ : Zeros) := (Ici (ordinate ρ / T)).indicator (deriv f)
  have hc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hi : IntegrableOn (deriv f) (Ioc a b) :=
    (hc.continuousOn.integrableOn_compact (μ := volume) isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hterm (ρ : Zeros) :
      IntegrableOn (fun u => multiplicity ρ * H ρ u) (Ioc a b) :=
    (hi.indicator measurableSet_Ici).const_mul _
  have hsum (u : ℝ) (hu : u ∈ Ioc a b) :
      deriv f u * Q u = ∑ ρ ∈ W, multiplicity ρ * H ρ u := by
    have he : zeroWindow (a * T) (u * T) = W.filter (fun ρ => ordinate ρ / T ≤ u) := by
      ext ρ
      simp only [Finset.mem_filter, W, mem_zeroWindow, div_le_iff₀ hT]
      constructor
      · intro h
        exact ⟨⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right hu.2 hT.le)⟩, h.2⟩
      · intro h
        exact ⟨h.1.1, h.2⟩
    dsimp only [Q]
    rw [Ncount_eq_sum_zeroWindow, he, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ _
    by_cases hz : ordinate ρ / T ≤ u
    · simp only [if_pos hz, H, indicator_of_mem (show u ∈ Ici (ordinate ρ / T) from hz)]
      ring
    · simp only [if_neg hz, H, indicator_of_notMem (show u ∉ Ici (ordinate ρ / T) from hz), mul_zero]
  have hterm_eval (ρ : Zeros) (hρ : ρ ∈ W) :
      (∫ u in Ioc a b, multiplicity ρ * H ρ u) =
        multiplicity ρ * (f b - f (ordinate ρ / T)) := by
    have hw := mem_zeroWindow.mp hρ
    let x := ordinate ρ / T
    have hx₁ : a < x := (lt_div_iff₀ hT).mpr hw.1
    have hx₂ : x ≤ b := (div_le_iff₀ hT).mpr hw.2
    have hset : Ici x ∩ Ioc a b = Icc x b := by
      ext u
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hx₁.trans_le h.1, h.2⟩⟩
    dsimp only [H]
    rw [integral_const_mul, integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici, hset, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hx₂]
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun y _ => hf.differentiable (by norm_num) y) (hc.intervalIntegrable _ _)]
  have hI : (∫ u in Ioc a b, deriv f u * Q u) =
      (∑ ρ ∈ W, multiplicity ρ) * f b - ∑ ρ ∈ W, multiplicity ρ * f (ordinate ρ / T) := by
    calc
      _ = ∫ u in Ioc a b, ∑ ρ ∈ W, multiplicity ρ * H ρ u :=
        setIntegral_congr_fun measurableSet_Ioc hsum
      _ = ∑ ρ ∈ W, ∫ u in Ioc a b, multiplicity ρ * H ρ u :=
        integral_finsetSum W (fun ρ _ => hterm ρ)
      _ = ∑ ρ ∈ W, multiplicity ρ * (f b - f (ordinate ρ / T)) :=
        Finset.sum_congr rfl hterm_eval
      _ = _ := by simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  let D := T * Real.log T
  have hd (u : ℝ) : deriv f u * scaledCount T a u = (deriv f u * Q u) * D⁻¹ := by
    unfold scaledCount Q D
    rw [div_eq_mul_inv, mul_assoc]
  simp_rw [hd, integral_mul_const]
  unfold scaledWindowTest scaledCount
  rw [hI, Ncount_eq_sum_zeroWindow]
  change _ / D = f b * (_ / D) - _ 
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- Convergence on a compact positive window with a continuously differentiable
test. Partial summation reduces the assertion to the cumulative counting limit. -/
theorem scaledWindowTest_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Tendsto (fun T : ℝ => scaledWindowTest T a b f) atTop
      (𝓝 ((∫ u in Ioc a b, f u) / (2 * Real.pi))) := by
  let J := Ioc a b
  let μ : Measure ℝ := volume.restrict J
  let K := (b - a) / (2 * Real.pi) + 1
  have hcount : Tendsto (fun T : ℝ => scaledCount T a b) atTop
      (𝓝 ((b - a) / (2 * Real.pi))) := scaled_positive_window_tendsto ha hab
  have hevent : ∀ᶠ T : ℝ in atTop, scaledCount T a b ≤ K :=
    (hcount.eventually (gt_mem_nhds (show (b - a) / (2 * Real.pi) < K by dsimp [K]; linarith))).mono
      (fun _ h => h.le)
  have hd : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hi : Integrable (deriv f) μ :=
    (hd.continuousOn.integrableOn_compact (μ := volume) isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hconv : Tendsto (fun T : ℝ => ∫ u in J, deriv f u * scaledCount T a u) atTop
      (𝓝 (∫ u in J, deriv f u * ((u - a) / (2 * Real.pi)))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (fun u => K * ‖deriv f u‖)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hm : Monotone (fun u : ℝ => (Ncount (a * T) (u * T) : ℝ)) := fun u v huv => by
        change (Ncount (a * T) (u * T) : ℝ) ≤ (Ncount (a * T) (v * T) : ℝ)
        exact_mod_cast Ncount_mono (a := a * T) (c := a * T) le_rfl
          (mul_le_mul_of_nonneg_right huv hT.le)
      exact (hd.measurable.mul (hm.measurable.div_const _)).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (1 : ℝ), hevent] with T hT hTB
      filter_upwards [ae_restrict_mem (μ := volume) (s := J) measurableSet_Ioc] with u hu
      have hdp := mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)
      have h0 : 0 ≤ scaledCount T a u := div_nonneg (Nat.cast_nonneg _) hdp.le
      have hub : scaledCount T a u ≤ scaledCount T a b := by
        apply div_le_div_of_nonneg_right _ hdp.le
        exact_mod_cast Ncount_mono (a := a * T) (c := a * T) le_rfl
          (mul_le_mul_of_nonneg_right hu.2 (zero_lt_one.trans hT).le)
      rw [norm_mul, Real.norm_of_nonneg h0, mul_comm K]
      exact mul_le_mul_of_nonneg_left (hub.trans hTB) (norm_nonneg _)
    · exact hi.norm.const_mul _
    · filter_upwards [ae_restrict_mem (μ := volume) (s := J) measurableSet_Ioc] with u hu
      exact (scaled_positive_window_tendsto ha (le_of_lt hu.1)).const_mul (deriv f u)
  have hh (u : ℝ) : HasDerivAt (fun x : ℝ => f x * ((x - a) / (2 * Real.pi)))
      (deriv f u * ((u - a) / (2 * Real.pi)) + f u / (2 * Real.pi)) u := by
    have h : HasDerivAt (fun x : ℝ => (x - a) / (2 * Real.pi)) (1 / (2 * Real.pi)) u :=
      ((hasDerivAt_id u).sub_const a).div_const _
    simpa only [mul_one_div] using ((hf.differentiable (by norm_num) u).hasDerivAt.fun_mul h)
  have hc₁ : Continuous (fun x => deriv f x * ((x - a) / (2 * Real.pi))) := hd.mul (by fun_prop)
  have hc₂ : Continuous (fun x => f x / (2 * Real.pi)) := hf.continuous.div_const _
  have hi₁ : IntegrableOn (fun x => deriv f x * ((x - a) / (2 * Real.pi))) (Ioc a b) :=
    (hc₁.continuousOn.integrableOn_compact (μ := volume) isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hi₂ : IntegrableOn (fun x => f x / (2 * Real.pi)) (Ioc a b) :=
    (hc₂.continuousOn.integrableOn_compact (μ := volume) isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hh u) ((hc₁.add hc₂).intervalIntegrable a b)
  rw [intervalIntegral.integral_of_le hab, integral_add hi₁ hi₂, sub_self, zero_div, mul_zero,
    sub_zero] at hFTC
  have h := (hcount.const_mul (f b)).sub hconv
  have he : (∫ u in J, f u) / (2 * Real.pi) = ∫ u in J, f u / (2 * Real.pi) := by
    simp_rw [div_eq_mul_inv]
    exact (integral_mul_const _ _).symm
  have hconst : f b * ((b - a) / (2 * Real.pi)) -
      (∫ u in J, deriv f u * ((u - a) / (2 * Real.pi))) =
      (∫ u in J, f u) / (2 * Real.pi) := by
    rw [he]
    change f b * ((b - a) / (2 * Real.pi)) - (∫ u in Ioc a b, deriv f u * ((u - a) / (2 * Real.pi))) = _
    linarith only [hFTC]
  rw [hconst] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact (scaledWindowTest_by_parts hT hf).symm

end GoldbachSpectrum
