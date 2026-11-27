import Goldbach.Explicit.ZeroCount
import Goldbach.Explicit.ProfileLogIntegral

/-! The continuous positive density that accompanies the finite zero count. -/

open Filter MeasureTheory Set
open scoped Interval Topology
noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum

/-- The Riemann–von Mangoldt main density, extended by zero below (2π). -/
def clippedZeroDensity (t : ℝ) : ℝ :=
  (Real.log (max t (2 * Real.pi)) - Real.log (2 * Real.pi)) / (2 * Real.pi)

theorem continuous_clippedZeroDensity : Continuous clippedZeroDensity := by
  have h : Continuous (fun t : ℝ => max t (2 * Real.pi)) := continuous_id.max continuous_const
  have hp (t : ℝ) : 0 < max t (2 * Real.pi) :=
    (by positivity : 0 < 2 * Real.pi).trans_le (le_max_right _ _)
  unfold clippedZeroDensity
  exact ((h.log (fun t => (hp t).ne')).sub continuous_const).div_const _

private theorem clippedZeroDensity_eq_zero {t : ℝ} (ht : t ≤ 2 * Real.pi) :
    clippedZeroDensity t = 0 := by simp [clippedZeroDensity, max_eq_right ht]

theorem zeroCountMain_eq_integral_clippedDensity {T : ℝ} (hT : 0 ≤ T) :
    zeroCountMain T = ∫ t in (0 : ℝ)..T, clippedZeroDensity t := by
  rw [zeroCountMain_eq_integral]
  let c := 2 * Real.pi
  have hc : 0 < c := by unfold c; positivity
  rcases le_or_gt T c with ht | ht
  · rw [show max T (2 * Real.pi) = 2 * Real.pi from max_eq_right ht,
      intervalIntegral.integral_same]
    symm
    have he : (∫ t in (0 : ℝ)..T, clippedZeroDensity t) = ∫ t in (0 : ℝ)..T, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t hm
      rw [uIcc_of_le hT] at hm
      exact clippedZeroDensity_eq_zero (hm.2.trans ht)
    simpa using he
  · rw [show max T (2 * Real.pi) = T from max_eq_left ht.le]
    have hlow : (∫ t in (0 : ℝ)..c, clippedZeroDensity t) = 0 := by
      have he : (∫ t in (0 : ℝ)..c, clippedZeroDensity t) = ∫ t in (0 : ℝ)..c, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t hm
        rw [uIcc_of_le hc.le] at hm
        exact clippedZeroDensity_eq_zero hm.2
      simpa using he
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (continuous_clippedZeroDensity.intervalIntegrable 0 c)
      (continuous_clippedZeroDensity.intervalIntegrable c T), hlow, zero_add]
    apply intervalIntegral.integral_congr
    intro t hm
    rw [uIcc_of_le ht.le] at hm
    have hp : 2 * Real.pi ≤ t := hm.1
    rw [clippedZeroDensity, max_eq_left hp]

theorem zeroCountMain_hasDerivAt (t : ℝ) :
    HasDerivAt zeroCountMain (clippedZeroDensity t) t := by
  have hglobal (u : ℝ) : zeroCountMain u = ∫ s in (0 : ℝ)..u, clippedZeroDensity s := by
    by_cases hu : 0 ≤ u
    · exact zeroCountMain_eq_integral_clippedDensity hu
    have hn : u ≤ 0 := le_of_not_ge hu
    have hp : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    rw [zeroCountMain_eq_integral, max_eq_right (hn.trans hp), intervalIntegral.integral_same]
    symm
    have he : (∫ s in (0 : ℝ)..u, clippedZeroDensity s) = ∫ s in (0 : ℝ)..u, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_ge hn] at hs
      exact clippedZeroDensity_eq_zero (hs.2.trans hp)
    simpa using he
  exact (intervalIntegral.integral_hasDerivAt_right
    (continuous_clippedZeroDensity.intervalIntegrable 0 t)
    continuous_clippedZeroDensity.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_clippedZeroDensity.continuousAt).congr_of_eventuallyEq (Eventually.of_forall hglobal)

theorem zeroCountMain_zero : zeroCountMain 0 = 0 := by
  rw [zeroCountMain_eq_integral_clippedDensity le_rfl, intervalIntegral.integral_same]

/-- Adding three inside the logarithm still allows the main density
to be bounded by the exact log-square integral. -/
theorem log_mul_clippedZeroDensity_le {t : ℝ} (ht : 0 ≤ t) :
    Real.log (t + 3) * clippedZeroDensity t ≤ (Real.log t)^2 / (2 * Real.pi) := by
  let c := 2 * Real.pi
  have hc : 0 < c := by unfold c; positivity
  rcases le_or_gt t c with h | h
  · rw [clippedZeroDensity_eq_zero h, mul_zero]
    positivity
  have ht₀ : 0 < t := hc.trans h
  have hlog := Real.log_le_log hc h.le
  have hc₂ : 2 ≤ c := by unfold c; linarith [Real.pi_gt_three]
  have ht₃ : 3 ≤ t := by unfold c at h; linarith [Real.pi_gt_three]
  have hmul := mul_le_mul_of_nonneg_right hc₂ ht
  have hl : Real.log (t + 3) ≤ Real.log t + Real.log c := by
    have he := Real.log_le_log (show 0 < t + 3 by linarith)
      ((show t + 3 ≤ 2 * t by linarith).trans hmul)
    rwa [mul_comm c t, Real.log_mul ht₀.ne' hc.ne'] at he
  have hm := mul_le_mul_of_nonneg_right hl (sub_nonneg.mpr hlog)
  change Real.log (t + 3) * ((Real.log (max t c) - Real.log c) / c) ≤ (Real.log t)^2 / c
  rw [max_eq_left h.le, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by nlinarith only [hm, sq_nonneg (Real.log c)]) hc.le

end GoldbachExplicit
