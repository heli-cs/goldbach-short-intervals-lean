import Goldbach.Explicit.Reflection
import Goldbach.Explicit.NumericalBounds

/-! Integration of the quadratic lower envelope for the reflected kernel. -/

open MeasureTheory Set
open scoped Interval
noncomputable section

namespace GoldbachExplicit

private theorem integral_log_ratio_sq_upper {x A : ℝ} (hA : 0 < A) (hAx : A ≤ x / 2) :
    (∫ y in A..(x / 2), (Real.log (x / y))^2) ≤
      x / 2 * ((Real.log 2)^2 + 2 * Real.log 2 + 2) := by
  have hx : 0 < x := by linarith
  let L (y : ℝ) := Real.log (x / y)
  let P (y : ℝ) := y * (L y ^ 2 + 2 * L y + 2)
  have hLog (y : ℝ) (hy : 0 < y) : HasDerivAt L (-y⁻¹) y := by
    have he : (fun t : ℝ => Real.log x - Real.log t) =ᶠ[nhds y] L := by
      filter_upwards [Ioi_mem_nhds hy] with t ht
      exact (Real.log_div hx.ne' (ne_of_gt ht)).symm
    exact ((Real.hasDerivAt_log hy.ne').const_sub (Real.log x)).congr_of_eventuallyEq he.symm
  have hP (y : ℝ) (hy : 0 < y) : HasDerivAt P (L y ^ 2) y := by
    have hl := hLog y hy
    have h := (hasDerivAt_id y).mul (((hl.pow 2).add (hl.const_mul 2)).add_const 2)
    convert h using 1 <;> first | rfl | (simp only [id_eq, Pi.add_apply, Pi.pow_apply]; field_simp [hy.ne']; ring)
  have hI : IntervalIntegrable (fun y => L y ^ 2) volume A (x / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hAx]
    refine ((continuousOn_const.div continuousOn_id (fun y hy => (hA.trans_le hy.1).ne')).log ?_).pow 2
    intro y hy
    exact (div_pos hx (hA.trans_le hy.1)).ne'
  rw [show (∫ y in A..(x / 2), L y ^ 2) = P (x / 2) - P A from
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy =>
      hP y (hA.trans_le ((uIcc_of_le hAx ▸ hy).1))) hI]
  have hh : L (x / 2) = Real.log 2 := by
    unfold L
    congr 1
    field_simp
  have hP₀ : 0 ≤ P A := by
    have hL₀ : 0 ≤ L A := Real.log_nonneg ((one_le_div hA).mpr (by linarith))
    dsimp [P]
    positivity
  dsimp [P] at *
  rw [hh]
  linarith

/-- The exact cosine kernel loses at most the integrated quadratic term
on the symmetric trimmed interval. -/
theorem reflected_weight_mass_ge {V x A : ℝ} (hV : 0 < V) (hA : 0 < A)
    (hAx : A ≤ x / 2) :
    x - 2 * A - (Real.pi^2 / (2 * V^2)) *
        (x * ((Real.log 2)^2 + 2 * Real.log 2 + 2)) ≤
      ∫ y in Icc A (x - A), reflectedWeight V x y := by
  let w := reflectedWeight V x
  let q (y : ℝ) := (Real.log (x / y))^2
  let C := Real.pi^2 / (2 * V^2)
  have hx : 0 < x := by linarith
  have hAB : A ≤ x - A := by linarith
  have hMB : x / 2 ≤ x - A := by linarith
  have hW : Measurable w := by
    have hm : Measurable (fun y : ℝ => Real.log (x / min y (x - y))) :=
      (measurable_const.div (measurable_id.min (measurable_const.sub measurable_id))).log
    exact (continuous_cosineWeight hV).measurable.comp hm
  have hwi : IntegrableOn w (Icc A (x - A)) := by
    have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc A (x - A)) :=
      integrableOn_const measure_Icc_lt_top.ne
    refine hi.mono' hW.aestronglyMeasurable ?_
    filter_upwards with y
    have hw₀ : 0 ≤ w y := cosineWeight_nonneg hV _
    rw [Real.norm_of_nonneg hw₀]
    exact cosineWeight_le_one hV _
  have hwl : IntervalIntegrable w volume A (x / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAx]
    exact hwi.mono_set (fun y hy => ⟨hy.1.le, hy.2.trans hMB⟩)
  have hwr : IntervalIntegrable w volume (x / 2) (x - A) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hMB]
    exact hwi.mono_set (fun y hy => ⟨hAx.trans hy.1.le, hy.2⟩)
  have hsym : (∫ y in (x / 2)..(x - A), w y) = ∫ y in A..(x / 2), w y := by
    have h := intervalIntegral.integral_comp_sub_left (a := A) (b := x / 2) w x
    simpa only [w, reflectedWeight_reflect, show x - x / 2 = x / 2 by ring] using h.symm
  have hqi : IntervalIntegrable q volume A (x / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hAx]
    refine ((continuousOn_const.div continuousOn_id (fun y hy => (hA.trans_le hy.1).ne')).log ?_).pow 2
    intro y hy
    exact (div_pos hx (hA.trans_le hy.1)).ne'
  have hc₀ : 0 ≤ C := by dsimp [C]; positivity
  have henv : (∫ y in A..(x / 2), 1 - C * q y) ≤ ∫ y in A..(x / 2), w y := by
    refine intervalIntegral.integral_mono_on hAx (intervalIntegrable_const.sub (hqi.const_mul C)) hwl ?_
    intro y hy
    have hmin : min y (x - y) = y := min_eq_left (by linarith [hy.2])
    change 1 - C * q y ≤ cosineWeight V (Real.log (x / min y (x - y)))
    rw [hmin]
    simpa only [C, q, div_mul_eq_mul_div] using cosineWeight_quadratic hV (Real.log (x / y))
  have hmain := integral_log_ratio_sq_upper hA hAx
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hqi.const_mul C),
    intervalIntegral.integral_const_mul] at henv
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at henv
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hAB,
    ← intervalIntegral.integral_add_adjacent_intervals hwl hwr, hsym]
  nlinarith only [henv, mul_le_mul_of_nonneg_left hmain hc₀]

end GoldbachExplicit
