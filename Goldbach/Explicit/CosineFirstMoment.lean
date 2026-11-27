import Goldbach.Explicit.CosineRegularity

/-! Integrals of the cosine weight and the coefficient in Abel summation. -/

open MeasureTheory Set
open scoped Interval
noncomputable section

namespace GoldbachExplicit

private theorem integral_unit_cosine_moment :
    (∫ s in (0 : ℝ)..1, s * unitCosineWeight s) = 1 / Real.pi^2 := by
  let F (s : ℝ) := ((s - s^2) / Real.pi + 3 / Real.pi^3) * Real.sin (Real.pi * s) +
    (1 - 3 * s) / Real.pi^2 * Real.cos (Real.pi * s)
  have hd (s : ℝ) : HasDerivAt F (s * unitCosineWeight s) s := by
    have ht := (hasDerivAt_id s).const_mul Real.pi
    have h₁ := ((((hasDerivAt_id s).sub (hasDerivAt_pow 2 s)).div_const Real.pi).add_const
      (3 / Real.pi^3)).mul ht.sin
    have h₂ := ((((hasDerivAt_id s).const_mul 3).const_sub 1).div_const (Real.pi^2)).mul ht.cos
    convert h₁.add h₂ using 1 <;> first | rfl | (funext z; rfl) |
      (simp only [unitCosineWeight, id_eq, Pi.sub_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one];
        field_simp [Real.pi_ne_zero] <;> ring)
  have hi : Continuous (fun s => s * unitCosineWeight s) := by unfold unitCosineWeight; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hi.intervalIntegrable _ _)]
  simp only [F, pow_zero, pow_one, one_pow, sub_self, zero_div, zero_add, mul_zero, Real.sin_pi,
    Real.cos_pi, mul_one]
  norm_num <;> ring

/-- First moment of the cosine weight on its positive support. -/
theorem integral_cosineWeight_first_moment {V : ℝ} (hV : 0 < V) :
    (∫ s in (0 : ℝ)..V, s * cosineWeight V s) = V^2 / Real.pi^2 := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun s => s * cosineWeight V s) V
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  rw [← h]
  have he :
      (∫ s in (0 : ℝ)..1, V * s * cosineWeight V (V * s)) =
        V * (∫ s in (0 : ℝ)..1, s * unitCosineWeight s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hu : V * s ≤ V := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hs.2 hV.le
    have hn : 0 ≤ V * s := mul_nonneg hV.le hs.1
    change V * s * cosineWeight V (V * s) = V * (s * unitCosineWeight s)
    rw [cosineWeight, abs_of_nonneg hn, if_pos hu, mul_comm V s, mul_div_cancel_right₀ _ hV.ne']
    ring
  rw [he, integral_unit_cosine_moment]
  ring

/-- Positive part of the log-coordinate coefficient in Abel summation. -/
def cosineAbelWeight (V s : ℝ) : ℝ :=
  max 0 (s * cosineWeight V s - deriv (fun u => u * cosineWeight V u) s)

theorem continuous_cosineAbelWeight {V : ℝ} (hV : 0 < V) :
    Continuous (cosineAbelWeight V) := by
  have h : ContDiff ℝ 2 (fun s => s * cosineWeight V s) :=
    contDiff_id.mul (contDiff_two_cosineWeight hV)
  unfold cosineAbelWeight
  exact continuous_const.max (h.continuous.sub (h.continuous_deriv (by norm_num)))

private theorem derivative_mul_cosineWeight {V s : ℝ} (hV : 0 < V) (hs : s ∈ Icc 0 V) :
    deriv (fun u => u * cosineWeight V u) s =
      cosineWeight V s - s * (Real.pi * (1 - s / V) * Real.sin (Real.pi * (s / V))) / V := by
  have hd := (hasDerivAt_id s).mul (cosineWeight_hasDerivAt_on hV hs)
  change deriv (id * cosineWeight V) s = _
  rw [hd.deriv]
  simp only [id_eq, one_mul]
  ring

private theorem derivative_deficit_nonpos {V s : ℝ} (hV : 0 < V) (hs : s ∈ Icc 0 V) :
    deriv (fun u => u * cosineWeight V u) s - s * cosineWeight V s ≤ max 0 (1 - s) := by
  have hs₀ : 0 ≤ s := hs.1
  have harg : Real.pi * (s / V) ≤ Real.pi := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ((div_le_one hV).mpr hs.2) Real.pi_pos.le
  have hsin : 0 ≤ Real.sin (Real.pi * (s / V)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) harg
  have hnon : 0 ≤ s * (Real.pi * (1 - s / V) * Real.sin (Real.pi * (s / V))) / V := by
    have ht : 0 ≤ 1 - s / V := sub_nonneg.mpr ((div_le_one hV).mpr hs.2)
    positivity
  rw [derivative_mul_cosineWeight hV hs]
  rcases le_or_gt s 1 with h | h
  · rw [max_eq_right (sub_nonneg.mpr h)]
    nlinarith only [hnon, mul_le_of_le_one_right (sub_nonneg.mpr h) (cosineWeight_le_one hV s)]
  · rw [max_eq_left (sub_nonpos.mpr h.le)]
    nlinarith only [hnon, mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h.le)
      (cosineWeight_nonneg hV s)]

/-- The unweighted positive-part integral in Abel summation. -/
theorem integral_cosineAbelWeight_le {V : ℝ} (hV : 1 ≤ V) :
    (∫ s in (0 : ℝ)..V, cosineAbelWeight V s) ≤ V^2 / Real.pi^2 + 1 / 2 := by
  let A (s : ℝ) := s * cosineWeight V s
  let C (s : ℝ) := max 0 (1 - s)
  have hV₀ : 0 < V := zero_lt_one.trans_le hV
  have hA : ContDiff ℝ 2 A := contDiff_id.mul (contDiff_two_cosineWeight hV₀)
  have hD : IntervalIntegrable (deriv A) volume 0 V :=
    (hA.continuous_deriv (by norm_num)).intervalIntegrable _ _
  have hC : Continuous C := by unfold C; fun_prop
  have hC₁ : (∫ s in (0 : ℝ)..1, C s) = 1 / 2 := by
    have he : (∫ s in (0 : ℝ)..1, C s) = ∫ s in (0 : ℝ)..1, 1 - s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      exact max_eq_right (sub_nonneg.mpr hs.2)
    have hId : IntervalIntegrable (fun s : ℝ => s) volume 0 1 := continuous_id.intervalIntegrable _ _
    rw [he, intervalIntegral.integral_sub intervalIntegrable_const hId,
      intervalIntegral.integral_const, integral_id]
    norm_num [smul_eq_mul]
  have hCV : (∫ s in (1 : ℝ)..V, C s) = 0 := by
    calc
      _ = ∫ s in (1 : ℝ)..V, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hV] at hs
        exact max_eq_left (sub_nonpos.mpr hs.1)
      _ = _ := intervalIntegral.integral_zero
  have hCt : (∫ s in (0 : ℝ)..V, C s) = 1 / 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hC.intervalIntegrable 0 1)
      (hC.intervalIntegrable 1 V), hC₁, hCV, add_zero]
  have hpoint (s : ℝ) (hs : s ∈ Icc 0 V) :
      cosineAbelWeight V s ≤ A s - deriv A s + C s := by
    unfold cosineAbelWeight
    have hd : deriv A s - A s ≤ C s := derivative_deficit_nonpos hV₀ hs
    apply max_le (by linarith only [hd])
    linarith [le_max_left (0 : ℝ) (1 - s)]
  have hAS : IntervalIntegrable (fun s => A s - deriv A s) volume 0 V :=
    (hA.continuous.intervalIntegrable 0 V).sub hD
  have ht := intervalIntegral.integral_mono_on hV₀.le
    ((continuous_cosineAbelWeight hV₀).intervalIntegrable 0 V)
    (hAS.add (hC.intervalIntegrable 0 V)) hpoint
  rw [intervalIntegral.integral_add hAS
    (hC.intervalIntegrable 0 V), intervalIntegral.integral_sub
    (hA.continuous.intervalIntegrable 0 V) hD, hCt] at ht
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun s _ => hA.differentiable (by norm_num) s) hD] at ht
  have hz : A 0 = 0 := by simp [A]
  have hv : A V = 0 := by simp [A, cosineWeight, abs_of_pos hV₀, hV₀.ne']
  rw [hz, hv, sub_self, sub_zero] at ht
  exact ht.trans_eq (by unfold A; rw [integral_cosineWeight_first_moment hV₀])

/-- A pointwise envelope suitable for the square-root error in the psi bound. -/
theorem cosineAbelWeight_le_quadratic {V s : ℝ} (hV : 0 < V) (hs : s ∈ Icc 0 V) :
    cosineAbelWeight V s ≤ s + (Real.pi^2 / V^2) * s^2 := by
  have hs₀ : 0 ≤ s := hs.1
  have hf : 0 ≤ 1 - s / V := sub_nonneg.mpr ((div_le_one hV).mpr hs.2)
  have hsin : Real.sin (Real.pi * (s / V)) ≤ Real.pi * (s / V) := Real.sin_le (by positivity)
  have hp : Real.pi * (1 - s / V) * Real.sin (Real.pi * (s / V)) / V ≤
      (Real.pi^2 / V^2) * s := by
    calc
      _ ≤ Real.pi * (1 - s / V) * (Real.pi * (s / V)) / V :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsin (by positivity)) hV.le
      _ ≤ Real.pi * 1 * (Real.pi * (s / V)) / V := by
        gcongr
        exact sub_le_self _ (by positivity)
      _ = _ := by field_simp [hV.ne']
  have hprod := mul_le_mul_of_nonneg_left hp hs₀
  have hw := mul_le_of_le_one_right hs₀ (cosineWeight_le_one hV s)
  unfold cosineAbelWeight
  rw [derivative_mul_cosineWeight hV hs]
  apply max_le (by positivity)
  have hw₀ := cosineWeight_nonneg hV s
  simp only [div_eq_mul_inv] at hprod ⊢
  nlinarith only [hprod, hw, hw₀]

end GoldbachExplicit
