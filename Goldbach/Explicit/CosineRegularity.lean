import Goldbach.Explicit.CosineKernel

/-! The cosine kernel and its first two derivatives agree at all joins. -/

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace GoldbachExplicit

private theorem hasDerivAt_join {f g f' g' : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hval : f a = g a) (hderiv : f' a = g' a) (x : ℝ) :
    HasDerivAt (fun y => if y ≤ a then f y else g y)
      (if x ≤ a then f' x else g' x) x := by
  rcases lt_trichotomy x a with hx | rfl | hx
  · rw [if_pos hx.le]
    apply (hf x).congr_of_eventuallyEq
    exact (gt_mem_nhds hx).mono (fun y hy => if_pos hy.le)
  · rw [if_pos le_rfl]
    have hL : HasDerivWithinAt (fun y => if y ≤ x then f y else g y) (f' x) (Iic x) x :=
      (hf x).hasDerivWithinAt.congr_of_mem (fun _ hy => if_pos hy) self_mem_Iic
    have hR : HasDerivWithinAt (fun y => if y ≤ x then f y else g y) (f' x) (Ici x) x := by
      refine ((hg x).hasDerivWithinAt.congr_deriv hderiv.symm).congr_of_mem ?_ self_mem_Ici
      intro y hy
      rcases eq_or_lt_of_le (mem_Ici.mp hy) with he | hy'
      · subst y
        simpa only [if_pos le_rfl] using hval
      · rw [if_neg hy'.not_ge]
    have h := hL.union hR
    rw [Iic_union_Ici] at h
    exact hasDerivWithinAt_univ.mp h
  · rw [if_neg hx.not_ge]
    apply (hg x).congr_of_eventuallyEq
    exact (lt_mem_nhds hx).mono (fun y hy => if_neg hy.not_ge)

private def unitSlope (x : ℝ) : ℝ :=
  -(Real.pi * (1 - x) * Real.sin (Real.pi * x))

private def unitSecond (x : ℝ) : ℝ :=
  Real.pi * Real.sin (Real.pi * x) - Real.pi^2 * (1 - x) * Real.cos (Real.pi * x)

private theorem unitSlope_hasDerivAt (x : ℝ) :
    HasDerivAt unitSlope (unitSecond x) x := by
  have h := (((hasDerivAt_id x).const_sub 1).const_mul Real.pi).mul
    (((hasDerivAt_id x).const_mul Real.pi).sin)
  convert h.neg using 1 <;>
    first | rfl | (simp only [unitSlope, unitSecond, id_eq]; ring)

private def cappedWeight (x : ℝ) : ℝ := if x ≤ 1 then unitCosineWeight x else 0
private def cappedSlope (x : ℝ) : ℝ := if x ≤ 1 then unitSlope x else 0
private def cappedSecond (x : ℝ) : ℝ := if x ≤ 1 then unitSecond x else 0

private theorem cappedWeight_hasDerivAt (x : ℝ) :
    HasDerivAt cappedWeight (cappedSlope x) x :=
  hasDerivAt_join (fun y => unitCosineWeight_hasDerivAt y) (fun y => hasDerivAt_const y (0 : ℝ))
    unitCosineWeight_one (by simp [unitSlope]) x

private theorem cappedSlope_hasDerivAt (x : ℝ) :
    HasDerivAt cappedSlope (cappedSecond x) x :=
  hasDerivAt_join unitSlope_hasDerivAt (fun y => hasDerivAt_const y (0 : ℝ))
    (by simp [unitSlope]) (by simp [unitSecond]) x

private theorem cappedSecond_continuous : Continuous cappedSecond := by
  have h : Continuous unitSecond := by unfold unitSecond; fun_prop
  unfold cappedSecond
  exact h.if_le continuous_const continuous_id continuous_const
    (fun x hx => by simp [hx, unitSecond])

private def cosineSlope (V x : ℝ) : ℝ :=
  if x ≤ 0 then -(cappedSlope (-x / V)) / V else cappedSlope (x / V) / V

private def cosineSecond (V x : ℝ) : ℝ :=
  if x ≤ 0 then cappedSecond (-x / V) / V^2 else cappedSecond (x / V) / V^2

private theorem cosineWeight_hasDerivAt {V : ℝ} (hV : 0 < V) (x : ℝ) :
    HasDerivAt (cosineWeight V) (cosineSlope V x) x := by
  have hL (y : ℝ) : HasDerivAt (fun z => cappedWeight (-z / V))
      (-(cappedSlope (-y / V)) / V) y := by
    convert (cappedWeight_hasDerivAt (-y / V)).comp y ((hasDerivAt_id y).neg.div_const V) using 1 <;>
      first | rfl | (funext z; rfl) |
        (simp (config := { failIfUnchanged := false }) only [Function.comp_def, id_eq];
          field_simp [hV.ne'] <;> ring)
  have hR (y : ℝ) : HasDerivAt (fun z => cappedWeight (z / V))
      (cappedSlope (y / V) / V) y := by
    convert (cappedWeight_hasDerivAt (y / V)).comp y ((hasDerivAt_id y).div_const V) using 1 <;>
      first | rfl | (funext z; rfl) |
        (simp (config := { failIfUnchanged := false }) only [Function.comp_def, id_eq];
          field_simp [hV.ne'] <;> ring)
  have hfun : cosineWeight V = fun z => if z ≤ 0 then cappedWeight (-z / V) else cappedWeight (z / V) := by
    funext z
    by_cases hz : z ≤ 0
    · simp [cosineWeight, cappedWeight, abs_of_nonpos hz, hz, div_le_iff₀ hV]
    · simp [cosineWeight, cappedWeight, abs_of_nonneg (le_of_lt (lt_of_not_ge hz)), hz, div_le_iff₀ hV]
  rw [hfun]
  exact hasDerivAt_join hL hR (by simp) (by simp [cappedSlope, unitSlope]) x

private theorem cosineSlope_hasDerivAt {V : ℝ} (hV : 0 < V) (x : ℝ) :
    HasDerivAt (cosineSlope V) (cosineSecond V x) x := by
  have hL (y : ℝ) : HasDerivAt (fun z => -(cappedSlope (-z / V)) / V)
      (cappedSecond (-y / V) / V^2) y := by
    have h := (cappedSlope_hasDerivAt (-y / V)).comp y ((hasDerivAt_id y).neg.div_const V)
    convert h.neg.div_const V using 1 <;>
      first | rfl | (funext z; rfl) |
        (simp (config := { failIfUnchanged := false }) only [Function.comp_def, id_eq];
          field_simp [hV.ne'] <;> ring)
  have hR (y : ℝ) : HasDerivAt (fun z => cappedSlope (z / V) / V)
      (cappedSecond (y / V) / V^2) y := by
    have h := (cappedSlope_hasDerivAt (y / V)).comp y ((hasDerivAt_id y).div_const V)
    convert h.div_const V using 1 <;>
      first | rfl | (funext z; rfl) |
        (simp (config := { failIfUnchanged := false }) only [Function.comp_def, id_eq];
          field_simp [hV.ne'] <;> ring)
  exact hasDerivAt_join hL hR (by simp [cappedSlope, unitSlope]) (by simp) x

/-- The real cosine weight is C² across the edges of its support and at zero. -/
theorem contDiff_two_cosineWeight {V : ℝ} (hV : 0 < V) : ContDiff ℝ 2 (cosineWeight V) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (cosineWeight_hasDerivAt hV x).differentiableAt, by simp, ?_⟩
  have h' : deriv (cosineWeight V) = cosineSlope V := by
    funext x
    exact (cosineWeight_hasDerivAt hV x).deriv
  rw [h', contDiff_one_iff_deriv]
  refine ⟨fun x => (cosineSlope_hasDerivAt hV x).differentiableAt, ?_⟩
  have h'' : deriv (cosineSlope V) = cosineSecond V := by
    funext x
    exact (cosineSlope_hasDerivAt hV x).deriv
  rw [h'']
  unfold cosineSecond
  exact ((cappedSecond_continuous.comp (continuous_id.neg.div_const V)).div_const (V^2)).if_le
    ((cappedSecond_continuous.comp (continuous_id.div_const V)).div_const (V^2))
    continuous_id continuous_const (fun x hx => by simp [hx])

/-- Derivative of the positive part of the explicit weight, including both endpoints. -/
theorem cosineWeight_hasDerivAt_on {V x : ℝ} (hV : 0 < V) (hx : x ∈ Icc 0 V) :
    HasDerivAt (cosineWeight V)
      (-(Real.pi * (1 - x / V) * Real.sin (Real.pi * (x / V))) / V) x := by
  have h := cosineWeight_hasDerivAt hV x
  have hxV : x / V ≤ 1 := (div_le_one hV).mpr hx.2
  rcases eq_or_lt_of_le hx.1 with rfl | hp
  · simpa [cosineSlope, cappedSlope, unitSlope] using h
  · simpa only [cosineSlope, if_neg hp.not_ge, cappedSlope, if_pos hxV, unitSlope] using h

end GoldbachExplicit
