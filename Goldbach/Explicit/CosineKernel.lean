import Mathlib

/-! The compact cosine-bump weight of Vynohradov, in angular frequency normalization. -/

open MeasureTheory Set
open scoped Interval
noncomputable section

namespace GoldbachExplicit

def unitCosineWeight (v : ℝ) : ℝ :=
  (1 - v) * Real.cos (Real.pi * v) + Real.sin (Real.pi * v) / Real.pi

def cosineWeight (V v : ℝ) : ℝ :=
  if |v| ≤ V then unitCosineWeight (|v| / V) else 0

def cosineBump (V : ℝ) : ℝ → ℝ :=
  (Icc (-V / 2) (V / 2)).indicator (fun s => Real.cos (Real.pi * s / V))

theorem cosineWeight_even (V : ℝ) : Function.Even (cosineWeight V) := fun v => by
  simp [cosineWeight]

theorem cosineWeight_zero_of_lt_abs {V v : ℝ} (h : V < |v|) :
    cosineWeight V v = 0 := by simp [cosineWeight, h.not_ge]

theorem cosineWeight_hasCompactSupport (V : ℝ) : HasCompactSupport (cosineWeight V) := by
  refine HasCompactSupport.intro' (K := Icc (-V) V) isCompact_Icc isClosed_Icc ?_
  intro v hv
  apply cosineWeight_zero_of_lt_abs
  exact lt_of_not_ge fun h => hv (abs_le.mp h)

@[simp] theorem unitCosineWeight_zero : unitCosineWeight 0 = 1 := by simp [unitCosineWeight]

@[simp] theorem unitCosineWeight_one : unitCosineWeight 1 = 0 := by simp [unitCosineWeight]

theorem unitCosineWeight_hasDerivAt (v : ℝ) :
    HasDerivAt unitCosineWeight (-(Real.pi * (1 - v) * Real.sin (Real.pi * v))) v := by
  have h := (hasDerivAt_id v).const_mul Real.pi
  have h' := (((hasDerivAt_id v).const_sub 1).mul h.cos).add
    (h.sin.div_const Real.pi)
  convert h' using 1 <;> first | rfl | (simp only [id_eq]; field_simp [Real.pi_ne_zero] <;> ring)

private theorem unitCosineWeight_antitone : AntitoneOn unitCosineWeight (Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (fun v _ => (unitCosineWeight_hasDerivAt v).continuousAt.continuousWithinAt)
    (fun v _ => (unitCosineWeight_hasDerivAt v).differentiableAt.differentiableWithinAt)
  intro v hv
  have hv' : v ∈ Icc (0 : ℝ) 1 := interior_subset hv
  rw [(unitCosineWeight_hasDerivAt v).deriv, neg_nonpos]
  exact mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hv'.2))
    (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le hv'.1) (by nlinarith [Real.pi_pos, hv'.2]))

theorem cosineWeight_antitoneOn {V : ℝ} (hV : 0 < V) :
    AntitoneOn (cosineWeight V) (Icc 0 V) := by
  intro u hu v hv huv
  rw [cosineWeight, cosineWeight, abs_of_nonneg hu.1, abs_of_nonneg hv.1, if_pos hu.2, if_pos hv.2]
  exact unitCosineWeight_antitone ⟨div_nonneg hu.1 hV.le, (div_le_one hV).mpr hu.2⟩
    ⟨div_nonneg hv.1 hV.le, (div_le_one hV).mpr hv.2⟩ (div_le_div_of_nonneg_right huv hV.le)

theorem cosineWeight_nonneg {V : ℝ} (hV : 0 < V) (v : ℝ) : 0 ≤ cosineWeight V v := by
  by_cases hv : |v| ≤ V
  · rw [cosineWeight, if_pos hv, ← unitCosineWeight_one]
    exact unitCosineWeight_antitone ⟨by positivity, (div_le_one hV).mpr hv⟩
      (by simp) ((div_le_one hV).mpr hv)
  · simp [cosineWeight, hv]

theorem cosineWeight_le_one {V : ℝ} (hV : 0 < V) (v : ℝ) : cosineWeight V v ≤ 1 := by
  by_cases hv : |v| ≤ V
  · rw [cosineWeight, if_pos hv, ← unitCosineWeight_zero]
    exact unitCosineWeight_antitone (by simp) ⟨by positivity, (div_le_one hV).mpr hv⟩ (by positivity)
  · simp [cosineWeight, hv]

@[simp] theorem cosineWeight_zero {V : ℝ} (hV : 0 ≤ V) : cosineWeight V 0 = 1 := by
  simp [cosineWeight, hV]

theorem continuous_cosineWeight {V : ℝ} (hV : 0 < V) : Continuous (cosineWeight V) := by
  have hc : Continuous (fun v : ℝ => unitCosineWeight (|v| / V)) :=
    (continuous_iff_continuousAt.mpr (fun t => (unitCosineWeight_hasDerivAt t).continuousAt)).comp
      (continuous_abs.div_const V)
  unfold cosineWeight
  exact hc.if_le continuous_const continuous_abs continuous_const
    (fun v he => by simp [he, hV.ne'])

private theorem unitCosineWeight_quadratic {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    1 - Real.pi^2 * u^2 / 2 ≤ unitCosineWeight u := by
  let f (t : ℝ) := unitCosineWeight t - 1 + Real.pi^2 * t^2 / 2
  have hf (t : ℝ) : HasDerivAt f
      (Real.pi * (Real.pi * t - (1 - t) * Real.sin (Real.pi * t))) t := by
    convert ((unitCosineWeight_hasDerivAt t).sub_const (1 : ℝ)).add
      (((hasDerivAt_pow 2 t).const_mul (Real.pi^2)).div_const 2) using 1
        <;> first | rfl | ring
  have hmono : MonotoneOn f (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun t _ => (hf t).continuousAt.continuousWithinAt)
      (fun t _ => (hf t).differentiableAt.differentiableWithinAt)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    have hs : 0 ≤ Real.pi * t := mul_nonneg Real.pi_pos.le ht'.1
    have h := (mul_le_mul_of_nonneg_left (Real.sin_le hs) (sub_nonneg.mpr ht'.2)).trans
      (mul_le_of_le_one_left hs (by linarith [ht'.1]))
    rw [(hf t).deriv]
    exact mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h)
  have hb := hmono (by simp : (0 : ℝ) ∈ Icc 0 1) hu hu.1
  have hz : f 0 = 0 := by simp [f]
  rw [hz] at hb
  dsimp [f] at hb
  linarith

theorem cosineWeight_quadratic {V : ℝ} (hV : 0 < V) (v : ℝ) :
    1 - Real.pi^2 * v^2 / (2 * V^2) ≤ cosineWeight V v := by
  by_cases hv : |v| ≤ V
  · rw [cosineWeight, if_pos hv]
    have h := unitCosineWeight_quadratic (u := |v| / V) ⟨by positivity, (div_le_one hV).mpr hv⟩
    simpa only [div_pow, sq_abs, ← mul_div_assoc, div_div, mul_comm (V^2) 2] using h
  · rw [cosineWeight, if_neg hv]
    have hvs : V^2 ≤ v^2 := by
      rw [← sq_abs v]
      exact pow_le_pow_left₀ hV.le (le_of_lt (lt_of_not_ge hv)) 2
    have hπ : 2 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
    rw [sub_nonpos, le_div_iff₀ (by positivity), one_mul]
    exact mul_le_mul hπ hvs (sq_nonneg V) (sq_nonneg _)

theorem cosineBump_nonneg {V : ℝ} (hV : 0 < V) (s : ℝ) : 0 ≤ cosineBump V s := by
  unfold cosineBump
  apply indicator_nonneg
  intro u hu
  have h : |u| ≤ V / 2 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
  have hl : -(Real.pi / 2) ≤ Real.pi * u / V := by
    apply (le_div_iff₀ hV).mpr
    nlinarith [mul_le_mul_of_nonneg_left (neg_abs_le u) Real.pi_pos.le,
      mul_le_mul_of_nonneg_left h Real.pi_pos.le]
  have hh : Real.pi * u / V ≤ Real.pi / 2 :=
    (div_le_iff₀ hV).mpr (by nlinarith [mul_le_mul_of_nonneg_left hu.2 Real.pi_pos.le])
  exact Real.cos_nonneg_of_mem_Icc ⟨hl, hh⟩

end GoldbachExplicit
