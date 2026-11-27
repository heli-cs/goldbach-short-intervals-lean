import Goldbach.Explicit.Archimedean
import Goldbach.Explicit.CosineMoment

/-! The archimedean convolution for the explicit kernel and all real centers. -/

open MeasureTheory Set
noncomputable section

namespace GoldbachExplicit

open Zeta23

private theorem gammaBracket_eq_mu (t : ℝ) :
    EF.gammaBracket t = (2 * Real.pi) * mu t := by
  unfold EF.gammaBracket mu
  field_simp [Real.pi_ne_zero]

private theorem gammaBracket_lower (t : ℝ) : EF.gammaBracket 0 ≤ EF.gammaBracket t := by
  have he : mu |t| = mu t := by
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, mu_even]
  have hm := MuFields.mu_monotoneOn (show (0 : ℝ) ∈ Ici 0 by simp)
    (mem_Ici.mpr (abs_nonneg t)) (abs_nonneg t)
  rw [he] at hm
  rw [gammaBracket_eq_mu, gammaBracket_eq_mu]
  exact mul_le_mul_of_nonneg_left hm (by positivity)

private theorem abs_gammaBracket_shift_le (t s : ℝ) :
    |EF.gammaBracket (t + s)| ≤ |EF.gammaBracket 0| + |t| + 4 + s^2 := by
  have h := gammaBracket_le_log_abs_add (t + s)
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < |t + s| + (5 / 2 : ℝ))
  have hs : |s| ≤ s^2 + 1 / 4 := by nlinarith only [sq_nonneg (|s| - 1 / 2), sq_abs s]
  apply abs_le.mpr
  constructor
  · linarith only [gammaBracket_lower (t + s), neg_abs_le (EF.gammaBracket 0),
      abs_nonneg t, sq_nonneg s]
  · linarith only [h, hlog, abs_add_le t s, hs, abs_nonneg (EF.gammaBracket 0)]

/-- The actual cosine-kernel convolution of the archimedean factor is
integrable and bounded by the logarithmic envelope used in v6. -/
theorem cosine_gamma_average_le {V : ℝ} (hV : 2 * Real.pi ≤ V) (t : ℝ) :
    Integrable (fun s : ℝ =>
      (cosineTransform V (s : ℂ)).re / (2 * Real.pi) * EF.gammaBracket (t + s)) ∧
    (∫ s : ℝ, (cosineTransform V (s : ℂ)).re / (2 * Real.pi) * EF.gammaBracket (t + s)) ≤
      Real.log (|t| + 3) := by
  have hpV : 0 < V := (by positivity : (0 : ℝ) < 2 * Real.pi).trans_le hV
  let K (s : ℝ) := (cosineTransform V (s : ℂ)).re
  let p (s : ℝ) := K s / (2 * Real.pi)
  have hp (s : ℝ) : 0 ≤ p s := div_nonneg (cosineTransform_ofReal_nonneg hpV s) (by positivity)
  have hpi : Integrable p := (cosineTransform_real_integral hpV).1.div_const _
  have hnorm : (∫ s, p s) = 1 := by
    unfold p
    rw [integral_div, (cosineTransform_real_integral hpV).2, div_self (by positivity : 2 * Real.pi ≠ 0)]
  have hweights (s : ℝ) : p s * s^2 = (K s * s^2) / (2 * Real.pi) := by unfold p; ring
  have hM := cosineTransform_second_moment hpV
  have h2I : Integrable (fun s => p s * s^2) := by
    simp_rw [hweights]
    exact hM.1.div_const _
  have h2 : (∫ s, p s * s^2) ≤ 1 / 4 := by
    simp_rw [hweights]
    rw [integral_div, hM.2, mul_div_cancel_left₀ _ (by positivity : 2 * Real.pi ≠ 0)]
    have he := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hV 2
    exact (div_le_iff₀ (by positivity : 0 < V^2)).2 (by nlinarith only [he])
  let D := |EF.gammaBracket 0| + |t| + 4
  have hiG : Integrable (fun s => p s * EF.gammaBracket (t + s)) := by
    have hDb : Integrable (fun s => p s * D + p s * s^2) := (hpi.mul_const D).add h2I
    have hGc : Continuous (fun s => EF.gammaBracket (t + s)) := by
      simp_rw [gammaBracket_eq_mu]
      exact continuous_const.mul (mu_smooth.continuous.comp (by fun_prop))
    refine hDb.mono' (hpi.aestronglyMeasurable.mul hGc.aestronglyMeasurable) ?_
    filter_upwards with s
    rw [norm_mul, Real.norm_of_nonneg (hp s), Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (abs_gammaBracket_shift_le t s) (hp s)).trans_eq
      (by unfold D; ring)
  exact ⟨hiG, gamma_average_le_log_add_three t hp hpi hnorm h2I h2 hiG⟩

end GoldbachExplicit
