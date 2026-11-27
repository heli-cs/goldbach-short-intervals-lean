import Goldbach.Explicit.CosineKernel
import Zeta23.Taper.Fourier

/-! The time-domain autocorrelation and the real Fourier square. -/

open MeasureTheory Set
open scoped Interval FourierTransform

noncomputable section
namespace GoldbachExplicit

open Zeta23

theorem cosineBump_even (V : ℝ) : Function.Even (cosineBump V) := by
  intro s
  by_cases h : s ∈ Icc (-V / 2) (V / 2)
  · have h' : -s ∈ Icc (-V / 2) (V / 2) := ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [cosineBump, indicator_of_mem h, indicator_of_mem h']
    rw [show Real.pi * -s / V = -(Real.pi * s / V) by ring, Real.cos_neg]
  · have h' : -s ∉ Icc (-V / 2) (V / 2) :=
      fun hs => h ⟨by linarith [hs.2], by linarith [hs.1]⟩
    rw [cosineBump, indicator_of_notMem h, indicator_of_notMem h']

theorem cosineBump_hasCompactSupport (V : ℝ) : HasCompactSupport (cosineBump V) := by
  refine HasCompactSupport.intro' (K := Icc (-V / 2) (V / 2)) isCompact_Icc isClosed_Icc ?_
  exact fun _ h => indicator_of_notMem h _

theorem continuous_cosineBump {V : ℝ} (hV : 0 < V) : Continuous (cosineBump V) := by
  have hcos : Continuous (fun s : ℝ => Real.cos (Real.pi * s / V)) := by fun_prop
  letI : DecidablePred (fun s : ℝ => s ∈ Icc (-V / 2) (V / 2)) := Classical.decPred _
  change Continuous ((Icc (-V / 2) (V / 2)).piecewise
    (fun s : ℝ => Real.cos (Real.pi * s / V)) (fun _ => 0))
  apply continuous_piecewise _ hcos.continuousOn continuousOn_const
  intro v hv
  have hv' : v = -V / 2 ∨ v = V / 2 := by
    rw [frontier_Icc (show -V / 2 ≤ V / 2 by linarith)] at hv
    simpa using hv
  rcases hv' with rfl | rfl
  · rw [show Real.pi * (-V / 2) / V = -(Real.pi / 2) by field_simp [hV.ne'] <;> ring,
      Real.cos_neg, Real.cos_pi_div_two]
  · rw [show Real.pi * (V / 2) / V = Real.pi / 2 by field_simp [hV.ne'], Real.cos_pi_div_two]

private theorem integral_bump_pair_nonneg {V v : ℝ} (hv : 0 ≤ v) (hvV : v ≤ V) :
    (∫ s, cosineBump V s * cosineBump V (s + v)) =
      ∫ s in (-V / 2)..(V / 2 - v), Real.cos (Real.pi * s / V) * Real.cos (Real.pi * (s + v) / V) := by
  rw [intervalIntegral.integral_of_le (show -V / 2 ≤ V / 2 - v by linarith),
    ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with s
  by_cases hs : s ∈ Icc (-V / 2) (V / 2 - v)
  · have h₁ : s ∈ Icc (-V / 2) (V / 2) := ⟨hs.1, by linarith [hs.2]⟩
    have h₂ : s + v ∈ Icc (-V / 2) (V / 2) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simp only [cosineBump, indicator_of_mem hs, indicator_of_mem h₁, indicator_of_mem h₂]
  · rw [indicator_of_notMem hs]
    by_cases h₁ : s ∈ Icc (-V / 2) (V / 2)
    · have h₂ : s + v ∉ Icc (-V / 2) (V / 2) :=
        fun h => hs ⟨h₁.1, by linarith [h.2]⟩
      rw [cosineBump, indicator_of_notMem h₂, mul_zero]
    · rw [cosineBump, indicator_of_notMem h₁, zero_mul]

private theorem integrate_cosine_pair {V v : ℝ} (hV : 0 < V) :
    (∫ s in (-V / 2)..(V / 2 - v), Real.cos (Real.pi * s / V) * Real.cos (Real.pi * (s + v) / V)) =
      (V - v) / 2 * Real.cos (Real.pi * v / V) +
        V / (2 * Real.pi) * Real.sin (Real.pi * v / V) := by
  let F (s : ℝ) : ℝ := 1 / 2 * (s * Real.cos (Real.pi * v / V) +
      V / (2 * Real.pi) * Real.sin (Real.pi * (2 * s + v) / V))
  have hd (s : ℝ) : HasDerivAt F
      (Real.cos (Real.pi * s / V) * Real.cos (Real.pi * (s + v) / V)) s := by
    have h₁ := ((hasDerivAt_id s).const_mul 2).add_const v
    have h₂ := (h₁.const_mul Real.pi).div_const V
    have h₃ := (((hasDerivAt_id s).mul_const (Real.cos (Real.pi * v / V))).add
      (h₂.sin.const_mul (V / (2 * Real.pi)))).const_mul (1 / 2)
    have hprod := Real.two_mul_cos_mul_cos (Real.pi * s / V) (Real.pi * (s + v) / V)
    rw [show Real.pi * s / V - Real.pi * (s + v) / V = -(Real.pi * v / V) by ring,
      Real.cos_neg, show Real.pi * s / V + Real.pi * (s + v) / V =
        Real.pi * (2 * s + v) / V by ring] at hprod
    have h₄ : HasDerivAt F ((Real.cos (Real.pi * v / V) +
        Real.cos (Real.pi * (2 * s + v) / V)) / 2) s := by
      convert h₃ using 1 <;> first | rfl | (simp only [id_eq, mul_one]; field_simp [hV.ne', Real.pi_ne_zero] <;> ring)
    convert h₄ using 1
    linarith only [hprod]
  have hInt : IntervalIntegrable (fun s : ℝ =>
      Real.cos (Real.pi * s / V) * Real.cos (Real.pi * (s + v) / V)) volume (-V / 2) (V / 2 - v) :=
    (by fun_prop : Continuous (fun s : ℝ =>
      Real.cos (Real.pi * s / V) * Real.cos (Real.pi * (s + v) / V))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F) (fun s _ => hd s) hInt]
  unfold F
  rw [show Real.pi * (2 * (V / 2 - v) + v) / V =
        Real.pi - Real.pi * v / V by field_simp; ring,
      show Real.pi * (2 * (-V / 2) + v) / V =
        -(Real.pi - Real.pi * v / V) by field_simp; ring,
    Real.sin_neg, Real.sin_pi_sub]
  ring

/-- The explicit cosine weight is its normalized autocorrelation. -/
theorem cosineWeight_eq_autocorr {V : ℝ} (hV : 0 < V) (v : ℝ) :
    cosineWeight V v = (2 / V) * Params.autocorr (cosineBump V) v := by
  suffices h : ∀ u : ℝ, 0 ≤ u →
      cosineWeight V u = (2 / V) * Params.autocorr (cosineBump V) u by
    rcases le_total 0 v with hv | hv
    · exact h v hv
    · have he := h (-v) (neg_nonneg.mpr hv)
      rw [cosineWeight_even, Taper.autocorr_neg] at he
      exact he
  intro v hv
  by_cases hvV : v ≤ V
  · rw [cosineWeight, abs_of_nonneg hv, if_pos hvV, Params.autocorr,
      integral_bump_pair_nonneg hv hvV, integrate_cosine_pair hV]
    unfold unitCosineWeight
    simp only [mul_div_assoc]
    field_simp [hV.ne', Real.pi_ne_zero] <;> ring
  · simp only [cosineWeight, abs_of_nonneg hv, if_neg hvV]
    rw [Params.autocorr, integral_eq_zero_of_ae]
    · ring
    · filter_upwards with s
      by_cases hs : s ∈ Icc (-V / 2) (V / 2)
      · have hs' : s + v ∉ Icc (-V / 2) (V / 2) :=
          fun h => hvV (by linarith [hs.1, h.2])
        rw [cosineBump, indicator_of_notMem hs', mul_zero]
        rfl
      · rw [cosineBump, indicator_of_notMem hs, zero_mul]
        rfl

/-- Angular-frequency transform of the cosine weight. -/
def cosineTransform (V : ℝ) (t : ℂ) : ℂ :=
  paperFT (fun v => (cosineWeight V v : ℂ)) t

def bumpTransform (V : ℝ) (t : ℂ) : ℂ :=
  paperFT (fun v => (cosineBump V v : ℂ)) t

theorem cosineTransform_ofReal_eq {V : ℝ} (hV : 0 < V) (t : ℝ) :
    cosineTransform V (t : ℂ) = (2 / V : ℝ) * (bumpTransform V (t : ℂ))^2 := by
  unfold cosineTransform bumpTransform
  simp_rw [cosineWeight_eq_autocorr hV, Complex.ofReal_mul, paperFT]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  congr 1
  have h := Taper.paperFT_autocorr (cosineBump_even V) (continuous_cosineBump hV)
    (cosineBump_hasCompactSupport V) t
  simpa only [paperFT, mul_assoc] using h

theorem cosineTransform_ofReal_nonneg {V : ℝ} (hV : 0 < V) (t : ℝ) :
    0 ≤ (cosineTransform V (t : ℂ)).re := by
  have hB : bumpTransform V (t : ℂ) = ((bumpTransform V (t : ℂ)).re : ℂ) :=
    Taper.paperFT_ofReal_eq_re (cosineBump_even V) t
  rw [cosineTransform_ofReal_eq hV t, hB]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

end GoldbachExplicit
