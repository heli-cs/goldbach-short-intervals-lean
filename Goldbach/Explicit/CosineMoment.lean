import Goldbach.Explicit.CosineDecay

/-! The exact second Fourier moment, by positive difference quotients,
Fatou's lemma and dominated convergence. -/

open Set Filter MeasureTheory
open scoped Topology Interval ENNReal
noncomputable section

namespace GoldbachExplicit

open Zeta23

private abbrev K (V t : ℝ) : ℝ := (cosineTransform V (t : ℂ)).re

private theorem continuous_K {V : ℝ} (hV : 0 < V) : Continuous (K V) :=
  (Taper.contDiff_re_paperFT_ofReal
    (Complex.continuous_ofReal.comp (continuous_cosineWeight hV))
    ((cosineWeight_hasCompactSupport V).comp_left Complex.ofReal_zero) 0).continuous

private theorem integral_K_cos {V : ℝ} (hV : 0 < V) (u : ℝ) :
    (∫ t, K V t * Real.cos (t * u)) = 2 * Real.pi * cosineWeight V u := by
  have hc := continuous_cosineWeight hV
  exact Taper.integral_mul_cos_of_paperFT_eq hc
    (hc.integrable_of_hasCompactSupport (cosineWeight_hasCompactSupport V))
    (cosineTransform_real_integral hV).1 (Taper.paperFT_ofReal_eq_re (cosineWeight_even V)) u

private theorem integrable_K_cos {V : ℝ} (hV : 0 < V) (u : ℝ) :
    Integrable (fun t => K V t * Real.cos (t * u)) := by
  refine (cosineTransform_real_integral hV).1.norm.mono'
    ((continuous_K hV).mul (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards with t
  rw [norm_mul, Real.norm_eq_abs (Real.cos _)]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)

private theorem second_cosine_quotient (t : ℝ) {u : ℝ} (hu : u ≠ 0) :
    t^2 * (Real.sinc (t * u / 2))^2 = 2 * (1 - Real.cos (t * u)) / u^2 := by
  by_cases ht : t = 0
  · subst t
    simp
  have hz : t * u / 2 ≠ 0 := div_ne_zero (mul_ne_zero ht hu) (by norm_num)
  rw [Real.sinc_of_ne_zero hz]
  conv_rhs => rw [show t * u = 2 * (t * u / 2) by ring, Real.cos_two_mul']
  have hs := Real.sin_sq_add_cos_sq (t * u / 2)
  field_simp [ht, hu] <;> ring_nf at hs ⊢ <;> linarith only [hs]

private def momentQuotient (V u t : ℝ) : ℝ :=
  K V t * (t^2 * (Real.sinc (t * u / 2))^2)

private theorem momentQuotient_nonneg {V : ℝ} (hV : 0 < V) (u t : ℝ) :
    0 ≤ momentQuotient V u t :=
  mul_nonneg (cosineTransform_ofReal_nonneg hV t) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

private theorem momentQuotient_integral {V u : ℝ} (hV : 0 < V) (hu : u ≠ 0) :
    Integrable (momentQuotient V u) ∧
      (∫ t, momentQuotient V u t) =
        (2 * Real.pi) * (2 * (1 - cosineWeight V u) / u^2) := by
  have he : momentQuotient V u = fun t =>
      (2 / u^2) * (K V t - K V t * Real.cos (t * u)) := by
    funext t
    rw [momentQuotient, second_cosine_quotient t hu]
    ring
  have h₁ := (cosineTransform_real_integral hV).1
  have h₂ := integrable_K_cos hV u
  rw [he]
  refine ⟨(h₁.sub h₂).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub h₁ h₂, (cosineTransform_real_integral hV).2, integral_K_cos hV]
  ring

private theorem correction_range {z : ℝ} (hz : 0 ≤ z) (hzπ : z ≤ Real.pi) :
    0 ≤ Real.sin z - z * Real.cos z ∧ Real.sin z - z * Real.cos z ≤ z^3 / 3 := by
  have h (r : ℝ) : HasDerivAt (fun t : ℝ => Real.sin t - t * Real.cos t) (r * Real.sin r) r := by
    convert (Real.hasDerivAt_sin r).sub ((hasDerivAt_id r).mul (Real.hasDerivAt_cos r))
      using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hc : Continuous (fun t : ℝ => t * Real.sin t) := by fun_prop
  have he : (∫ r in (0 : ℝ)..z, r * Real.sin r) = Real.sin z - z * Real.cos z := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => h r) (hc.intervalIntegrable _ _)]
    simp
  rw [← he]
  refine ⟨intervalIntegral.integral_nonneg hz (fun r hr => ?_), ?_⟩
  · exact mul_nonneg hr.1 (Real.sin_nonneg_of_nonneg_of_le_pi hr.1 (hr.2.trans hzπ))
  · calc
      _ ≤ ∫ r in (0 : ℝ)..z, r^2 := by
        apply intervalIntegral.integral_mono_on hz (hc.intervalIntegrable _ _)
          ((continuous_pow 2).intervalIntegrable _ _)
        intro r hr
        simpa only [pow_two] using mul_le_mul_of_nonneg_left (Real.sin_le hr.1) hr.1
      _ = _ := by rw [integral_pow]; norm_num

private theorem second_weight_quotient_limit {V : ℝ} (hV : 0 < V) :
    Tendsto (fun u : ℝ => 2 * (1 - cosineWeight V u) / u^2) (𝓝[>] 0)
      (𝓝 (Real.pi^2 / V^2)) := by
  let a := Real.pi / V
  let C := 2 * a^3 / (3 * Real.pi)
  have ha : 0 < a := div_pos Real.pi_pos hV
  have hpos : ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u := self_mem_nhdsWithin
  have hup : ∀ᶠ u : ℝ in 𝓝[>] 0, u < V :=
    (show ∀ᶠ u : ℝ in 𝓝 0, u < V from Iio_mem_nhds hV).filter_mono nhdsWithin_le_nhds
  have hsmall (u : ℝ) (hu : 0 < u) (huV : u < V) :
      0 ≤ 2 * (Real.sin (a*u) - a*u * Real.cos (a*u)) / (Real.pi * u^2) ∧
        2 * (Real.sin (a*u) - a*u * Real.cos (a*u)) / (Real.pi * u^2) ≤ C * u := by
    have h₀ : 0 ≤ a*u := by positivity
    have hπ : a*u ≤ Real.pi := by
      dsimp [a]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hV).mpr
      exact mul_le_mul_of_nonneg_left huV.le Real.pi_pos.le
    have hr := correction_range h₀ hπ
    refine ⟨div_nonneg (mul_nonneg (by norm_num) hr.1) (by positivity), ?_⟩
    apply (div_le_iff₀ (show 0 < Real.pi * u^2 by positivity)).mpr
    dsimp [C]
    have hh : 2 * a^3 / (3 * Real.pi) * u * (Real.pi * u^2) =
        2 * (a * u)^3 / 3 := by field_simp [Real.pi_ne_zero] <;> ring
    rw [hh]
    linarith only [hr.2]
  let F (u : ℝ) := 2 * (Real.sin (a*u) - a*u * Real.cos (a*u)) / (Real.pi * u^2)
  have hF : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun u : ℝ => C * u) (𝓝[>] 0) (𝓝 0) by
        have h : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
          (continuous_id.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
        simpa only [mul_zero] using h.const_mul C)
    · filter_upwards [hpos, hup] with u hu hv
      exact (hsmall u hu hv).1
    · filter_upwards [hpos, hup] with u hu hv
      exact (hsmall u hu hv).2
  let G (u : ℝ) := a^2 * (Real.sinc (a*u/2))^2
  have hGc : Continuous G := continuous_const.mul
    ((Real.continuous_sinc.comp (by fun_prop : Continuous (fun u : ℝ => a*u/2))).pow 2)
  have hG : Tendsto G (𝓝[>] 0) (𝓝 (Real.pi^2 / V^2)) := by
    have h : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (G 0)) :=
      (hGc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    simpa [G, a, div_pow] using h
  have h := hG.sub hF
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [hpos, hup] with u hu huV
  dsimp [G, F]
  rw [second_cosine_quotient a hu.ne', cosineWeight, abs_of_pos hu, if_pos huV.le, unitCosineWeight]
  have hz : Real.pi * (u / V) = a * u := by unfold a; ring
  rw [hz]
  dsimp [a]
  field_simp [hV.ne', hu.ne', Real.pi_ne_zero] <;> ring

/-- The angular-frequency second moment of the normalized cosine bump autocorrelation. -/
theorem cosineTransform_second_moment {V : ℝ} (hV : 0 < V) :
    Integrable (fun t : ℝ => K V t * t^2) ∧
      (∫ t : ℝ, K V t * t^2) = (2 * Real.pi) * (Real.pi^2 / V^2) := by
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  let G := momentQuotient V
  let F (t : ℝ) := K V t * t^2
  let C := (2 * Real.pi) * (Real.pi^2 / V^2)
  have hGc (u : ℝ) : Continuous (G u) := by
    unfold G momentQuotient
    exact (continuous_K hV).mul ((continuous_pow 2).mul
      ((Real.continuous_sinc.comp (by fun_prop : Continuous (fun t : ℝ => t*u/2))).pow 2))
  have hFc : Continuous F := (continuous_K hV).mul (continuous_pow 2)
  have hF₀ (t : ℝ) : 0 ≤ F t := mul_nonneg (cosineTransform_ofReal_nonneg hV t) (sq_nonneg _)
  have hp : ∀ t : ℝ, Tendsto (fun u => G u t) l (𝓝 (F t)) := by
    intro t
    have hc : Continuous (fun u => G u t) := by
      unfold G momentQuotient
      exact continuous_const.mul (continuous_const.mul
        ((Real.continuous_sinc.comp (by fun_prop : Continuous (fun u : ℝ => t*u/2))).pow 2))
    simpa [G, momentQuotient, F] using (hc.continuousAt (x := 0)).tendsto.mono_left
      (show l ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hI (u : ℝ) (hu : 0 < u) := momentQuotient_integral hV hu.ne'
  have hpos : ∀ᶠ u : ℝ in l, 0 < u := self_mem_nhdsWithin
  have hU : ∀ᶠ u : ℝ in l, (∫⁻ t, ENNReal.ofReal (G u t)) ≤ ENNReal.ofReal C := by
    filter_upwards [hpos] with u hu
    rw [← ofReal_integral_eq_lintegral_ofReal (hI u hu).1
      (Eventually.of_forall (momentQuotient_nonneg hV u)), (hI u hu).2]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (div_le_iff₀ (show 0 < u^2 by positivity)).mpr
    have h := cosineWeight_quadratic hV u
    field_simp [hV.ne'] at h ⊢
    linarith only [h]
  have he (t : ℝ) : l.liminf (fun u => ENNReal.ofReal (G u t)) = ENNReal.ofReal (F t) :=
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hp t)).liminf_eq
  have hE : (∫⁻ t, ENNReal.ofReal (F t)) ≤ ENNReal.ofReal C := by
    simp_rw [← he]
    refine (lintegral_liminf_le (fun u => (hGc u).measurable.ennreal_ofReal)).trans ?_
    refine liminf_le_of_le (by isBoundedDefault) fun r hr => ?_
    obtain ⟨u, h₁, h₂⟩ := (hr.and hU).exists
    exact h₁.trans h₂
  have hFI : Integrable F :=
    ⟨hFc.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hF₀)).mpr (hE.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hFI, ?_⟩
  have hlim : Tendsto (fun u => ∫ t, G u t) l (𝓝 (∫ t, F t)) := by
    apply tendsto_integral_filter_of_dominated_convergence F
      (Eventually.of_forall (fun u => (hGc u).aestronglyMeasurable)) ?_ hFI
      (Eventually.of_forall hp)
    apply Eventually.of_forall
    intro u
    apply Eventually.of_forall
    intro t
    rw [Real.norm_of_nonneg (momentQuotient_nonneg hV u t)]
    have hs : Real.sinc (t*u/2)^2 ≤ 1 := by
      have h : Real.sinc (t*u/2)^2 ≤ (1 : ℝ)^2 :=
        sq_le_sq.mpr (by simpa only [abs_one] using Real.abs_sinc_le_one (t*u/2))
      simpa only [one_pow] using h
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (sq_nonneg _) hs)
      (cosineTransform_ofReal_nonneg hV t)
  have hlim' : Tendsto (fun u => ∫ t, G u t) l (𝓝 C) := by
    apply ((second_weight_quotient_limit hV).const_mul (2 * Real.pi)).congr'
    filter_upwards [hpos] with u hu
    exact (hI u hu).2.symm
  exact tendsto_nhds_unique hlim hlim'

end GoldbachExplicit
