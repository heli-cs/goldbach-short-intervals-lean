import Goldbach.Coefficient
import Zeta23.ExplicitFormula

open MeasureTheory Set
open scoped Interval FourierTransform Convolution ComplexConjugate

noncomputable section
namespace GoldbachSpectrum

private def box : ℝ → ℂ := (Icc (0 : ℝ) 1).indicator (fun _ => 1)

private def tent (x : ℝ) : ℂ := (max (min 1 (x + 1) - max 0 x) 0 : ℝ)

private theorem box_integrable : Integrable box := by
  unfold box
  rw [integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const measure_Icc_lt_top.ne

private theorem tilde_box_eq (x : ℝ) : Zeta23.EF.tilde box x = box (-x) := by
  by_cases h : -x ∈ Icc (0 : ℝ) 1 <;> simp [Zeta23.EF.tilde, box, h]

private theorem tilde_box_integrable : Integrable (Zeta23.EF.tilde box) := by
  refine box_integrable.comp_neg.congr ?_
  exact Filter.Eventually.of_forall fun x => (tilde_box_eq x).symm

private theorem box_convolution_eq_tent :
    box ⋆[ContinuousLinearMap.mul ℂ ℂ] Zeta23.EF.tilde box = tent := by
  funext x
  rw [MeasureTheory.convolution_def]
  have hprod (y : ℝ) :
      ContinuousLinearMap.mul ℂ ℂ (box y) (Zeta23.EF.tilde box (x - y)) =
        (Icc (max 0 x) (min 1 (x + 1))).indicator (fun _ => (1 : ℂ)) y := by
    rw [ContinuousLinearMap.mul_apply', tilde_box_eq, neg_sub]
    have hm : y ∈ Icc (max (0 : ℝ) x) (min 1 (x + 1)) ↔
        y ∈ Icc (0 : ℝ) 1 ∧ y - x ∈ Icc (0 : ℝ) 1 := by
      simp only [mem_Icc, max_le_iff, le_min_iff]
      constructor
      · rintro ⟨⟨h₀, hx⟩, h₁, hx₁⟩
        exact ⟨⟨h₀, h₁⟩, by constructor <;> linarith⟩
      · rintro ⟨⟨h₀, h₁⟩, hx, hx₁⟩
        exact ⟨⟨h₀, by linarith⟩, h₁, by linarith⟩
    by_cases h₁ : y ∈ Icc (0 : ℝ) 1 <;> by_cases h₂ : y - x ∈ Icc (0 : ℝ) 1 <;>
      simp [box, hm, h₁, h₂]
  simp_rw [hprod]
  rw [integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc, Complex.real_smul, mul_one]
  rfl

private theorem paperFT_box (t : ℝ) : Zeta23.paperFT box t = profileIntegral 0 t := by
  unfold Zeta23.paperFT profileIntegral
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with y
  unfold box
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · simp [hy, exponent]
    congr 1
    ring
  · simp [hy]

private theorem paperFT_tent (t : ℝ) :
    Zeta23.paperFT tent t = (profile 0 t : ℂ) := by
  let r := -t / (2 * Real.pi)
  calc
    _ = 𝓕 (box ⋆[ContinuousLinearMap.mul ℂ ℂ] Zeta23.EF.tilde box) r := by
      rw [box_convolution_eq_tent, Zeta23.EF.paperFT_ofReal_eq_fourier]
    _ = (𝓕 box r) * (𝓕 (Zeta23.EF.tilde box) r) :=
      Real.fourier_mul_convolution_eq box_integrable tilde_box_integrable r
    _ = _ := by
      dsimp only [r]
      rw [← Zeta23.EF.paperFT_ofReal_eq_fourier, ← Zeta23.EF.paperFT_ofReal_eq_fourier,
        Zeta23.EF.paperFT_tilde, Complex.conj_ofReal, paperFT_box, Complex.mul_conj']
      simp only [profile, Complex.ofReal_pow]

private theorem fourier_tent_apply (r : ℝ) :
    𝓕 tent r = (profile 0 (-(2 * Real.pi) * r) : ℂ) := by
  have h := paperFT_tent (-(2 * Real.pi) * r)
  rw [Zeta23.EF.paperFT_ofReal_eq_fourier] at h
  have hr : - (-(2 * Real.pi) * r) / (2 * Real.pi) = r := by
    field_simp [Real.pi_ne_zero]
  rwa [hr] at h

/-- The angular-frequency Plancherel normalization. The proof uses
Fourier inversion at zero for the autocorrelation of the unit box. -/
theorem integral_profile_zero : (∫ t, profile 0 t) = 2 * Real.pi := by
  have hcont : Continuous tent := by unfold tent; fun_prop
  have hint : Integrable tent := by
    rw [← box_convolution_eq_tent]
    exact box_integrable.integrable_convolution _ tilde_box_integrable
  let D : ℝ := Real.exp 1 + (1 + Real.exp (1 / 2))^2
  have hbound (t : ℝ) : profile 0 t ≤ D / (1 + t^2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    dsimp only [D]
    nlinarith only [profile_le_exp_one (show (0 : ℝ) ≤ 0 from le_rfl) (by norm_num) t,
      sq_mul_profile_le (show (0 : ℝ) ≤ 0 from le_rfl) (by norm_num) t]
  have hFi : Integrable (𝓕 tent) := by
    let g := fun r : ℝ => D * (1 + (-(2 * Real.pi) * r)^2)⁻¹
    have hg : Integrable g :=
      ((integrable_inv_one_add_sq.const_mul D).comp_mul_left'
        (neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)))
    have hFcont : Continuous (𝓕 tent) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hint
    apply hg.mono' hFcont.aestronglyMeasurable
    filter_upwards with r
    rw [fourier_tent_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (hbound _).trans_eq (div_eq_mul_inv _ _)
  have h := Zeta23.EF.paper_inversion hcont hint hFi 0
  have hzero : tent 0 = 1 := by norm_num [tent]
  rw [hzero] at h
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, paperFT_tent] at h
  rw [integral_complex_ofReal, div_mul_eq_mul_div, one_mul] at h
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  have h' : Complex.ofReal (∫ t : ℝ, profile 0 t) = 2 * (Real.pi : ℂ) := by
    simpa only [one_mul] using ((eq_div_iff hπ).mp h).symm
  exact_mod_cast h'

/-- The frequency profile is even, because negating the ordinate
conjugates the integral defining it. -/
theorem profile_even (lam u : ℝ) : profile lam (-u) = profile lam u := by
  have h : profileIntegral lam (-u) = conj (profileIntegral lam u) := by
    unfold profileIntegral
    rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro s _
    change Complex.exp (exponent lam (-u) * (s : ℂ)) =
      conj (Complex.exp (exponent lam u * (s : ℂ)))
    rw [← Complex.exp_conj]
    congr 1
    unfold exponent
    simp only [map_mul, map_add, map_div₀, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
      Complex.ofReal_neg]
    ring
  rw [profile, h, Complex.norm_conj, profile]

private theorem tent_hasCompactSupport : HasCompactSupport tent := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) (fun x hx => ?_)
  have hn := Function.mem_support.mp hx
  refine ⟨?_, ?_⟩
  · by_contra! h
    apply hn
    have hle : min 1 (x + 1) - max 0 x ≤ 0 := by
      linarith [min_le_right (1 : ℝ) (x + 1), le_max_left (0 : ℝ) x]
    simp [tent, max_eq_right hle]
  · by_contra! h
    apply hn
    have hle : min 1 (x + 1) - max 0 x ≤ 0 := by
      linarith [min_le_left (1 : ℝ) (x + 1), le_max_right (0 : ℝ) x]
    simp [tent, max_eq_right hle]

/-- Smoothness of the limiting profile follows from the compact support
of the autocorrelation of the box. -/
theorem profile_zero_contDiff_one : ContDiff ℝ 1 (profile 0) := by
  have hc : Continuous tent := by unfold tent; fun_prop
  have hFourier : ContDiff ℝ 1 (𝓕 tent) := by
    apply Real.contDiff_fourier
    intro n _
    have hcont : Continuous (fun x : ℝ => ‖x‖ ^ n * ‖tent x‖) :=
      (continuous_norm.pow n).mul hc.norm
    exact hcont.integrable_of_hasCompactSupport tent_hasCompactSupport.norm.mul_left
  have harg : ContDiff ℝ 1 (fun r : ℝ => -r / (2 * Real.pi)) :=
    contDiff_neg.div_const _
  have h := Complex.reCLM.contDiff.comp (hFourier.comp harg)
  have he : (fun r : ℝ => (𝓕 tent (-r / (2 * Real.pi))).re) = profile 0 := by
    funext r
    rw [← Zeta23.EF.paperFT_ofReal_eq_fourier, paperFT_tent, Complex.ofReal_re]
  rw [← he]
  exact h

theorem profile_zero_integrable : Integrable (profile 0) := by
  let D : ℝ := Real.exp 1 + (1 + Real.exp (1 / 2))^2
  refine (integrable_inv_one_add_sq.const_mul D).mono' profile_zero_contDiff_one.continuous.aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (by unfold profile; positivity), ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  dsimp [D]
  nlinarith only [profile_le_exp_one (show (0 : ℝ) ≤ 0 from le_rfl) (by norm_num) t,
    sq_mul_profile_le (show (0 : ℝ) ≤ 0 from le_rfl) (by norm_num) t]

theorem integral_profile_zero_positive : (∫ t in Ioi (0 : ℝ), profile 0 t) = Real.pi := by
  have h : (∫ t, profile 0 |t|) = ∫ t, profile 0 t := by
    apply integral_congr_ae
    filter_upwards with t
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht.le, profile_even]
  rw [integral_profile_zero, integral_comp_abs] at h
  linarith

end GoldbachSpectrum
