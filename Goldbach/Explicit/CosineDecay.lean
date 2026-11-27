import Goldbach.Explicit.CosineTransform

/-! Fourier inversion, complex strip decay, and pole-test estimates for the cosine bump. -/

open MeasureTheory Set Filter Complex
open scoped Interval
noncomputable section

namespace GoldbachExplicit

open Zeta23

private def waveC (z : ℂ) (v : ℝ) : ℂ := Complex.exp (Complex.I * z * (v : ℂ))

private theorem continuous_waveC (z : ℂ) : Continuous (waveC z) := by
  unfold waveC
  fun_prop

private theorem waveC_add (z : ℂ) (v u : ℝ) : waveC z (v + u) = waveC z v * waveC z u := by
  unfold waveC
  push_cast
  rw [mul_add, Complex.exp_add]

private theorem waveC_hasDerivAt (z : ℂ) (v : ℝ) :
    HasDerivAt (waveC z) (waveC z v * (Complex.I * z)) v := by
  have he := (Complex.hasDerivAt_exp (Complex.I * z * (v : ℂ))).comp (v : ℂ)
    ((hasDerivAt_id (v : ℂ)).const_mul (Complex.I * z))
  simpa only [waveC, id_eq, mul_one, Function.comp_def] using! he.comp_ofReal

private theorem norm_waveC_le (z : ℂ) {V v : ℝ} (hV : 0 < V)
    (hv : v ∈ Icc (-V / 2) (V / 2)) :
    ‖waveC z v‖ ≤ Real.exp (|z.im| * (V / 2)) := by
  have hvs : |v| ≤ V / 2 := abs_le.mpr ⟨by linarith [hv.1], hv.2⟩
  rw [waveC, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.I_mul_re]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |(-z.im) * v| := le_abs_self _
    _ = |z.im| * |v| := by rw [abs_mul, abs_neg]
    _ ≤ _ := mul_le_mul_of_nonneg_left hvs (abs_nonneg _)

/-- The cosine-bump Fourier square holds at every complex frequency. -/
theorem cosineTransform_eq {V : ℝ} (hV : 0 < V) (z : ℂ) :
    cosineTransform V z = (2 / V : ℝ) * bumpTransform V z ^ 2 := by
  let b (v : ℝ) := (cosineBump V v : ℂ)
  let k (v : ℝ) := b v * waveC z v
  let M := ContinuousLinearMap.mul ℂ ℂ
  have hkI : Integrable k := by
    have hc : Continuous b := Complex.continuous_ofReal.comp (continuous_cosineBump hV)
    have hs : HasCompactSupport b := (cosineBump_hasCompactSupport V).comp_left Complex.ofReal_zero
    exact (hc.mul (continuous_waveC z)).integrable_of_hasCompactSupport hs.mul_right
  have hb : (fun v => (Params.autocorr (cosineBump V) v : ℂ)) =
      convolution b b M volume := Taper.ofReal_autocorr_eq_convolution (cosineBump_even V)
  have conv (u : ℝ) :
      (Params.autocorr (cosineBump V) u : ℂ) * waveC z u = convolution k k M volume u := by
    rw [congrFun hb u, convolution_def, convolution_def, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with v
    simp only [M, ContinuousLinearMap.mul_apply', k]
    rw [show u = v + (u - v) by ring, waveC_add]
    have he : v + (u - v) - v = u - v := by ring
    rw [he]
    ring
  unfold cosineTransform bumpTransform
  simp_rw [cosineWeight_eq_autocorr hV, Complex.ofReal_mul, paperFT_def]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  simp_rw [← mul_assoc Complex.I z]
  change (2 / V : ℝ) * (∫ u, (Params.autocorr (cosineBump V) u : ℂ) * waveC z u) =
    (2 / V : ℝ) * (∫ v, k v)^2
  congr 1
  simp_rw [conv]
  rw [MeasureTheory.integral_convolution M hkI hkI, ContinuousLinearMap.mul_apply', sq]

private def inside (V v : ℝ) : ℝ := Real.cos (Real.pi * v / V)

private def slope (V v : ℝ) : ℝ := -(Real.pi / V) * Real.sin (Real.pi * v / V)

private theorem inside_deriv {V : ℝ} (v : ℝ) : HasDerivAt (inside V) (slope V v) v := by
  have h := (((hasDerivAt_id v).const_mul Real.pi).div_const V).cos
  convert h using 1 <;> first | rfl | (simp only [id_eq, mul_one, slope]; ring)

private theorem inside_endpoints {V : ℝ} (hV : 0 < V) :
    inside V (-V / 2) = 0 ∧ inside V (V / 2) = 0 := by
  have h₁ : Real.pi * (-V / 2) / V = -(Real.pi / 2) := by field_simp [hV.ne']
  have h₂ : Real.pi * (V / 2) / V = Real.pi / 2 := by field_simp [hV.ne']
  simp [inside, h₁, h₂, Real.cos_pi_div_two]

private theorem integral_abs_slope {V : ℝ} (hV : 0 < V) :
    (∫ v in (-V / 2)..(V / 2), |slope V v|) = 2 := by
  have hl : -V / 2 ≤ (0 : ℝ) := by linarith
  have hu : (0 : ℝ) ≤ V / 2 := by positivity
  have hs : Continuous (slope V) := by unfold slope; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hs.abs.intervalIntegrable (-V/2) 0)
    (hs.abs.intervalIntegrable 0 (V/2))]
  have h₁ : (∫ v in (-V / 2)..0, |slope V v|) = ∫ v in (-V / 2)..0, slope V v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hl] at hv
    have hsin : Real.sin (Real.pi * v / V) ≤ 0 := by
      apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
      · exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hv.2) hV.le
      · apply (le_div_iff₀ hV).mpr
        have h : -V ≤ v := by linarith [hv.1]
        simpa only [mul_neg, neg_mul] using mul_le_mul_of_nonneg_left h Real.pi_pos.le
    exact abs_of_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (div_nonneg Real.pi_pos.le hV.le)) hsin)
  have h₂ : (∫ v in (0 : ℝ)..(V / 2), |slope V v|) = ∫ v in (0 : ℝ)..(V / 2), -slope V v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hu] at hv
    have hsin : 0 ≤ Real.sin (Real.pi * v / V) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · exact div_nonneg (mul_nonneg Real.pi_pos.le hv.1) hV.le
      · apply (div_le_iff₀ hV).mpr
        have h : v ≤ V := by linarith [hv.2]
        exact mul_le_mul_of_nonneg_left h Real.pi_pos.le
    exact abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg Real.pi_pos.le hV.le)) hsin)
  rw [h₁, h₂, intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => inside_deriv v) (hs.intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => inside_deriv v) (hs.intervalIntegrable _ _),
    (inside_endpoints hV).1, (inside_endpoints hV).2]
  norm_num [inside]

private theorem bumpTransform_eq_interval {V : ℝ} (hV : 0 < V) (z : ℂ) :
    bumpTransform V z = ∫ v in (-V / 2)..(V / 2), (inside V v : ℂ) * waveC z v := by
  rw [bumpTransform, paperFT_def, intervalIntegral.integral_of_le (by linarith : -V / 2 ≤ V / 2),
    ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with v
  by_cases hv : v ∈ Icc (-V / 2) (V / 2)
  · simp [cosineBump, indicator_of_mem hv, inside, waveC]
  · simp [cosineBump, indicator_of_notMem hv]

private theorem bumpTransform_mul_frequency {V : ℝ} (hV : 0 < V) (z : ℂ) :
    bumpTransform V z * (Complex.I * z) =
      -∫ v in (-V / 2)..(V / 2), (slope V v : ℂ) * waveC z v := by
  have h₁ : Continuous (fun v : ℝ => (slope V v : ℂ)) := by unfold slope; fun_prop
  have h₂ : Continuous (fun v => waveC z v * (Complex.I * z)) :=
    (continuous_waveC z).mul continuous_const
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := -V / 2) (b := V / 2)
    (fun v _ => (inside_deriv (V := V) v).ofReal_comp)
    (fun v _ => waveC_hasDerivAt z v)
    (h₁.intervalIntegrable _ _) (h₂.intervalIntegrable _ _)
  rw [(inside_endpoints hV).1, (inside_endpoints hV).2, Complex.ofReal_zero,
    zero_mul, zero_mul, sub_self, zero_sub] at hb
  rw [bumpTransform_eq_interval hV, ← intervalIntegral.integral_mul_const, ← hb]
  apply intervalIntegral.integral_congr
  intro v _
  ring

/-- Strip decay of the unnormalized Fourier bump, with its exact first
derivative variation constant. -/
theorem norm_bumpTransform_mul_freq_le {V : ℝ} (hV : 0 < V) (z : ℂ) :
    ‖bumpTransform V z‖ * ‖z‖ ≤ 2 * Real.exp (|z.im| * (V / 2)) := by
  let E := Real.exp (|z.im| * (V / 2))
  have hl : -V / 2 ≤ V / 2 := by linarith
  have hs : Continuous (slope V) := by unfold slope; fun_prop
  have hc : Continuous (fun v => (slope V v : ℂ) * waveC z v) :=
    (Complex.continuous_ofReal.comp hs).mul (continuous_waveC z)
  have hfactor : ‖bumpTransform V z * (Complex.I * z)‖ = ‖bumpTransform V z‖ * ‖z‖ := by
    simp [norm_mul]
  rw [← hfactor, bumpTransform_mul_frequency hV, norm_neg]
  calc
    _ ≤ ∫ v in (-V / 2)..(V / 2), ‖(slope V v : ℂ) * waveC z v‖ :=
      intervalIntegral.norm_integral_le_integral_norm hl
    _ ≤ ∫ v in (-V / 2)..(V / 2), |slope V v| * E := by
      apply intervalIntegral.integral_mono_on hl (hc.norm.intervalIntegrable _ _)
        ((hs.abs.mul continuous_const).intervalIntegrable _ _)
      intro v hv
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_waveC_le z hV hv) (abs_nonneg _)
    _ = _ := by rw [intervalIntegral.integral_mul_const, integral_abs_slope hV]

theorem norm_cosineTransform_pole_le {V : ℝ} (hV : 0 < V) (t : ℝ) (σ : ℝ)
    (hσ : |σ| = 1 / 2) :
    ‖cosineTransform V ((t : ℂ) + (σ : ℂ) * Complex.I)‖ ≤
      8 * Real.exp (V / 2) / (V * (t^2 + 1 / 4)) := by
  let z := (t : ℂ) + (σ : ℂ) * Complex.I
  have hzim : z.im = σ := by simp [z, Complex.mul_im]
  have hzre : z.re = t := by simp [z, Complex.mul_re]
  have hσsq : σ^2 = 1 / 4 := by
    rw [← sq_abs σ, hσ]
    norm_num
  have hzsq : ‖z‖ ^ 2 = t^2 + 1 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    nlinarith
  have hprod := norm_bumpTransform_mul_freq_le hV z
  rw [hzim, hσ] at hprod
  have hsq := pow_le_pow_left₀ (show 0 ≤ ‖bumpTransform V z‖ * ‖z‖ by positivity) hprod 2
  rw [mul_pow, hzsq, mul_pow, ← Real.exp_nat_mul] at hsq
  have he : (2 : ℕ) * ((1 / 2 : ℝ) * (V / 2)) = V / 2 := by push_cast; ring
  rw [he] at hsq
  change ‖cosineTransform V z‖ ≤ _
  rw [cosineTransform_eq hV, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / V)]
  apply (le_div_iff₀ (by positivity : 0 < V * (t^2 + 1 / 4))).mpr
  have h := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)
  field_simp [hV.ne'] <;> nlinarith only [h]

/-- Integrability and inversion give the exact mass of the cosine transform. -/
theorem cosineTransform_real_integral {V : ℝ} (hV : 0 < V) :
    Integrable (fun t : ℝ => (cosineTransform V (t : ℂ)).re) ∧
      (∫ t : ℝ, (cosineTransform V (t : ℂ)).re) = 2 * Real.pi := by
  let K (t : ℝ) := (cosineTransform V (t : ℂ)).re
  let b (v : ℝ) := (cosineBump V v : ℂ)
  have hc : Continuous (cosineWeight V) := continuous_cosineWeight hV
  have hcs := cosineWeight_hasCompactSupport V
  have hB (t : ℝ) : ‖bumpTransform V (t : ℂ)‖ ≤ ∫ v, ‖b v‖ := by
    rw [bumpTransform, paperFT_def]
    apply (norm_integral_le_integral_norm _).trans_eq
    apply integral_congr_ae
    filter_upwards with v
    change ‖b v * waveC (t : ℂ) v‖ = ‖b v‖
    unfold waveC
    rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_mul_re, Complex.ofReal_im, neg_zero, zero_mul, mul_zero, sub_zero, Real.exp_zero, mul_one]
  have hreal (t : ℝ) : cosineTransform V (t : ℂ) = (K t : ℂ) :=
    Taper.paperFT_ofReal_eq_re (cosineWeight_even V) t
  have hK : Integrable K := by
    apply Taper.integrable_of_abs_mul_one_add_sq_le
      ((Taper.contDiff_re_paperFT_ofReal (Complex.continuous_ofReal.comp hc)
        (hcs.comp_left Complex.ofReal_zero) 0).continuous)
      (K := (2 / V) * ((∫ v, ‖b v‖)^2 + 4))
    intro t
    change |K t| * (1 + t^2) ≤ _
    rw [abs_of_nonneg (cosineTransform_ofReal_nonneg hV t)]
    have hkn : K t = (2 / V) * ‖bumpTransform V (t : ℂ)‖^2 := by
      have h := congrArg norm (cosineTransform_ofReal_eq hV t)
      rw [hreal, Complex.norm_real, Real.norm_of_nonneg (cosineTransform_ofReal_nonneg hV t),
        norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / V)] at h
      exact h
    change K t * (1 + t^2) ≤ _
    rw [hkn]
    have hBsq := pow_le_pow_left₀ (norm_nonneg _) (hB t) 2
    have hD := norm_bumpTransform_mul_freq_le hV (t : ℂ)
    simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, mul_one,
      Complex.norm_real, Real.norm_eq_abs] at hD
    have hDsq := pow_le_pow_left₀ (by positivity : 0 ≤ ‖bumpTransform V (t : ℂ)‖ * |t|) hD 2
    rw [mul_pow, sq_abs] at hDsq
    calc
      _ = (2 / V) * (‖bumpTransform V (t : ℂ)‖^2 + ‖bumpTransform V (t : ℂ)‖^2 * t^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hBsq (by norm_num at hDsq ⊢; exact hDsq))
        (by positivity)
  refine ⟨hK, ?_⟩
  have h := Taper.integral_mul_cos_of_paperFT_eq hc (hc.integrable_of_hasCompactSupport hcs)
    hK hreal 0
  simpa only [mul_zero, Real.cos_zero, mul_one, cosineWeight_zero hV.le] using h

end GoldbachExplicit
