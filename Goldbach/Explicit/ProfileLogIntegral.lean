import Goldbach.Explicit.CoefficientMass
import Goldbach.Explicit.LogMoments

/-! The main density integral for the sharp spectral coefficient. -/

open MeasureTheory Set
open scoped Interval
noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum

private theorem exponent_ne_of_width {lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    exponent lam u ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [exponent_re, Complex.zero_re] at hre
  linarith

private theorem profileIntegral_eq_of_width {lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    profileIntegral lam u = (Complex.exp (exponent lam u) - 1) / exponent lam u := by
  rw [profileIntegral, integral_exp_mul_complex (exponent_ne_of_width hlam u)]
  simp

private theorem continuous_profile {lam : ℝ} (hlam : 0 < lam) : Continuous (profile lam) := by
  have hc : Continuous (exponent lam) := by unfold exponent; fun_prop
  unfold profile
  simp_rw [profileIntegral_eq_of_width hlam]
  exact (((hc.cexp.sub continuous_const).div hc (exponent_ne_of_width hlam)).norm.pow 2)

private theorem profile_le_exp_width {lam : ℝ} (hlam : 0 ≤ lam) (u : ℝ) :
    profile lam u ≤ Real.exp lam := by
  have hi : Continuous (fun s : ℝ => Complex.exp (exponent lam u * (s : ℂ))) := by fun_prop
  have h : ‖profileIntegral lam u‖ ≤ Real.exp (lam / 2) := by
    unfold profileIntegral
    calc
      _ ≤ ∫ s : ℝ in 0..1, ‖Complex.exp (exponent lam u * (s : ℂ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ _ : ℝ in 0..1, Real.exp (lam / 2) := by
        apply intervalIntegral.integral_mono_on zero_le_one (hi.norm.intervalIntegrable _ _)
          intervalIntegrable_const
        intro s hs
        rw [norm_exp_exponent_mul]
        exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hs.2 hlam])
      _ = _ := by simp
  unfold profile
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring)

private theorem sq_mul_profile_le_exp_width {lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    u^2 * profile lam u ≤ 4 * Real.exp lam := by
  have hd : |u| ≤ ‖exponent lam u‖ := by
    simpa only [exponent_im] using Complex.abs_im_le_norm (exponent lam u)
  have hn := norm_sub_le (Complex.exp (exponent lam u)) (1 : ℂ)
  rw [norm_one, Complex.norm_exp, exponent_re] at hn
  have he : 1 ≤ Real.exp (lam / 2) := Real.one_le_exp (by linarith)
  have h : |u| * ‖profileIntegral lam u‖ ≤ 2 * Real.exp (lam / 2) := by
    calc
      _ ≤ ‖exponent lam u‖ * ‖profileIntegral lam u‖ :=
        mul_le_mul_of_nonneg_right hd (norm_nonneg _)
      _ = ‖Complex.exp (exponent lam u) - 1‖ := by
        rw [profileIntegral_eq_of_width hlam, norm_div, mul_comm, div_mul_cancel₀ _
          (norm_ne_zero_iff.mpr (exponent_ne_of_width hlam u))]
      _ ≤ _ := by linarith
  have hq := pow_le_pow_left₀ (by positivity : 0 ≤ |u| * ‖profileIntegral lam u‖) h 2
  rw [mul_pow, sq_abs, mul_pow, ← Real.exp_nat_mul,
    show (2 : ℕ) * (lam / 2) = lam by push_cast; ring] at hq
  simpa only [profile, show (2 : ℝ)^2 = 4 by norm_num] using hq

/-- The main density integral uses the full sharp profile. Its leading
coefficient is fixed by the exact Fourier mass. -/
theorem coefficient_log_square_integral_le {lam : ℝ} (hlam : 0 < lam) (hlam₁ : lam ≤ 1) :
    IntegrableOn (fun t => ‖coefficient lam t‖^2 * (Real.log t)^2) (Ioi (0 : ℝ)) ∧
      (∫ t in Ioi (0 : ℝ), ‖coefficient lam t‖^2 * (Real.log t)^2) ≤
        Real.pi * (Real.exp lam - 1) * (-Real.log lam)^2 +
          lam * Real.exp lam * (8 * (-Real.log lam) + 10) := by
  let B := -Real.log lam
  let F := profile lam
  let Q (u : ℝ) := F u * (B + Real.log u)^2
  have hB : 0 ≤ B := neg_nonneg.mpr (Real.log_nonpos hlam.le hlam₁)
  have hFi : Integrable F := by
    refine (integrable_inv_one_add_sq.const_mul (5 * Real.exp lam)).mono'
      (continuous_profile hlam).aestronglyMeasurable ?_
    filter_upwards with u
    have hn : 0 ≤ F u := sq_nonneg _
    rw [Real.norm_of_nonneg hn, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have h₁ : F u ≤ Real.exp lam := profile_le_exp_width hlam.le u
    have h₂ : u^2 * F u ≤ 4 * Real.exp lam := sq_mul_profile_le_exp_width hlam u
    nlinarith only [h₁, h₂]
  have hle (u : ℝ) (hu : 0 < u) : F u ≤ 4 * Real.exp lam / u^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
    have h : u^2 * F u ≤ 4 * Real.exp lam := sq_mul_profile_le_exp_width hlam u
    rwa [mul_comm] at h
  obtain ⟨hQi, hQbound⟩ := integral_log_sq_le_of_envelope (continuous_profile hlam).measurable
    hFi.integrableOn hB (Real.exp_pos lam).le (fun _ _ => sq_nonneg _)
    (fun u _ => profile_le_exp_width hlam.le u) hle
  have hs (g : ℝ → ℝ) : (∫ t in Ioi (0 : ℝ), g (lam * t)) =
      lam⁻¹ * (∫ u in Ioi (0 : ℝ), g u) := by
    simpa only [mul_zero, smul_eq_mul] using integral_comp_mul_left_Ioi g (0 : ℝ) hlam
  have hMass : lam * (∫ u in Ioi (0 : ℝ), F u) = Real.pi * (Real.exp lam - 1) := by
    have h := coefficient_sq_integral_positive hlam.le hlam₁
    simp_rw [coefficient_sq_scale hlam.le] at h
    change (∫ t in Ioi (0 : ℝ), lam^2 * F (lam * t)) = _ at h
    rw [integral_const_mul, hs] at h
    rwa [← mul_assoc, pow_two, mul_assoc lam lam, mul_inv_cancel₀ hlam.ne', mul_one] at h
  have hEq (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      ‖coefficient lam t‖^2 * (Real.log t)^2 = lam^2 * Q (lam * t) := by
    rw [coefficient_sq_scale hlam.le]
    have hlog := Real.log_mul hlam.ne' (mem_Ioi.mp ht).ne'
    dsimp [Q, F, B]
    rw [hlog]
    ring
  have hQshift : IntegrableOn (fun t => Q (lam * t)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff _ _ hlam).2
    simpa only [mul_zero] using hQi
  have hQi' : IntegrableOn (fun t => lam^2 * Q (lam * t)) (Ioi (0 : ℝ)) := hQshift.const_mul _
  refine ⟨hQi'.congr_fun (fun t ht => (hEq t ht).symm) measurableSet_Ioi, ?_⟩
  calc
    (∫ t in Ioi (0 : ℝ), ‖coefficient lam t‖^2 * (Real.log t)^2) =
        ∫ t in Ioi (0 : ℝ), lam^2 * Q (lam * t) :=
      setIntegral_congr_fun measurableSet_Ioi hEq
    _ = lam * (∫ u in Ioi (0 : ℝ), Q u) := by
      rw [integral_const_mul, hs, ← mul_assoc, pow_two, mul_assoc lam lam,
        mul_inv_cancel₀ hlam.ne', mul_one]
    _ ≤ lam * (B^2 * (∫ u in Ioi (0 : ℝ), F u) + Real.exp lam * (8 * B + 10)) :=
      mul_le_mul_of_nonneg_left hQbound hlam.le
    _ = _ := by
      change _ = Real.pi * (Real.exp lam - 1) * B^2 + lam * Real.exp lam * (8 * B + 10)
      rw [← hMass]
      ring

end GoldbachExplicit
