import Goldbach.Gaussian

open MeasureTheory Set
open scoped Interval

noncomputable section
namespace GoldbachSpectrum

def exponent (r t : ℝ) : ℂ := (r : ℂ) / 2 + (t : ℂ) * Complex.I

def coefficient (lam γ : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..lam, Complex.exp (exponent 1 γ * (s : ℂ))

def profileIntegral (lam u : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..1, Complex.exp (exponent lam u * (s : ℂ))

def profile (lam u : ℝ) : ℝ := ‖profileIntegral lam u‖ ^ 2

theorem exponent_re (r t : ℝ) : (exponent r t).re = r / 2 := by
  simp [exponent]

theorem exponent_im (r t : ℝ) : (exponent r t).im = t := by
  simp [exponent]

theorem norm_exp_exponent_mul (r t s : ℝ) :
    ‖Complex.exp (exponent r t * (s : ℂ))‖ = Real.exp (r * s / 2) := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, exponent_re]
  congr 1
  ring

private theorem exponent_one_ne_zero (γ : ℝ) : exponent 1 γ ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [exponent_re] at hre

theorem coefficient_formula (lam γ : ℝ) :
    coefficient lam γ = (Complex.exp (exponent 1 γ * (lam : ℂ)) - 1) / exponent 1 γ := by
  rw [coefficient, integral_exp_mul_complex (exponent_one_ne_zero γ)]
  simp

theorem coefficient_scale (lam γ : ℝ) :
    coefficient lam γ = (lam : ℂ) * profileIntegral lam (lam * γ) := by
  unfold coefficient profileIntegral
  have h := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (fun s : ℝ => Complex.exp (exponent 1 γ * (s : ℂ))) lam
  simp only [mul_zero, mul_one, Complex.real_smul] at h
  rw [← h]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  apply congrArg Complex.exp
  unfold exponent
  push_cast
  ring

theorem coefficient_sq_scale {lam γ : ℝ} (hlam : 0 ≤ lam) :
    ‖coefficient lam γ‖ ^ 2 = lam^2 * profile lam (lam * γ) := by
  rw [coefficient_scale, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlam, mul_pow, profile]

private theorem norm_profile_le {lam u : ℝ} (hlam : 0 ≤ lam) :
    ‖profileIntegral lam u‖ ≤ Real.exp (lam / 2) := by
  unfold profileIntegral
  have hi : IntervalIntegrable (fun s : ℝ => Complex.exp (exponent lam u * (s : ℂ)))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    _ ≤ ∫ s : ℝ in 0..1, ‖Complex.exp (exponent lam u * (s : ℂ))‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ _ : ℝ in 0..1, Real.exp (lam / 2) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hi.norm intervalIntegrable_const
      intro s hs
      rw [norm_exp_exponent_mul]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hs.2 hlam]
    _ = _ := by simp

theorem profile_le_exp_one {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (u : ℝ) :
    profile lam u ≤ Real.exp 1 := by
  unfold profile
  have h := (norm_profile_le (u := u) hlam₀).trans
    (Real.exp_le_exp.mpr (show lam / 2 ≤ 1 / 2 by linarith))
  calc
    _ ≤ (Real.exp (1 / 2))^2 := pow_le_pow_left₀ (norm_nonneg _) h _
    _ = _ := by rw [← Real.exp_nat_mul]; norm_num

/-- The inverse-square estimate, stated without division at zero. -/
theorem sq_mul_profile_le {lam : ℝ} (_hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (u : ℝ) :
    u^2 * profile lam u ≤ (1 + Real.exp (1 / 2))^2 := by
  by_cases hu : u = 0
  · simp [hu]
    positivity
  have hz : exponent lam u ≠ 0 := by
    intro h
    apply hu
    simpa only [exponent_im, Complex.zero_im] using congrArg Complex.im h
  have hexact : profileIntegral lam u =
      (Complex.exp (exponent lam u) - 1) / exponent lam u := by
    rw [profileIntegral, integral_exp_mul_complex hz]
    simp
  have hden : |u| ≤ ‖exponent lam u‖ := by
    simpa only [exponent_im] using Complex.abs_im_le_norm (exponent lam u)
  have hnum : ‖Complex.exp (exponent lam u) - 1‖ ≤ 1 + Real.exp (1 / 2) := by
    have htri := norm_sub_le (Complex.exp (exponent lam u)) (1 : ℂ)
    rw [norm_one, Complex.norm_exp, exponent_re] at htri
    linarith [Real.exp_le_exp.mpr (show lam / 2 ≤ 1 / 2 by linarith)]
  have hmul : |u| * ‖profileIntegral lam u‖ ≤ 1 + Real.exp (1 / 2) := by
    rw [hexact, norm_div]
    calc
      _ ≤ ‖exponent lam u‖ * (‖Complex.exp (exponent lam u) - 1‖ / ‖exponent lam u‖) :=
        mul_le_mul_of_nonneg_right hden (by positivity)
      _ = ‖Complex.exp (exponent lam u) - 1‖ := by
        rw [mul_comm, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]
      _ ≤ _ := hnum
  rw [profile, ← sq_abs u, ← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hmul _


theorem norm_profileIntegral_sub_le {lam : ℝ} (hlam : 0 ≤ lam) (u : ℝ) :
    ‖profileIntegral lam u - profileIntegral 0 u‖ ≤ Real.exp (lam / 2) - 1 := by
  let f := fun (r s : ℝ) => Complex.exp (exponent r u * (s : ℂ))
  have hi (r : ℝ) : IntervalIntegrable (f r) volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp [f]
    fun_prop
  change ‖(∫ s in (0 : ℝ)..1, f lam s) - (∫ s in (0 : ℝ)..1, f 0 s)‖ ≤ _
  rw [← intervalIntegral.integral_sub (hi lam) (hi 0)]
  calc
    _ ≤ ∫ s in (0 : ℝ)..1, ‖f lam s - f 0 s‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ _ : ℝ in 0..1, (Real.exp (lam / 2) - 1) := by
      apply intervalIntegral.integral_mono_on (by norm_num) ((hi lam).sub (hi 0)).norm
        intervalIntegrable_const
      intro s hs
      have he : f lam s = (Real.exp (lam * s / 2) : ℂ) * f 0 s := by
        dsimp [f]
        rw [Complex.ofReal_exp, ← Complex.exp_add]
        apply congrArg Complex.exp
        unfold exponent
        push_cast
        ring
      have hf₀ : ‖f 0 s‖ = 1 := by simp [f, norm_exp_exponent_mul]
      rw [he, ← sub_one_mul, norm_mul, hf₀, mul_one, ← Complex.ofReal_one,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hp : 0 ≤ lam * s / 2 := by exact div_nonneg (mul_nonneg hlam hs.1) (by norm_num)
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hp))]
      apply sub_le_sub_right (Real.exp_le_exp.mpr _) _
      nlinarith [mul_le_mul_of_nonneg_left hs.2 hlam]
    _ = _ := by simp

/-- A uniform estimate over all real frequencies for the convergence
of the squared profiles as the relative log width tends to zero. -/
theorem profile_sub_le {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (u : ℝ) :
    |profile lam u - profile 0 u| ≤
      (Real.exp (1 / 2) + 1) * (Real.exp (lam / 2) - 1) := by
  have ha := (norm_profile_le (u := u) hlam₀).trans
    (Real.exp_le_exp.mpr (show lam / 2 ≤ 1 / 2 by linarith))
  have hb : ‖profileIntegral 0 u‖ ≤ 1 := by
    simpa using norm_profile_le (u := u) (le_rfl : (0 : ℝ) ≤ 0)
  rw [profile, profile, show ‖profileIntegral lam u‖^2 - ‖profileIntegral 0 u‖^2 =
    (‖profileIntegral lam u‖ + ‖profileIntegral 0 u‖) *
      (‖profileIntegral lam u‖ - ‖profileIntegral 0 u‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul (add_le_add ha hb)
    ((abs_norm_sub_norm_le _ _).trans (norm_profileIntegral_sub_le hlam₀ u))
    (abs_nonneg _) (by positivity)

end GoldbachSpectrum
