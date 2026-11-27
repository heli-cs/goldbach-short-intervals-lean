import Goldbach.Explicit.CoefficientMass

/-! Width-sensitive bounds at small frequencies, using the compact inverse test. -/

open Filter MeasureTheory
noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum Zeta23

private theorem inverseTest_nonneg (lam u : ℝ) : 0 ≤ inverseTest lam u := by
  unfold inverseTest
  split
  · exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.one_le_exp (by linarith)))
  · exact le_rfl

private theorem integrable_inverseTest_cos (lam t : ℝ) :
    Integrable (fun u => inverseTest lam u * Real.cos (t * u)) := by
  apply (inverseTest_integrable lam).mul_bdd (c := 1) (by fun_prop)
  exact Eventually.of_forall (fun u => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

private theorem coefficient_sq_eq_integral_cos {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) :
    ‖coefficient lam t‖^2 = ∫ u, inverseTest lam u * Real.cos (t * u) := by
  have h := congrArg Complex.re (inverseTest_paperFT hlam t)
  have hi : Integrable (fun u => (inverseTest lam u : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))) := by
    have h₀ := Complex.ofRealCLM.integrable_comp (inverseTest_integrable lam)
    apply h₀.mul_bdd (c := 1) (by fun_prop)
    filter_upwards with u
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  unfold paperFT at h
  have hre : (∫ u, (inverseTest lam u : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))).re =
      ∫ u, ((inverseTest lam u : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))).re :=
    (integral_re hi).symm
  change (∫ u, (inverseTest lam u : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))).re = _ at h
  rw [hre, Complex.ofReal_re] at h
  refine h.symm.trans (integral_congr_ae (Eventually.of_forall fun u => ?_))
  change ((inverseTest lam u : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))).re = _
  rw [Complex.re_ofReal_mul, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

private theorem coefficient_zero_norm_le {lam : ℝ} (hlam : 0 ≤ lam) :
    ‖coefficient lam 0‖ ≤ lam * Real.exp (lam / 2) := by
  have hz : coefficient lam 0 = (2 * (Real.exp (lam / 2) - 1) : ℝ) := by
    rw [coefficient_formula, show exponent 1 0 = (1 / 2 : ℂ) by simp [exponent],
      show (1 / 2 : ℂ) * (lam : ℂ) = ((lam / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
    push_cast
    ring
  have hE : 1 ≤ Real.exp (lam / 2) := Real.one_le_exp (by linarith)
  have h := Real.add_one_le_exp (-(lam / 2))
  rw [Real.exp_neg] at h
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (lam / 2)).le
  rw [inv_mul_cancel₀ (Real.exp_pos (lam / 2)).ne'] at hm
  rw [hz, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  nlinarith only [hm]

private theorem inverseTest_integral_le {lam : ℝ} (hlam : 0 ≤ lam) :
    (∫ u, inverseTest lam u) ≤ lam^2 * Real.exp lam := by
  have h := coefficient_sq_eq_integral_cos hlam 0
  simp only [zero_mul, Real.cos_zero, mul_one] at h
  rw [← h]
  have hn := pow_le_pow_left₀ (norm_nonneg _) (coefficient_zero_norm_le hlam) 2
  rw [mul_pow, ← Real.exp_nat_mul, show (2 : ℕ) * (lam / 2) = lam by push_cast; ring] at hn
  exact hn

/-- Uniform squared coefficient bound with the correct power of the width. -/
theorem coefficient_sq_uniform_le {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) :
    ‖coefficient lam t‖^2 ≤ lam^2 * Real.exp lam := by
  rw [coefficient_sq_eq_integral_cos hlam]
  apply (integral_mono (integrable_inverseTest_cos lam t) (inverseTest_integrable lam)
    (fun u => mul_le_of_le_one_right (inverseTest_nonneg lam u) (Real.cos_le_one _))).trans
  exact inverseTest_integral_le hlam

/-- Differentiating the compact Fourier test costs one more power of the width. -/
theorem coefficient_sq_uniform_deriv_le {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) :
    |deriv (fun s => ‖coefficient lam s‖^2) t| ≤ lam^3 * Real.exp lam := by
  rw [← Real.norm_eq_abs]
  apply norm_deriv_le_of_lip' (by positivity)
  apply Eventually.of_forall
  intro s
  have hS := integrable_inverseTest_cos lam s
  have hT := integrable_inverseTest_cos lam t
  have hpoint (u : ℝ) :
      |inverseTest lam u * Real.cos (s * u) - inverseTest lam u * Real.cos (t * u)| ≤
        (lam * |s - t|) * inverseTest lam u := by
    by_cases hu : |u| ≤ lam
    · have hc : |Real.cos (s * u) - Real.cos (t * u)| ≤ |(s - t) * u| := by
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul, sub_mul] using
          Real.lipschitzWith_cos.dist_le_mul (s * u) (t * u)
      rw [abs_mul] at hc
      have hd := (mul_le_mul_of_nonneg_left hu (abs_nonneg (s - t)))
      rw [← mul_sub, abs_mul, abs_of_nonneg (inverseTest_nonneg lam u)]
      calc
        _ ≤ inverseTest lam u * (|s - t| * lam) :=
          mul_le_mul_of_nonneg_left (hc.trans hd) (inverseTest_nonneg _ _)
        _ = _ := by ring
    · simp [inverseTest, hu]
  simp only [Real.norm_eq_abs, coefficient_sq_eq_integral_cos hlam, ← integral_sub hS hT]
  calc
    _ ≤ ∫ u, |inverseTest lam u * Real.cos (s * u) -
        inverseTest lam u * Real.cos (t * u)| := abs_integral_le_integral_abs
    _ ≤ ∫ u, (lam * |s - t|) * inverseTest lam u := by
      have hi : Integrable (fun u => inverseTest lam u * Real.cos (s * u) -
        inverseTest lam u * Real.cos (t * u)) := hS.sub hT
      exact integral_mono hi.abs ((inverseTest_integrable _).const_mul _) hpoint
    _ ≤ _ := by
      rw [integral_const_mul]
      have hm := mul_le_mul_of_nonneg_left (inverseTest_integral_le hlam)
        (mul_nonneg hlam (abs_nonneg (s - t)))
      nlinarith only [hm]

end GoldbachExplicit
