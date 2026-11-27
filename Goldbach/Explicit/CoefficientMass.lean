import Goldbach.Explicit.InverseTestTransform
import Goldbach.SpectrumEnergy
import Goldbach.Plancherel

/-! The exact angular-frequency mass of the squared sharp coefficient. -/

open MeasureTheory Set
open scoped FourierTransform Interval
noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum Zeta23

private theorem continuous_inverseTest (lam : ℝ) : Continuous (inverseTest lam) := by
  have h : Continuous (fun t : ℝ => Real.exp (|t| / 2) * (Real.exp (lam - |t|) - 1)) := by
    fun_prop
  unfold inverseTest
  exact h.if_le continuous_const continuous_abs continuous_const (fun t ht => by simp [ht])

private theorem inverseTest_hasCompactSupport (lam : ℝ) : HasCompactSupport (inverseTest lam) := by
  refine HasCompactSupport.intro' (K := Icc (-lam) lam) isCompact_Icc isClosed_Icc ?_
  intro t ht
  exact inverseTest_eq_zero_of_lt_abs (lt_of_not_ge (fun h => ht (abs_le.mp h)))

theorem inverseTest_integrable (lam : ℝ) : Integrable (inverseTest lam) :=
  (continuous_inverseTest lam).integrable_of_hasCompactSupport (inverseTest_hasCompactSupport lam)

/-- The squared sharp coefficient has total mass (2π(e^λ−1)). -/
theorem coefficient_sq_integral {lam : ℝ} (hlam : 0 ≤ lam) (hlam₁ : lam ≤ 1) :
    Integrable (fun t => ‖coefficient lam t‖^2) ∧
      (∫ t : ℝ, ‖coefficient lam t‖^2) = 2 * Real.pi * (Real.exp lam - 1) := by
  let h (t : ℝ) := ‖coefficient lam t‖^2
  let k (u : ℝ) : ℂ := (inverseTest lam u : ℂ)
  have hki : Integrable k :=
    (Complex.continuous_ofReal.comp (continuous_inverseTest lam)).integrable_of_hasCompactSupport
      ((inverseTest_hasCompactSupport lam).comp_left Complex.ofReal_zero)
  have hF (v : ℝ) : 𝓕 k v = (h (-(2 * Real.pi) * v) : ℂ) := by
    have ht := inverseTest_paperFT hlam (-(2 * Real.pi) * v)
    rw [EF.paperFT_ofReal_eq_fourier] at ht
    have he : -(-(2 * Real.pi) * v) / (2 * Real.pi) = v := by field_simp [Real.pi_ne_zero]
    rwa [he] at ht
  let C := Real.exp 1 + (1 + Real.exp (1 / 2))^2
  have hc (t : ℝ) : h t ≤ C / (1 + t^2) := coefficient_sq_le hlam hlam₁ t
  have hFi : Integrable (𝓕 k) := by
    have hg : Integrable (fun v : ℝ => C * (1 + (-(2 * Real.pi) * v)^2)⁻¹) :=
      (integrable_inv_one_add_sq.const_mul C).comp_mul_left'
        (neg_ne_zero.mpr (by positivity))
    have hFc : Continuous (𝓕 k) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hki
    refine hg.mono' hFc.aestronglyMeasurable (Filter.Eventually.of_forall (fun v => ?_))
    rw [hF, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    exact (hc _).trans_eq (div_eq_mul_inv _ _)
  have hIc := EF.integrable_paperFT_ofReal hFi
  simp_rw [show ∀ r : ℝ, paperFT k r = (h r : ℂ) from inverseTest_paperFT hlam] at hIc
  have hi : Integrable h := by
    have hr := Complex.reCLM.integrable_comp hIc
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using hr
  refine ⟨hi, ?_⟩
  have he := EF.paper_inversion (k := k)
    (Complex.continuous_ofReal.comp (continuous_inverseTest lam)) hki hFi 0
  change (inverseTest lam 0 : ℂ) = _ at he
  simp only [inverseTest_zero hlam, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    show ∀ r : ℝ, paperFT k r = (h r : ℂ) from inverseTest_paperFT hlam,
    integral_complex_ofReal, div_mul_eq_mul_div, one_mul] at he
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  have h' := ((eq_div_iff hπ).mp he).symm
  exact_mod_cast (show (↑(∫ t : ℝ, h t) : ℂ) =
    2 * (Real.pi : ℂ) * (Real.exp lam - 1 : ℝ) by rw [h']; ring)

/-- The positive half-line contains exactly half of the sharp Fourier mass. -/
theorem coefficient_sq_integral_positive {lam : ℝ} (hlam : 0 ≤ lam) (hlam₁ : lam ≤ 1) :
    (∫ t in Ioi (0 : ℝ), ‖coefficient lam t‖^2) = Real.pi * (Real.exp lam - 1) := by
  let f (t : ℝ) := ‖coefficient lam t‖^2
  have h (t : ℝ) : f |t| = f t := by
    unfold f
    rw [coefficient_sq_scale hlam, coefficient_sq_scale hlam]
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht.le, mul_neg, profile_even]
  have he : (∫ t : ℝ, f |t|) = ∫ t : ℝ, f t := by simp_rw [h]
  rw [integral_comp_abs] at he
  have hm : (∫ t : ℝ, f t) = 2 * Real.pi * (Real.exp lam - 1) :=
    (coefficient_sq_integral hlam hlam₁).2
  rw [hm] at he
  change (∫ t in Ioi (0 : ℝ), f t) = _
  linarith

end GoldbachExplicit
