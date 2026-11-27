import Mathlib

open MeasureTheory Set

noncomputable section
namespace GoldbachLogIntegral

/-- The logarithmic change of variables is valid for Bochner set
integrals, with the exact Jacobian `dy/y`. -/
theorem integral_log_change {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (f : ℝ → ℝ) :
    (∫ y in Icc u v, f (Real.log y) / y) =
      ∫ t in Icc (Real.log u) (Real.log v), f t := by
  have hpre : Real.exp '' Icc (Real.log u) (Real.log v) = Icc u v := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by simpa only [Real.exp_log hu] using Real.exp_le_exp.mpr ht.1,
        by simpa only [Real.exp_log hv] using Real.exp_le_exp.mpr ht.2⟩
    · intro hy
      have hy0 : 0 < y := hu.trans_le hy.1
      exact ⟨Real.log y, ⟨Real.log_le_log hu hy.1, Real.log_le_log hy0 hy.2⟩,
        Real.exp_log hy0⟩
  have hchange := integral_image_eq_integral_abs_deriv_smul (f := Real.exp)
    (f' := Real.exp) (s := Icc (Real.log u) (Real.log v)) measurableSet_Icc
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn (fun y => f (Real.log y) / y)
  rw [hpre] at hchange
  refine hchange.trans (setIntegral_congr_fun measurableSet_Icc (fun t _ => ?_))
  rw [smul_eq_mul, abs_of_pos (Real.exp_pos t), Real.log_exp]
  exact mul_div_cancel₀ _ (Real.exp_pos t).ne' |> fun h => by simpa [mul_div_assoc, mul_comm] using h

/-- The square-root normalization in the explicit formula combines
with the logarithmic Jacobian to give a denominator of `y²`. -/
theorem integral_normalized_error {u v z : ℝ} (hu : 0 < u) (hv : 0 < v)
    (w A : ℝ → ℝ) :
    (∫ y in Icc u v, w (Real.log y - z) * (A y)^2 / y^2) =
      ∫ t in Icc (Real.log u) (Real.log v),
        w (t - z) * (A (Real.exp t) / Real.sqrt (Real.exp t))^2 := by
  rw [← integral_log_change hu hv (fun t => w (t - z) *
    (A (Real.exp t) / Real.sqrt (Real.exp t))^2)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  have hy' : 0 < y := hu.trans_le hy.1
  simp only [Real.exp_log hy', div_pow, Real.sq_sqrt hy'.le]
  ring

/-- Removing both possible prime-power endpoints is legitimate almost
everywhere. Excluding all natural endpoints gives the stronger null-set statement. -/
theorem ae_avoids_natural_endpoints {d : ℝ} (hd : 0 < 1 + d) :
    ∀ᵐ y : ℝ ∂volume, (∀ n : ℕ, y ≠ (n : ℝ)) ∧
      (∀ n : ℕ, (1 + d) * y ≠ (n : ℝ)) := by
  have h₁ : ∀ᵐ y : ℝ ∂volume, y ∉ range (fun n : ℕ => (n : ℝ)) :=
    ae_iff.mpr (by
      simp only [not_not, ofPred_mem_eq]
      exact (countable_range _).measure_zero (μ := (volume : Measure ℝ)))
  have h₂ : ∀ᵐ y : ℝ ∂volume, y ∉ range (fun n : ℕ => (n : ℝ) / (1 + d)) :=
    ae_iff.mpr (by
      simp only [not_not, ofPred_mem_eq]
      exact (countable_range _).measure_zero (μ := (volume : Measure ℝ)))
  filter_upwards [h₁, h₂] with y hy₁ hy₂
  refine ⟨fun n h => hy₁ ⟨n, h.symm⟩, fun n h => hy₂ ⟨n, ?_⟩⟩
  apply (div_eq_iff hd.ne').mpr
  simpa only [mul_comm] using h.symm

end GoldbachLogIntegral
