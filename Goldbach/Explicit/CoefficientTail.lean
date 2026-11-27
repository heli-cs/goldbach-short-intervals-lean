import Goldbach.Coefficient

/-! Exact real-axis formula and tail bounds for the differentiated sharp coefficient. -/

open scoped ComplexConjugate
noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum

/-- Numerator in the real-axis quotient for the squared coefficient. -/
def sharpNumerator (lam t : ℝ) : ℝ :=
  (Real.exp (lam / 2))^2 + 1 - 2 * Real.exp (lam / 2) * Real.cos (lam * t)

/-- Exact squared sharp coefficient, including the constant numerator term. -/
theorem coefficient_sq_eq_quotient (lam t : ℝ) :
    ‖coefficient lam t‖^2 = sharpNumerator lam t / (t^2 + 1 / 4) := by
  let z := exponent 1 t * (lam : ℂ)
  have hz₁ : z.re = lam / 2 := by
    simp only [z, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, exponent_re,
      one_div, mul_zero, sub_zero]
    ring
  have hz₂ : z.im = lam * t := by
    simp only [z, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, exponent_im,
      mul_zero, zero_add]
    ring
  have hden : ‖exponent 1 t‖^2 = t^2 + 1 / 4 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, exponent_re, exponent_im]
    ring
  rw [coefficient_formula, norm_div, div_pow, hden]
  congr 1
  change ‖Complex.exp z - 1‖^2 = _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  simp only [map_one, mul_one]
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, Complex.exp_re, hz₁, hz₂]
  unfold sharpNumerator
  ring

/-- Squared sharp coefficients are continuously differentiable on the real axis. -/
theorem contDiff_coefficient_sq (lam : ℝ) :
    ContDiff ℝ 1 (fun t => ‖coefficient lam t‖^2) := by
  simp_rw [coefficient_sq_eq_quotient]
  have hn : ContDiff ℝ 1 (sharpNumerator lam) := by unfold sharpNumerator; fun_prop
  have hd : ContDiff ℝ 1 (fun t : ℝ => t^2 + 1 / 4) := by fun_prop
  exact hn.div hd (fun t => (by positivity : 0 < t^2 + 1 / 4).ne')

private theorem sharpNumerator_bounds {lam : ℝ} (hE : Real.exp (lam / 2) ≤ 11 / 10) (t : ℝ) :
    0 ≤ sharpNumerator lam t ∧ sharpNumerator lam t ≤ 5 := by
  let E := Real.exp (lam / 2)
  change E ≤ 11 / 10 at hE
  have hE₀ : 0 ≤ E := (Real.exp_pos _).le
  have hE₂ : E^2 ≤ (11 / 10 : ℝ)^2 := pow_le_pow_left₀ hE₀ hE 2
  have hcos₁ := mul_le_mul_of_nonneg_left (Real.cos_le_one (lam * t)) hE₀
  have hcos₂ := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (lam * t)) hE₀
  change 0 ≤ E^2 + 1 - 2 * E * Real.cos (lam * t) ∧
    E^2 + 1 - 2 * E * Real.cos (lam * t) ≤ 5
  exact ⟨by nlinarith only [hcos₁, sq_nonneg (E - 1)], by nlinarith only [hE, hE₂, hcos₂]⟩

/-- The reciprocal-square majorant for the tail of the sharp test. -/
theorem coefficient_sq_tail_le {lam t : ℝ} (hE : Real.exp (lam / 2) ≤ 11 / 10) (ht : 0 < t) :
    ‖coefficient lam t‖^2 ≤ 5 / t^2 := by
  rw [coefficient_sq_eq_quotient]
  refine (div_le_div_of_nonneg_right (sharpNumerator_bounds hE t).2 (by positivity)).trans ?_
  exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ht) (by linarith)

private theorem hasDerivAt_sharpNumerator (lam t : ℝ) :
    HasDerivAt (sharpNumerator lam)
      (2 * Real.exp (lam / 2) * lam * Real.sin (lam * t)) t := by
  have h := ((hasDerivAt_id t).const_mul lam).cos.const_mul (2 * Real.exp (lam / 2))
  convert h.const_sub ((Real.exp (lam / 2))^2 + 1) using 1 <;>
    first | rfl | (funext z; rfl) | (simp only [id_eq, one_mul]; ring)

/-- The derivative has a summable tail after multiplication by either logarithm. -/
theorem coefficient_sq_tail_deriv_le {lam t : ℝ}
    (hlam : 0 ≤ lam) (hE : Real.exp (lam / 2) ≤ 11 / 10) (ht : 0 < t) :
    |deriv (fun s => ‖coefficient lam s‖^2) t| ≤ 3 * lam / t^2 + 10 / t^3 := by
  let N := sharpNumerator lam
  let D (s : ℝ) := s^2 + 1 / 4
  let M := 2 * Real.exp (lam / 2) * lam
  have hD₀ : 0 < D t := by unfold D; positivity
  have hD : t^2 ≤ D t := by unfold D; linarith
  have hD' : HasDerivAt D (2 * t) t := by
    simpa only [D, Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      (hasDerivAt_pow 2 t).add_const (1 / 4 : ℝ)
  have hN := (hasDerivAt_sharpNumerator lam t).div hD' hD₀.ne'
  have he : deriv (fun s => ‖coefficient lam s‖^2) t =
      (M * Real.sin (lam * t) * D t - N t * (2 * t)) / D t^2 := by
    simp_rw [coefficient_sq_eq_quotient]
    exact hN.deriv
  obtain ⟨hN₀, hN₁⟩ := sharpNumerator_bounds hE t
  have hM₀ : 0 ≤ M := by unfold M; positivity
  have hM : M ≤ 3 * lam := by
    calc
      _ ≤ 2 * (11 / 10) * lam := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hE (by norm_num)) hlam
      _ ≤ _ := by linarith
  have hNsin : |M * Real.sin (lam * t)| ≤ 3 * lam := by
    rw [abs_mul, abs_of_nonneg hM₀]
    exact (mul_le_of_le_one_right hM₀ (Real.abs_sin_le_one _)).trans hM
  rw [he, abs_div, abs_of_pos (sq_pos_of_pos hD₀)]
  calc
    _ ≤ (|M * Real.sin (lam * t) * D t| + |N t * (2 * t)|) / D t^2 :=
      div_le_div_of_nonneg_right (abs_sub _ _) (sq_nonneg _)
    _ ≤ (3 * lam * D t + 5 * (2 * t)) / D t^2 := by
      rw [abs_mul (M * Real.sin _), abs_of_pos hD₀,
        abs_of_nonneg (mul_nonneg hN₀ (by positivity))]
      exact div_le_div_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_right hNsin hD₀.le)
        (mul_le_mul_of_nonneg_right hN₁ (by positivity))) (sq_nonneg _)
    _ = 3 * lam / D t + 5 * (2 * t) / D t^2 := by field_simp [hD₀.ne']
    _ ≤ 3 * lam / t^2 + 5 * (2 * t) / (t^2)^2 :=
      add_le_add (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ht) hD)
        (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (sq_nonneg t) hD 2))
    _ = _ := by field_simp [ht.ne'] <;> ring

end GoldbachExplicit
