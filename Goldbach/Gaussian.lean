import Goldbach.Schur

open MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section
namespace GoldbachGaussian

/-- Gaussian in log coordinates, with the manuscript's width given by `b = 1/V²`. -/
def weight (b u : ℝ) : ℝ := Real.exp (-b * u ^ 2)

/-- The Fourier transform with angular frequency and no prefactor. -/
def kernel (b t : ℝ) : ℝ := Real.sqrt (Real.pi / b) * Real.exp (-t ^ 2 / (4 * b))

def wave (t u : ℝ) : ℂ := Complex.exp ((↑(t * u) : ℂ) * Complex.I)

theorem kernel_nonneg (b t : ℝ) : 0 ≤ kernel b t :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le

theorem kernel_even (b t : ℝ) : kernel b (-t) = kernel b t := by
  simp [kernel]

theorem integrable_weight {b : ℝ} (hb : 0 < b) : Integrable (weight b) :=
  integrable_exp_neg_mul_sq hb

theorem integrable_kernel {b : ℝ} (hb : 0 < b) : Integrable (kernel b) := by
  have h : kernel b = fun t => Real.sqrt (Real.pi / b) * Real.exp (-(1 / (4 * b)) * t ^ 2) := by
    funext t
    unfold kernel
    congr 2
    ring
  rw [h]
  exact (integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (4 * b))).const_mul _

theorem integral_kernel {b : ℝ} (hb : 0 < b) :
    (∫ t, kernel b t) = 2 * Real.pi := by
  have h : kernel b = fun t => Real.sqrt (Real.pi / b) * Real.exp (-(1 / (4 * b)) * t ^ 2) := by
    funext t
    unfold kernel
    congr 2
    ring
  rw [h, integral_const_mul, integral_gaussian]
  have hpos : 0 ≤ Real.pi / b := (div_pos Real.pi_pos hb).le
  rw [← Real.sqrt_mul hpos]
  have hp : Real.pi / b * (Real.pi / (1 / (4 * b))) = (2 * Real.pi) ^ 2 := by
    field_simp [hb.ne']
    ring
  rw [hp, Real.sqrt_sq (by positivity)]

@[simp] theorem norm_wave (t u : ℝ) : ‖wave t u‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem wave_add_right (t u v : ℝ) : wave t (u + v) = wave t u * wave t v := by
  rw [wave, wave, wave, ← Complex.exp_add]
  push_cast
  congr 1
  ring

theorem wave_sub_mul_conj (t s u : ℝ) :
    wave t u * conj (wave s u) = wave (t - s) u := by
  rw [wave, wave, wave, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    ← Complex.exp_add]
  push_cast
  congr 1
  ring

theorem integral_weight_wave {b : ℝ} (hb : 0 < b) (t : ℝ) :
    (∫ u : ℝ, (weight b u : ℂ) * wave t u) = (kernel b t : ℂ) := by
  have hb' : 0 < (b : ℂ).re := by simpa using hb
  have hpow := Complex.ofReal_cpow (x := Real.pi / b) (div_nonneg Real.pi_pos.le hb.le) (1 / 2)
  rw [← Real.sqrt_eq_rpow] at hpow
  have hpow' : (↑(Real.sqrt (Real.pi / b)) : ℂ) =
      (↑Real.pi / (b : ℂ)) ^ (1 / 2 : ℂ) := by
    push_cast at hpow
    exact hpow
  unfold kernel
  rw [Complex.ofReal_mul, hpow', Complex.ofReal_exp]
  convert fourierIntegral_gaussian hb' (t : ℂ) using 2
  · funext u
    unfold weight wave
    rw [Complex.ofReal_exp]
    push_cast
    rw [mul_comm]
    congr 2
    ring
  · push_cast
    norm_num

theorem integral_shifted_weight_wave {b : ℝ} (hb : 0 < b) (z t : ℝ) :
    (∫ u : ℝ, (weight b (u - z) : ℂ) * wave t u) =
      (kernel b t : ℂ) * wave t z := by
  calc
    _ = ∫ u : ℝ, ((weight b (u - z) : ℂ) * wave t (u - z)) * wave t z := by
      apply integral_congr_ae
      filter_upwards with u
      conv_lhs => rw [show u = u - z + z by ring, add_sub_cancel_right]
      rw [wave_add_right, mul_assoc]
    _ = (∫ u : ℝ, (weight b (u - z) : ℂ) * wave t (u - z)) * wave t z := integral_mul_const _ _
    _ = _ := by
      rw [integral_sub_right_eq_self (fun u : ℝ => (weight b u : ℂ) * wave t u) z,
        integral_weight_wave hb]

/-- A reciprocal quadratic envelope suffices for summing the Gaussian over zeros. -/
theorem kernel_le_inv_sq {b : ℝ} (hb : 0 < b) (t : ℝ) :
    kernel b t ≤ Real.sqrt (Real.pi / b) * max 1 (4 * b) / (1 + t ^ 2) := by
  have h := Real.add_one_le_exp (t ^ 2 / (4 * b))
  have hd : 0 < 4 * b := by positivity
  have hT : 0 ≤ t ^ 2 / (4 * b) := by positivity
  have hM : 0 ≤ max 1 (4 * b) := (zero_le_one' ℝ).trans (le_max_left _ _)
  have hpoly : 1 + t ^ 2 ≤ max 1 (4 * b) * (1 + t ^ 2 / (4 * b)) := by
    calc
      _ = 1 + (4 * b) * (t ^ 2 / (4 * b)) := by field_simp
      _ ≤ max 1 (4 * b) + max 1 (4 * b) * (t ^ 2 / (4 * b)) :=
        add_le_add (le_max_left _ _) (mul_le_mul_of_nonneg_right (le_max_right _ _) hT)
      _ = _ := by ring
  have hquot : Real.exp (-t ^ 2 / (4 * b)) ≤ max 1 (4 * b) / (1 + t ^ 2) := by
    have he : 0 < Real.exp (t ^ 2 / (4 * b)) := Real.exp_pos _
    rw [neg_div, Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ he (by positivity)]
    simpa using hpoly.trans (mul_le_mul_of_nonneg_left
      (by simpa [add_comm] using h) hM)
  rw [kernel, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hquot (Real.sqrt_nonneg _)

end GoldbachGaussian
