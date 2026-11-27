import Goldbach.Explicit.ZeroCount
import Goldbach.SpectrumEnergy

/-! Decay of the Stieltjes boundary term for the explicit spectral test. -/

open Set Filter
open scoped Topology
noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum Zeta23

private theorem log_add_three_bound {T : ℝ} (hT : 1 ≤ T) :
    Real.log (T + 3) ≤ 4 * Real.sqrt T := by
  have h := Real.log_le_rpow_div (show 0 ≤ T + 3 by linarith)
    (show 0 < (1 / 2 : ℝ) by norm_num)
  rw [← Real.sqrt_eq_rpow] at h
  have hs : Real.sqrt (T + 3) ≤ 2 * Real.sqrt T := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ T)]
    linarith
  linarith

/-- The upper boundary term in the signed zero-counting discrepancy
vanishes when the sharp spectral test is multiplied by log(t + 3). -/
theorem spectral_discrepancy_boundary_tendsto (hRH : RiemannHypothesis)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam₁ : lam ≤ 1) :
    Tendsto (fun T : ℝ => ‖coefficient lam T‖^2 * Real.log (T + 3) *
      ((Ncount 0 T : ℝ) - zeroCountMain T)) atTop (𝓝 0) := by
  let C := Real.exp 1 + (1 + Real.exp (1 / 2))^2
  have hC : 0 ≤ C := by unfold C; positivity
  have hlim : Tendsto (fun T : ℝ => (4000 * C) / T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0)).const_mul (4000 * C)
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT₀ : 0 < T := by linarith
  have hlog : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hlog' : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hl := log_add_three_bound hT
  have hl' : Real.log (T + 2) ≤ 4 * Real.sqrt T :=
    (Real.log_le_log (by linarith : 0 < T + 2) (by linarith)).trans hl
  have hcoeff : ‖coefficient lam T‖^2 ≤ C / (1 + T^2) := coefficient_sq_le hlam hlam₁ T
  have hcount := cumulative_zero_count_le hRH hT₀.le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) hlog)]
  calc
    _ ≤ (C / (1 + T^2)) * (4 * Real.sqrt T) * (250 * (4 * Real.sqrt T)) := by
      exact mul_le_mul (mul_le_mul hcoeff hl hlog (by positivity))
        (hcount.trans (mul_le_mul_of_nonneg_left hl' (by norm_num)))
        (abs_nonneg _) (by positivity)
    _ = (4000 * C) * (Real.sqrt T)^2 / (1 + T^2) := by ring
    _ = (4000 * C) * T / (1 + T^2) := by rw [Real.sq_sqrt hT₀.le]
    _ ≤ (4000 * C) / T := by
      apply (div_le_div_iff₀ (by positivity) hT₀).mpr
      nlinarith only [hC]

end GoldbachExplicit
