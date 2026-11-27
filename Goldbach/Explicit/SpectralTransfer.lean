import Goldbach.SharpSpectrum
import Goldbach.Explicit.CosineKernel

/-! Transfer from the Gaussian convergence statement to the compact
weight on the actual logarithmic integration interval. -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum GoldbachGaussian

/-- The common-height truncations converge to exactly the same sharp
spectral value in any nonnegative bounded weight on a compact log interval. -/
theorem compact_weight_spectral_identification (hRH : RiemannHypothesis)
    {lam a b : ℝ} (hlam : 0 < lam) (hlam₁ : lam ≤ 1) (ha : 0 < a) (hab : a ≤ b)
    {W : ℝ → ℝ} (hW : Measurable W) (hWb : ∀ u ∈ Icc a b, 0 ≤ W u ∧ W u ≤ 1) :
    (∀ T : ℝ, IntegrableOn (fun u => W u *
      ‖(sharpSpectralValue lam u : ℂ) - partialSum (sharpCoefficient lam) T u‖^2) (Icc a b)) ∧
    Tendsto (fun T : ℝ => ∫ u in Icc a b, W u *
      ‖(sharpSpectralValue lam u : ℂ) - partialSum (sharpCoefficient lam) T u‖^2)
      atTop (𝓝 0) := by
  let J := Icc a b
  let μ := volume.restrict J
  let G (u : ℝ) := weight 1 (u - a)
  let E (T u : ℝ) := ‖(sharpSpectralValue lam u : ℂ) - partialSum (sharpCoefficient lam) T u‖^2
  let C := Real.exp ((b - a)^2)
  have hG : Continuous G := by unfold G weight; fun_prop
  have hG₀ (u : ℝ) : 0 < G u := Real.exp_pos _
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hpoint (u : ℝ) (hu : u ∈ J) : W u ≤ C * G u := by
    apply (hWb u hu).2.trans
    dsimp [C, G, weight]
    rw [← Real.exp_add]
    apply Real.one_le_exp
    have hq := pow_le_pow_left₀ (by linarith [hu.1] : 0 ≤ u - a)
      (by linarith [hu.2] : u - a ≤ b - a) 2
    nlinarith only [hq]
  have hJ : J ⊆ Ioi 0 := fun _ hu => ha.trans_le hu.1
  have hGi (T : ℝ) : Integrable (fun u => G u * E T u) μ :=
    (local_sharp_spectral_tail hRH zero_lt_one hlam hlam₁ a J measurableSet_Icc hJ T).1
  have hlim : Tendsto (fun T : ℝ => ∫ u, G u * E T u ∂μ) atTop (𝓝 0) :=
    sharp_spectral_identification hRH zero_lt_one hlam hlam₁ a J measurableSet_Icc hJ
  have hEi (T : ℝ) : AEStronglyMeasurable (E T) μ := by
    have hi : Continuous (fun u => (G u)⁻¹) := hG.inv₀ (fun u => (hG₀ u).ne')
    apply ((hGi T).aestronglyMeasurable.mul hi.aestronglyMeasurable).congr
    filter_upwards with u
    change (G u * E T u) * (G u)⁻¹ = E T u
    rw [mul_comm (G u), mul_assoc, mul_inv_cancel₀ (hG₀ u).ne', mul_one]
  have hdom (T : ℝ) : ∀ᵐ u ∂μ, W u * E T u ≤ C * (G u * E T u) := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := J) measurableSet_Icc] with u hu
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hpoint u hu) (sq_nonneg _)
  have hWi (T : ℝ) : Integrable (fun u => W u * E T u) μ := by
    apply ((hGi T).const_mul C).mono' (hW.aestronglyMeasurable.mul (hEi T))
    filter_upwards [ae_restrict_mem (μ := volume) (s := J) measurableSet_Icc, hdom T] with u hu hle
    change ‖W u * E T u‖ ≤ _
    have he : 0 ≤ E T u := sq_nonneg _
    rw [Real.norm_of_nonneg (mul_nonneg (hWb u hu).1 he)]
    exact hle
  refine ⟨hWi, ?_⟩
  have hU : Tendsto (fun T : ℝ => C * (∫ u, G u * E T u ∂μ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU
  · intro T
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (μ := volume) (s := J) measurableSet_Icc] with u hu
    exact mul_nonneg (hWb u hu).1 (sq_nonneg _)
  · intro T
    change (∫ u, W u * E T u ∂μ) ≤ C * (∫ u, G u * E T u ∂μ)
    rw [← integral_const_mul]
    exact integral_mono_ae (hWi T) ((hGi T).const_mul C) (hdom T)

end GoldbachExplicit
