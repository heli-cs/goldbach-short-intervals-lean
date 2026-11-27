import Goldbach.LocalSpectrum

open Filter MeasureTheory Set
open scoped BigOperators Topology
noncomputable section

namespace GoldbachSpectrum

open GoldbachZeros GoldbachGaussian

private theorem fatou_real_bound {μ : Measure ℝ} {Q : ℕ → ℝ → ℝ} {L : ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hq : ∀ (n : ℕ) (u : ℝ), 0 ≤ Q n u) (hl : ∀ u, 0 ≤ L u)
    (hQi : ∀ n, Integrable (Q n) μ) (hL : AEStronglyMeasurable L μ)
    (hbound : ∀ n, (∫ u, Q n u ∂μ) ≤ B)
    (hlim : ∀ᵐ u ∂μ, Tendsto (fun n => Q n u) atTop (𝓝 (L u))) :
    Integrable L μ ∧ (∫ u, L u ∂μ) ≤ B := by
  have hlim' : ∀ᵐ u ∂μ,
      Tendsto (fun n => ENNReal.ofReal (Q n u)) atTop (𝓝 (ENNReal.ofReal (L u))) :=
    hlim.mono (fun _ h => ENNReal.continuous_ofReal.continuousAt.tendsto.comp h)
  have hle : (∫⁻ u, ENNReal.ofReal (L u) ∂μ) ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ u, liminf (fun n : ℕ => ENNReal.ofReal (Q n u)) atTop ∂μ :=
        lintegral_congr_ae (hlim'.mono (fun _ h => h.liminf_eq.symm))
      _ ≤ liminf (fun n : ℕ => ∫⁻ u, ENNReal.ofReal (Q n u) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hQi n).aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal B := by
        apply liminf_le_of_frequently_le'
        apply Frequently.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hQi n) (Eventually.of_forall (hq n))]
        exact ENNReal.ofReal_le_ofReal (hbound n)
  have hLi := (lintegral_ofReal_ne_top_iff_integrable hL (Eventually.of_forall hl)).mp
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
  rw [← ofReal_integral_eq_lintegral_ofReal hLi (Eventually.of_forall hl)] at hle
  exact ⟨hLi, (ENNReal.ofReal_le_ofReal_iff hB).mp hle⟩

theorem continuous_partialSum (a : Zeros → ℂ) (T : ℝ) : Continuous (partialSum a T) := by
  unfold partialSum wave
  fun_prop

theorem partialSum_tendsto_of_hasSum (a : Zeros → ℂ) (u : ℝ) (S : ℂ)
    (h : HasSum (fun ρ : Zeros => (multiplicity ρ : ℂ) * a ρ * wave (ordinate ρ) u) S) :
    Tendsto (fun T : ℝ => partialSum a T u) atTop (𝓝 S) :=
  h.comp zerosUpTo_tendsto_atTop

private theorem integrable_weighted_diff {b : ℝ} (hb : 0 < b) (z T U : ℝ)
    (a : Zeros → ℂ) :
    Integrable (fun u => weight b (u - z) * ‖partialSum a U u - partialSum a T u‖^2) := by
  let A := (∑ ρ ∈ zerosUpTo U, ‖(multiplicity ρ : ℂ) * a ρ‖) +
    (∑ ρ ∈ zerosUpTo T, ‖(multiplicity ρ : ℂ) * a ρ‖)
  have hn (V u : ℝ) : ‖partialSum a V u‖ ≤ ∑ ρ ∈ zerosUpTo V, ‖(multiplicity ρ : ℂ) * a ρ‖ :=
    (norm_sum_le _ _).trans_eq (by simp)
  refine (((integrable_weight hb).comp_sub_right z).mul_const (A^2)).mono' ?_ ?_
  · exact ((show Continuous (fun u => weight b (u - z)) by unfold weight; fun_prop).mul
      (((continuous_partialSum a U).sub (continuous_partialSum a T)).norm.pow 2)).aestronglyMeasurable
  · filter_upwards with u
    have hw : 0 ≤ weight b (u - z) := (Real.exp_pos _).le
    rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hn U u) (hn T u))) _) hw

/-- Gaussian mean square of the sharp limit minus its height-T truncation.
The two applications of Fatou use the same symmetric height on both terms
of each smoothed difference. -/
theorem local_weighted_spectral_tail {b : ℝ} (hb : 0 < b) (z : ℝ) (J : Set ℝ)
    (a : Zeros → ℂ) (aN : ℕ → Zeros → ℂ) (S : ℕ → ℝ → ℂ) (F : ℝ → ℂ)
    (hE : Summable (diagonalEnergy b a))
    (hdom : ∀ n ρ, ‖aN n ρ‖ ≤ ‖a ρ‖)
    (hcoeff : ∀ ρ, Tendsto (fun n => aN n ρ) atTop (𝓝 (a ρ)))
    (hS : ∀ n u, HasSum (fun ρ : Zeros => (multiplicity ρ : ℂ) * aN n ρ *
      wave (ordinate ρ) u) (S n u))
    (hSM : ∀ n, Measurable (S n)) (hFM : Measurable F)
    (hSF : ∀ᵐ u ∂volume.restrict J, Tendsto (fun n => S n u) atTop (𝓝 (F u))) (T : ℝ) :
    IntegrableOn (fun u => weight b (u - z) * ‖F u - partialSum a T u‖^2) J ∧
    (∫ u in J, weight b (u - z) * ‖F u - partialSum a T u‖^2) ≤
      (∑' ρ : Zeros, diagonalEnergy b a ρ) - ∑ ρ ∈ zerosUpTo T, diagonalEnergy b a ρ := by
  classical
  let μ := volume.restrict J
  let W (u : ℝ) := weight b (u - z)
  let B := (∑' ρ : Zeros, diagonalEnergy b a ρ) - ∑ ρ ∈ zerosUpTo T, diagonalEnergy b a ρ
  have hWM : Measurable W := (show Continuous W by unfold W weight; fun_prop).measurable
  have hW (u : ℝ) : 0 ≤ W u := (Real.exp_pos _).le
  have hnn (f : ℝ → ℂ) (u : ℝ) : 0 ≤ W u * ‖f u‖^2 := mul_nonneg (hW u) (sq_nonneg _)
  have hB : 0 ≤ B := sub_nonneg.mpr (hE.sum_le_tsum _ (fun ρ _ => energy_nonneg b a ρ))
  have hmono (n : ℕ) (ρ : Zeros) : diagonalEnergy b (aN n) ρ ≤ diagonalEnergy b a ρ := by
    have hr : 0 ≤ row b (ordinate ρ) := tsum_nonneg
      (fun σ => mul_nonneg (multiplicity_nonneg σ) (kernel_nonneg _ _))
    unfold diagonalEnergy
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hdom n ρ) _) (multiplicity_nonneg _)) hr
  have hfin (n : ℕ) (U : ℝ) (hTU : T ≤ U) :
      (∫ u, W u * ‖partialSum (aN n) U u - partialSum (aN n) T u‖^2 ∂μ) ≤ B := by
    have hsub : zerosUpTo T ⊆ zerosUpTo U := fun ρ hρ =>
      (mem_zerosUpTo U ρ).mpr (((mem_zerosUpTo T ρ).mp hρ).trans hTU)
    calc
      _ ≤ ∫ u, W u * ‖partialSum (aN n) U u - partialSum (aN n) T u‖^2 :=
        integral_mono_measure Measure.restrict_le_self (Eventually.of_forall (hnn _))
          (integrable_weighted_diff hb z T U (aN n))
      _ ≤ ∑ ρ ∈ zerosUpTo U \ zerosUpTo T, diagonalEnergy b (aN n) ρ :=
        partialSum_sub_mean_square hb z hTU (aN n)
      _ ≤ ∑ ρ ∈ zerosUpTo U \ zerosUpTo T, diagonalEnergy b a ρ :=
        Finset.sum_le_sum (fun ρ _ => hmono n ρ)
      _ = (∑ ρ ∈ zerosUpTo U, diagonalEnergy b a ρ) -
          ∑ ρ ∈ zerosUpTo T, diagonalEnergy b a ρ :=
        eq_sub_of_add_eq (Finset.sum_sdiff hsub)
      _ ≤ B := sub_le_sub_right (hE.sum_le_tsum _ (fun ρ _ => energy_nonneg b a ρ)) _
  have hSmooth (n : ℕ) :
      Integrable (fun u => W u * ‖S n u - partialSum (aN n) T u‖^2) μ ∧
        (∫ u, W u * ‖S n u - partialSum (aN n) T u‖^2 ∂μ) ≤ B := by
    let U := fun j : ℕ => max T (j : ℝ)
    have hU : Tendsto U atTop atTop := by
      apply tendsto_atTop.mpr
      intro v
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop v)] with j hj
      exact hj.trans (le_max_right _ _)
    refine fatou_real_bound hB (fun _ => hnn _) (hnn _)
      (fun j => (integrable_weighted_diff hb z T (U j) (aN n)).integrableOn)
      (hWM.mul (((hSM n).sub (continuous_partialSum (aN n) T).measurable).norm.pow_const 2)).aestronglyMeasurable
      (fun j => hfin n (U j) (le_max_left _ _)) ?_
    apply Eventually.of_forall
    intro u
    exact ((((partialSum_tendsto_of_hasSum (aN n) u (S n u) (hS n u)).comp hU).sub_const _).norm.pow 2).const_mul _
  refine fatou_real_bound hB (fun _ => hnn _) (hnn _) (fun n => (hSmooth n).1)
    (hWM.mul ((hFM.sub (continuous_partialSum a T).measurable).norm.pow_const 2)).aestronglyMeasurable
    (fun n => (hSmooth n).2) ?_
  filter_upwards [hSF] with u hu
  have hpartial : Tendsto (fun n => partialSum (aN n) T u) atTop (𝓝 (partialSum a T u)) := by
    unfold partialSum
    apply tendsto_finsetSum
    intro ρ _
    exact ((hcoeff ρ).const_mul _).mul_const _
  exact ((hu.sub hpartial).norm.pow 2).const_mul _

theorem diagonal_tail_tendsto_zero {b : ℝ} (a : Zeros → ℂ)
    (hE : Summable (diagonalEnergy b a)) :
    Tendsto (fun T : ℝ => (∑' ρ : Zeros, diagonalEnergy b a ρ) -
      ∑ ρ ∈ zerosUpTo T, diagonalEnergy b a ρ) atTop (𝓝 0) := by
  simpa only [Function.comp_def, sub_self] using (hE.hasSum.comp zerosUpTo_tendsto_atTop).const_sub (∑' ρ : Zeros, diagonalEnergy b a ρ)

end GoldbachSpectrum
