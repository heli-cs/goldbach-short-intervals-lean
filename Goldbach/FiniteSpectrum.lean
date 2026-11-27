import Goldbach.Gaussian

open MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section
namespace GoldbachGaussian

theorem integrable_shifted_weight_wave {b : ℝ} (hb : 0 < b) (z t : ℝ) :
    Integrable (fun u : ℝ => (weight b (u - z) : ℂ) * wave t u) := by
  refine ((integrable_weight hb).comp_sub_right z).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold weight wave
    fun_prop
  · filter_upwards with u
    have hw : 0 ≤ weight b (u - z) := (Real.exp_pos _).le
    simp [abs_of_nonneg hw]

/-- The weighted square integral of any finite exponential sum is
bounded by its diagonal Schur expression. -/
theorem integral_norm_sq_le_schur {ι : Type*} (s : Finset ι)
    {b : ℝ} (hb : 0 < b) (z : ℝ) (γ : ι → ℝ) (m : ι → ℝ) (a : ι → ℂ)
    (hm : ∀ i, 0 ≤ m i) :
    (∫ u : ℝ, weight b (u - z) * ‖∑ i ∈ s, (m i : ℂ) * a i * wave (γ i) u‖ ^ 2) ≤
      ∑ i ∈ s, m i * ‖a i‖ ^ 2 * (∑ j ∈ s, m j * kernel b (γ i - γ j)) := by
  let f := fun (i : ι) (u : ℝ) => (m i : ℂ) * a i * wave (γ i) u
  let g := fun (i j : ι) (u : ℝ) => (weight b (u - z) : ℂ) * f i u * conj (f j u)
  let C := fun i j => (m i : ℂ) * (m j : ℂ) * a i * conj (a j)
  have hg (i j : ι) (u : ℝ) :
      g i j u = C i j * ((weight b (u - z) : ℂ) * wave (γ i - γ j) u) := by
    dsimp [g, f, C]
    simp only [map_mul, Complex.conj_ofReal]
    rw [← wave_sub_mul_conj]
    ring
  have hgi (i j : ι) : Integrable (g i j) := by
    refine ((integrable_shifted_weight_wave hb z (γ i - γ j)).const_mul (C i j)).congr ?_
    exact Filter.Eventually.of_forall (fun u => (hg i j u).symm)
  have hH : Integrable (fun u => ∑ i ∈ s, ∑ j ∈ s, g i j u) :=
    integrable_finsetSum s (fun i _ => integrable_finsetSum s (fun j _ => hgi i j))
  have hpoint (u : ℝ) : (∑ i ∈ s, ∑ j ∈ s, g i j u).re =
      weight b (u - z) * ‖∑ i ∈ s, f i u‖ ^ 2 := by
    have hs : (∑ i ∈ s, ∑ j ∈ s, g i j u) =
        (weight b (u - z) : ℂ) * ((∑ i ∈ s, f i u) * conj (∑ j ∈ s, f j u)) := by
      simp_rw [g, map_sum, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [hs, Complex.mul_conj']
    simp [Complex.mul_re, ← Complex.ofReal_pow]
  have hint :
      (∫ u : ℝ, weight b (u - z) * ‖∑ i ∈ s, f i u‖ ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, (∫ u, g i j u).re := by
    simp_rw [← hpoint]
    have hre : (∫ u : ℝ, ∑ i ∈ s, ∑ j ∈ s, g i j u).re =
        ∫ u : ℝ, (∑ i ∈ s, ∑ j ∈ s, g i j u).re := (integral_re hH).symm
    rw [← hre, integral_finsetSum s
      (fun i _ => integrable_finsetSum s (fun j _ => hgi i j))]
    simp_rw [integral_finsetSum s (fun j _ => hgi _ j), Complex.re_sum]
  have hterm (i j : ι) :
      (∫ u, g i j u).re ≤ m i * m j * kernel b (γ i - γ j) * (‖a i‖ * ‖a j‖) := by
    simp_rw [hg]
    rw [integral_const_mul, integral_shifted_weight_wave hb]
    apply (Complex.re_le_norm _).trans_eq
    simp only [C, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm _),
      abs_of_nonneg (kernel_nonneg _ _), Complex.norm_conj, norm_wave, mul_one]
    ring
  change (∫ u : ℝ, weight b (u - z) * ‖∑ i ∈ s, f i u‖ ^ 2) ≤ _
  rw [hint]
  refine (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))).trans ?_
  apply GoldbachSchur.finite_schur_weighted s (fun i j => kernel b (γ i - γ j)) m
    (fun i => ‖a i‖) hm (fun _ _ => kernel_nonneg _ _)
  intro i j
  rw [← kernel_even b (γ j - γ i), neg_sub]

end GoldbachGaussian
