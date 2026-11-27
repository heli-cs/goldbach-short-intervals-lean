import Goldbach.Explicit.CosineDecay
import Goldbach.FiniteSpectrum

/-! The finite Schur inequality with the cosine kernel. -/

open MeasureTheory Set
open scoped BigOperators ComplexConjugate
noncomputable section

namespace GoldbachExplicit

open GoldbachGaussian Zeta23

def cosineKernel (V t : ℝ) : ℝ := (cosineTransform V (t : ℂ)).re

theorem cosineKernel_nonneg {V : ℝ} (hV : 0 < V) (t : ℝ) : 0 ≤ cosineKernel V t :=
  cosineTransform_ofReal_nonneg hV t

theorem cosineKernel_even (V : ℝ) : Function.Even (cosineKernel V) := by
  intro t
  unfold cosineKernel cosineTransform
  rw [Complex.ofReal_neg, Taper.paperFT_neg_of_even (cosineWeight_even V)]

private theorem integrable_cosineWeight_wave {V : ℝ} (hV : 0 < V) (z t : ℝ) :
    Integrable (fun u : ℝ => (cosineWeight V (u - z) : ℂ) * wave t u) := by
  have hw : Integrable (cosineWeight V) := (continuous_cosineWeight hV).integrable_of_hasCompactSupport
    (cosineWeight_hasCompactSupport V)
  refine (hw.comp_sub_right z).mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp ((continuous_cosineWeight hV).comp
      (continuous_id.sub continuous_const))).mul
      (by unfold wave; fun_prop)).aestronglyMeasurable
  · filter_upwards with u
    have h := cosineWeight_nonneg hV (u - z)
    simp [abs_of_nonneg h]

private theorem integral_cosineWeight_wave {V : ℝ} (_hV : 0 < V) (z t : ℝ) :
    (∫ u : ℝ, (cosineWeight V (u - z) : ℂ) * wave t u) = (cosineKernel V t : ℂ) * wave t z := by
  have hft : (∫ u : ℝ, (cosineWeight V u : ℂ) * wave t u) = (cosineKernel V t : ℂ) := by
    unfold cosineKernel cosineTransform
    rw [← Taper.paperFT_ofReal_eq_re (cosineWeight_even V) t]
    unfold paperFT wave
    apply integral_congr_ae
    filter_upwards with u
    congr 2
    push_cast
    ring
  calc
    _ = ∫ u : ℝ, ((cosineWeight V (u - z) : ℂ) * wave t (u - z)) * wave t z := by
      apply integral_congr_ae
      filter_upwards with u
      conv_lhs => rw [show u = u - z + z by ring, add_sub_cancel_right]
      rw [wave_add_right, mul_assoc]
    _ = (∫ u : ℝ, (cosineWeight V (u - z) : ℂ) * wave t (u - z)) * wave t z :=
      integral_mul_const _ _
    _ = _ := by
      rw [integral_sub_right_eq_self (fun u : ℝ => (cosineWeight V u : ℂ) * wave t u) z, hft]

/-- The weighted square integral of any finite exponential sum is
bounded by its diagonal Schur expression. -/
theorem integral_cosine_norm_sq_le_schur {ι : Type*} (s : Finset ι)
    {V : ℝ} (hV : 0 < V) (z : ℝ) (γ : ι → ℝ) (m : ι → ℝ) (a : ι → ℂ)
    (hm : ∀ i, 0 ≤ m i) :
    (∫ u : ℝ, cosineWeight V (u - z) * ‖∑ i ∈ s, (m i : ℂ) * a i * wave (γ i) u‖ ^ 2) ≤
      ∑ i ∈ s, m i * ‖a i‖ ^ 2 * (∑ j ∈ s, m j * cosineKernel V (γ i - γ j)) := by
  let f := fun (i : ι) (u : ℝ) => (m i : ℂ) * a i * wave (γ i) u
  let g := fun (i j : ι) (u : ℝ) => (cosineWeight V (u - z) : ℂ) * f i u * conj (f j u)
  let C := fun i j => (m i : ℂ) * (m j : ℂ) * a i * conj (a j)
  have hg (i j : ι) (u : ℝ) :
      g i j u = C i j * ((cosineWeight V (u - z) : ℂ) * wave (γ i - γ j) u) := by
    dsimp [g, f, C]
    simp only [map_mul, Complex.conj_ofReal]
    rw [← wave_sub_mul_conj]
    ring
  have hgi (i j : ι) : Integrable (g i j) := by
    refine ((integrable_cosineWeight_wave hV z (γ i - γ j)).const_mul (C i j)).congr ?_
    exact Filter.Eventually.of_forall (fun u => (hg i j u).symm)
  have hH : Integrable (fun u => ∑ i ∈ s, ∑ j ∈ s, g i j u) :=
    integrable_finsetSum s (fun i _ => integrable_finsetSum s (fun j _ => hgi i j))
  have hpoint (u : ℝ) : (∑ i ∈ s, ∑ j ∈ s, g i j u).re =
      cosineWeight V (u - z) * ‖∑ i ∈ s, f i u‖ ^ 2 := by
    have hs : (∑ i ∈ s, ∑ j ∈ s, g i j u) =
        (cosineWeight V (u - z) : ℂ) * ((∑ i ∈ s, f i u) * conj (∑ j ∈ s, f j u)) := by
      simp_rw [g, map_sum, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [hs, Complex.mul_conj']
    simp [Complex.mul_re, ← Complex.ofReal_pow]
  have hint :
      (∫ u : ℝ, cosineWeight V (u - z) * ‖∑ i ∈ s, f i u‖ ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, (∫ u, g i j u).re := by
    simp_rw [← hpoint]
    have hre : (∫ u : ℝ, ∑ i ∈ s, ∑ j ∈ s, g i j u).re =
        ∫ u : ℝ, (∑ i ∈ s, ∑ j ∈ s, g i j u).re := (integral_re hH).symm
    rw [← hre, integral_finsetSum s
      (fun i _ => integrable_finsetSum s (fun j _ => hgi i j))]
    simp_rw [integral_finsetSum s (fun j _ => hgi _ j), Complex.re_sum]
  have hterm (i j : ι) :
      (∫ u, g i j u).re ≤ m i * m j * cosineKernel V (γ i - γ j) * (‖a i‖ * ‖a j‖) := by
    simp_rw [hg]
    rw [integral_const_mul, integral_cosineWeight_wave hV]
    apply (Complex.re_le_norm _).trans_eq
    simp only [C, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm _),
      abs_of_nonneg (cosineKernel_nonneg hV _), Complex.norm_conj, norm_wave, mul_one]
    ring
  change (∫ u : ℝ, cosineWeight V (u - z) * ‖∑ i ∈ s, f i u‖ ^ 2) ≤ _
  rw [hint]
  refine (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))).trans ?_
  apply GoldbachSchur.finite_schur_weighted s (fun i j => cosineKernel V (γ i - γ j)) m
    (fun i => ‖a i‖) hm (fun _ _ => cosineKernel_nonneg hV _)
  intro i j
  rw [← cosineKernel_even V (γ j - γ i), neg_sub]


end GoldbachExplicit
