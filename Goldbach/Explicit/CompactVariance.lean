import Goldbach.Explicit.CosineRow
import Goldbach.Explicit.SpectralLinear

/-! The compact Schur bound passes to the common-height sharp limit. -/

open Filter MeasureTheory Set
open scoped Topology
noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum GoldbachZeros

/-- The diagonal term for the compact weight at one zero. -/
def cosineEnergy (V lam : ℝ) (ρ : Zeros) : ℝ :=
  multiplicity ρ * ‖sharpCoefficient lam ρ‖^2 * cosineRow V (ordinate ρ)

theorem cosineEnergy_nonneg {V : ℝ} (hV : 0 < V) (lam : ℝ) (ρ : Zeros) :
    0 ≤ cosineEnergy V lam ρ := by
  unfold cosineEnergy cosineRow
  exact mul_nonneg (mul_nonneg (multiplicity_nonneg _) (sq_nonneg _))
    (tsum_nonneg fun σ => mul_nonneg (multiplicity_nonneg _) (cosineKernel_nonneg hV _))

/-- A logarithm in the summand is compatible with the sharp coefficient
and the unit-interval zero count. -/
theorem sharp_coefficient_log_summable {lam : ℝ} (hlam : 0 ≤ lam) (hlam₁ : lam ≤ 1) :
    Summable (fun ρ : Zeros => multiplicity ρ * ‖sharpCoefficient lam ρ‖^2 *
      Real.log (|ordinate ρ| + 3)) := by
  let K := Real.exp 1 + (1 + Real.exp (1 / 2))^2
  have hlog (t : ℝ) : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  refine (summable_log_over_ordinates.mul_left K).of_nonneg_of_le
    (fun ρ => mul_nonneg (mul_nonneg (multiplicity_nonneg _) (sq_nonneg _)) (hlog _)) ?_
  intro ρ
  calc
    _ ≤ multiplicity ρ * (K / (1 + ordinate ρ ^ 2)) * Real.log (|ordinate ρ| + 3) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (coefficient_sq_le hlam hlam₁ _) (multiplicity_nonneg _)) (hlog _)
    _ = _ := by ring

private theorem sq_norm_le_add {eps : ℝ} (heps : 0 < eps) (P E : ℂ) :
    ‖P + E‖^2 ≤ (1 + eps) * ‖P‖^2 + (1 + 1 / eps) * ‖E‖^2 := by
  have hcross : 2 * ‖P‖ * ‖E‖ ≤ eps * ‖P‖^2 + ‖E‖^2 / eps := by
    apply (mul_le_mul_iff_left₀ heps).mp
    rw [add_mul, div_mul_cancel₀ _ heps.ne']
    nlinarith only [sq_nonneg (eps * ‖P‖ - ‖E‖)]
  calc
    _ ≤ (‖P‖ + ‖E‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) _
    _ ≤ _ := by
      nlinarith only [hcross, show (1 / eps : ℝ) * ‖E‖^2 = ‖E‖^2 / eps by ring]

/-- On a compact interval of positive log coordinates, the sharp
spectral value satisfies the same Schur bound as the finite sums. -/
theorem cosine_sharp_meanSquare_le (hRH : RiemannHypothesis)
    {lam a b V : ℝ} (hlam : 0 < lam) (hlam₁ : lam ≤ 1) (ha : 0 < a) (hab : a ≤ b)
    (hV : 0 < V) (z : ℝ) (hE : Summable (cosineEnergy V lam)) :
    (∫ u in Icc a b, cosineWeight V (u - z) * ‖(sharpSpectralValue lam u : ℂ)‖^2) ≤
      ∑' ρ : Zeros, cosineEnergy V lam ρ := by
  let μ := volume.restrict (Icc a b)
  let W (u : ℝ) := cosineWeight V (u - z)
  let S (u : ℝ) : ℂ := (sharpSpectralValue lam u : ℂ)
  let P (T : ℝ) := partialSum (sharpCoefficient lam) T
  let B := ∑' ρ : Zeros, cosineEnergy V lam ρ
  have hW : Continuous W := (continuous_cosineWeight hV).comp (by fun_prop)
  have hWc : HasCompactSupport W :=
    (cosineWeight_hasCompactSupport V).comp_homeomorph (Homeomorph.subRight z)
  have hW₀ (u : ℝ) : 0 ≤ W u := cosineWeight_nonneg hV _
  have hW₁ (u : ℝ) : W u ≤ 1 := cosineWeight_le_one hV _
  have hS : MemLp S 2 μ := sharpSpectralValue_memLp hRH hlam hlam₁ ha hab
  have hWn : ∀ᵐ u ∂μ, ‖W u‖ ≤ 1 :=
    Eventually.of_forall (fun u => by rw [Real.norm_of_nonneg (hW₀ u)]; exact hW₁ u)
  have hSi : Integrable (fun u => W u * ‖S u‖^2) μ :=
    ((memLp_two_iff_integrable_sq_norm hS.aestronglyMeasurable).1 hS).bdd_mul
      hW.aestronglyMeasurable hWn
  have hWhole (T : ℝ) : Integrable (fun u => W u * ‖P T u‖^2) :=
    (hW.mul ((continuous_partialSum _ T).norm.pow 2)).integrable_of_hasCompactSupport hWc.mul_right
  have hFin (T : ℝ) : (∫ u, W u * ‖P T u‖^2 ∂μ) ≤ B := by
    calc
      _ ≤ ∫ u, W u * ‖P T u‖^2 :=
        integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall (fun u => mul_nonneg (hW₀ u) (sq_nonneg _))) (hWhole T)
      _ ≤ ∑ ρ ∈ zerosUpTo T, multiplicity ρ * ‖sharpCoefficient lam ρ‖^2 *
          (∑ σ ∈ zerosUpTo T, multiplicity σ * cosineKernel V (ordinate ρ - ordinate σ)) :=
        integral_cosine_norm_sq_le_schur (zerosUpTo T) hV z ordinate multiplicity
          (sharpCoefficient lam) multiplicity_nonneg
      _ ≤ ∑ ρ ∈ zerosUpTo T, cosineEnergy V lam ρ := by
        apply Finset.sum_le_sum
        intro ρ _
        apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg (multiplicity_nonneg _) (sq_nonneg _))
        exact (cosine_row_formula hRH hV _).1.sum_le_tsum _ (fun σ _ =>
          mul_nonneg (multiplicity_nonneg _) (cosineKernel_nonneg hV _))
      _ ≤ B := hE.sum_le_tsum _ (fun ρ _ => cosineEnergy_nonneg hV lam ρ)
  have herr := compact_weight_spectral_identification hRH hlam hlam₁ ha hab hW.measurable
    (fun u _ => ⟨hW₀ u, hW₁ u⟩)
  have hbound (eps : ℝ) (heps : 0 < eps) : (∫ u, W u * ‖S u‖^2 ∂μ) ≤ (1 + eps) * B := by
    let C := 1 + 1 / eps
    have hlim : Tendsto (fun T : ℝ => (1 + eps) * B +
        C * (∫ u, W u * ‖S u - P T u‖^2 ∂μ)) atTop (𝓝 ((1 + eps) * B)) := by
      simpa only [mul_zero, add_zero] using (herr.2.const_mul C).const_add ((1 + eps) * B)
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
    intro T
    have hPf : Integrable (fun u => W u * ‖P T u‖^2) μ := (hWhole T).integrableOn
    have hIf : Integrable (fun u => W u * ‖S u - P T u‖^2) μ := herr.1 T
    have hp (u : ℝ) : W u * ‖S u‖^2 ≤
        (1 + eps) * (W u * ‖P T u‖^2) + C * (W u * ‖S u - P T u‖^2) := by
      have h := sq_norm_le_add heps (P T u) (S u - P T u)
      rw [show P T u + (S u - P T u) = S u by ring] at h
      have he := mul_le_mul_of_nonneg_left h (hW₀ u)
      dsimp [C]
      nlinarith only [he]
    have hi := integral_mono hSi ((hPf.const_mul (1 + eps)).add (hIf.const_mul C)) hp
    simp only [Pi.add_apply] at hi
    rw [integral_add (hPf.const_mul (1 + eps)) (hIf.const_mul C), integral_const_mul,
      integral_const_mul] at hi
    have hm := mul_le_mul_of_nonneg_left (hFin T) (show 0 ≤ 1 + eps by linarith)
    linarith only [hi, hm]
  have hB : 0 ≤ B := tsum_nonneg (cosineEnergy_nonneg hV lam)
  change (∫ u, W u * ‖S u‖^2 ∂μ) ≤ B
  apply le_of_forall_pos_le_add
  intro e he
  have hB₁ : 0 < B + 1 := by linarith
  have h := hbound (e / (B + 1)) (div_pos he hB₁)
  refine h.trans ?_
  rw [add_mul, one_mul, div_mul_eq_mul_div]
  have hSmall : e * B / (B + 1) ≤ e := (div_le_iff₀ hB₁).2
    (show e * B ≤ e * (B + 1) by nlinarith only [he])
  linarith only [hSmall]

end GoldbachExplicit
