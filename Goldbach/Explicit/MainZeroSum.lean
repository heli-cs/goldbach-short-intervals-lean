import Goldbach.Explicit.CountingStieltjes
import Goldbach.Explicit.CountBoundary
import Goldbach.Explicit.UpperNumerics
import Goldbach.Explicit.WeightedMangoldt

/-! The explicit bound on the complete archimedean zero sum. -/

open Filter MeasureTheory Set
open scoped Topology
noncomputable section

namespace GoldbachExplicit

open GoldbachZeros GoldbachSpectrum Zeta23

/-- The verified continuous profile and the effective Stieltjes error
bound the whole two-sided zero sum with leading coefficient one. -/
theorem archimedeanZeroSum_log_le (hRH : RiemannHypothesis) {lam : ℝ}
    (hlam : 0 < lam) (hlam₁ : lam ≤ 1 / 10) :
    archimedeanZeroSum lam ≤
      (Real.exp lam - 1) * (-Real.log lam)^2 + lam * Real.exp lam * (8 * (-Real.log lam) + 10) / Real.pi +
        50000 * lam^2 * (-Real.log lam + 1)^2 := by
  let G (ρ : Zeros) := multiplicity ρ * ‖sharpCoefficient lam ρ‖^2 * Real.log (|ordinate ρ| + 3)
  let P (ρ : Zeros) := if 0 < ordinate ρ then G ρ else 0
  let N (ρ : Zeros) := if ordinate ρ < 0 then G ρ else 0
  let I := ∫ t in Ioi (0 : ℝ), ‖coefficient lam t‖^2 * (Real.log t)^2
  let E := ∫ t in Ioi (0 : ℝ), countErrorIntegrand lam t
  have hlam₂ : lam ≤ 1 := hlam₁.trans (by norm_num)
  have hG := sharp_coefficient_log_summable hlam.le hlam₂
  have hG₀ (ρ : Zeros) : 0 ≤ G ρ := by
    exact mul_nonneg (mul_nonneg (multiplicity_nonneg _) (sq_nonneg _))
      (Real.log_nonneg (by linarith [abs_nonneg (ordinate ρ)]))
  have hPm : Summable P := by
    refine hG.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_)
    · unfold P; split <;> first | exact hG₀ _ | exact le_rfl
    · unfold P; split <;> first | exact le_rfl | exact hG₀ _
  have hNm : Summable N := by
    refine hG.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_)
    · unfold N; split <;> first | exact hG₀ _ | exact le_rfl
    · unfold N; split <;> first | exact le_rfl | exact hG₀ _
  have hconj (ρ : Zeros) : G (conjugation ρ) = G ρ := by
    unfold G sharpCoefficient
    rw [multiplicity_conjugation, ordinate_conjugation, abs_neg, coefficient_sq_scale hlam.le,
      coefficient_sq_scale hlam.le, mul_neg, profile_even]
  have hN : (∑' ρ, N ρ) = ∑' ρ, P ρ := by
    rw [← conjugation.tsum_eq N]
    apply tsum_congr
    intro ρ
    simp only [N, P, ordinate_conjugation, neg_lt_zero, hconj]
  have hTwo : archimedeanZeroSum lam = 2 * ∑' ρ, P ρ := by
    have he (ρ : Zeros) : G ρ = P ρ + N ρ := by
      have hn : ordinate ρ ≠ 0 := by
        intro h
        have ht := ordinate_abs_gt_nine_halves hRH ρ
        norm_num [h] at ht
      rcases lt_or_gt_of_ne hn with hn | hp
      · simp [P, N, hn, not_lt_of_ge hn.le]
      · simp [P, N, hp, not_lt_of_ge hp.le]
    unfold archimedeanZeroSum
    change (∑' ρ, G ρ) = _
    simp_rw [he]
    rw [hPm.tsum_add hNm, hN]
    ring
  have hFin (T : ℝ) : (∑ ρ ∈ zerosUpTo T, P ρ) =
      ∑ ρ ∈ zeroWindow 0 T, multiplicity ρ * logarithmicCoefficient lam (ordinate ρ) := by
    have hs : (zerosUpTo T).filter (fun ρ => 0 < ordinate ρ) = zeroWindow 0 T := by
      ext ρ
      simp only [Finset.mem_filter, mem_zerosUpTo, mem_zeroWindow]
      constructor
      · rintro ⟨ht, hp⟩
        exact ⟨hp, by simpa only [abs_of_pos hp] using ht⟩
      · rintro ⟨hp, ht⟩
        exact ⟨by simpa only [abs_of_pos hp] using ht, hp⟩
    unfold P
    rw [← Finset.sum_filter, hs]
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    have hp := (mem_zeroWindow.mp hρ).1
    unfold G logarithmicCoefficient sharpCoefficient
    rw [abs_of_pos hp]
    ring
  have hPS : Tendsto (fun T : ℝ => ∑ ρ ∈ zeroWindow 0 T,
      multiplicity ρ * logarithmicCoefficient lam (ordinate ρ)) atTop (𝓝 (∑' ρ, P ρ)) := by
    simpa only [Function.comp_def, hFin] using hPm.hasSum.comp zerosUpTo_tendsto_atTop
  have hL : Tendsto (fun T : ℝ => logarithmicCoefficient lam T * ((Ncount 0 T : ℝ) - zeroCountMain T) +
      I / (2 * Real.pi) + 250 * E) atTop (𝓝 (I / (2 * Real.pi) + 250 * E)) := by
    simpa only [logarithmicCoefficient, zero_add] using
      ((spectral_discrepancy_boundary_tendsto hRH hlam.le hlam₂).add_const
        (I / (2 * Real.pi))).add_const (250 * E)
  have hPos : (∑' ρ, P ρ) ≤ I / (2 * Real.pi) + 250 * E := by
    exact le_of_tendsto_of_tendsto hPS hL ((eventually_ge_atTop (0 : ℝ)).mono
      (fun T hT => finite_logarithmic_zero_sum_le hRH hlam hlam₁ hT))
  have hI := (coefficient_log_square_integral_le hlam hlam₂).2
  have hE := (counting_derivative_integral_le hlam hlam₁).2
  rw [Real.log_inv] at hE
  have hMain : I / Real.pi ≤ (Real.exp lam - 1) * (-Real.log lam)^2 +
      lam * Real.exp lam * (8 * (-Real.log lam) + 10) / Real.pi := by
    change I ≤ _ at hI
    refine (div_le_div_of_nonneg_right hI Real.pi_pos.le).trans_eq ?_
    field_simp [Real.pi_ne_zero] <;> ring
  rw [hTwo]
  have ht := mul_le_mul_of_nonneg_left hPos (by norm_num : (0 : ℝ) ≤ 2)
  change E ≤ _ at hE
  calc
    _ ≤ 2 * (I / (2 * Real.pi) + 250 * E) := ht
    _ = I / Real.pi + 500 * E := by ring
    _ ≤ _ := by nlinarith only [hMain, hE]

/-- The discrete gamma envelope in the full original range. -/
theorem archimedeanZeroSum_explicit_le (hRH : RiemannHypothesis) {L : ℝ} (hL : 42 ≤ L) :
    archimedeanZeroSum (logWidth L) ≤ delta L * ((L - 2 * Real.log L)^2 + (8 / 3) * L + 5) := by
  have h := (logWidth_le_delta hL).trans ((delta_lt hL).le.trans (by norm_num : (2 / 10^15 : ℝ) ≤ 1 / 10))
  exact (archimedeanZeroSum_log_le hRH (logWidth_pos hL) h).trans (archimedean_expression_le hL)

/-- Explicit bound on the complete cosine energy with the finite prime
contribution included. -/
theorem cosine_energy_explicit_le (hRH : RiemannHypothesis) {L : ℝ} (hL : 42 ≤ L) :
    Summable (cosineEnergy (bandwidth L) (logWidth L)) ∧
      (∑' ρ : Zeros, cosineEnergy (bandwidth L) (logWidth L) ρ) <
        delta L * ((L - 2 * Real.log L)^2 + (11 / 3) * L + 104) := by
  obtain ⟨hs, he⟩ := cosine_energy_le hRH hL
  refine ⟨hs, he.trans_le ?_⟩
  have hP := mul_le_mul_of_nonneg_left (twice_weightedMangoldtSquares_le hL) (delta_pos hL).le
  have hG := archimedeanZeroSum_explicit_le hRH hL
  nlinarith only [hP, hG]

theorem archimedeanZeroSum_explicit_le_of_ge_28 (hRH : RiemannHypothesis)
    {L : ℝ} (hL : 28 ≤ L) :
    archimedeanZeroSum (logWidth L) ≤ delta L * ((L - 2 * Real.log L)^2 + (8 / 3) * L - 12) := by
  have hL₀ : 0 < L := by linarith
  have h := (logWidth_le_delta_of_pos hL₀).trans
    ((delta_lt_of_ge_28 hL).le.trans (by norm_num : (1 / 10^8 : ℝ) ≤ 1 / 10))
  exact (archimedeanZeroSum_log_le hRH (logWidth_pos_of_pos hL₀) h).trans
    (archimedean_expression_le_of_ge_28 hL)

/-- The tighter archimedean and prime allowances in the earlier range. -/
theorem cosine_energy_explicit_le_of_ge_28 (hRH : RiemannHypothesis) {L : ℝ} (hL : 28 ≤ L) :
    Summable (cosineEnergy (bandwidth L) (logWidth L)) ∧
      (∑' ρ : Zeros, cosineEnergy (bandwidth L) (logWidth L) ρ) <
        delta L * ((L - 2 * Real.log L)^2 + (9 / 2) * L - 8) := by
  obtain ⟨hs, he⟩ := cosine_energy_le_of_ge_28 hRH hL
  refine ⟨hs, he.trans_le ?_⟩
  have hP := mul_le_mul_of_nonneg_left (twice_weightedMangoldtSquares_le_of_ge_28 hL)
    (delta_pos_of_pos (show 0 < L by linarith)).le
  have hG := archimedeanZeroSum_explicit_le_of_ge_28 hRH hL
  nlinarith only [hP, hG]

end GoldbachExplicit
