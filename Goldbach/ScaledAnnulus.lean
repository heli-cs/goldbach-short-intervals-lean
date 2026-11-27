import Goldbach.ScaledCounting
import Goldbach.ScaledTail
import Goldbach.Plancherel

open Filter MeasureTheory Set
open scoped BigOperators Topology
noncomputable section

namespace GoldbachSpectrum

open GoldbachZeros Zeta23

/-- The Gaussian row divided by log T converges uniformly when the scaled
ordinate stays on a fixed positive compact window. -/
theorem row_scaled_uniform (hRH : RiemannHypothesis) {b a B : ℝ} (hb : 0 < b)
    (ha : 0 < a) (haB : a ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ γ : ℝ, a * T ≤ γ → γ ≤ B * T →
      |row b γ / Real.log T - 1| ≤ ε := by
  let K := |Real.log a| + |Real.log B|
  have hB : 0 < B := ha.trans_le haB
  let η := min (1 / 2) (ε / 4)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη₁ : η ≤ 1 / 2 := min_le_left _ _
  have hηε : η ≤ ε / 4 := min_le_right _ _
  have ht := (Metric.tendsto_nhds.mp (row_div_log_tendsto_one hRH hb)) η hη
  obtain ⟨Y, hY⟩ := eventually_atTop.mp ht
  have hlog := (Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul K)
  rw [mul_zero] at hlog
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (max 2 Y / a),
    hlog.eventually (gt_mem_nhds hη)] with T hT hTa htη
  intro γ hγa hγB
  have hT₀ : 0 < T := by linarith
  have hTa' := (div_le_iff₀ ha).mp hTa
  have hγ₂ : 2 ≤ γ := (le_max_left _ _).trans (by linarith)
  have hγY : Y ≤ γ := (le_max_right _ _).trans (by linarith)
  have hγ₀ : 0 < γ := by linarith
  have hL := Real.log_pos (show 1 < T by linarith)
  have hLg := Real.log_pos (show 1 < γ by linarith)
  have hscaled₁ : a ≤ γ / T := (le_div_iff₀ hT₀).mpr hγa
  have hscaled₂ : γ / T ≤ B := (div_le_iff₀ hT₀).mpr hγB
  have hg : |Real.log (γ / T)| ≤ K := by
    have h₁ := Real.log_le_log ha hscaled₁
    have h₂ := Real.log_le_log (div_pos hγ₀ hT₀) hscaled₂
    apply abs_le.mpr
    dsimp [K]
    exact ⟨by linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log B)],
      by linarith [le_abs_self (Real.log B), abs_nonneg (Real.log a)]⟩
  have hratio : |Real.log γ / Real.log T - 1| ≤ η := by
    have he : Real.log γ / Real.log T - 1 = Real.log (γ / T) / Real.log T := by
      rw [Real.log_div hγ₀.ne' hT₀.ne', sub_div, div_self hL.ne']
    rw [he, abs_div, abs_of_pos hL, div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_right hg (inv_nonneg.mpr hL.le)).trans htη.le
  have hrow : |row b γ / Real.log γ - 1| ≤ η := by
    simpa only [Real.dist_eq] using (hY γ hγY).le
  have htwo : |Real.log γ / Real.log T| ≤ 2 := by
    have ht := abs_add_le (Real.log γ / Real.log T - 1) 1
    rw [sub_add_cancel, abs_one] at ht
    linarith
  have he : row b γ / Real.log T - 1 =
      (row b γ / Real.log γ - 1) * (Real.log γ / Real.log T) +
        (Real.log γ / Real.log T - 1) := by
    field_simp [hL.ne', hLg.ne']
    ring
  rw [he]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have ht := mul_le_mul hrow htwo (abs_nonneg _) hη.le
  linarith

private theorem profile_scaled_row_uniform (hRH : RiemannHypothesis) {b a B : ℝ}
    (hb : 0 < b) (ha : 0 < a) (haB : a ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ γ : ℝ, a * T ≤ γ → γ ≤ B * T →
      |profile (1 / T) (γ / T) * (row b γ / Real.log T) - profile 0 (γ / T)| ≤ ε := by
  have hhalf : 0 < ε / (2 * Real.exp 1) := by positivity
  have hInv := (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).div_const 2
  rw [zero_div] at hInv
  have he := (Real.continuous_exp.continuousAt.tendsto.comp hInv).sub_const 1
  rw [Real.exp_zero, sub_self] at he
  have hc := he.const_mul (Real.exp (1 / 2) + 1)
  rw [mul_zero] at hc
  filter_upwards [row_scaled_uniform hRH hb ha haB hhalf,
    hc.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)),
    eventually_ge_atTop (2 : ℝ)] with T hrow hProfile hT
  intro γ hγ₁ hγ₂
  have hT₀ : 0 < T := by linarith
  have hlam₀ : 0 ≤ (1 : ℝ) / T := by positivity
  have hlam₁ : (1 : ℝ) / T ≤ 1 := (div_le_one hT₀).mpr (by linarith)
  let p := profile (1 / T) (γ / T)
  let q := profile 0 (γ / T)
  let R := row b γ / Real.log T
  have hp : 0 ≤ p := sq_nonneg _
  have hpr : |p - q| ≤ ε / 2 := by
    apply (profile_sub_le hlam₀ hlam₁ _).trans
    simpa only [Function.comp_def, one_div] using hProfile.le
  have hr := hrow γ hγ₁ hγ₂
  change |p * R - q| ≤ ε
  rw [show p * R - q = p * (R - 1) + (p - q) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hp]
  have h := mul_le_mul (profile_le_exp_one hlam₀ hlam₁ (γ / T)) hr (abs_nonneg _) (Real.exp_pos _).le
  have hv : Real.exp 1 * (ε / (2 * Real.exp 1)) = ε / 2 := by
    field_simp [(Real.exp_pos 1).ne']
  rw [hv] at h
  linarith

/-- Spectral mass on the compact window. -/
def scaledWindowEnergy (b T a B : ℝ) : ℝ :=
  ∑ ρ ∈ zeroWindow (a * T) (B * T), scaledEnergyTerm b T ρ

/-- On each compact positive annulus the actual spectral weights converge to
the limiting profile against the scaled counting measure. -/
theorem scaledWindowEnergy_tendsto (hRH : RiemannHypothesis) {b a B : ℝ} (hb : 0 < b)
    (ha : 0 < a) (haB : a ≤ B) :
    Tendsto (fun T : ℝ => scaledWindowEnergy b T a B) atTop
      (𝓝 ((∫ u in Ioc a B, profile 0 u) / (2 * Real.pi))) := by
  have ht := scaledWindowTest_tendsto ha haB profile_zero_contDiff_one
  apply ht.congr_dist
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let M := (B - a) / (2 * Real.pi) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let δ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hcount := (scaled_positive_window_tendsto ha haB).eventually
    (gt_mem_nhds (show (B - a) / (2 * Real.pi) < M by unfold M; linarith))
  filter_upwards [profile_scaled_row_uniform hRH hb ha haB hδ, hcount,
    eventually_ge_atTop (2 : ℝ)] with T hrow hmass hT
  have hT₀ : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  let W := zeroWindow (a * T) (B * T)
  let D := T * Real.log T
  let R (ρ : Zeros) := profile (1 / T) (ordinate ρ / T) * (row b (ordinate ρ) / Real.log T)
  let P (ρ : Zeros) := profile 0 (ordinate ρ / T)
  have hD : 0 < D := mul_pos hT₀ hL
  have he : scaledWindowEnergy b T a B = (∑ ρ ∈ W, multiplicity ρ * R ρ) / D := by
    rw [scaledWindowEnergy, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ρ _
    dsimp only [scaledEnergyTerm, R, D]
    field_simp [hT₀.ne', hL.ne']
  rw [Real.dist_eq, sub_zero]
  change |dist (scaledWindowTest T a B (profile 0)) (scaledWindowEnergy b T a B)| < ε
  rw [abs_of_nonneg dist_nonneg, dist_comm, Real.dist_eq, he]
  change |(∑ ρ ∈ W, multiplicity ρ * R ρ) / D - (∑ ρ ∈ W, multiplicity ρ * P ρ) / D| < ε
  rw [← sub_div, abs_div, abs_of_pos hD, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have hbound : |∑ ρ ∈ W, multiplicity ρ * (R ρ - P ρ)| ≤ δ * (Ncount (a*T) (B*T) : ℝ) := by
    rw [Ncount_eq_sum_zeroWindow, Finset.mul_sum]
    have hnorm := norm_sum_le W (fun ρ => multiplicity ρ * (R ρ - P ρ))
    simp only [Real.norm_eq_abs] at hnorm
    apply hnorm.trans
    apply Finset.sum_le_sum
    intro ρ hρ
    have hu := mem_zeroWindow.mp hρ
    rw [abs_mul, abs_of_nonneg (multiplicity_nonneg ρ), mul_comm δ]
    exact mul_le_mul_of_nonneg_left (hrow (ordinate ρ) hu.1.le hu.2) (multiplicity_nonneg ρ)
  calc
    _ ≤ (δ * (Ncount (a*T) (B*T) : ℝ)) / D :=
      div_le_div_of_nonneg_right hbound hD.le
    _ = δ * ((Ncount (a*T) (B*T) : ℝ) / D) := by ring
    _ < δ * M := mul_lt_mul_of_pos_left hmass hδ
    _ < ε := by
      have he : δ * (M + 1) = ε := by dsimp [δ]; field_simp [show M + 1 ≠ 0 by linarith]
      nlinarith

end GoldbachSpectrum
