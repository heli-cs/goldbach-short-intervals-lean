import Goldbach.Zeros

open Filter Set
open scoped BigOperators Topology
noncomputable section

namespace GoldbachZeros

/-- Offset of a zero in the translated partition into half-open unit intervals. -/
def unitCell (t : ℝ) (ρ : Zeros) : ℤ := Zeta23.WeilEF.key (ordinate ρ - t)

theorem unitCell_bounds (t : ℝ) (ρ : Zeros) :
    (unitCell t ρ : ℝ) < ordinate ρ - t ∧ ordinate ρ - t ≤ (unitCell t ρ : ℝ) + 1 :=
  ⟨Zeta23.WeilEF.key_lt _, Zeta23.WeilEF.le_key_add_one _⟩

/-- The summable cell envelope obtained from a logarithmic count and quadratic decay. -/
def unitEnvelope (n : ℤ) : ℝ := Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ)^2)

theorem unitEnvelope_nonneg (n : ℤ) : 0 ≤ unitEnvelope n := by
  unfold unitEnvelope
  exact div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)

theorem unitEnvelope_summable : Summable unitEnvelope := Zeta23.WeilEF.summable_weight

private theorem log_shift_le (t n : ℝ) :
    Real.log (|t + n| + 3) ≤ (2 / Real.log 3) *
      (Real.log (|t| + 3) * Real.log (|n| + 3)) := by
  have hp : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ht := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
    (show 3 ≤ |t| + 3 by linarith [abs_nonneg t])
  have hn := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
    (show 3 ≤ |n| + 3 by linarith [abs_nonneg n])
  have hprod : |t + n| + 3 ≤ (|t| + 3) * (|n| + 3) := by
    nlinarith [abs_add_le t n, abs_nonneg t, abs_nonneg n,
      mul_nonneg (abs_nonneg t) (abs_nonneg n)]
  calc
    _ ≤ Real.log ((|t| + 3) * (|n| + 3)) := Real.log_le_log (by positivity) hprod
    _ = Real.log (|t| + 3) + Real.log (|n| + 3) := Real.log_mul (by positivity) (by positivity)
    _ ≤ _ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hp]
      nlinarith only [mul_le_mul_of_nonneg_left ht (hp.le.trans hn),
        mul_le_mul_of_nonneg_left hn (hp.le.trans ht)]

private theorem reciprocal_sum_by_cells :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (s : Finset Zeros),
      (∑ ρ ∈ s, multiplicity ρ / (1 + (ordinate ρ - t)^2)) ≤
        C * Real.log (|t| + 3) * ∑ n ∈ s.image (unitCell t), unitEnvelope n := by
  classical
  obtain ⟨A, hA, hlocal⟩ := riemannVonMangoldt.local_count
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hLC := Zeta23.Tail.LocalCount.ofWindowCount Zeta23.zetaZeroConfig hA hlocal
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let C := 4 * A * (2 / Real.log 3)
  refine ⟨C, by dsimp [C]; positivity, fun t s => ?_⟩
  let κ := unitCell t
  rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ)
    (fun ρ hρ => Finset.mem_image_of_mem κ hρ), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have hwin (ρ : Zeros) (hρ : ρ ∈ s.filter (fun ρ => κ ρ = n)) :
      (n : ℝ) < ordinate ρ - t ∧ ordinate ρ - t ≤ (n : ℝ) + 1 := by
    have h := (Finset.mem_filter.mp hρ).2
    simpa only [← h] using unitCell_bounds t ρ
  have hcnt := hLC.window (t + (n : ℝ)) (s.filter (fun ρ => κ ρ = n)) (fun ρ hρ => by
    obtain ⟨h₁, h₂⟩ := hwin ρ hρ
    change t + (n : ℝ) < ordinate ρ ∧ ordinate ρ ≤ t + (n : ℝ) + 1
    exact ⟨by linarith, by linarith⟩)
  calc
    _ ≤ ∑ ρ ∈ s with κ ρ = n, (4 / (1 + (n : ℝ)^2)) * multiplicity ρ := by
      apply Finset.sum_le_sum
      intro ρ hρ
      obtain ⟨h₁, h₂⟩ := hwin ρ hρ
      have h := Zeta23.WeilEF.one_add_sq_ge h₁ h₂
      have hq : 1 / (1 + (ordinate ρ - t)^2) ≤ 4 / (1 + (n : ℝ)^2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      rw [div_eq_mul_inv, ← one_div (1 + (ordinate ρ - t)^2), mul_comm]
      exact mul_le_mul_of_nonneg_right hq (multiplicity_nonneg ρ)
    _ = (4 / (1 + (n : ℝ)^2)) * ∑ ρ ∈ s with κ ρ = n, multiplicity ρ := by rw [Finset.mul_sum]
    _ ≤ (4 / (1 + (n : ℝ)^2)) * (A * Real.log (|t + (n : ℝ)| + 3)) :=
      mul_le_mul_of_nonneg_left hcnt (by positivity)
    _ ≤ (4 / (1 + (n : ℝ)^2)) *
        (A * ((2 / Real.log 3) * (Real.log (|t| + 3) * Real.log (|(n : ℝ)| + 3)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (log_shift_le _ _) hA0.le) (by positivity)
    _ = _ := by dsimp [C, unitEnvelope]; ring

/-- A uniform bound for any restricted collection of translated unit cells.
Taking the complement of a growing finite set gives uniform tail domination. -/
theorem translated_cell_tsum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (E : Set ℤ),
      let q := fun ρ : Zeros => E.indicator (fun _ =>
        multiplicity ρ / (1 + (ordinate ρ - t)^2)) (unitCell t ρ)
      Summable q ∧ (∑' ρ, q ρ) ≤ C * Real.log (|t| + 3) * ∑' n, E.indicator unitEnvelope n := by
  classical
  obtain ⟨C, hC, hfinite⟩ := reciprocal_sum_by_cells
  refine ⟨C, hC, fun t E => ?_⟩
  dsimp
  let q := fun ρ : Zeros => E.indicator (fun _ =>
    multiplicity ρ / (1 + (ordinate ρ - t)^2)) (unitCell t ρ)
  have hq (ρ : Zeros) : 0 ≤ q ρ := by
    by_cases h : unitCell t ρ ∈ E
    · simp only [q, Set.indicator_of_mem h]
      exact div_nonneg (multiplicity_nonneg ρ) (by positivity)
    · simp [q, Set.indicator_of_notMem h]
  have hE : Summable (E.indicator unitEnvelope) := unitEnvelope_summable.indicator E
  have hlog : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hfin (s : Finset Zeros) :
      (∑ ρ ∈ s, q ρ) ≤ C * Real.log (|t| + 3) * ∑' n, E.indicator unitEnvelope n := by
    let s' := s.filter (fun ρ => unitCell t ρ ∈ E)
    have hs : (∑ ρ ∈ s, q ρ) =
        ∑ ρ ∈ s', multiplicity ρ / (1 + (ordinate ρ - t)^2) := by
      simp only [q, s', Finset.sum_filter, Set.indicator]
    rw [hs]
    apply (hfinite t s').trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hlog)
    have him (n : ℤ) (hn : n ∈ s'.image (unitCell t)) : n ∈ E := by
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hn
      exact (Finset.mem_filter.mp hρ).2
    calc
      _ = ∑ n ∈ s'.image (unitCell t), E.indicator unitEnvelope n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Set.indicator_of_mem (him n hn)]
      _ ≤ _ := hE.sum_le_tsum _ (fun n _ => Set.indicator_nonneg (fun n _ => unitEnvelope_nonneg n) n)
  have hs := summable_of_sum_le hq hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

/-- Uniform continuity of the translated zero sums in the reciprocal-quadratic weighted norm. -/
theorem translated_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (f : ℝ → ℂ) (B : ℝ), 0 ≤ B →
      (∀ u, ‖f u‖ ≤ B / (1 + u^2)) →
      Summable (fun ρ : Zeros => (multiplicity ρ : ℂ) * f (ordinate ρ - t)) ∧
      ‖∑' ρ : Zeros, (multiplicity ρ : ℂ) * f (ordinate ρ - t)‖ ≤
        C * B * Real.log (|t| + 3) := by
  obtain ⟨C, hC, hcell⟩ := translated_cell_tsum_bound
  have hs : 0 < ∑' n, unitEnvelope n := by
    have h := unitEnvelope_summable.le_tsum (0 : ℤ) (fun n _ => unitEnvelope_nonneg n)
    refine lt_of_lt_of_le ?_ h
    unfold unitEnvelope
    simpa using Real.log_pos (show (1 : ℝ) < 3 by norm_num)
  refine ⟨C * ∑' n, unitEnvelope n, mul_pos hC hs, fun t f B hB hf => ?_⟩
  have H := hcell t Set.univ
  simp only [Set.indicator_univ] at H
  let e := fun ρ : Zeros => (multiplicity ρ : ℂ) * f (ordinate ρ - t)
  have he (ρ : Zeros) : ‖e ρ‖ ≤ B * (multiplicity ρ / (1 + (ordinate ρ - t)^2)) := by
    dsimp [e]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (multiplicity_nonneg ρ)]
    exact (mul_le_mul_of_nonneg_left (hf _) (multiplicity_nonneg ρ)).trans_eq (by ring)
  have hsum := (H.1.mul_left B).of_nonneg_of_le (fun ρ => norm_nonneg (e ρ)) he
  refine ⟨hsum.of_norm, ?_⟩
  calc
    _ ≤ ∑' ρ, ‖e ρ‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' ρ : Zeros, B * (multiplicity ρ / (1 + (ordinate ρ - t)^2)) :=
      hsum.tsum_le_tsum he (H.1.mul_left B)
    _ ≤ _ := by
      rw [tsum_mul_left]
      exact (mul_le_mul_of_nonneg_left H.2 hB).trans_eq (by ring)

end GoldbachZeros
