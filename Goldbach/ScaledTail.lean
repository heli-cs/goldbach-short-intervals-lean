import Goldbach.LocalDensity
import Goldbach.CumulativeZeros
import Goldbach.SpectrumEnergy

open Filter Set
open scoped BigOperators Topology
noncomputable section

namespace GoldbachSpectrum

open GoldbachZeros Zeta23

/-- The spectral summand at inverse log width T, divided by the target scale. -/
def scaledEnergyTerm (b T : ℝ) (ρ : Zeros) : ℝ :=
  multiplicity ρ * profile (1 / T) (ordinate ρ / T) * row b (ordinate ρ) /
    (T * (Real.log T)^2)

theorem scaledEnergyTerm_nonneg {b T : ℝ} (hT : 0 ≤ T) (ρ : Zeros) :
    0 ≤ scaledEnergyTerm b T ρ := by
  have hrow : 0 ≤ row b (ordinate ρ) :=
    tsum_nonneg fun σ => mul_nonneg (multiplicity_nonneg σ) (GoldbachGaussian.kernel_nonneg _ _)
  exact div_nonneg (mul_nonneg (mul_nonneg (multiplicity_nonneg ρ) (sq_nonneg _)) hrow)
    (mul_nonneg hT (sq_nonneg _))

theorem scaledEnergyTerm_eq {b T : ℝ} (hT : 0 < T) (ρ : Zeros) :
    scaledEnergyTerm b T ρ =
      diagonalEnergy b (fun σ => coefficient (1 / T) (ordinate σ)) ρ /
        ((1 / T) * (Real.log T)^2) := by
  unfold scaledEnergyTerm diagonalEnergy
  rw [coefficient_sq_scale (by positivity),
    show 1 / T * ordinate ρ = ordinate ρ / T by ring]
  by_cases hL : Real.log T = 0
  · simp [hL]
  · field_simp [hT.ne', hL]

theorem scaledEnergyTerm_summable {b T : ℝ} (hb : 0 < b) (hT : 1 ≤ T) :
    Summable (scaledEnergyTerm b T) := by
  have hT₀ : 0 < T := zero_lt_one.trans_le hT
  refine ((diagonalEnergy_summable hb (div_nonneg zero_le_one hT₀.le)
    ((div_le_one hT₀).mpr hT)).div_const ((1 / T) * (Real.log T)^2)).congr ?_
  intro ρ
  exact (scaledEnergyTerm_eq (b := b) hT₀ ρ).symm

private theorem cumulative_upper :
    ∃ A : ℝ, 0 < A ∧ ∃ t₀ : ℝ, 3 ≤ t₀ ∧
      ∀ u ≥ t₀, (Ncount 0 u : ℝ) ≤ A * (u * Real.log u) := by
  let A := 1 + 1 / (2 * Real.pi)
  have hA : 0 < A := by dsimp [A]; positivity
  have h := cumulative_count_tendsto.eventually
    (gt_mem_nhds (show 1 / (2 * Real.pi) < A by dsimp [A]; linarith))
  obtain ⟨v, hv⟩ := eventually_atTop.mp h
  refine ⟨A, hA, max v 3, le_max_right _ _, fun u hu => ?_⟩
  have hu₁ : 1 < u := by linarith [(le_max_right v (3 : ℝ)).trans hu]
  exact (div_le_iff₀ (mul_pos (zero_lt_one.trans hu₁) (Real.log_pos hu₁))).mp
    (hv u ((le_max_left v 3).trans hu)).le

private theorem log_add_three_le {u : ℝ} (hu : 3 ≤ u) :
    Real.log (u + 3) ≤ 2 * Real.log u := by
  have hu₀ : 0 < u := by linarith
  calc
    _ ≤ Real.log (u^2) := Real.log_le_log (by positivity) (by
      nlinarith [mul_nonneg (by linarith : 0 ≤ u - 3) hu₀.le])
    _ = _ := by rw [Real.log_pow]; norm_num

/-- Uniform control of the small frequencies on the positive half-line. -/
theorem scaledEnergy_small_bound {b : ℝ} (hb : 0 < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ᶠ T : ℝ in atTop,
      (∑ ρ ∈ zeroWindow 0 (r * T), scaledEnergyTerm b T ρ) ≤ K * r := by
  obtain ⟨A, hA, T₀, hT₀, hcnt⟩ := cumulative_upper
  obtain ⟨C, hC, hrow⟩ := row_summable_and_bound hb
  refine ⟨2 * C * Real.exp 1 * A, by positivity, fun r hr hr₁ => ?_⟩
  filter_upwards [eventually_ge_atTop (3 : ℝ), eventually_ge_atTop (T₀ / r)] with T hT hTr
  have hT₀' : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hrT : T₀ ≤ r * T := by linarith [(div_le_iff₀ hr).mp hTr]
  have hrT' : r * T ≤ T := by nlinarith [mul_le_mul_of_nonneg_right hr₁ hT₀'.le]
  have hmass : (Ncount 0 (r * T) : ℝ) ≤ A * (r * T * Real.log T) := by
    apply (hcnt _ hrT).trans
    apply mul_le_mul_of_nonneg_left _ hA.le
    gcongr
  let D := (2 * C * Real.exp 1) / (T * Real.log T)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hterm (ρ : Zeros) (hρ : ρ ∈ zeroWindow 0 (r*T)) :
      scaledEnergyTerm b T ρ ≤ D * multiplicity ρ := by
    obtain ⟨hγ, hγT⟩ := mem_zeroWindow.mp hρ
    have hR : row b (ordinate ρ) ≤ C * (2 * Real.log T) := by
      apply (hrow _).2.trans
      apply mul_le_mul_of_nonneg_left _ hC
      rw [abs_of_nonneg hγ.le]
      exact (Real.log_le_log (by positivity) (by linarith [hγT.trans hrT'])).trans
        (log_add_three_le hT)
    have hp := profile_le_exp_one (div_nonneg zero_le_one hT₀'.le)
      ((div_le_one hT₀').mpr (by linarith : 1 ≤ T)) (ordinate ρ / T)
    have hR0 : 0 ≤ row b (ordinate ρ) :=
      tsum_nonneg fun σ => mul_nonneg (multiplicity_nonneg σ) (GoldbachGaussian.kernel_nonneg _ _)
    calc
      _ ≤ multiplicity ρ * (Real.exp 1 * (C * (2 * Real.log T))) /
          (T * (Real.log T)^2) := by
        unfold scaledEnergyTerm
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hp hR hR0 (by positivity))
          (multiplicity_nonneg ρ)
      _ = _ := by dsimp [D]; field_simp [hT₀'.ne', hL.ne']
  calc
    _ ≤ ∑ ρ ∈ zeroWindow 0 (r*T), D * multiplicity ρ := Finset.sum_le_sum hterm
    _ = D * (Ncount 0 (r*T) : ℝ) := by rw [← Finset.mul_sum, Ncount_eq_sum_zeroWindow]
    _ ≤ D * (A * (r * T * Real.log T)) := mul_le_mul_of_nonneg_left hmass hD
    _ = _ := by dsimp [D]; field_simp [hT₀'.ne', hL.ne']

private theorem exists_dyadic_upper (x : ℝ) : ∃ j : ℕ, x ≤ (2 : ℝ)^(j + 1) := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt x (show (1 : ℝ) < 2 by norm_num)
  exact ⟨j, hj.le.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ _))⟩

private def dyadicIndex (x : ℝ) : ℕ := Nat.find (exists_dyadic_upper x)

private theorem dyadicIndex_bounds {x : ℝ} (hx : 1 < x) :
    (2 : ℝ)^(dyadicIndex x) < x ∧ x ≤ (2 : ℝ)^(dyadicIndex x + 1) := by
  refine ⟨?_, Nat.find_spec (exists_dyadic_upper x)⟩
  cases h : dyadicIndex x with
  | zero => simpa only [h, pow_zero] using hx
  | succ j =>
    have hj : j < Nat.find (exists_dyadic_upper x) := by change j < dyadicIndex x; rw [h]; omega
    exact lt_of_not_ge (Nat.find_min (exists_dyadic_upper x) hj)

def dyadicMajorant (j : ℕ) : ℝ := ((j : ℝ) + 2)^2 / (2 : ℝ)^j

private theorem dyadicMajorant_nonneg (j : ℕ) : 0 ≤ dyadicMajorant j := by
  unfold dyadicMajorant
  positivity

private theorem dyadicMajorant_summable : Summable dyadicMajorant := by
  have h := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).comp_injective (i := fun j : ℕ => j + 2)
      (fun _ _ h => Nat.add_right_cancel h)
  refine (h.mul_left 4).congr ?_
  intro j
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat, pow_add _ j 2,
    one_div, inv_pow, dyadicMajorant]
  ring

/-- The summable dyadic envelope is independent of T once T is sufficiently large. -/
theorem scaledEnergy_dyadic_tail_bound {b : ℝ} (hb : 0 < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ T ≥ T₀, ∀ J : ℕ,
      (∑' ρ : Zeros, {ρ | (2 : ℝ)^J * T < ordinate ρ}.indicator
        (scaledEnergyTerm b T) ρ) ≤ K *
        ((∑' j : ℕ, dyadicMajorant j) - ∑ j ∈ Finset.range J, dyadicMajorant j) := by
  classical
  obtain ⟨A, hA, T₀, hT₀, hcnt⟩ := cumulative_upper
  obtain ⟨C, hC, hrow⟩ := row_summable_and_bound hb
  let D := (1 + Real.exp (1 / 2))^2
  let K := 4 * A * C * D
  have hD : 0 ≤ D := by unfold D; positivity
  have hK : 0 ≤ K := by unfold K; positivity
  refine ⟨K, hK, T₀, hT₀, fun T hT J => ?_⟩
  have hT₃ := hT₀.trans hT
  have hTp : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  let E : Set Zeros := {ρ | (2 : ℝ)^J * T < ordinate ρ}
  have hpos (ρ : Zeros) : 0 ≤ E.indicator (scaledEnergyTerm b T) ρ :=
    indicator_nonneg (fun σ _ => scaledEnergyTerm_nonneg hTp.le σ) ρ
  apply Real.tsum_le_of_sum_le hpos
  intro s
  let s' := s.filter (· ∈ E)
  let κ (ρ : Zeros) := dyadicIndex (ordinate ρ / T)
  have hfilter : (∑ ρ ∈ s, E.indicator (scaledEnergyTerm b T) ρ) =
      ∑ ρ ∈ s', scaledEnergyTerm b T ρ := by simp only [s', Finset.sum_filter, Set.indicator]
  rw [hfilter, ← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s'.image κ)
    (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
  have hmem (ρ : Zeros) (hρ : ρ ∈ s') : (2 : ℝ)^J < ordinate ρ / T :=
    (lt_div_iff₀ hTp).mpr (Finset.mem_filter.mp hρ).2
  have hlow (ρ : Zeros) (hρ : ρ ∈ s') : 1 < ordinate ρ / T :=
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans_lt (hmem ρ hρ)
  have hgroup (j : ℕ) :
      (∑ ρ ∈ s' with κ ρ = j, scaledEnergyTerm b T ρ) ≤ K * dyadicMajorant j := by
    let B : ℝ := 2^j
    let U := (2 : ℝ)^(j+1) * T
    have hB : 0 < B := by unfold B; positivity
    have hB₁ : 1 ≤ B := one_le_pow₀ (by norm_num)
    have hU : U = 2 * B * T := by simp only [U, B, pow_succ']
    have hTU : T ≤ U := by
      rw [hU]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (show 1 ≤ 2 * B by linarith) hTp.le
    have hU₃ := hT₃.trans hTU
    have hUp : 0 < U := hTp.trans_le hTU
    have hLU : Real.log U ≤ ((j : ℝ) + 2) * Real.log T := by
      dsimp only [U]
      rw [Real.log_mul (by positivity) hTp.ne', Real.log_pow, Nat.cast_add, Nat.cast_one]
      have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ T by linarith)
      nlinarith only [mul_le_mul_of_nonneg_left hle (show 0 ≤ (j : ℝ) + 1 by positivity)]
    let Q := D * (2 * C * ((j : ℝ) + 2)) / (B^2 * T * Real.log T)
    have hQ : 0 ≤ Q := by unfold Q; positivity
    let F := s'.filter (fun ρ => κ ρ = j)
    have hcell (ρ : Zeros) (hρ : ρ ∈ F) :
        B < ordinate ρ / T ∧ ordinate ρ ≤ U := by
      obtain ⟨hρ', hj⟩ := Finset.mem_filter.mp hρ
      have h := dyadicIndex_bounds (hlow ρ hρ')
      change dyadicIndex (ordinate ρ / T) = j at hj
      rw [hj] at h
      exact ⟨h.1, (div_le_iff₀ hTp).mp h.2⟩
    have hsub : F ⊆ zeroWindow 0 U := by
      intro ρ hρ
      obtain ⟨h₁,h₂⟩ := hcell ρ hρ
      exact mem_zeroWindow.mpr ⟨(mul_pos hB hTp).trans ((lt_div_iff₀ hTp).mp h₁), h₂⟩
    have hmass : (∑ ρ ∈ F, multiplicity ρ) ≤ A * (U * (((j : ℝ) + 2) * Real.log T)) := by
      calc
        _ ≤ ∑ ρ ∈ zeroWindow 0 U, multiplicity ρ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ => multiplicity_nonneg ρ)
        _ = (Ncount 0 U : ℝ) := (Ncount_eq_sum_zeroWindow _ _).symm
        _ ≤ A * (U * Real.log U) := hcnt _ (hT.trans hTU)
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLU hUp.le) hA.le
    have hterm (ρ : Zeros) (hρ : ρ ∈ F) : scaledEnergyTerm b T ρ ≤ Q * multiplicity ρ := by
      obtain ⟨h₁,h₂⟩ := hcell ρ hρ
      have hγ : 0 < ordinate ρ := (mul_pos hB hTp).trans ((lt_div_iff₀ hTp).mp h₁)
      have hp : profile (1 / T) (ordinate ρ / T) ≤ D / B^2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hB)).mpr
        rw [mul_comm]
        exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB.le h₁.le _) (sq_nonneg _)).trans
          (sq_mul_profile_le (div_nonneg zero_le_one hTp.le)
            ((div_le_one hTp).mpr (by linarith : 1 ≤ T)) _)
      have hR : row b (ordinate ρ) ≤ C * (2 * (((j : ℝ) + 2) * Real.log T)) := by
        apply (hrow _).2.trans
        apply mul_le_mul_of_nonneg_left _ hC
        rw [abs_of_nonneg hγ.le]
        exact (Real.log_le_log (by positivity) (by linarith)).trans
          ((log_add_three_le hU₃).trans (mul_le_mul_of_nonneg_left hLU (by norm_num)))
      have hR₀ : 0 ≤ row b (ordinate ρ) :=
        tsum_nonneg fun σ => mul_nonneg (multiplicity_nonneg σ) (GoldbachGaussian.kernel_nonneg _ _)
      calc
        _ ≤ multiplicity ρ * (D / B^2 * (C * (2 * (((j : ℝ) + 2) * Real.log T)))) /
            (T * (Real.log T)^2) := by
          unfold scaledEnergyTerm
          apply div_le_div_of_nonneg_right _ (by positivity)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hp hR hR₀ (by positivity))
            (multiplicity_nonneg ρ)
        _ = _ := by dsimp [Q]; field_simp [hB.ne', hTp.ne', hL.ne']
    calc
      _ ≤ ∑ ρ ∈ F, Q * multiplicity ρ := Finset.sum_le_sum hterm
      _ = Q * ∑ ρ ∈ F, multiplicity ρ := by rw [Finset.mul_sum]
      _ ≤ Q * (A * (U * (((j : ℝ) + 2) * Real.log T))) := mul_le_mul_of_nonneg_left hmass hQ
      _ = _ := by
        rw [hU]
        unfold Q K dyadicMajorant
        change _ = (4 * A * C * D) * (((j : ℝ) + 2)^2 / B)
        field_simp [hB.ne', hTp.ne', hL.ne']
        ring
  have hdis : Disjoint (s'.image κ) (Finset.range J) := by
    rw [Finset.disjoint_left]
    intro j hj hjJ
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hj
    have hlt : κ ρ < J := Finset.mem_range.mp hjJ
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show κ ρ + 1 ≤ J by omega)
    exact (not_le_of_gt (hmem ρ hρ)) ((dyadicIndex_bounds (hlow ρ hρ)).2.trans hpow)
  have hsum : (∑ j ∈ s'.image κ, dyadicMajorant j) ≤
      (∑' j : ℕ, dyadicMajorant j) - ∑ j ∈ Finset.range J, dyadicMajorant j := by
    apply (le_sub_iff_add_le).mpr
    rw [← Finset.sum_union hdis]
    exact dyadicMajorant_summable.sum_le_tsum _ (fun j _ => dyadicMajorant_nonneg j)
  calc
    _ ≤ ∑ j ∈ s'.image κ, K * dyadicMajorant j := Finset.sum_le_sum (fun j _ => hgroup j)
    _ = K * ∑ j ∈ s'.image κ, dyadicMajorant j := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hK

theorem dyadicMajorant_tail_tendsto_zero :
    Tendsto (fun J : ℕ => (∑' j : ℕ, dyadicMajorant j) - ∑ j ∈ Finset.range J, dyadicMajorant j)
      atTop (𝓝 0) := by
  simpa only [sub_self] using ((tendsto_const_nhds (x := ∑' j : ℕ, dyadicMajorant j)).sub
    dyadicMajorant_summable.hasSum.tendsto_sum_nat)

end GoldbachSpectrum
