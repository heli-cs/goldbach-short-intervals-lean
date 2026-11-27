import Goldbach.ScaledAnnulus

open Filter MeasureTheory Set
open scoped BigOperators Topology
noncomputable section

namespace GoldbachSpectrum

open GoldbachZeros Zeta23

/-- Normalized spectral mass restricted to the stated ordinate set. -/
def scaledEnergyOn (b T : ℝ) (s : Set ℝ) : ℝ :=
  ∑' ρ : Zeros, (ordinate ⁻¹' s).indicator (scaledEnergyTerm b T) ρ

private theorem scaledEnergyOn_nonneg {b T : ℝ} (hT : 0 ≤ T) (s : Set ℝ) :
    0 ≤ scaledEnergyOn b T s :=
  tsum_nonneg (fun ρ => indicator_nonneg (fun σ _ => scaledEnergyTerm_nonneg hT σ) ρ)

private theorem scaledEnergyOn_union {b T : ℝ} (hb : 0 < b) (hT : 1 ≤ T)
    {s t : Set ℝ} (hst : Disjoint s t) :
    scaledEnergyOn b T (s ∪ t) = scaledEnergyOn b T s + scaledEnergyOn b T t := by
  classical
  have h := scaledEnergyTerm_summable hb hT
  unfold scaledEnergyOn
  rw [← (h.indicator (ordinate ⁻¹' s)).tsum_add (h.indicator (ordinate ⁻¹' t))]
  apply tsum_congr
  intro ρ
  by_cases hs : ordinate ρ ∈ s
  · have ht : ordinate ρ ∉ t := fun ht => Set.disjoint_left.mp hst hs ht
    rw [indicator_of_mem (show ρ ∈ ordinate ⁻¹' (s ∪ t) from Or.inl hs),
      indicator_of_mem (show ρ ∈ ordinate ⁻¹' s from hs),
      indicator_of_notMem (show ρ ∉ ordinate ⁻¹' t from ht), add_zero]
  · by_cases ht : ordinate ρ ∈ t
    · rw [indicator_of_mem (show ρ ∈ ordinate ⁻¹' (s ∪ t) from Or.inr ht),
        indicator_of_notMem (show ρ ∉ ordinate ⁻¹' s from hs),
        indicator_of_mem (show ρ ∈ ordinate ⁻¹' t from ht), zero_add]
    · rw [indicator_of_notMem (show ρ ∉ ordinate ⁻¹' (s ∪ t) from
          fun he => he.elim hs ht),
        indicator_of_notMem (show ρ ∉ ordinate ⁻¹' s from hs),
        indicator_of_notMem (show ρ ∉ ordinate ⁻¹' t from ht), add_zero]

private theorem scaledEnergyOn_Ioc (b T a B : ℝ) :
    scaledEnergyOn b T (Ioc a B) = ∑ ρ ∈ zeroWindow a B, scaledEnergyTerm b T ρ := by
  classical
  unfold scaledEnergyOn
  rw [tsum_eq_sum (s := zeroWindow a B)]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    have hm : ρ ∈ ordinate ⁻¹' Ioc a B := mem_zeroWindow.mp hρ
    exact indicator_of_mem hm (scaledEnergyTerm b T)
  · intro ρ hρ
    have hn : ρ ∉ ordinate ⁻¹' Ioc a B := fun he => hρ (mem_zeroWindow.mpr he)
    rw [indicator_of_notMem hn]

private theorem spectral_neg_eq_pos (b T : ℝ) :
    scaledEnergyOn b T (Iio 0) = scaledEnergyOn b T (Ioi 0) := by
  classical
  unfold scaledEnergyOn
  rw [← conjugation.tsum_eq ((ordinate ⁻¹' Iio 0).indicator (scaledEnergyTerm b T))]
  apply tsum_congr
  intro ρ
  have hsym : scaledEnergyTerm b T (conjugation ρ) = scaledEnergyTerm b T ρ := by
    simp only [scaledEnergyTerm, multiplicity_conjugation, ordinate_conjugation,
      neg_div, profile_even, row_even]
  simp only [Set.indicator, mem_preimage, mem_Iio, mem_Ioi, ordinate_conjugation, neg_lt_zero, hsym]

private theorem expanding_annulus_integral :
    Tendsto (fun J : ℕ => (∫ u in Ioc ((2 : ℝ)^J)⁻¹ ((2 : ℝ)^J), profile 0 u) /
      (2 * Real.pi)) atTop (𝓝 (1 / 2)) := by
  let s := fun J : ℕ => Ioc ((2 : ℝ)^J)⁻¹ ((2 : ℝ)^J)
  have hs : Monotone s := by
    intro n m hnm x hx
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnm
    exact ⟨(inv_anti₀ (by positivity) h).trans_lt hx.1, hx.2.trans h⟩
  have hbig := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hsmall := tendsto_inv_atTop_zero.comp hbig
  have hu : (⋃ J, s J) = Ioi (0 : ℝ) := by
    ext x
    rw [mem_iUnion, mem_Ioi]
    constructor
    · rintro ⟨J, hJ⟩
      exact (by positivity : 0 < ((2 : ℝ)^J)⁻¹).trans hJ.1
    · intro hx
      obtain ⟨J, hj, hJ⟩ :=
        ((hsmall.eventually (gt_mem_nhds hx)).and (hbig.eventually (eventually_ge_atTop x))).exists
      exact ⟨J, hj, hJ⟩
  have h := tendsto_setIntegral_of_monotone (f := profile 0)
    (fun J => (measurableSet_Ioc : MeasurableSet (s J))) hs profile_zero_integrable.integrableOn
  rw [hu, integral_profile_zero_positive] at h
  have hscale : Real.pi / (2 * Real.pi) = (1 : ℝ) / 2 := by
    field_simp [Real.pi_pos.ne']
  simpa only [hscale] using h.div_const (2 * Real.pi)

private theorem positive_energy_three_regions {b T r R : ℝ} (hb : 0 < b) (hT : 1 ≤ T)
    (hr : 0 ≤ r) (hrR : r ≤ R) :
    scaledEnergyOn b T (Ioi 0) =
      scaledWindowEnergy b T 0 r + scaledWindowEnergy b T r R + scaledEnergyOn b T (Ioi (R*T)) := by
  have hT' : 0 ≤ T := zero_le_one.trans hT
  have h₁ : Disjoint (Ioc (0 : ℝ) (r*T)) (Ioc (r*T) (R*T)) :=
    Set.disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2) hy.1
  have h₂ : Disjoint (Ioc (0 : ℝ) (R*T)) (Ioi (R*T)) :=
    Set.disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2) hy
  unfold scaledWindowEnergy
  rw [zero_mul, ← scaledEnergyOn_Ioc, ← scaledEnergyOn_Ioc, ← scaledEnergyOn_union hb hT h₁,
    Ioc_union_Ioc_eq_Ioc (mul_nonneg hr hT') (mul_le_mul_of_nonneg_right hrR hT'),
    ← scaledEnergyOn_union hb hT h₂,
    Ioc_union_Ioi_eq_Ioi (mul_nonneg (hr.trans hrR) hT')]

/-- The positive half of the spectrum gives exactly one half of the main term. -/
theorem scaledEnergy_positive_tendsto (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun T : ℝ => scaledEnergyOn b T (Ioi 0)) atTop (𝓝 (1 / 2)) := by
  obtain ⟨As, hAs, hsmall⟩ := scaledEnergy_small_bound hb
  obtain ⟨At, hAt, T₀, hT₀, htail⟩ := scaledEnergy_dyadic_tail_bound hb
  have hbound := ((tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))).const_mul As).add
      (dyadicMajorant_tail_tendsto_zero.const_mul At)
  simp only [mul_zero, zero_add] at hbound
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hnear := (Metric.tendsto_nhds.mp expanding_annulus_integral) (ε / 3) (by positivity)
  have hfar := hbound.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))
  obtain ⟨J, hNear, hFar⟩ := (hnear.and hfar).exists
  let r : ℝ := ((2 : ℝ)^J)⁻¹
  let R : ℝ := (2 : ℝ)^J
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hr : 0 < r := by unfold r; positivity
  have hr₁ : r ≤ 1 := by
    change R⁻¹ ≤ 1
    exact (inv_le_one₀ (zero_lt_one.trans_le hR)).mpr hR
  have hrR := hr₁.trans hR
  have he := (Metric.tendsto_nhds.mp (scaledWindowEnergy_tendsto hRH hb hr hrR))
    (ε / 3) (by positivity)
  filter_upwards [hsmall r hr hr₁, eventually_ge_atTop T₀, he] with T hS hT hE
  have hT₁ : 1 ≤ T := by linarith [hT₀.trans hT]
  have hT₀' : 0 ≤ T := zero_le_one.trans hT₁
  let A := scaledWindowEnergy b T r R
  let S := scaledWindowEnergy b T 0 r
  let D := scaledEnergyOn b T (Ioi (R*T))
  let L := (∫ u in Ioc r R, profile 0 u) / (2 * Real.pi)
  have hS₀ : 0 ≤ S := Finset.sum_nonneg (fun ρ _ => scaledEnergyTerm_nonneg hT₀' ρ)
  have hD₀ : 0 ≤ D := scaledEnergyOn_nonneg hT₀' _
  have hs : S ≤ As * r := by simpa only [S, scaledWindowEnergy, zero_mul] using hS
  have hd : D ≤ At * ((∑' j : ℕ, dyadicMajorant j) - ∑ j ∈ Finset.range J, dyadicMajorant j) :=
    htail T hT J
  have hSD : S + D < ε / 3 := (add_le_add hs hd).trans_lt hFar
  have hM : |A - L| < ε / 3 := by simpa only [Real.dist_eq] using hE
  have hL : |L - 1 / 2| < ε / 3 := by simpa only [Real.dist_eq] using hNear
  rw [Real.dist_eq, positive_energy_three_regions hb hT₁ hr.le hrR]
  change |S + A + D - 1 / 2| < ε
  have eq : S + A + D - 1 / 2 = (S + D) + (A - L) + (L - 1 / 2) := by ring
  rw [eq]
  calc
    _ ≤ |(S + D) + (A - L)| + |L - 1 / 2| := abs_add_le _ _
    _ ≤ |S + D| + |A - L| + |L - 1 / 2| := add_le_add (abs_add_le _ _) le_rfl
    _ < ε := by rw [abs_of_nonneg (add_nonneg hS₀ hD₀)]; linarith

private theorem zero_frequency_tendsto (b : ℝ) :
    Tendsto (fun T : ℝ => scaledEnergyOn b T {0}) atTop (𝓝 0) := by
  classical
  let W := zeroWindow (-1) 0
  let C := (∑ ρ ∈ W, multiplicity ρ) * (Real.exp 1 * row b 0)
  have hR : 0 ≤ row b 0 :=
    tsum_nonneg (fun ρ => mul_nonneg (multiplicity_nonneg ρ) (GoldbachGaussian.kernel_nonneg _ _))
  have h := (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).const_mul C
  rw [mul_zero] at h
  apply squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop (max 2 (Real.exp 1))] with T hT
  have hT₂ := (le_max_left _ _).trans hT
  have hT₀ : 0 < T := by linarith
  have hL : 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hT)
  rw [Real.norm_of_nonneg (scaledEnergyOn_nonneg hT₀.le _)]
  unfold scaledEnergyOn
  rw [tsum_eq_sum (s := W) (fun ρ hρ => indicator_of_notMem (fun h => hρ <| by
    have hγ : ordinate ρ = 0 := h
    exact mem_zeroWindow.mpr ⟨by linarith, by linarith⟩) _)]
  let D := (Real.exp 1 * row b 0) / T
  have hterm (ρ : Zeros) : (ordinate ⁻¹' {0}).indicator (scaledEnergyTerm b T) ρ ≤ multiplicity ρ * D := by
    by_cases hρ : ordinate ρ = 0
    · rw [indicator_of_mem (show ρ ∈ ordinate ⁻¹' {0} from hρ), scaledEnergyTerm, hρ]
      have hp := profile_le_exp_one (div_nonneg zero_le_one hT₀.le)
        ((div_le_one hT₀).mpr (by linarith : 1 ≤ T)) (0 / T)
      have hsq : 1 ≤ (Real.log T)^2 := by nlinarith [sq_nonneg (Real.log T - 1)]
      have hden : T ≤ T * (Real.log T)^2 := by nlinarith [mul_le_mul_of_nonneg_left hsq hT₀.le]
      rw [mul_assoc, mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (multiplicity_nonneg ρ)
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hp hR) hT₀ hden
    · rw [indicator_of_notMem (show ρ ∉ ordinate ⁻¹' {0} from hρ)]
      exact mul_nonneg (multiplicity_nonneg ρ) (by unfold D; positivity)
  calc
    _ ≤ ∑ ρ ∈ W, multiplicity ρ * D := Finset.sum_le_sum (fun ρ _ => hterm ρ)
    _ = _ := by rw [← Finset.sum_mul]; unfold D C; rw [div_eq_mul_inv]; ring

theorem scaledEnergy_tendsto_one (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun T : ℝ => ∑' ρ : Zeros, scaledEnergyTerm b T ρ) atTop (𝓝 1) := by
  have H := ((scaledEnergy_positive_tendsto hRH hb).const_mul 2).add (zero_frequency_tendsto b)
  norm_num at H
  apply H.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have h₁ : Disjoint (Iio (0 : ℝ)) ({0} : Set ℝ) :=
    Set.disjoint_left.mpr (fun u hu hz => (ne_of_lt hu) hz)
  have h₂ : Disjoint (Iio (0 : ℝ) ∪ {0}) (Ioi (0 : ℝ)) := by
    apply Set.disjoint_left.mpr
    rintro u (hu | hu) hv
    · exact (not_lt_of_ge (show u ≤ 0 from (show u < 0 from hu).le)) (show 0 < u from hv)
    · exact (ne_of_gt (show 0 < u from hv)) (show u = 0 from hu)
  have he : (Iio (0 : ℝ) ∪ {0}) ∪ Ioi 0 = univ := by
    ext u
    simp only [mem_union, mem_Iio, mem_singleton_iff, mem_Ioi, mem_univ, iff_true]
    rcases lt_trichotomy u 0 with h | h | h <;> tauto
  have hz := scaledEnergyOn_union hb hT h₁
  have H' := scaledEnergyOn_union hb hT h₂
  rw [he, hz, spectral_neg_eq_pos] at H'
  simp only [scaledEnergyOn, preimage_univ, indicator_univ] at H'
  unfold scaledEnergyOn
  rw [H']
  ring

/-- The spectral asymptotic in the original width variable. -/
theorem weighted_spectral_asymptotic (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun lam : ℝ => (∑' ρ : Zeros, diagonalEnergy b (fun σ => coefficient lam (ordinate σ)) ρ) /
      (lam * (Real.log (1 / lam))^2)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h := (scaledEnergy_tendsto_one hRH hb).comp tendsto_inv_nhdsGT_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  have hTp : 0 < lam⁻¹ := inv_pos.mpr hlam
  change (∑' ρ : Zeros, scaledEnergyTerm b lam⁻¹ ρ) = _
  simp_rw [scaledEnergyTerm_eq hTp, one_div, inv_inv, tsum_div_const]

end GoldbachSpectrum
