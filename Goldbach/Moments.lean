import Goldbach.Concrete

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace GoldbachConcrete

/-- The contribution of one odd prime to the relative-interval density. -/
def densityTerm (d : ℝ) (p : ℕ) (y : ℝ) : ℝ :=
  primeWeight d y p / (d * y)

theorem densityTerm_zero_of_upper_lt {d y : ℝ} {p : ℕ}
    (h : (1 + d) * y < p) : densityTerm d p y = 0 := by
  have hn : ¬ ((p : ℝ) ≤ (1 + d) * y) := not_le_of_gt h
  simp [densityTerm, primeWeight, hn]

theorem densityTerm_eq_indicator {d : ℝ} (hd : 0 < d) (p : ℕ) :
    densityTerm d p =
      (Ico ((p : ℝ) / (1 + d)) (p : ℝ)).indicator
        (fun y => (if Nat.Prime p ∧ Odd p then Real.log (p : ℝ) else 0) / (d * y)) := by
  classical
  funext y
  have hpos : 0 < 1 + d := by linarith
  by_cases hp : Nat.Prime p ∧ Odd p
  · by_cases hy : y ∈ Ico ((p : ℝ) / (1 + d)) (p : ℝ)
    · have hu : (p : ℝ) ≤ (1 + d) * y := by
        rw [mul_comm]
        exact (div_le_iff₀ hpos).mp hy.1
      simp [densityTerm, primeWeight, hp.1, hp.2, hy, hy.2, hu]
    · have hup : ¬ (y < (p : ℝ) ∧ (p : ℝ) ≤ (1 + d) * y) := by
        intro h
        apply hy
        refine ⟨(div_le_iff₀ hpos).mpr ?_, h.1⟩
        simpa only [mul_comm] using h.2
      simp [densityTerm, primeWeight, hp.1, hp.2, hy, hup]
  · have hn : ¬ (Nat.Prime p ∧ Odd p ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ (1 + d) * y) :=
      fun h => hp ⟨h.1, h.2.1⟩
    simp [densityTerm, primeWeight, hp, hn]

theorem density_eq_sum_of_le {d y : ℝ} {N : ℕ}
    (hN : ⌈(1 + d) * y⌉₊ + 1 ≤ N) :
    density d y = ∑ p ∈ Finset.range N, densityTerm d p y := by
  rw [density, Finset.sum_div]
  change (∑ p ∈ Finset.range (⌈(1 + d) * y⌉₊ + 1), densityTerm d p y) = _
  apply Finset.sum_subset (Finset.range_mono hN)
  intro p _ hp
  have hle : ⌈(1 + d) * y⌉₊ + 1 ≤ p := not_lt.mp (mt Finset.mem_range.mpr hp)
  apply densityTerm_zero_of_upper_lt
  exact (Nat.le_ceil _).trans_lt (by exact_mod_cast (Nat.lt_of_succ_le hle))

theorem measurable_densityTerm {d : ℝ} (hd : 0 < d) (p : ℕ) :
    Measurable (densityTerm d p) := by
  classical
  rw [densityTerm_eq_indicator hd]
  exact (measurable_const.div (measurable_const.mul measurable_id)).indicator measurableSet_Ico

theorem measurable_density {d : ℝ} (hd : 0 < d) : Measurable (density d) := by
  have h : density d = fun y => ∑' p, densityTerm d p y := by
    funext y
    rw [density_eq_sum_of_le (N := ⌈(1 + d) * y⌉₊ + 1) le_rfl]
    symm
    apply tsum_eq_sum
    intro p hp
    have hle : ⌈(1 + d) * y⌉₊ + 1 ≤ p := not_lt.mp (mt Finset.mem_range.mpr hp)
    apply densityTerm_zero_of_upper_lt
    exact (Nat.le_ceil _).trans_lt (by exact_mod_cast (Nat.lt_of_succ_le hle))
  rw [h]
  exact Measurable.tsum (measurable_densityTerm hd)

theorem densityTerm_nonneg {d y : ℝ} (hd : 0 ≤ d) (hy : 0 ≤ y) (p : ℕ) :
    0 ≤ densityTerm d p y := by
  unfold densityTerm primeWeight
  apply div_nonneg _ (mul_nonneg hd hy)
  split
  · rename_i hp
    apply Real.log_nonneg
    exact_mod_cast hp.1.one_lt.le
  · exact le_rfl

theorem integrableOn_densityTerm {d u v : ℝ} (hd : 0 < d) (hu : 0 < u) (p : ℕ) :
    IntegrableOn (densityTerm d p) (Icc u v) := by
  classical
  rw [densityTerm_eq_indicator hd]
  apply Integrable.indicator _ measurableSet_Ico
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact continuousOn_const.div (continuousOn_const.mul continuousOn_id)
    (fun y hy => (mul_pos hd (hu.trans_le hy.1)).ne')

theorem integral_density_eq_sum {d u v : ℝ} (hd : 0 < d) (hu : 0 < u) :
    (∫ y in Icc u v, density d y) =
      ∑ p ∈ Finset.range (⌈(1 + d) * v⌉₊ + 1), ∫ y in Icc u v, densityTerm d p y := by
  calc
    (∫ y in Icc u v, density d y) =
        ∫ y in Icc u v, ∑ p ∈ Finset.range (⌈(1 + d) * v⌉₊ + 1), densityTerm d p y := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      apply density_eq_sum_of_le
      exact Nat.add_le_add_right (Nat.ceil_le_ceil
        (mul_le_mul_of_nonneg_left hy.2 (by linarith))) 1
    _ = _ := integral_finsetSum _ (fun p _ => integrableOn_densityTerm hd hu p)

theorem density_boundedOn_Icc {d u v : ℝ} (hd : 0 < d) (hu : 0 < u) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Icc u v, 0 ≤ density d y ∧ density d y ≤ M := by
  let N : ℕ := ⌈(1 + d) * v⌉₊ + 1
  have hlog (p : ℕ) : 0 ≤ Real.log (p : ℝ) := by
    cases p with
    | zero => simp
    | succ p => exact Real.log_nonneg (by exact_mod_cast Nat.succ_pos p)
  refine ⟨∑ p ∈ Finset.range N, Real.log (p : ℝ) / (d * u), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun p _ => div_nonneg (hlog p) (mul_pos hd hu).le)
  · intro y hy
    have hypos : 0 < y := hu.trans_le hy.1
    rw [density_eq_sum_of_le (N := N)
      (Nat.add_le_add_right (Nat.ceil_le_ceil (mul_le_mul_of_nonneg_left hy.2 (by linarith))) 1)]
    refine ⟨Finset.sum_nonneg (fun p _ => densityTerm_nonneg hd.le hypos.le p), ?_⟩
    apply Finset.sum_le_sum
    intro p _
    unfold densityTerm primeWeight
    split
    · exact div_le_div_of_nonneg_left (hlog p) (mul_pos hd hu)
        (mul_le_mul_of_nonneg_left hy.1 hd.le)
    · simp only [zero_div]
      exact div_nonneg (hlog p) (mul_pos hd hu).le

theorem integrableOn_density {d u v : ℝ} (hd : 0 < d) (hu : 0 < u) :
    IntegrableOn (density d) (Icc u v) := by
  obtain ⟨M, _, hM⟩ := density_boundedOn_Icc (v := v) hd hu
  have hi : IntegrableOn (fun _ : ℝ => M) (Icc u v) := integrableOn_const measure_Icc_lt_top.ne
  apply hi.mono' (measurable_density hd).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) (s := Icc u v) measurableSet_Icc] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (hM y hy).1]
  exact (hM y hy).2

theorem integrableOn_density_error {d u v : ℝ} (hd : 0 < d) (hu : 0 < u) :
    IntegrableOn (fun y => (density d y - 1)^2) (Icc u v) := by
  obtain ⟨M, hM0, hM⟩ := density_boundedOn_Icc (v := v) hd hu
  have hi : IntegrableOn (fun _ : ℝ => (M + 1)^2) (Icc u v) := integrableOn_const measure_Icc_lt_top.ne
  apply hi.mono' (((measurable_density hd).sub measurable_const).pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) (s := Icc u v) measurableSet_Icc] with y hy
  obtain ⟨hFy, hFM⟩ := hM y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change (density d y - 1)^2 ≤ (M + 1)^2
  exact sq_le_sq.mpr (by rw [abs_of_nonneg (by linarith : 0 ≤ M + 1)]; exact abs_le.mpr (by constructor <;> linarith))

theorem measurePreserving_reflect_region (c x : ℝ) :
    MeasurePreserving (fun y : ℝ => x - y) (regionMeasure c x) (regionMeasure c x) := by
  have hpre : (fun y : ℝ => x - y) ⁻¹' region c x = region c x := by
    ext y
    simp only [region, mem_preimage, mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simpa only [regionMeasure, hpre] using
    (volume.measurePreserving_sub_left x).restrict_preimage
      (s := region c x) measurableSet_Icc

theorem integral_reflect_region (c x : ℝ) (f : ℝ → ℝ) :
    (∫ y, f (x - y) ∂regionMeasure c x) = ∫ y, f y ∂regionMeasure c x := by
  have he : MeasurableEmbedding (fun y : ℝ => x - y) :=
    (Homeomorph.subLeft x).measurableEmbedding
  exact (measurePreserving_reflect_region c x).integral_comp he f

theorem firstIntegrand_integral {c x : ℝ} (hax : 0 < trim c * x)
    (hd : 0 < relativeWidth c x) (horder : trim c * x ≤ (1 - trim c) * x) :
    Integrable (firstIntegrand c x) (regionMeasure c x) ∧
    (∫ y, firstIntegrand c x y ∂regionMeasure c x) =
      4 * (∫ y, density (relativeWidth c x) y ∂regionMeasure c x) -
        2 * ((1 - 2 * trim c) * x) := by
  let μ := regionMeasure c x
  let F := density (relativeWidth c x)
  have hF : Integrable F μ := integrableOn_density hd hax
  have hR : Integrable (fun y => F (x - y)) μ :=
    (measurePreserving_reflect_region c x).integrable_comp_of_integrable hF
  have hC : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrableOn_const measure_Icc_lt_top.ne
  have hsum : Integrable (fun y => F y + F (x - y)) μ := hF.add hR
  refine ⟨((hF.add hR).sub hC).const_mul 2, ?_⟩
  change (∫ y, 2 * (F y + F (x - y) - 1) ∂μ) = _
  rw [integral_const_mul, integral_sub hsum hC, integral_add hF hR,
    integral_reflect_region]
  have hmass : (∫ _ : ℝ, (1 : ℝ) ∂μ) = (1 - 2 * trim c) * x := by
    change (∫ _ : ℝ in region c x, (1 : ℝ)) = _
    rw [setIntegral_const, region, Real.volume_real_Icc_of_le horder, smul_eq_mul, mul_one]
    ring
  rw [hmass]
  change _ = 4 * (∫ y, F y ∂μ) - _
  ring

theorem errorIntegrand_integral {c x : ℝ} (hax : 0 < trim c * x)
    (hd : 0 < relativeWidth c x) :
    Integrable (errorIntegrand c x) (regionMeasure c x) ∧
    (∫ y, errorIntegrand c x y ∂regionMeasure c x) =
      2 * (∫ y, (density (relativeWidth c x) y - 1)^2 ∂regionMeasure c x) := by
  let G := fun y => (density (relativeWidth c x) y - 1)^2
  have hG : Integrable G (regionMeasure c x) := integrableOn_density_error hd hax
  have hR : Integrable (fun y => G (x - y)) (regionMeasure c x) :=
    (measurePreserving_reflect_region c x).integrable_comp_of_integrable hG
  refine ⟨hG.add hR, ?_⟩
  change (∫ y, G y + G (x - y) ∂regionMeasure c x) = _
  rw [integral_add hG hR, integral_reflect_region]
  change _ = 2 * (∫ y, G y ∂regionMeasure c x)
  ring

end GoldbachConcrete
