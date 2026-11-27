import Goldbach.Moments

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace GoldbachConcrete

private theorem densityTerm_integral_lower {d u v : ℝ} {p : ℕ}
    (hd : 0 < d) (hu : 0 < u) (hp : p.Prime) (hop : Odd p)
    (hlo : (1 + d) * u ≤ p) (hhi : (p : ℝ) ≤ v) :
    Real.log (p : ℝ) / (1 + d) ≤ ∫ y in Icc u v, densityTerm d p y := by
  have hD : 0 < 1 + d := by linarith
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  let s := Ico ((p : ℝ) / (1 + d)) (p : ℝ)
  let g := s.indicator (fun _ : ℝ => Real.log (p : ℝ) / (d * p))
  have hs : s ⊆ Icc u v := by
    intro y hy
    have hlo' : u ≤ (p : ℝ) / (1 + d) := by
      apply (le_div_iff₀ hD).mpr
      simpa only [mul_comm] using hlo
    exact ⟨hlo'.trans hy.1, hy.2.le.trans hhi⟩
  have hgi : IntegrableOn g (Icc u v) := by
    exact (integrableOn_const (C := Real.log (p : ℝ) / (d * p))
      (s := Icc u v) (μ := volume) measure_Icc_lt_top.ne).indicator measurableSet_Ico
  have hmono : (∫ y in Icc u v, g y) ≤ ∫ y in Icc u v, densityTerm d p y := by
    apply integral_mono_ae hgi (integrableOn_densityTerm hd hu p)
    filter_upwards [ae_restrict_mem (μ := volume) (s := Icc u v) measurableSet_Icc] with y hy
    rw [densityTerm_eq_indicator hd]
    by_cases hys : y ∈ s
    · change s.indicator _ y ≤ s.indicator _ y
      rw [indicator_of_mem hys, indicator_of_mem hys, if_pos ⟨hp, hop⟩]
      exact div_le_div_of_nonneg_left hlog (mul_pos hd (hu.trans_le hy.1))
        (mul_le_mul_of_nonneg_left hys.2.le hd.le)
    · change s.indicator _ y ≤ s.indicator _ y
      rw [indicator_of_notMem hys, indicator_of_notMem hys]
  have hends : (p : ℝ) / (1 + d) ≤ p := by
    exact (div_le_iff₀ hD).mpr (by nlinarith [mul_nonneg hp0.le hd.le])
  have hvalue : (∫ y in Icc u v, g y) = Real.log (p : ℝ) / (1 + d) := by
    rw [show g = s.indicator (fun _ : ℝ => Real.log (p : ℝ) / (d * p)) from rfl]
    rw [integral_indicator (show MeasurableSet s from measurableSet_Ico),
      Measure.restrict_restrict (show MeasurableSet s from measurableSet_Ico),
      inter_eq_left.mpr hs, setIntegral_const]
    change volume.real (Ico ((p : ℝ) / (1 + d)) (p : ℝ)) *
      (Real.log (p : ℝ) / (d * p)) = _
    rw [Real.volume_real_Ico_of_le hends]
    field_simp [hd.ne', hp0.ne', hD.ne']
    ring
  exact hvalue ▸ hmono

/-- Every prime whose complete contribution interval lies in `[u,v]`
gives at least its logarithmic weight divided by `1+d`. -/
theorem integral_density_lower_chebyshev {d u v : ℝ} (hd : 0 < d)
    (hu : 2 ≤ u) (huv : (1 + d) * u ≤ v) :
    (Chebyshev.theta v - Chebyshev.theta ((1 + d) * u)) / (1 + d) ≤
      ∫ y in Icc u v, density d y := by
  classical
  have hD : 0 < 1 + d := by linarith
  have hu0 : 0 < u := by linarith
  have hdu : u ≤ (1 + d) * u := by nlinarith [mul_nonneg hd.le hu0.le]
  have hdu0 : 0 ≤ (1 + d) * u := (mul_pos hD hu0).le
  have hv0 : 0 ≤ v := hdu0.trans huv
  let hi := Nat.primesLE ⌊v⌋₊
  let lo := Nat.primesLE ⌊(1 + d) * u⌋₊
  let s := hi \ lo
  let N := ⌈(1 + d) * v⌉₊ + 1
  have hlo : lo ⊆ hi := Nat.primesLE_mono (Nat.floor_mono huv)
  have hs (p : ℕ) (hp : p ∈ s) :
      p.Prime ∧ (1 + d) * u < (p : ℝ) ∧ (p : ℝ) ≤ v := by
    have hmem := Finset.mem_sdiff.mp hp
    have hp' := Nat.mem_primesLE.mp hmem.1
    refine ⟨hp'.2, ?_, (Nat.le_floor_iff hv0).mp hp'.1⟩
    exact (Nat.floor_lt hdu0).mp (lt_of_not_ge fun h => hmem.2 (Nat.mem_primesLE.mpr ⟨h, hp'.2⟩))
  have hsN : s ⊆ Finset.range N := by
    intro p hp
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    have hvD : v ≤ (1 + d) * v := by nlinarith [mul_nonneg hd.le hv0]
    exact_mod_cast ((hs p hp).2.2.trans hvD).trans (Nat.le_ceil ((1 + d) * v))
  have hsum : ∑ p ∈ s, Real.log (p : ℝ) =
      Chebyshev.theta v - Chebyshev.theta ((1 + d) * u) := by
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    exact eq_sub_of_add_eq (Finset.sum_sdiff hlo)
  calc
    _ = ∑ p ∈ s, Real.log (p : ℝ) / (1 + d) := by rw [← Finset.sum_div, hsum]
    _ ≤ ∑ p ∈ s, ∫ y in Icc u v, densityTerm d p y := by
      apply Finset.sum_le_sum
      intro p hps
      obtain ⟨hp, hlow, hhigh⟩ := hs p hps
      have hp2 : p ≠ 2 := by
        intro he
        have htwo : (p : ℝ) = 2 := by exact_mod_cast he
        rw [htwo] at hlow
        exact (not_lt_of_ge (hu.trans hdu)) hlow
      exact densityTerm_integral_lower hd hu0 hp (hp.odd_of_ne_two hp2) hlow.le hhigh
    _ ≤ ∑ p ∈ Finset.range N, ∫ y in Icc u v, densityTerm d p y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsN
      intro p _ _
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem (μ := volume) (s := Icc u v) measurableSet_Icc] with y hy
      exact densityTerm_nonneg hd.le (hu0.trans_le hy.1).le p
    _ = _ := (integral_density_eq_sum hd hu0).symm


/-- Above 2 the concrete odd-prime count agrees exactly with the
difference of Mathlib's Chebyshev theta function. -/
theorem density_eq_theta_sub {d y : ℝ} (hd : 0 < d) (hy : 2 ≤ y) :
    density d y = (Chebyshev.theta ((1 + d) * y) - Chebyshev.theta y) / (d * y) := by
  classical
  have hy0 : 0 ≤ y := by linarith
  have hdy : y ≤ (1 + d) * y := by nlinarith [mul_nonneg hd.le hy0]
  have hdy0 := hy0.trans hdy
  let hi := Nat.primesLE ⌊(1 + d) * y⌋₊
  let lo := Nat.primesLE ⌊y⌋₊
  have hsub : lo ⊆ hi := Nat.primesLE_mono (Nat.floor_mono hdy)
  have hsum : (∑ p ∈ hi \ lo, Real.log (p : ℝ)) =
      Chebyshev.theta ((1 + d) * y) - Chebyshev.theta y := by
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    exact eq_sub_of_add_eq (Finset.sum_sdiff hsub)
  rw [density, ← hsum]
  congr 1
  let P := fun p : ℕ => Nat.Prime p ∧ Odd p ∧ y < (p : ℝ) ∧
    (p : ℝ) ≤ (1 + d) * y
  change (∑ p ∈ Finset.range (⌈(1 + d) * y⌉₊ + 1), if P p then Real.log (p : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
  constructor
  · rintro ⟨_, hp, _, hlo, hhi⟩
    refine ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hdy0).mpr hhi, hp⟩, ?_⟩
    intro hp'
    exact ((Nat.floor_lt hy0).mpr hlo).not_ge (Nat.mem_primesLE.mp hp').1
  · rintro ⟨hp', hlo⟩
    obtain ⟨hp_le, hp⟩ := Nat.mem_primesLE.mp hp'
    have hhi := (Nat.le_floor_iff hdy0).mp hp_le
    have hlo' : y < (p : ℝ) :=
      (Nat.floor_lt hy0).mp (lt_of_not_ge (fun h => hlo (Nat.mem_primesLE.mpr ⟨h, hp⟩)))
    have hp₂ : p ≠ 2 := by
      intro h
      have hpcast : (p : ℝ) = 2 := by exact_mod_cast h
      linarith
    refine ⟨Nat.lt_succ_of_le ?_, hp, hp.odd_of_ne_two hp₂, hlo', hhi⟩
    exact_mod_cast hhi.trans (Nat.le_ceil ((1 + d) * y))

end GoldbachConcrete
