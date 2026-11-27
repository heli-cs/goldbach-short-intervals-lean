import Goldbach.RowAsymptotic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open Filter MeasureTheory Set
open scoped Topology ContDiff FourierTransform SchwartzMap
noncomputable section

namespace GoldbachZeros

open Zeta23

/-- Convergence of the translated zero sums against a Schwartz test
in the ordinate variable. The angular-frequency normalization is exact. -/
theorem translatedAverage_schwartz_tendsto (hRH : RiemannHypothesis) (F : 𝓢(ℝ, ℂ)) :
    Tendsto (translatedAverage F) atTop
      (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, F u)) := by
  let C := -(2 * Real.pi)
  have hC : C ≠ 0 := (neg_ne_zero.mpr (by positivity : 0 < 2 * Real.pi).ne')
  let U : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 C hC)
  let F' := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ U F
  let k : 𝓢(ℝ, ℂ) := 𝓕⁻ F'
  have hFK (r : ℝ) : paperFT k (r : ℂ) = F r := by
    rw [paperFT_ofReal_eq_fourier, ← SchwartzMap.fourier_coe]
    change (𝓕 (𝓕⁻ F')) (-r / (2 * Real.pi)) = _
    rw [FourierTransform.fourier_fourierInv_eq]
    have h : U (-r / (2 * Real.pi)) = r := by
      simp only [U, ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0, C]
      field_simp [Real.pi_pos.ne']
    simp only [F', SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, h]
  have hk₀ : Integrable (k : ℝ → ℂ) := k.integrable
  have hk₁ : Integrable (deriv (k : ℝ → ℂ)) := (SchwartzMap.derivCLM ℂ ℂ k).integrable
  have hk₂ : Integrable (deriv (deriv (k : ℝ → ℂ))) :=
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ k)).integrable
  have hkF : Integrable (𝓕 (k : ℝ → ℂ)) := SchwartzMap.fourier_coe k ▸ (𝓕 k).integrable
  have h := translatedAverage_paperFT_tendsto hRH (k.smooth 2) hk₀ hk₁ hk₂
  have h0 := EF.paper_inversion k.continuous hk₀ hkF 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, hFK] at h0
  simpa only [hFK, h0] using h

/-- Finite half-open ordinate window on the subtype of nontrivial zeros. -/
def zeroWindow (r s : ℝ) : Finset Zeros := by
  classical
  exact (zetaZeroConfig.finite_window r s).toFinset.subtype (· ∈ zetaZeroConfig.carrier)

@[simp] theorem mem_zeroWindow {r s : ℝ} {ρ : Zeros} :
    ρ ∈ zeroWindow r s ↔ r < ordinate ρ ∧ ordinate ρ ≤ s := by
  classical
  rw [zeroWindow, Finset.mem_subtype, Set.Finite.mem_toFinset]
  exact and_iff_right ρ.property

theorem Ncount_eq_sum_zeroWindow (r s : ℝ) :
    (Ncount r s : ℝ) = ∑ ρ ∈ zeroWindow r s, multiplicity ρ := by
  classical
  unfold multiplicity
  have hfin : (zetaZeroConfig.window r s).Finite := zetaZeroConfig.finite_window r s
  rw [← zetaZeroConfig_N, ZeroConfig.N, finsum_mem_eq_finite_toFinset_sum _ hfin, zeroWindow,
    Finset.sum_subtype_of_mem (f := fun ρ : ℂ => (zetaZeroConfig.mult ρ : ℝ))]
  · push_cast
    rfl
  · intro x hx
    exact ((Set.Finite.mem_toFinset _).mp hx).1

/-- The weighted sum of a compactly supported test on a translated zero family. -/
theorem summable_translated_real_of_compact {f : ℝ → ℝ} (hf : HasCompactSupport f) (t : ℝ) :
    Summable (fun ρ : Zeros => multiplicity ρ * f (ordinate ρ - t)) := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  let W := zeroWindow (t - R - 1) (t + R)
  apply summable_of_ne_finset_zero (s := W)
  intro ρ hρ
  by_contra H
  have hF : f (ordinate ρ - t) ≠ 0 := right_ne_zero_of_mul H
  have h := hR (subset_tsupport f hF)
  have hb : |ordinate ρ - t| ≤ R := by simpa [Real.dist_eq] using h
  have h' := abs_le.mp hb
  apply hρ
  exact mem_zeroWindow.mpr ⟨by linarith [h'.1], by linarith [h'.2]⟩

/-- Convergence against a compact smooth real test in the ordinate variable. -/
theorem translated_test_tendsto (hRH : RiemannHypothesis) {f : ℝ → ℝ}
    (hfs : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Tendsto (fun t : ℝ => (∑' ρ : Zeros, multiplicity ρ * f (ordinate ρ - t)) / Real.log t)
      atTop (𝓝 ((∫ x : ℝ, f x) / (2 * Real.pi))) := by
  have hcomp : HasCompactSupport (fun x => (f x : ℂ)) := by
    have he : Function.support (fun x => (f x : ℂ)) = Function.support f := by
      ext x
      simp [Function.mem_support]
    unfold HasCompactSupport tsupport
    rw [he]
    exact hfc
  let F := hcomp.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hfs)
  have hF (u : ℝ) : F u = (f u : ℂ) := rfl
  have hI : (∫ x : ℝ, F x) = Complex.ofReal (∫ x : ℝ, f x) := by
    calc
      _ = ∫ x : ℝ, (f x : ℂ) := integral_congr_ae (Eventually.of_forall hF)
      _ = _ := integral_complex_ofReal
  have hlim : ((1 / (2 * Real.pi) : ℂ) * ∫ x : ℝ, F x).re =
      (∫ x : ℝ, f x) / (2 * Real.pi) := by
    have he : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
    rw [hI, he, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (translatedAverage_schwartz_tendsto hRH F)
  change Tendsto (fun t => (translatedAverage F t).re) atTop
    (𝓝 (((1 / (2 * Real.pi) : ℂ) * ∫ x : ℝ, F x).re)) at h
  rw [hlim] at h
  apply h.congr'
  filter_upwards with t
  unfold translatedAverage
  simp_rw [hF, ← Complex.ofReal_mul]
  rw [← Complex.ofReal_tsum, Complex.smul_re, Complex.ofReal_re, smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem bump_one_on_radius {z : ℝ} (g : ContDiffBump z) {x : ℝ}
    (h : |x - z| ≤ g.rIn) : g x = 1 := by
  apply g.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq] using h

private theorem bump_zero_outside_radius {z : ℝ} (g : ContDiffBump z) {x : ℝ}
    (h : g.rOut ≤ |x - z|) : g x = 0 :=
  g.zero_of_le_dist (by simpa only [Real.dist_eq] using h)

private theorem bump_integral_bounds {z : ℝ} (g : ContDiffBump z) :
    2 * g.rIn ≤ (∫ x : ℝ, g x) ∧ (∫ x : ℝ, g x) ≤ 2 * g.rOut := by
  let J (a : ℝ) := Icc (z - a) (z + a)
  have hint (a : ℝ) : Integrable ((J a).indicator (fun _ => (1 : ℝ))) := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const measure_Icc_lt_top.ne
  have hvol {a : ℝ} (ha : 0 ≤ a) : ∫ x, (J a).indicator (fun _ => (1 : ℝ)) x = 2 * a := by
    dsimp only [J]
    rw [integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, mul_one]
    ring
  have hg : Integrable (g : ℝ → ℝ) := g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  constructor
  · rw [← hvol g.rIn_pos.le]
    apply integral_mono (hint g.rIn) hg
    intro x
    by_cases hx : x ∈ J g.rIn
    · rw [Set.indicator_of_mem hx, bump_one_on_radius g]
      exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · rw [Set.indicator_of_notMem hx]
      exact g.nonneg
  · rw [← hvol g.rOut_pos.le]
    apply integral_mono hg (hint g.rOut)
    intro x
    by_cases hx : x ∈ J g.rOut
    · rw [Set.indicator_of_mem hx]
      exact g.le_one
    · rw [Set.indicator_of_notMem hx, bump_zero_outside_radius g]
      by_contra! h
      have h' := abs_lt.mp h
      exact hx ⟨by linarith [h'.1], by linarith [h'.2]⟩

/-- The fixed-width local density, including analytic multiplicities.
Smooth upper and lower tests remove both endpoint ambiguities. -/
theorem translated_window_count_tendsto (hRH : RiemannHypothesis) {r s : ℝ} (hrs : r < s) :
    Tendsto (fun t : ℝ => (Ncount (t + r) (t + s) : ℝ) / Real.log t)
      atTop (𝓝 ((s - r) / (2 * Real.pi))) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let z := (r + s) / 2
  let a := (s - r) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let δ := min (a / 2) (Real.pi * ε / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδa : δ ≤ a / 2 := min_le_left _ _
  have hδε : δ ≤ Real.pi * ε / 2 := min_le_right _ _
  let g : ContDiffBump z := ⟨a - δ, a, by linarith, by linarith⟩
  let h : ContDiffBump z := ⟨a, a + δ, ha, by linarith⟩
  let M := (s - r) / (2 * Real.pi)
  have hπ : 0 < 2 * Real.pi := by positivity
  have hlg := translated_test_tendsto hRH g.contDiff g.hasCompactSupport
  have huh := translated_test_tendsto hRH h.contDiff h.hasCompactSupport
  have hlow : M - ε < (∫ x : ℝ, g x) / (2 * Real.pi) := by
    apply (lt_div_iff₀ hπ).mpr
    have hg := (bump_integral_bounds g).1
    change 2 * (a - δ) ≤ _ at hg
    have he : M * (2 * Real.pi) = 2 * a := by dsimp [M, a]; field_simp [Real.pi_pos.ne']
    rw [sub_mul, he]
    nlinarith [mul_pos Real.pi_pos hε]
  have hhigh : (∫ x : ℝ, h x) / (2 * Real.pi) < M + ε := by
    apply (div_lt_iff₀ hπ).mpr
    have hh := (bump_integral_bounds h).2
    change _ ≤ 2 * (a + δ) at hh
    have he : M * (2 * Real.pi) = 2 * a := by dsimp [M, a]; field_simp [Real.pi_pos.ne']
    rw [add_mul, he]
    nlinarith [mul_pos Real.pi_pos hε]
  filter_upwards [hlg.eventually (lt_mem_nhds hlow), huh.eventually (gt_mem_nhds hhigh),
    eventually_gt_atTop (1 : ℝ)] with t hgt hht ht
  let W := zeroWindow (t+r) (t+s)
  let I := fun ρ : Zeros => if ρ ∈ W then multiplicity ρ else 0
  have hi : Summable I := summable_of_ne_finset_zero (s := W) fun ρ hρ => by simp only [I, if_neg hρ]
  have hI : (∑' ρ : Zeros, I ρ) = (Ncount (t+r) (t+s) : ℝ) := by
    rw [tsum_eq_sum (s := W) (fun ρ hρ => by simp only [I, if_neg hρ]), Ncount_eq_sum_zeroWindow]
    exact Finset.sum_congr rfl (fun ρ hρ => by
      change ρ ∈ W at hρ
      simp only [I, if_pos hρ])
  have hgl : (∑' ρ : Zeros, multiplicity ρ * g (ordinate ρ - t)) ≤ ∑' ρ : Zeros, I ρ := by
    apply (summable_translated_real_of_compact g.hasCompactSupport t).tsum_le_tsum _ hi
    intro ρ
    by_cases hm : ρ ∈ W
    · simp only [I, if_pos hm]
      exact mul_le_of_le_one_right (multiplicity_nonneg ρ) g.le_one
    · have hn : ¬(t + r < ordinate ρ ∧ ordinate ρ ≤ t + s) :=
        fun hw => hm (mem_zeroWindow.mpr hw)
      have hz : g (ordinate ρ - t) = 0 := by
        apply bump_zero_outside_radius g
        change a ≤ |ordinate ρ - t - z|
        by_contra! H
        have H' := abs_lt.mp H
        exact hn ⟨by dsimp [a,z] at H'; linarith [H'.1],
          by dsimp [a,z] at H'; linarith [H'.2]⟩
      simp only [I, if_neg hm, hz, mul_zero, le_rfl]
  have hhu : (∑' ρ : Zeros, I ρ) ≤ ∑' ρ : Zeros, multiplicity ρ * h (ordinate ρ - t) := by
    apply hi.tsum_le_tsum _ (summable_translated_real_of_compact h.hasCompactSupport t)
    intro ρ
    by_cases hm : ρ ∈ W
    · have hw := mem_zeroWindow.mp hm
      have ho : h (ordinate ρ - t) = 1 := by
        apply bump_one_on_radius h
        change |ordinate ρ - t - z| ≤ a
        apply abs_le.mpr
        dsimp [a,z]
        exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
      simp only [I, if_pos hm, ho, mul_one, le_rfl]
    · simpa only [I, if_neg hm] using
        mul_nonneg (multiplicity_nonneg ρ) (h.nonneg' (ordinate ρ - t))
  rw [hI] at hgl hhu
  have hlog := (Real.log_pos ht).le
  have hl := div_le_div_of_nonneg_right hgl hlog
  have hu := div_le_div_of_nonneg_right hhu hlog
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- A single summable envelope dominates Gaussian tails on any collection
of the translated unit cells, uniformly in the centre after division by
the logarithmic count bound. -/
theorem gaussian_cell_tail_bound {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (E : Set ℤ),
      let g := fun ρ : Zeros => E.indicator (fun _ =>
        multiplicity ρ * GoldbachGaussian.kernel b (t - ordinate ρ)) (unitCell t ρ)
      Summable g ∧ (∑' ρ, g ρ) ≤
        C * Real.log (|t| + 3) * ∑' n, E.indicator unitEnvelope n := by
  obtain ⟨C, hC, hc⟩ := translated_cell_tsum_bound
  let D := Real.sqrt (Real.pi / b) * max 1 (4 * b)
  have hD : 0 < D := mul_pos (Real.sqrt_pos.mpr (div_pos Real.pi_pos hb))
    (zero_lt_one.trans_le (le_max_left _ _))
  refine ⟨D * C, mul_pos hD hC, fun t E => ?_⟩
  let g := fun ρ : Zeros => E.indicator (fun _ =>
    multiplicity ρ * GoldbachGaussian.kernel b (t - ordinate ρ)) (unitCell t ρ)
  let q := fun ρ : Zeros => E.indicator (fun _ =>
    multiplicity ρ / (1 + (ordinate ρ - t)^2)) (unitCell t ρ)
  have hq : Summable q ∧ (∑' ρ, q ρ) ≤
      C * Real.log (|t| + 3) * ∑' n, E.indicator unitEnvelope n := hc t E
  have hg (ρ : Zeros) : 0 ≤ g ρ :=
    Set.indicator_nonneg (fun _ _ => mul_nonneg (multiplicity_nonneg ρ)
      (GoldbachGaussian.kernel_nonneg _ _)) _
  have hle (ρ : Zeros) : g ρ ≤ D * q ρ := by
    by_cases hm : unitCell t ρ ∈ E
    · simp only [g, q, Set.indicator_of_mem hm]
      have h := GoldbachGaussian.kernel_le_inv_sq hb (ordinate ρ - t)
      rw [show t - ordinate ρ = -(ordinate ρ - t) by ring, GoldbachGaussian.kernel_even]
      exact (mul_le_mul_of_nonneg_left h (multiplicity_nonneg ρ)).trans_eq (by
        change multiplicity ρ * (D / (1 + (ordinate ρ - t)^2)) = _
        ring)
    · simp only [g, q, Set.indicator_of_notMem hm, mul_zero, le_rfl]
  have hs := (hq.1.mul_left D).of_nonneg_of_le hg hle
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' ρ, D * q ρ := hs.tsum_le_tsum hle (hq.1.mul_left D)
    _ = D * ∑' ρ, q ρ := tsum_mul_left
    _ ≤ _ := (mul_le_mul_of_nonneg_left hq.2 hD.le).trans_eq (by ring)

end GoldbachZeros
