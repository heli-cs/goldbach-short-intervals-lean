import Goldbach.PositiveWeil
import Goldbach.SmoothBox
import Goldbach.WeightedLimit
import Goldbach.SpectrumEnergy

open Filter MeasureTheory Set
open scoped BigOperators Topology
noncomputable section

namespace GoldbachSpectrum

open GoldbachGaussian GoldbachZeros Zeta23 GoldbachArithmetic

def sharpCoefficient (lam : ℝ) (ρ : Zeros) : ℂ := coefficient lam (ordinate ρ)

def smoothedCoefficient (lam : ℝ) (n : ℕ) (ρ : Zeros) : ℂ :=
  mollifierMultiplier n (ordinate ρ) * sharpCoefficient lam ρ

private def smoothedSum (lam : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  ∑' ρ : Zeros, (multiplicity ρ : ℂ) * smoothedCoefficient lam n ρ * wave (ordinate ρ) u

/-- The logarithmic spectral value, including the trivial-zero correction. -/
def sharpSpectralValue (lam u : ℝ) : ℝ :=
  Real.exp (-u / 2) * (Real.exp (u + lam) - Real.exp u +
      (trivialZeroTerm (Real.exp (u + lam)) - trivialZeroTerm (Real.exp u)) -
    (Chebyshev.psi (Real.exp (u + lam)) - Chebyshev.psi (Real.exp u)))

private theorem sharpSpectralValue_measurable (lam : ℝ) : Measurable (sharpSpectralValue lam) := by
  have hψ := Chebyshev.psi_mono.measurable
  have hg : Measurable trivialZeroTerm := by unfold trivialZeroTerm; fun_prop
  have h₁ : Measurable (fun u : ℝ => Real.exp (u + lam)) := by fun_prop
  have h₂ := Real.continuous_exp.measurable
  exact (by fun_prop : Measurable (fun u : ℝ => Real.exp (-u / 2))).mul
    (((h₁.sub h₂).add ((hg.comp h₁).sub (hg.comp h₂))).sub ((hψ.comp h₁).sub (hψ.comp h₂)))

private def shiftedBox (lam u : ℝ) (n : ℕ) : ℝ → ℂ := fun v => smoothLogBox lam n (v - u)

private theorem shiftedBox_contDiff (lam u : ℝ) (n : ℕ) : ContDiff ℝ 2 (shiftedBox lam u n) :=
  (smoothLogBox_contDiff lam n).comp (by fun_prop)

private theorem shiftedBox_compact (lam u : ℝ) (n : ℕ) : HasCompactSupport (shiftedBox lam u n) :=
  (smoothLogBox_hasCompactSupport lam n).comp_homeomorph (Homeomorph.subRight u)

private theorem shiftedBox_transform {lam : ℝ} (hlam : 0 ≤ lam) (u : ℝ) (n : ℕ) (ρ : Zeros) :
    (multiplicity ρ : ℂ) * paperFT (shiftedBox lam u n) (ordinate ρ) =
      (multiplicity ρ : ℂ) * smoothedCoefficient lam n ρ * wave (ordinate ρ) u := by
  unfold shiftedBox
  rw [paperFT_shift, paperFT_smoothLogBox hlam]
  have hw : Complex.exp (Complex.I * (ordinate ρ : ℂ) * (u : ℂ)) = wave (ordinate ρ) u := by
    unfold wave
    congr 1
    push_cast
    ring
  rw [hw]
  unfold smoothedCoefficient sharpCoefficient
  ring

private theorem smoothedSum_hasSum (hRH : RiemannHypothesis) {lam : ℝ} (hlam : 0 ≤ lam)
    (n : ℕ) (u : ℝ) :
    HasSum (fun ρ : Zeros => (multiplicity ρ : ℂ) * smoothedCoefficient lam n ρ *
      wave (ordinate ρ) u) (smoothedSum lam n u) := by
  have h := (weil_explicit_on_line hRH (shiftedBox lam u n)
    (shiftedBox_contDiff lam u n) (shiftedBox_compact lam u n)).1
  simp_rw [shiftedBox_transform hlam] at h
  exact h.hasSum

private theorem smoothedSum_measurable (hRH : RiemannHypothesis) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) :
    Measurable (smoothedSum lam n) := by
  apply measurable_of_tendsto_metrizable
    (fun j : ℕ => (continuous_partialSum (smoothedCoefficient lam n) (j : ℝ)).measurable)
  apply tendsto_pi_nhds.mpr
  intro u
  exact (partialSum_tendsto_of_hasSum _ _ _ (smoothedSum_hasSum hRH hlam n u)).comp
    tendsto_natCast_atTop_atTop

theorem sqrt_exp_eq (v : ℝ) : Real.sqrt (Real.exp v) = Real.exp (v / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _)).mpr
  rw [← Real.exp_add]
  congr 1
  ring

private theorem primeWindow_eq {u lam B : ℝ} (hlam : 0 < lam) (hB : u + lam ≤ B) :
    (∑ n ∈ Finset.Ioc 0 ⌊Real.exp B⌋₊,
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * logBox lam (Real.log n - u)) =
      (Real.exp (-u / 2) *
        (Chebyshev.psi (Real.exp (u + lam)) - Chebyshev.psi (Real.exp u)) : ℝ) := by
  classical
  let S := Finset.Ioc 0 ⌊Real.exp B⌋₊
  let P := Finset.Ioc 0 ⌊Real.exp u⌋₊
  let Q := Finset.Ioc 0 ⌊Real.exp (u + lam)⌋₊
  let A := fun n : ℕ => u < Real.log n ∧ Real.log n ≤ u + lam
  have hQ : Q ⊆ S := Finset.Ioc_subset_Ioc_right (Nat.floor_mono (Real.exp_le_exp.mpr hB))
  have hP : P ⊆ Q := Finset.Ioc_subset_Ioc_right
    (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith)))
  have hfilter : S.filter A = Q \ P := by
    ext n
    rw [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hS, hA⟩
      have hn : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hS).1
      refine ⟨Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hS).1, ?_⟩, ?_⟩
      · exact (Nat.le_floor_iff (Real.exp_pos (u + lam)).le).mpr
          ((Real.log_le_iff_le_exp hn).mp hA.2)
      · intro hnP
        exact (not_le_of_gt hA.1) ((Real.log_le_iff_le_exp hn).mpr
          ((Nat.le_floor_iff (Real.exp_pos u).le).mp (Finset.mem_Ioc.mp hnP).2))
    · rintro ⟨hnQ, hnP⟩
      have hn₀ := (Finset.mem_Ioc.mp hnQ).1
      have hn : (0 : ℝ) < n := by exact_mod_cast hn₀
      refine ⟨hQ hnQ, lt_of_not_ge fun h => hnP (Finset.mem_Ioc.mpr ⟨hn₀, ?_⟩), ?_⟩
      · exact (Nat.le_floor_iff (Real.exp_pos u).le).mpr ((Real.log_le_iff_le_exp hn).mp h)
      · exact (Real.log_le_iff_le_exp hn).mpr
          ((Nat.le_floor_iff (Real.exp_pos (u + lam)).le).mp (Finset.mem_Ioc.mp hnQ).2)
  have hterm (n : ℕ) (hnS : n ∈ S) :
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * logBox lam (Real.log n - u) =
      if A n then (Real.exp (-u / 2) * ArithmeticFunction.vonMangoldt n : ℝ) else 0 := by
    have hn : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hnS).1
    have hA : Real.log n - u ∈ Ioc 0 lam ↔ A n := by
      simp only [A, mem_Ioc, lt_sub_iff_add_lt, sub_le_iff_le_add, zero_add, add_comm lam u]
    by_cases h : A n
    · rw [if_pos h, logBox, indicator_of_mem (hA.mpr h), ← Complex.ofReal_mul]
      apply congrArg Complex.ofReal
      have he : Real.exp ((Real.log n - u) / 2) = Real.sqrt n * Real.exp (-u / 2) := by
        rw [show (Real.log n - u) / 2 = Real.log n / 2 + -u / 2 by ring,
          Real.exp_add, ← sqrt_exp_eq, Real.exp_log hn]
      rw [he, ← mul_assoc, div_mul_cancel₀ _ (Real.sqrt_pos.mpr hn).ne', mul_comm]
    · rw [if_neg h, logBox, indicator_of_notMem (hA.not.mpr h), mul_zero, Complex.ofReal_zero]
  have hreal :
      (∑ n ∈ Q \ P, Real.exp (-u / 2) * ArithmeticFunction.vonMangoldt n) =
        Real.exp (-u / 2) * (Chebyshev.psi (Real.exp (u + lam)) - Chebyshev.psi (Real.exp u)) := by
    rw [← Finset.mul_sum, Chebyshev.psi, Chebyshev.psi]
    congr 1
    exact eq_sub_of_add_eq (Finset.sum_sdiff hP)
  calc
    _ = (((∑ n ∈ S, if A n then Real.exp (-u / 2) * ArithmeticFunction.vonMangoldt n else 0) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl hterm
    _ = (((∑ n ∈ Q \ P, Real.exp (-u / 2) * ArithmeticFunction.vonMangoldt n) : ℝ) : ℂ) :=
      congrArg Complex.ofReal (by rw [← Finset.sum_filter, hfilter])
    _ = _ := congrArg Complex.ofReal hreal

private theorem sharpMoment_limit {u lam : ℝ} (hu : 0 < u) (hlam : 0 < lam) :
    Tendsto (fun n => ∫ v in Icc (u / 2) (u + lam + 1),
      shiftedBox lam u n v * (positiveWeilKernel v : ℂ)) atTop
      (𝓝 ((Real.exp (-u / 2) * (Real.exp (u + lam) - Real.exp u +
        (trivialZeroTerm (Real.exp (u + lam)) - trivialZeroTerm (Real.exp u))) : ℝ) : ℂ)) := by
  let J := Icc (u / 2) (u + lam + 1)
  have hc : ContinuousOn positiveWeilKernel J := continuousOn_positiveWeilKernel (by linarith)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have h :
      Tendsto (fun n => ∫ v in J, shiftedBox lam u n v * (positiveWeilKernel v : ℂ)) atTop
        (𝓝 (∫ v in J, logBox lam (v - u) * (positiveWeilKernel v : ℂ))) := by
    apply tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict J)
      (fun _ => Real.exp (lam / 2) * M)
    · apply Eventually.of_forall
      intro n
      exact ((shiftedBox_contDiff lam u n).continuous.aestronglyMeasurable).mul
        ((Complex.continuous_ofReal.comp_continuousOn hc).aestronglyMeasurable measurableSet_Icc)
    · apply Eventually.of_forall
      intro n
      filter_upwards [ae_restrict_mem (μ := volume) (s := J) measurableSet_Icc] with v hv
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul (smoothLogBox_norm_le lam n (v - u)) (hM v hv) (norm_nonneg _)
        (Real.exp_pos _).le
    · exact integrable_const _
    · have h₀ : ∀ᵐ v : ℝ ∂volume, v ≠ u := ae_iff.mpr (by simp)
      have h₁ : ∀ᵐ v : ℝ ∂volume, v ≠ u + lam := ae_iff.mpr (by simp)
      filter_upwards [ae_restrict_of_ae h₀, ae_restrict_of_ae h₁] with v hv₀ hv₁
      exact (smoothLogBox_tendsto hlam (sub_ne_zero.mpr hv₀)
        (fun h => hv₁ (by linarith))).mul_const _
  have he := sharpWeilMoment (a := u / 2) (B := u + lam + 1)
    (by linarith : 0 < u / 2) (by linarith : u / 2 ≤ u) hlam (by linarith : u + lam ≤ u + lam + 1)
  rw [show (∫ v in J, logBox lam (v - u) * (positiveWeilKernel v : ℂ)) = _ from he] at h
  exact h

/-- The smoothed explicit formula tends to the sharp Chebyshev expression
at every positive log-coordinate away from the two integer endpoints. -/
theorem smoothedSum_tendsto_sharp (hRH : RiemannHypothesis) {u lam : ℝ}
    (hu : 0 < u) (hlam : 0 < lam) (h₀ : ∀ n : ℕ, u ≠ Real.log n)
    (h₁ : ∀ n : ℕ, u + lam ≠ Real.log n) :
    Tendsto (fun n => smoothedSum lam n u) atTop (𝓝 (sharpSpectralValue lam u : ℂ)) := by
  let B := u + lam + 1
  let S := Finset.Ioc 0 ⌊Real.exp B⌋₊
  let c (n : ℕ) : ℂ := ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
  have hP : Tendsto (fun j => ∑ n ∈ S, c n * shiftedBox lam u j (Real.log n)) atTop
      (𝓝 (∑ n ∈ S, c n * logBox lam (Real.log n - u))) := by
    apply tendsto_finsetSum
    intro n _
    exact (smoothLogBox_tendsto hlam (sub_ne_zero.mpr (h₀ n).symm)
      (fun h => h₁ n (by linarith))).const_mul _
  rw [show (∑ n ∈ S, c n * logBox lam (Real.log n - u)) = _ from
    primeWindow_eq hlam (B := B) (by dsimp [B]; linarith)] at hP
  have hlim := (sharpMoment_limit hu hlam).sub hP
  rw [← Complex.ofReal_sub] at hlim
  unfold sharpSpectralValue
  have he : (fun n : ℕ =>
      (∫ v in Icc (u / 2) B, shiftedBox lam u n v * (positiveWeilKernel v : ℂ)) -
        ∑ j ∈ S, c j * shiftedBox lam u n (Real.log j)) =ᶠ[atTop]
        (fun n => smoothedSum lam n u) := by
    filter_upwards [eventual_mollifier_radius_lt (show 0 < u / 2 by linarith)] with n hn
    have hBelow (v : ℝ) (hv : v ≤ u / 2) : shiftedBox lam u n v = 0 :=
      smoothLogBox_zero_outside lam n (v - u) (Or.inl (by linarith))
    have hAbove (v : ℝ) (hv : B < v) : shiftedBox lam u n v = 0 :=
      smoothLogBox_zero_outside lam n (v - u)
        (Or.inr (by dsimp [B] at hv; linarith [mollifier_radius_le_one n]))
    symm
    unfold smoothedSum
    simp_rw [← shiftedBox_transform hlam.le]
    exact smooth_vonMangoldt_positive hRH (shiftedBox_contDiff lam u n) (shiftedBox_compact lam u n)
      (by linarith : 0 < u / 2) (by dsimp [B]; linarith : u / 2 ≤ B) hBelow hAbove
  simpa only [mul_sub] using hlim.congr' he

private theorem ae_logWindow_regular (lam : ℝ) :
    ∀ᵐ u : ℝ ∂volume, (∀ n : ℕ, u ≠ Real.log n) ∧ (∀ n : ℕ, u + lam ≠ Real.log n) := by
  have h₁ : ∀ᵐ u : ℝ ∂volume, u ∉ range (fun n : ℕ => Real.log n) :=
    ae_iff.mpr (by
      simp only [not_not, ofPred_mem_eq]
      exact (countable_range _).measure_zero (μ := (volume : Measure ℝ)))
  have h₂ : ∀ᵐ u : ℝ ∂volume, u ∉ range (fun n : ℕ => Real.log n - lam) :=
    ae_iff.mpr (by
      simp only [not_not, ofPred_mem_eq]
      exact (countable_range _).measure_zero (μ := (volume : Measure ℝ)))
  filter_upwards [h₁, h₂] with u hu₁ hu₂
  exact ⟨fun n hn => hu₁ ⟨n, hn.symm⟩, fun n hn => hu₂ ⟨n, by linarith⟩⟩

/-- Identification in local Gaussian weighted mean square of the limit
of the symmetric sharp zero sums. The diagonal tail retains coefficient one. -/
theorem local_sharp_spectral_tail (hRH : RiemannHypothesis) {b lam : ℝ}
    (hb : 0 < b) (hlam : 0 < lam) (hlam₁ : lam ≤ 1) (z : ℝ) (J : Set ℝ)
    (hJ : MeasurableSet J) (hpos : J ⊆ Ioi 0) (T : ℝ) :
    IntegrableOn (fun u => weight b (u - z) *
      ‖(sharpSpectralValue lam u : ℂ) - partialSum (sharpCoefficient lam) T u‖^2) J ∧
    (∫ u in J, weight b (u - z) *
      ‖(sharpSpectralValue lam u : ℂ) - partialSum (sharpCoefficient lam) T u‖^2) ≤
      (∑' ρ : Zeros, diagonalEnergy b (sharpCoefficient lam) ρ) -
        ∑ ρ ∈ zerosUpTo T, diagonalEnergy b (sharpCoefficient lam) ρ := by
  refine local_weighted_spectral_tail hb z J (sharpCoefficient lam) (smoothedCoefficient lam)
    (smoothedSum lam) (fun u => (sharpSpectralValue lam u : ℂ))
    (diagonalEnergy_summable hb hlam.le hlam₁) ?_ ?_ (smoothedSum_hasSum hRH hlam.le)
    (smoothedSum_measurable hRH hlam.le)
    (Complex.continuous_ofReal.measurable.comp (sharpSpectralValue_measurable lam)) ?_ T
  · intro n ρ
    rw [smoothedCoefficient, norm_mul]
    exact (mul_le_mul_of_nonneg_right (mollifierMultiplier_norm_le n (ordinate ρ)) (norm_nonneg _)).trans_eq
      (one_mul _)
  · intro ρ
    simpa only [smoothedCoefficient, one_mul] using (mollifierMultiplier_tendsto_one (ordinate ρ)).mul_const (sharpCoefficient lam ρ)
  · filter_upwards [ae_restrict_mem (μ := volume) hJ, ae_restrict_of_ae (ae_logWindow_regular lam)]
      with u hu hr
    exact smoothedSum_tendsto_sharp hRH (hpos hu) hlam hr.1 hr.2

theorem local_sharp_spectral_mean_square (hRH : RiemannHypothesis) {b lam : ℝ}
    (hb : 0 < b) (hlam : 0 < lam) (hlam₁ : lam ≤ 1) (z : ℝ) (J : Set ℝ)
    (hJ : MeasurableSet J) (hpos : J ⊆ Ioi 0) :
    IntegrableOn (fun u => weight b (u - z) * (sharpSpectralValue lam u)^2) J ∧
    (∫ u in J, weight b (u - z) * (sharpSpectralValue lam u)^2) ≤
      ∑' ρ : Zeros, diagonalEnergy b (sharpCoefficient lam) ρ := by
  have hc : zerosUpTo (-1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ρ hρ
    have h := (mem_zerosUpTo (-1) ρ).mp hρ
    linarith [abs_nonneg (ordinate ρ)]
  have he (y : ℝ) : |y|^2 = y^2 := sq_abs y
  simpa only [partialSum, hc, Finset.sum_empty, sub_zero, Complex.norm_real, Real.norm_eq_abs, he] using
    local_sharp_spectral_tail hRH hb hlam hlam₁ z J hJ hpos (-1)

/-- Thus the unmodified symmetric truncations converge in the local
Gaussian weighted L² seminorm. -/
theorem sharp_spectral_identification (hRH : RiemannHypothesis) {b lam : ℝ}
    (hb : 0 < b) (hlam : 0 < lam) (hlam₁ : lam ≤ 1) (z : ℝ) (J : Set ℝ)
    (hJ : MeasurableSet J) (hpos : J ⊆ Ioi 0) :
    Tendsto (fun T : ℝ => ∫ u in J, weight b (u - z) *
      ‖(sharpSpectralValue lam u : ℂ) - partialSum (sharpCoefficient lam) T u‖^2) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (diagonal_tail_tendsto_zero (sharpCoefficient lam) (diagonalEnergy_summable hb hlam.le hlam₁))
    (fun T => integral_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  intro T
  exact (local_sharp_spectral_tail hRH hb hlam hlam₁ z J hJ hpos T).2

end GoldbachSpectrum
