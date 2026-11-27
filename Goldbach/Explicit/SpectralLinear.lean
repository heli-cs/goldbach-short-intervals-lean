import Goldbach.Explicit.SpectralTransfer

/-! Testing the compact spectral limit against an L² multiplier. -/

open Filter MeasureTheory Set
open scoped Topology
noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum GoldbachGaussian GoldbachZeros

private theorem sharpSpectralValue_aestronglyMeasurable (lam : ℝ) (μ : Measure ℝ) :
    AEStronglyMeasurable (fun u => (sharpSpectralValue lam u : ℂ)) μ := by
  apply Measurable.aestronglyMeasurable
  have hψ := Chebyshev.psi_mono.measurable
  have hg : Measurable GoldbachArithmetic.trivialZeroTerm := by
    unfold GoldbachArithmetic.trivialZeroTerm
    fun_prop
  have he : Measurable (fun u : ℝ => Real.exp (u + lam)) := by fun_prop
  have he' := Real.continuous_exp.measurable
  exact Complex.continuous_ofReal.measurable.comp
    ((by fun_prop : Measurable (fun u : ℝ => Real.exp (-u / 2))).mul
      (((he.sub he').add ((hg.comp he).sub (hg.comp he'))).sub
        ((hψ.comp he).sub (hψ.comp he'))))

/-- The sharp spectral value belongs to L² on every compact positive log interval. -/
theorem sharpSpectralValue_memLp (hRH : RiemannHypothesis) {lam a b : ℝ}
    (hlam : 0 < lam) (hlam₁ : lam ≤ 1) (ha : 0 < a) (hab : a ≤ b) :
    MemLp (fun u => (sharpSpectralValue lam u : ℂ)) 2 (volume.restrict (Icc a b)) := by
  have h := compact_weight_spectral_identification hRH hlam hlam₁ ha hab
    (W := fun _ => 1) measurable_const (fun _ _ => ⟨zero_le_one, le_rfl⟩)
  have hzero : zerosUpTo (-1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ρ hρ
    exact (not_le_of_gt (by linarith [abs_nonneg (ordinate ρ)] : -1 < |ordinate ρ|))
      ((mem_zerosUpTo _ _).1 hρ)
  apply (memLp_two_iff_integrable_sq_norm (sharpSpectralValue_aestronglyMeasurable _ _)).2
  simpa only [one_mul, IntegrableOn, partialSum, hzero, Finset.sum_empty, sub_zero] using h.1 (-1)

/-- An absolutely convergent spectrum of tested coefficients equals the
integral of the compact sharp spectral limit. -/
theorem sharp_spectral_integral_eq_tsum (hRH : RiemannHypothesis)
    {lam a b : ℝ} (hlam : 0 < lam) (hlam₁ : lam ≤ 1) (ha : 0 < a) (hab : a ≤ b)
    {W : ℝ → ℂ} (hW : MemLp W 2 (volume.restrict (Icc a b)))
    (hseries : Summable (fun ρ : Zeros =>
      (multiplicity ρ : ℂ) * sharpCoefficient lam ρ *
        (∫ u in Icc a b, W u * wave (ordinate ρ) u))) :
    (∫ u in Icc a b, W u * (sharpSpectralValue lam u : ℂ)) =
      ∑' ρ : Zeros, (multiplicity ρ : ℂ) * sharpCoefficient lam ρ *
        (∫ u in Icc a b, W u * wave (ordinate ρ) u) := by
  let μ := volume.restrict (Icc a b)
  let S (u : ℝ) : ℂ := (sharpSpectralValue lam u : ℂ)
  let P (T : ℝ) := partialSum (sharpCoefficient lam) T
  let E (T : ℝ) := P T - S
  have hW' : MemLp W 2 μ := hW
  have hSmeas : AEStronglyMeasurable S μ := sharpSpectralValue_aestronglyMeasurable _ _
  have hP (T : ℝ) : Continuous (P T) := by
    unfold P partialSum wave
    fun_prop
  have h := compact_weight_spectral_identification hRH hlam hlam₁ ha hab
    (W := fun _ => 1) measurable_const (fun _ _ => ⟨zero_le_one, le_rfl⟩)
  simp only [one_mul] at h
  have hEI (T : ℝ) : Integrable (fun u => ‖E T u‖ ^ 2) μ := by
    simpa only [μ, IntegrableOn, E, Pi.sub_apply, S, P, norm_sub_rev] using h.1 T
  have hEp (T : ℝ) : MemLp (E T) 2 μ :=
    (memLp_two_iff_integrable_sq_norm ((hP T).aestronglyMeasurable.sub hSmeas)).2 (hEI T)
  have hSp : MemLp S 2 μ := sharpSpectralValue_memLp hRH hlam hlam₁ ha hab
  have hPp (T : ℝ) : MemLp (P T) 2 μ := by
    convert (hEp T).add hSp using 1
    ext u
    simp [E]
  have hL : Tendsto (fun T : ℝ => ∫ u, ‖E T u‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa only [E, S, P, Pi.sub_apply, norm_sub_rev] using h.2
  have hroot : Tendsto (fun T : ℝ => Real.sqrt (∫ u, ‖E T u‖ ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hL
  have htest : Tendsto (fun T : ℝ => ∫ u, W u * P T u ∂μ) atTop
      (𝓝 (∫ u, W u * S u ∂μ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    let K := Real.sqrt (∫ u, ‖W u‖ ^ 2 ∂μ)
    have hu : Tendsto (fun T : ℝ => K * Real.sqrt (∫ u, ‖E T u‖ ^ 2 ∂μ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hroot.const_mul K
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun _ => norm_nonneg _)
    intro T
    have hPI : Integrable (fun u => W u * P T u) μ := hW'.integrable_mul (hPp T)
    have hSI : Integrable (fun u => W u * S u) μ := hW'.integrable_mul hSp
    have hHolder := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := W) (g := E T)
      Real.HolderConjugate.two_two (by simpa using hW') (by simpa using hEp T)
    change ‖(∫ u, W u * P T u ∂μ) - (∫ u, W u * S u ∂μ)‖ ≤ _
    calc
      _ = ‖∫ u, W u * E T u ∂μ‖ := by
        rw [← integral_sub hPI hSI]
        simp only [E, Pi.sub_apply, mul_sub]
      _ ≤ ∫ u, ‖W u‖ * ‖E T u‖ ∂μ := by
        simpa only [norm_mul] using norm_integral_le_integral_norm (μ := μ) (fun u => W u * E T u)
      _ ≤ _ := by
        simpa only [K, Real.sqrt_eq_rpow, Real.rpow_two] using hHolder
  have hwave (ρ : Zeros) : Integrable (fun u => W u * wave (ordinate ρ) u) μ := by
    have hnorm : ∀ u, ‖wave (ordinate ρ) u‖ = 1 := norm_wave _
    let : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
    have hi : Integrable W μ := hW'.integrable (by norm_num)
    have hc : Continuous (wave (ordinate ρ)) := by unfold wave; fun_prop
    refine hi.norm.mono' (hi.aestronglyMeasurable.mul hc.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall (fun u => by rw [norm_mul, hnorm, mul_one])
  have hfinite (T : ℝ) : (∫ u, W u * P T u ∂μ) =
      ∑ ρ ∈ zerosUpTo T, (multiplicity ρ : ℂ) * sharpCoefficient lam ρ *
        (∫ u, W u * wave (ordinate ρ) u ∂μ) := by
    let C (ρ : Zeros) := (multiplicity ρ : ℂ) * sharpCoefficient lam ρ
    have he (u : ℝ) : W u * P T u =
        ∑ ρ ∈ zerosUpTo T, C ρ * (W u * wave (ordinate ρ) u) := by
      unfold P partialSum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      unfold C
      ring
    simp_rw [he]
    rw [integral_finsetSum _ (fun ρ _ => (hwave ρ).const_mul (C ρ))]
    exact Finset.sum_congr rfl (fun ρ _ => integral_const_mul _ _)
  exact tendsto_nhds_unique (htest.congr hfinite) (hseries.hasSum.comp zerosUpTo_tendsto_atTop)

end GoldbachExplicit
