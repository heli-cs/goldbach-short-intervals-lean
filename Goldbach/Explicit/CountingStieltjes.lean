import Goldbach.Explicit.CountingDerivative
import Goldbach.Explicit.CountingMainDensity
import Goldbach.Explicit.ZeroIntegration

/-! The finite Stieltjes comparison for the actual logarithmic spectral test. -/

open Filter MeasureTheory Set
open scoped Interval Topology
noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum GoldbachZeros Zeta23

private def cutLog (t : ℝ) : ℝ :=
  Real.smoothTransition (t + 2) * Real.log (t + 3)

private theorem contDiff_cutLog : ContDiff ℝ 1 cutLog := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t + 3 = 0
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds (show t < -2 by linarith)] with u hu
    rw [cutLog, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  have h₂ : ContDiffAt ℝ 1 (fun u : ℝ => u + 2) t := by fun_prop
  have h₃ : ContDiffAt ℝ 1 (fun u : ℝ => u + 3) t := by fun_prop
  unfold cutLog
  exact (Real.smoothTransition.contDiffAt.comp t h₂).mul (h₃.log ht)

private def cutLogarithmicCoefficient (lam t : ℝ) : ℝ :=
  ‖coefficient lam t‖^2 * cutLog t

private theorem cutLogarithmicCoefficient_contDiff (lam : ℝ) :
    ContDiff ℝ 1 (cutLogarithmicCoefficient lam) :=
  (contDiff_coefficient_sq lam).mul contDiff_cutLog

private theorem eventually_cutLogarithmicCoefficient_eq (lam : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    cutLogarithmicCoefficient lam =ᶠ[𝓝 t] logarithmicCoefficient lam := by
  filter_upwards [lt_mem_nhds (show (-1 : ℝ) < t by linarith)] with u hu
  rw [cutLogarithmicCoefficient, cutLog, Real.smoothTransition.one_of_one_le (by linarith),
    one_mul, logarithmicCoefficient]

/-- The positive-ordinate finite sum is bounded by the continuous main
integral, the vanishing discrepancy boundary, and the absolute counting error. -/
theorem finite_logarithmic_zero_sum_le (hRH : RiemannHypothesis) {lam T : ℝ}
    (hlam : 0 < lam) (hlam₁ : lam ≤ 1 / 10) (hT : 0 ≤ T) :
    (∑ ρ ∈ zeroWindow 0 T, multiplicity ρ * logarithmicCoefficient lam (ordinate ρ)) ≤
      logarithmicCoefficient lam T * ((Ncount 0 T : ℝ) - zeroCountMain T) +
        (∫ t in Ioi (0 : ℝ), ‖coefficient lam t‖^2 * (Real.log t)^2) / (2 * Real.pi) +
        250 * (∫ t in Ioi (0 : ℝ), countErrorIntegrand lam t) := by
  let f := cutLogarithmicCoefficient lam
  let q := logarithmicCoefficient lam
  let N (t : ℝ) := (Ncount 0 t : ℝ)
  let I := Ioc (0 : ℝ) T
  let M := zeroCountMain
  let G (t : ℝ) := (‖coefficient lam t‖^2 * (Real.log t)^2) / (2 * Real.pi)
  have hf := cutLogarithmicCoefficient_contDiff lam
  have hDf : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hEq (t : ℝ) (ht : 0 ≤ t) : f t = q t :=
    (eventually_cutLogarithmicCoefficient_eq lam ht).eq_of_nhds
  have hEqD (t : ℝ) (ht : 0 ≤ t) : deriv f t = deriv q t :=
    (eventually_cutLogarithmicCoefficient_eq lam ht).deriv_eq
  have hN := zero_window_integration_by_parts (a := (0 : ℝ)) (b := T) hf
  have hSup :
      (∑ ρ ∈ zeroWindow 0 T, multiplicity ρ * q (ordinate ρ)) =
        f T * N T - ∫ t in I, deriv f t * N t := by
    change _ = _ - ∫ t in Ioc (0 : ℝ) T, deriv f t * N t
    rw [← hN]
    exact Finset.sum_congr rfl (fun ρ hρ => by
      change multiplicity ρ * q (ordinate ρ) = multiplicity ρ * f (ordinate ρ)
      rw [hEq (ordinate ρ) (mem_zeroWindow.mp hρ).1.le])
  have hM : (∫ t in I, f t * clippedZeroDensity t) =
      f T * M T - ∫ t in I, deriv f t * M t := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := f) (v := M)
      (a := (0 : ℝ)) (b := T)
      (fun t _ => (hf.differentiable (by norm_num) t).hasDerivAt)
      (fun t _ => zeroCountMain_hasDerivAt t)
      (hDf.intervalIntegrable 0 T) (continuous_clippedZeroDensity.intervalIntegrable 0 T)
    rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT] at h
    have hM₀ : M 0 = 0 := zeroCountMain_zero
    rwa [hM₀, mul_zero, sub_zero] at h
  have hMc : Continuous M := continuous_iff_continuousAt.mpr (fun t => (zeroCountMain_hasDerivAt t).continuousAt)
  have hNm : Monotone N := by
    intro u v huv
    change (Ncount 0 u : ℝ) ≤ (Ncount 0 v : ℝ)
    exact_mod_cast Ncount_mono (a := (0 : ℝ)) le_rfl huv
  have hNi : IntegrableOn N (Icc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hNm.intervalIntegrable
  have hNDi : IntegrableOn (fun t => deriv f t * N t) I :=
    (IntegrableOn.continuousOn_mul hDf.continuousOn hNi isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hMDi : IntegrableOn (fun t => deriv f t * M t) I :=
    ((hDf.mul hMc).continuousOn.integrableOn_compact (μ := volume) isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hErrI : IntegrableOn (fun t => deriv f t * (N t - M t)) I := by
    simpa only [mul_sub, Pi.sub_def] using hNDi.sub hMDi
  have hSub : (∫ t in I, deriv f t * (N t - M t)) =
      (∫ t in I, deriv f t * N t) - ∫ t in I, deriv f t * M t := by
    simp_rw [mul_sub]
    exact integral_sub hNDi hMDi
  have hId :
      (∑ ρ ∈ zeroWindow 0 T, multiplicity ρ * q (ordinate ρ)) =
        q T * (N T - M T) + (∫ t in I, f t * clippedZeroDensity t) -
          ∫ t in I, deriv f t * (N t - M t) := by
    rw [hSup, hM, hSub, ← hEq T hT]
    ring
  have hGi : IntegrableOn G (Ioi (0 : ℝ)) :=
    (coefficient_log_square_integral_le hlam (hlam₁.trans (by norm_num))).1.div_const _
  have hfd : IntegrableOn (fun t => f t * clippedZeroDensity t) I :=
    ((hf.continuous.mul continuous_clippedZeroDensity).continuousOn.integrableOn_compact
      (μ := volume) isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hMain : (∫ t in I, f t * clippedZeroDensity t) ≤ ∫ t in Ioi (0 : ℝ), G t := by
    calc
      _ ≤ ∫ t in I, G t := by
        refine integral_mono_ae hfd (hGi.mono_set Ioc_subset_Ioi_self) ?_
        filter_upwards [ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioc] with t ht
        rw [hEq t ht.1.le]
        have hh := mul_le_mul_of_nonneg_left (log_mul_clippedZeroDensity_le ht.1.le)
          (sq_nonneg ‖coefficient lam t‖)
        change ‖coefficient lam t‖^2 * Real.log (t + 3) * clippedZeroDensity t ≤ G t
        unfold G
        simp only [div_eq_mul_inv] at hh ⊢
        nlinarith only [hh]
      _ ≤ _ := by
        apply setIntegral_mono_set hGi
        · exact Eventually.of_forall (fun _ => by unfold G; positivity)
        · exact Eventually.of_forall (fun _ ht => ht.1)
  have hEC := (counting_derivative_integral_le hlam hlam₁).1
  have hErr : -(∫ t in I, deriv f t * (N t - M t)) ≤
      250 * ∫ t in Ioi (0 : ℝ), countErrorIntegrand lam t := by
    rw [← integral_neg]
    calc
      _ ≤ ∫ t in I, 250 * countErrorIntegrand lam t := by
        refine integral_mono_ae hErrI.neg ((hEC.mono_set Ioc_subset_Ioi_self).const_mul 250) ?_
        filter_upwards [ae_restrict_mem (μ := volume) (s := I) measurableSet_Ioc] with t ht
        have hCount := cumulative_zero_count_le hRH ht.1.le
        change |N t - M t| ≤ 250 * Real.log (t + 2) at hCount
        calc
          _ ≤ |deriv f t * (N t - M t)| := neg_le_abs _
          _ ≤ _ := by
            rw [abs_mul, hEqD t ht.1.le]
            have hh := mul_le_mul_of_nonneg_left hCount (abs_nonneg (deriv q t))
            change _ ≤ 250 * (Real.log (t + 2) * |deriv q t|)
            nlinarith only [hh]
      _ ≤ _ := by
        rw [integral_const_mul]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply setIntegral_mono_set hEC
        · filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi] with t ht
          exact mul_nonneg (Real.log_nonneg (by linarith [show 0 < t from ht])) (abs_nonneg _)
        · exact Eventually.of_forall (fun _ ht => ht.1)
  change (∑ ρ ∈ zeroWindow 0 T, multiplicity ρ * q (ordinate ρ)) ≤
    q T * (N T - M T) + _ + _
  unfold G at hMain
  rw [integral_div] at hMain
  rw [hId]
  linarith only [hMain, hErr]

end GoldbachExplicit
