import Goldbach.Coefficient
import Goldbach.Zeros
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Fourier.Convolution

open Filter Function MeasureTheory Set ContinuousLinearMap
open scoped Convolution Topology FourierTransform
noncomputable section

namespace GoldbachSpectrum

open Zeta23 GoldbachGaussian

/-- Logarithmic sharp window in the von Mangoldt formula. -/
def logBox (lam : ℝ) : ℝ → ℂ :=
  (Ioc 0 lam).indicator (fun s => (Real.exp (s / 2) : ℂ))

theorem logBox_measurable (lam : ℝ) : Measurable (logBox lam) :=
  (by fun_prop : Measurable (fun s : ℝ => (Real.exp (s / 2) : ℂ))).indicator measurableSet_Ioc

theorem logBox_integrable (lam : ℝ) : Integrable (logBox lam) := by
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  exact (by fun_prop : Continuous (fun s : ℝ => (Real.exp (s / 2) : ℂ))).integrableOn_Icc.mono_set
    Ioc_subset_Icc_self

private theorem logBox_norm_le (lam t : ℝ) : ‖logBox lam t‖ ≤ Real.exp (lam / 2) := by
  by_cases ht : t ∈ Ioc 0 lam
  · rw [logBox, indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith [ht.2])
  · rw [logBox, indicator_of_notMem ht, norm_zero]
    exact (Real.exp_pos _).le

private theorem logBox_continuousAt {lam t : ℝ} (_hlam : 0 < lam)
    (h₀ : t ≠ 0) (h₁ : t ≠ lam) : ContinuousAt (logBox lam) t := by
  rcases lt_or_gt_of_ne h₀ with ht | ht
  · have he : logBox lam =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [gt_mem_nhds ht] with s hs
      exact indicator_of_notMem (show s ∉ Ioc 0 lam from fun hm => (not_lt_of_ge hs.le) hm.1) _
    exact continuousAt_const.congr he.symm
  rcases lt_or_gt_of_ne h₁ with hl | hl
  · have he : logBox lam =ᶠ[𝓝 t] fun s => (Real.exp (s / 2) : ℂ) := by
      filter_upwards [lt_mem_nhds ht, gt_mem_nhds hl] with s hs hs'
      exact indicator_of_mem (show s ∈ Ioc 0 lam from ⟨hs, hs'.le⟩) _
    exact (by fun_prop : ContinuousAt (fun s : ℝ => (Real.exp (s / 2) : ℂ)) t).congr he.symm
  · have he : logBox lam =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [lt_mem_nhds hl] with s hs
      exact indicator_of_notMem (show s ∉ Ioc 0 lam from fun hm => (not_le_of_gt hs) hm.2) _
    exact continuousAt_const.congr he.symm

theorem paperFT_logBox {lam : ℝ} (hlam : 0 ≤ lam) (g : ℝ) :
    paperFT (logBox lam) (g : ℂ) = coefficient lam g := by
  unfold paperFT coefficient
  rw [intervalIntegral.integral_of_le hlam, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with s
  by_cases hs : s ∈ Ioc 0 lam
  · rw [logBox, indicator_of_mem hs, indicator_of_mem hs, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    unfold exponent
    push_cast
    ring
  · simp [logBox, hs]

/-- Radii tend to zero, with nonnegative mollifiers of Lebesgue integral one. -/
def mollifierBump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨((n : ℝ) + 1)⁻¹ / 2, ((n : ℝ) + 1)⁻¹, by positivity, by linarith [show 0 < ((n : ℝ) + 1)⁻¹ by positivity]⟩

def mollifier (n : ℕ) : ℝ → ℝ := (mollifierBump n).normed volume

private theorem mollifier_radius_tendsto :
    Tendsto (fun n : ℕ => (mollifierBump n).rOut) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem mollifier_radius_le_one (n : ℕ) : (mollifierBump n).rOut ≤ 1 := by
  exact (inv_le_one₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    (le_add_of_nonneg_left (Nat.cast_nonneg n))

theorem eventual_mollifier_radius_lt {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n in atTop, (mollifierBump n).rOut < r :=
  mollifier_radius_tendsto.eventually (gt_mem_nhds hr)

def smoothLogBox (lam : ℝ) (n : ℕ) : ℝ → ℂ :=
  mollifier n ⋆[lsmul ℝ ℝ, volume] logBox lam

theorem smoothLogBox_contDiff (lam : ℝ) (n : ℕ) :
    ContDiff ℝ 2 (smoothLogBox lam n) :=
  (mollifierBump n).hasCompactSupport_normed.contDiff_convolution_left _
    (mollifierBump n).contDiff_normed (logBox_integrable lam).locallyIntegrable

theorem smoothLogBox_hasCompactSupport (lam : ℝ) (n : ℕ) :
    HasCompactSupport (smoothLogBox lam n) := by
  have hb : HasCompactSupport (logBox lam) := by
    apply HasCompactSupport.intro' (K := Icc 0 lam) isCompact_Icc isClosed_Icc
    intro t ht
    exact indicator_of_notMem (fun hm => ht (Ioc_subset_Icc_self hm)) _
  exact (mollifierBump n).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hb

theorem smoothLogBox_norm_le (lam : ℝ) (n : ℕ) (t : ℝ) :
    ‖smoothLogBox lam n t‖ ≤ Real.exp (lam / 2) := by
  unfold smoothLogBox
  rw [convolution_def]
  refine (norm_integral_le_of_norm_le
    (((mollifierBump n).integrable_normed (μ := volume)).mul_const (Real.exp (lam / 2))) ?_).trans_eq ?_
  · exact Eventually.of_forall fun s => by
      rw [lsmul_apply, norm_smul, mollifier, Real.norm_of_nonneg ((mollifierBump n).nonneg_normed (μ := volume) s)]
      exact mul_le_mul_of_nonneg_left (logBox_norm_le lam (t - s))
        ((mollifierBump n).nonneg_normed (μ := volume) s)
  · rw [integral_mul_const]
    change (∫ s, (mollifierBump n).normed volume s) * _ = _
    rw [(mollifierBump n).integral_normed, one_mul]

theorem smoothLogBox_zero_outside (lam : ℝ) (n : ℕ) (t : ℝ)
    (ht : t ≤ -(mollifierBump n).rOut ∨ lam + (mollifierBump n).rOut ≤ t) :
    smoothLogBox lam n t = 0 := by
  by_contra hn
  have hmem := support_convolution_subset (lsmul ℝ ℝ) (show t ∈ support (smoothLogBox lam n) from hn)
  rcases hmem with ⟨s, hs, v, hv, he⟩
  have hs' : s ∈ Metric.ball (0 : ℝ) (mollifierBump n).rOut := by
    rwa [← (mollifierBump n).support_normed_eq (μ := volume)]
  have habs : |s| < (mollifierBump n).rOut := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hs'
  have hv' : v ∈ Ioc 0 lam := by
    by_contra hn'
    exact hv (indicator_of_notMem hn' _)
  have hb := abs_lt.mp habs
  rcases ht with h | h <;> linarith [hv'.1, hv'.2, hb.1, hb.2]

theorem smoothLogBox_tendsto {lam t : ℝ} (hlam : 0 < lam) (h₀ : t ≠ 0) (h₁ : t ≠ lam) :
    Tendsto (fun n => smoothLogBox lam n t) atTop (𝓝 (logBox lam t)) :=
  ContDiffBump.convolution_tendsto_right mollifier_radius_tendsto
    (Eventually.of_forall fun _ => (logBox_integrable lam).aestronglyMeasurable)
    ((logBox_continuousAt hlam h₀ h₁).tendsto.comp tendsto_snd) tendsto_const_nhds

/-- Fourier multiplier of the probability mollifier, at angular frequency. -/
def mollifierMultiplier (n : ℕ) (g : ℝ) : ℂ :=
  paperFT (fun s => (mollifier n s : ℂ)) (g : ℂ)

theorem mollifierMultiplier_norm_le (n : ℕ) (g : ℝ) : ‖mollifierMultiplier n g‖ ≤ 1 := by
  unfold mollifierMultiplier paperFT
  calc
    _ ≤ ∫ s, ‖(mollifier n s : ℂ) * Complex.exp (Complex.I * (g : ℂ) * (s : ℂ))‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ s, mollifier n s := by
      apply integral_congr_ae
      filter_upwards with s
      have he : Complex.exp (Complex.I * (g : ℂ) * (s : ℂ)) = wave g s := by
        unfold wave
        congr 1
        push_cast
        ring
      rw [he, norm_mul, norm_wave, mul_one, Complex.norm_real, mollifier, Real.norm_of_nonneg
        ((mollifierBump n).nonneg_normed (μ := volume) s)]
    _ = 1 := (mollifierBump n).integral_normed

theorem mollifierMultiplier_tendsto_one (g : ℝ) :
    Tendsto (fun n => mollifierMultiplier n g) atTop (𝓝 1) := by
  have hc : Continuous (wave (-g)) := by unfold wave; fun_prop
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) mollifier_radius_tendsto hc 0
  rw [show wave (-g) 0 = 1 by simp [wave]] at h
  apply h.congr
  intro n
  unfold mollifierMultiplier paperFT
  rw [convolution_def]
  apply integral_congr_ae
  filter_upwards with s
  rw [lsmul_apply, Complex.real_smul]
  congr 1
  unfold wave
  congr 1
  push_cast
  ring

theorem paperFT_smoothLogBox {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) (g : ℝ) :
    paperFT (smoothLogBox lam n) (g : ℂ) =
      mollifierMultiplier n g * coefficient lam g := by
  have he : smoothLogBox lam n =
      ((fun s => (mollifier n s : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] logBox lam) := by
    funext t
    simp_rw [smoothLogBox, convolution_def, lsmul_apply, Complex.real_smul, mul_apply']
  have hI : Integrable (fun s => (mollifier n s : ℂ)) :=
    Complex.ofRealCLM.integrable_comp (mollifierBump n).integrable_normed
  rw [he, ← paperFT_logBox hlam, mollifierMultiplier]
  simp_rw [Zeta23.paperFT_ofReal_eq_fourier]
  exact Real.fourier_mul_convolution_eq hI (logBox_integrable lam) _

theorem paperFT_shift (k : ℝ → ℂ) (u : ℝ) (z : ℂ) :
    paperFT (fun v => k (v - u)) z = Complex.exp (Complex.I * z * (u : ℂ)) * paperFT k z := by
  unfold paperFT
  rw [← EF.cintegral_const_mul]
  rw [← integral_sub_right_eq_self (fun v : ℝ => Complex.exp (Complex.I * z * (u : ℂ)) *
    (k v * Complex.exp (Complex.I * z * (v : ℂ)))) u]
  apply integral_congr_ae
  filter_upwards with v
  rw [mul_comm (Complex.exp (Complex.I * z * (u : ℂ))), mul_assoc (k (v - u)), ← Complex.exp_add]
  congr 2
  push_cast
  ring

end GoldbachSpectrum
