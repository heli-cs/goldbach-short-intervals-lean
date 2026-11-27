import Goldbach.Zeros
import Goldbach.GammaBracket
import Zeta23.ExplicitFormula.Bridge

open Filter MeasureTheory Set
open scoped BigOperators Topology FourierTransform
noncomputable section

namespace GoldbachZeros

open Zeta23

/-- The translated zero sum, divided by the logarithm of its centre. -/
def translatedAverage (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.log t)⁻¹ • ∑' ρ : Zeros, (multiplicity ρ : ℂ) * f (ordinate ρ - t)

private def modulate (k : ℝ → ℂ) (t : ℝ) : ℝ → ℂ :=
  fun u => k u * GoldbachGaussian.wave (-t) u

private theorem modulate_norm (k : ℝ → ℂ) (t u : ℝ) : ‖modulate k t u‖ = ‖k u‖ := by
  simp [modulate]

private theorem modulate_contDiff {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (t : ℝ) :
    ContDiff ℝ 2 (modulate k t) := by
  have hcast : ContDiff ℝ 2 (fun u : ℝ => ((-t * u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  unfold modulate GoldbachGaussian.wave
  exact hk.mul ((hcast.mul contDiff_const).cexp)

private theorem paperFT_modulate (k : ℝ → ℂ) (t r : ℝ) :
    paperFT (modulate k t) (r : ℂ) = paperFT k ((r - t : ℝ) : ℂ) := by
  unfold paperFT modulate GoldbachGaussian.wave
  apply integral_congr_ae
  filter_upwards with u
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private def nonArchimedean (k : ℝ → ℂ) : ℂ :=
  paperFT k (Complex.I / 2) + paperFT k (-Complex.I / 2)
    - ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n))

private theorem norm_modulated_nonArchimedean_le {k : ℝ → ℂ} (hk : Continuous k)
    (hkc : HasCompactSupport k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖nonArchimedean (modulate k t)‖ ≤ C := by
  obtain ⟨Λ, hΛ⟩ := EF.exists_abs_le_of_hasCompactSupport hkc
  let poles (z : ℂ) := Real.exp (|z.im| * Λ) * ∫ u, ‖k u‖
  let S := Finset.Ioc 0 ⌊Real.exp Λ⌋₊
  let c (n : ℕ) : ℂ := ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
  let Q := ∑ n ∈ S, ‖c n‖ * (‖k (Real.log n)‖ + ‖k (-Real.log n)‖)
  have hp (z : ℂ) : 0 ≤ poles z :=
    mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun n _ => by positivity
  refine ⟨poles (Complex.I / 2) + poles (-Complex.I / 2) + Q,
    add_nonneg (add_nonneg (hp _) (hp _)) hQ, fun t => ?_⟩
  let K := modulate k t
  have hKc : HasCompactSupport K := hkc.mul_right
  have hKn (u : ℝ) : ‖K u‖ = ‖k u‖ := modulate_norm k t u
  have hKΛ (u : ℝ) (hu : K u ≠ 0) : |u| ≤ Λ :=
    hΛ u (fun hz => hu (by simp [K, modulate, hz]))
  have hKs : tsupport K ⊆ Icc (-Λ) Λ :=
    closure_minimal (fun u hu => abs_le.mp (hKΛ u hu)) isClosed_Icc
  have hKi : Integrable K := (hk.mul (by unfold GoldbachGaussian.wave; fun_prop)).integrable_of_hasCompactSupport hKc
  have hpole (z : ℂ) : ‖paperFT K z‖ ≤ poles z := by
    simpa only [hKn, poles] using norm_paperFT_le hKi hKΛ z
  have hpr : ‖∑' n, c n * (K (Real.log n) + K (-Real.log n))‖ ≤ Q := by
    rw [tsum_eq_sum (s := S) (fun n hn => EF.prime_summand_eq_zero hKs hn)]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n _
    rw [norm_mul, ← hKn (Real.log n), ← hKn (-Real.log n)]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
  exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (hpole _) (hpole _))) hpr)

private theorem integrable_log_moment_of_decay {f : ℝ → ℂ} (hf : Continuous f)
    {C : ℝ} (hC : 0 ≤ C) (hdecay : ∀ u, ‖f u‖ ≤ C / (1 + u^2)) :
    Integrable (fun u => ‖f u‖ * Real.log (3 + |u|)) := by
  have hbase : Integrable (fun u : ℝ => ((1 : ℝ) + ‖u‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (by rw [Module.finrank_self]; norm_num)
  refine (hbase.const_mul (10 * C)).mono' ?_ (Eventually.of_forall fun u => ?_)
  · apply Continuous.aestronglyMeasurable
    have hc : Continuous (fun u : ℝ => 3 + |u|) := continuous_const.add continuous_abs
    exact hf.norm.mul (hc.log (fun u => (show 0 < 3 + |u| by positivity).ne'))
  have hL : 0 ≤ Real.log (3 + |u|) := Real.log_nonneg (by linarith [abs_nonneg u])
  have hp : 0 < 1 + u^2 := by positivity
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hL)]
  have hq : Real.log (3 + |u|) ≤ 10 * (1 + u^2) ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_log (show 0 < 3 + |u| by positivity)
      (show 3 + |u| ≤ (2 + |u|)^2 by nlinarith [abs_nonneg u, sq_nonneg |u|])
    rw [Real.log_pow] at h
    norm_num at h
    have h₂ := Zeta23.WeilEF.log_two_add_le (abs_nonneg u)
    rw [sq_abs] at h₂
    linarith
  have he : (1 + u^2 : ℝ) ^ (-(3 / 2 : ℝ) / 2) =
      (1 + u^2) ^ (1 / 4 : ℝ) / (1 + u^2) := by
    rw [show (-(3 / 2 : ℝ) / 2) = (1 / 4 : ℝ) - 1 by norm_num, Real.rpow_sub hp, Real.rpow_one]
  calc
    _ ≤ C / (1 + u^2) * (10 * (1 + u^2) ^ (1 / 4 : ℝ)) :=
      mul_le_mul (hdecay u) hq hL (by positivity)
    _ = _ := by rw [Real.norm_eq_abs, sq_abs, he]; ring

private theorem archimedean_shift (F : ℝ → ℂ) (t : ℝ) :
    (Real.log t)⁻¹ • (∫ r : ℝ, F (r - t) * (EF.gammaBracket r : ℂ)) =
      ∫ u : ℝ, (EF.gammaBracket (t + u) / Real.log t) • F u := by
  have he :
      (∫ r : ℝ, F (r - t) * (EF.gammaBracket r : ℂ)) =
        ∫ u : ℝ, F u * (EF.gammaBracket (t + u) : ℂ) := by
    rw [← integral_sub_right_eq_self (fun u : ℝ => F u * (EF.gammaBracket (t + u) : ℂ)) t]
    apply integral_congr_ae
    filter_upwards with u
    rw [show t + (u - t) = u by ring]
  rw [he, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_div]
  ring

/-- Modulated compact smooth tests recover the translated zero density.
The main term comes from the archimedean factor. -/
theorem translatedAverage_paperFT_compact_tendsto (hRH : RiemannHypothesis) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Tendsto (translatedAverage (fun r : ℝ => paperFT k (r : ℂ))) atTop (𝓝 (k 0)) := by
  let F (r : ℝ) : ℂ := paperFT k (r : ℂ)
  let a : ℂ := 1 / (2 * Real.pi)
  have hkI : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  have hFI := EF.integrable_fourier_of_contDiff_two hk hkc
  have hFc : Continuous F := by
    unfold F
    simp_rw [paperFT_ofReal_eq_fourier]
    exact (EF.continuous_fourier_of_integrable hkI).comp (continuous_neg.div_const _)
  obtain ⟨Λ, hΛ⟩ := EF.exists_abs_le_of_hasCompactSupport hkc
  let B := (∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖
  have hB : 0 ≤ B := add_nonneg (integral_nonneg fun _ => norm_nonneg _)
    (integral_nonneg fun _ => norm_nonneg _)
  have hFB (u : ℝ) : ‖F u‖ ≤ B / (1 + u^2) :=
    (le_div_iff₀ (by positivity)).mpr (EF.norm_paperFT_mul_one_add_sq_le hk hΛ u)
  have hFint : Integrable F := EF.integrable_paperFT_ofReal hFI
  have hArch := (integral_gammaBracket_shift_smul_div_log hFint
    (integrable_log_moment_of_decay hFc hB hFB)).const_mul a
  have hK0 : a * (∫ u : ℝ, F u) = k 0 := by
    symm
    simpa only [F, a, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] using
      EF.paper_inversion hk.continuous hkI hFI 0
  rw [hK0] at hArch
  obtain ⟨C, hC, hbound⟩ := norm_modulated_nonArchimedean_le hk.continuous hkc
  have hnon : Tendsto (fun t : ℝ => (Real.log t)⁻¹ • nonArchimedean (modulate k t)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_
      (by simpa only [zero_mul] using Real.tendsto_log_atTop.inv_tendsto_atTop.mul_const C)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.log_nonneg ht.le))]
    exact mul_le_mul_of_nonneg_left (hbound t) (inv_nonneg.mpr (Real.log_nonneg ht.le))
  have h := hnon.add hArch
  rw [zero_add] at h
  apply h.congr'
  filter_upwards with t
  have hp := (weil_explicit_on_line hRH (modulate k t) (modulate_contDiff hk t) hkc.mul_right).2
  simp_rw [paperFT_modulate] at hp
  unfold translatedAverage
  rw [hp]
  unfold EF.literatureRHS nonArchimedean
  rw [smul_add]
  congr 1
  simp_rw [paperFT_modulate]
  rw [← archimedean_shift F t]
  simp only [Complex.real_smul]
  unfold a
  ring

end GoldbachZeros
