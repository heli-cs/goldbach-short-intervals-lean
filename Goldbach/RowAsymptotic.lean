import Goldbach.CompactWeil
import Goldbach.TranslatedZeros
import Goldbach.FourierCutoff

open Filter MeasureTheory
open scoped Topology
noncomputable section

namespace GoldbachZeros

open Zeta23

private theorem log_abs_add_three_le_two_log {t : ℝ} (ht : 3 ≤ t) :
    Real.log (|t| + 3) ≤ 2 * Real.log t := by
  have ht₀ : 0 < t := by linarith
  rw [abs_of_nonneg ht₀.le]
  calc
    _ ≤ Real.log (t^2) := Real.log_le_log (by positivity) (by
      nlinarith [mul_nonneg (by linarith : 0 ≤ t - 3) ht₀.le])
    _ = _ := by rw [Real.log_pow]; norm_num

private theorem translatedAverage_sub (f g : ℝ → ℂ) {t : ℝ}
    (hf : Summable (fun ρ : Zeros => (multiplicity ρ : ℂ) * f (ordinate ρ - t)))
    (hg : Summable (fun ρ : Zeros => (multiplicity ρ : ℂ) * g (ordinate ρ - t))) :
    translatedAverage (fun u => f u - g u) t = translatedAverage f t - translatedAverage g t := by
  unfold translatedAverage
  rw [← smul_sub, ← hf.tsum_sub hg]
  congr 1
  exact tsum_congr (fun ρ => mul_sub _ _ _)

/-- The translated Weil limit extends to twice differentiable tests
whose zeroth, first, and second derivatives are integrable. -/
theorem translatedAverage_paperFT_tendsto (hRH : RiemannHypothesis) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hki : Integrable k) (hdi : Integrable (deriv k))
    (hddi : Integrable (deriv (deriv k))) :
    Tendsto (translatedAverage (fun r : ℝ => paperFT k (r : ℂ))) atTop (𝓝 (k 0)) := by
  obtain ⟨A, hA, htrans⟩ := translated_sum_bound
  have hsum {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgi : Integrable g)
      (hg₁ : Integrable (deriv g)) (hg₂ : Integrable (deriv (deriv g))) (t : ℝ) :
      Summable (fun ρ : Zeros => (multiplicity ρ : ℂ) * paperFT g ((ordinate ρ - t : ℝ) : ℂ)) := by
    exact (htrans t (fun r => paperFT g (r : ℂ)) _
      (add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _))
      (paperFT_real_norm_le_quadratic hg hgi hg₁ hg₂)).1
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (4 * A)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨g, hg, hgc, hg0, hdiff⟩ := exists_compact_paperFT_approx hk hki hdi hddi hδ
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hg₁ : Integrable (deriv g) :=
    (hg.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport hgc.deriv
  have hg₂ : Integrable (deriv (deriv g)) :=
    ((hg.deriv' : ContDiff ℝ 1 (deriv g)).continuous_deriv le_rfl).integrable_of_hasCompactSupport
      hgc.deriv.deriv
  let F (r : ℝ) := paperFT k (r : ℂ)
  let G (r : ℝ) := paperFT g (r : ℂ)
  have ht := (Metric.tendsto_nhds.mp (translatedAverage_paperFT_compact_tendsto hRH hg hgc))
    (ε / 2) (by positivity)
  filter_upwards [ht, eventually_ge_atTop (3 : ℝ)] with t htg ht₃
  have hgt : ‖translatedAverage G t - k 0‖ < ε / 2 := by
    simpa only [G, dist_eq_norm, hg0] using htg
  have hb := (htrans t (fun u => G u - F u) δ hδ.le hdiff).2
  have hd := translatedAverage_sub G F (hsum hg hgi hg₁ hg₂ t) (hsum hk hki hdi hddi t)
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have hgf : ‖translatedAverage G t - translatedAverage F t‖ ≤ ε / 2 := by
    rw [← hd, translatedAverage, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hlog.le)]
    calc
      _ ≤ (Real.log t)⁻¹ * (A * δ * Real.log (|t| + 3)) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hlog.le)
      _ ≤ (Real.log t)⁻¹ * (A * δ * (2 * Real.log t)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (log_abs_add_three_le_two_log ht₃) (mul_nonneg hA.le hδ.le))
          (inv_nonneg.mpr hlog.le)
      _ = _ := by dsimp [δ]; field_simp [hA.ne', hlog.ne']; ring
  rw [dist_eq_norm]
  change ‖translatedAverage F t - k 0‖ < ε
  calc
    _ = ‖(translatedAverage F t - translatedAverage G t) + (translatedAverage G t - k 0)‖ := by
      rw [sub_add_sub_cancel]
    _ ≤ ‖translatedAverage G t - translatedAverage F t‖ + ‖translatedAverage G t - k 0‖ := by
      rw [norm_sub_rev (translatedAverage G t) (translatedAverage F t)]
      exact norm_add_le _ _
    _ < ε := by linarith

private theorem weight_hasDerivAt (b x : ℝ) :
    HasDerivAt (GoldbachGaussian.weight b) ((-2 * b) * x * GoldbachGaussian.weight b x) x := by
  unfold GoldbachGaussian.weight
  have hd := (((hasDerivAt_id x).pow 2).const_mul (-b)).exp
  convert hd using 1 <;> norm_num [Pi.pow_apply, id_eq] <;> ring

private theorem gaussian_test_regular {b : ℝ} (hb : 0 < b) :
    let W := fun x => (GoldbachGaussian.weight b x : ℂ)
    ContDiff ℝ 2 W ∧ Integrable W ∧ Integrable (deriv W) ∧ Integrable (deriv (deriv W)) := by
  let W := fun x => (GoldbachGaussian.weight b x : ℂ)
  have hw : ContDiff ℝ 2 (GoldbachGaussian.weight b) := by unfold GoldbachGaussian.weight; fun_prop
  have hc : ContDiff ℝ 2 W := Complex.ofRealCLM.contDiff.comp hw
  have i₀ := GoldbachGaussian.integrable_weight hb
  have i₁ : Integrable (fun x : ℝ => x * GoldbachGaussian.weight b x) := integrable_mul_exp_neg_mul_sq hb
  have i₂ : Integrable (fun x : ℝ => x^2 * GoldbachGaussian.weight b x) := by
    simpa only [GoldbachGaussian.weight, Real.rpow_two] using
      integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)
  have hd₁ (x : ℝ) : deriv W x = (((-2 * b) * x * GoldbachGaussian.weight b x : ℝ) : ℂ) :=
    (weight_hasDerivAt b x).ofReal_comp.deriv
  have hd₂ (x : ℝ) : deriv (deriv W) x =
      (((-2 * b) * GoldbachGaussian.weight b x +
        (4 * b^2) * (x^2 * GoldbachGaussian.weight b x) : ℝ) : ℂ) := by
    rw [funext hd₁]
    have hd := (((hasDerivAt_id x).const_mul (-2 * b)).mul (weight_hasDerivAt b x)).ofReal_comp.deriv
    refine hd.trans ?_
    push_cast
    simp only [id_eq, mul_one]
    ring
  have hI₁ := Complex.ofRealCLM.integrable_comp (i₁.const_mul (-2 * b))
  have hI₂ := Complex.ofRealCLM.integrable_comp ((i₀.const_mul (-2 * b)).add (i₂.const_mul (4 * b^2)))
  refine ⟨hc, Complex.ofRealCLM.integrable_comp i₀, ?_, ?_⟩
  · rw [funext hd₁]
    convert hI₁ using 1
    funext x
    change _ = (((-2 * b) * (x * GoldbachGaussian.weight b x) : ℝ) : ℂ)
    push_cast
    ring
  · rw [funext hd₂]
    exact hI₂

private theorem paperFT_gaussian {b : ℝ} (hb : 0 < b) (r : ℝ) :
    paperFT (fun x => (GoldbachGaussian.weight b x : ℂ)) (r : ℂ) =
      (GoldbachGaussian.kernel b r : ℂ) := by
  rw [← GoldbachGaussian.integral_weight_wave hb r]
  unfold paperFT GoldbachGaussian.wave
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    push_cast
    congr 2
    ring

/-- The Gaussian zero row has leading coefficient one at positive heights. -/
theorem row_div_log_tendsto_one (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => row b t / Real.log t) atTop (𝓝 1) := by
  obtain ⟨hc, hi, hd, hdd⟩ := gaussian_test_regular hb
  have h := translatedAverage_paperFT_tendsto hRH hc hi hd hdd
  have ht := Complex.continuous_re.continuousAt.tendsto.comp h
  have h0 : ((GoldbachGaussian.weight b 0 : ℝ) : ℂ).re = 1 := by simp [GoldbachGaussian.weight]
  rw [h0] at ht
  apply ht.congr'
  filter_upwards with t
  change (translatedAverage (fun r : ℝ => paperFT (fun x => (GoldbachGaussian.weight b x : ℂ))
    (r : ℂ)) t).re = _
  simp_rw [paperFT_gaussian hb]
  unfold translatedAverage
  have he : (∑' ρ : Zeros, (multiplicity ρ : ℂ) * (GoldbachGaussian.kernel b (ordinate ρ - t) : ℂ)) =
      (row b t : ℂ) := by
    unfold row
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro ρ
    push_cast
    rw [show ordinate ρ - t = -(t - ordinate ρ) by ring, GoldbachGaussian.kernel_even]
  rw [he, Complex.smul_re, Complex.ofReal_re, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The Gaussian zero row is asymptotic to the logarithm at both ends. -/
theorem row_div_log_abs_tendsto_one (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => row b t / Real.log |t|) (atTop ⊔ atBot) (𝓝 1) := by
  rw [Filter.tendsto_sup]
  have h := row_div_log_tendsto_one hRH hb
  constructor
  · apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [abs_of_nonneg ht]
  · apply (h.comp tendsto_neg_atBot_atTop).congr'
    filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
    change row b (-t) / Real.log (-t) = _
    rw [row_even, abs_of_nonpos ht]

end GoldbachZeros
