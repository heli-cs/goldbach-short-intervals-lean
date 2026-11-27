import Mathlib
import Zeta23.WeilEF.FullLine

open Filter MeasureTheory
open scoped Topology

noncomputable section
namespace GoldbachZeros

open Zeta23.EF (gammaBracket)

private def gammaArgument (t : ℝ) : ℂ := 1 / 4 + Complex.I * (t : ℂ) / 2

private theorem gammaArgument_re (t : ℝ) : (gammaArgument t).re = 1 / 4 := by
  norm_num [gammaArgument, Complex.div_re, Complex.mul_re]

private theorem gammaArgument_im (t : ℝ) : (gammaArgument t).im = t / 2 := by
  norm_num [gammaArgument, Complex.div_im, Complex.mul_re, Complex.mul_im]

private theorem continuous_gammaBracket : Continuous gammaBracket := by
  apply (Complex.continuous_re.comp ?_).sub continuous_const
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hz : gammaArgument t ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have hr := congrArg Complex.re hn
    simp only [gammaArgument_re, Complex.intCast_re] at hr
    have h₀ : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < (n : ℝ) by linarith)
    have h₁ : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
    omega
  exact ContinuousAt.comp (g := Complex.digamma) (f := gammaArgument)
    (Zeta23.Stirling.differentiableAt_digamma hz).continuousAt
    (show Continuous gammaArgument by unfold gammaArgument; fun_prop).continuousAt

/-- The zeta gamma factor has the logarithmic main term and coefficient used by the Gaussian row. -/
theorem gammaBracket_sub_log_le {t : ℝ} (ht : 1 ≤ t) :
    |gammaBracket t - Real.log t + Real.log (2 * Real.pi)| ≤ 20 / t^2 := by
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  have hu : 0 ≤ t / 2 := by positivity
  have hp : 1 / 2 ≤ |t / 2| := by rw [abs_of_nonneg hu]; linarith
  have h := Zeta23.StirlingVert.re_digamma_stirling' (a := 1 / 4) (by norm_num) (by norm_num) hp
  rw [abs_of_nonneg hu, Real.log_div ht₀.ne' two_ne_zero] at h
  have ha : gammaArgument t = ((1 / 4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) := by
    unfold gammaArgument
    push_cast
    ring
  have he : gammaBracket t - Real.log t + Real.log (2 * Real.pi) =
      (Complex.digamma (gammaArgument t)).re - (Real.log t - Real.log 2) := by
    change (Complex.digamma (gammaArgument t)).re - Real.log Real.pi -
      Real.log t + Real.log (2 * Real.pi) = _
    rw [Real.log_mul two_ne_zero Real.pi_ne_zero]
    ring
  rw [he, ha]
  exact h.trans_eq (by ring)

private theorem gammaBracket_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |gammaBracket t| ≤ C * Real.log (3 + |t|) := by
  obtain ⟨C, hC, hg⟩ := Zeta23.WeilEF.digamma_growth_strip
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨C + |Real.log Real.pi| / Real.log 3, by positivity, fun t => ?_⟩
  have hz := hg (gammaArgument t) (by rw [gammaArgument_re]) (by rw [gammaArgument_re]; norm_num)
  have hIm : |(gammaArgument t).im| ≤ |t| := by
    rw [gammaArgument_im, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact div_le_self (abs_nonneg _) (by norm_num)
  have hl := Real.log_le_log (show (0 : ℝ) < 2 + |(gammaArgument t).im| by positivity)
    (show 2 + |(gammaArgument t).im| ≤ 3 + |t| by linarith)
  have h₃ := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
    (show 3 ≤ 3 + |t| by linarith [abs_nonneg t])
  change |(Complex.digamma (gammaArgument t)).re - Real.log Real.pi| ≤ _
  calc
    _ ≤ |(Complex.digamma (gammaArgument t)).re| + |Real.log Real.pi| := abs_sub _ _
    _ ≤ C * Real.log (3 + |t|) + |Real.log Real.pi| :=
      add_le_add ((Complex.abs_re_le_norm _).trans (hz.trans (mul_le_mul_of_nonneg_left hl hC.le))) le_rfl
    _ ≤ _ := by
      rw [add_mul]
      refine add_le_add le_rfl ?_
      have he : |Real.log Real.pi| = |Real.log Real.pi| / Real.log 3 * Real.log 3 :=
        (div_mul_cancel₀ _ hlog.ne').symm
      calc
        |Real.log Real.pi| = _ := he
        _ ≤ _ := mul_le_mul_of_nonneg_left h₃ (by positivity)

theorem gammaBracket_shift_div_log_tendsto_one (s : ℝ) :
    Tendsto (fun t : ℝ => gammaBracket (t + s) / Real.log t) atTop (𝓝 1) := by
  let C := 20 + |Real.log (2 * Real.pi)| + Real.log 2
  have hi : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hsmall : Tendsto (fun t : ℝ => (gammaBracket (t + s) - Real.log t) / Real.log t)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa only [mul_zero] using hi.const_mul C)
    filter_upwards [eventually_ge_atTop (2 + 2 * |s|)] with t ht
    have ht₀ : 1 < t := by linarith [abs_nonneg s]
    have hlog := Real.log_pos ht₀
    have hs : 1 ≤ t + s := by linarith [neg_abs_le s, abs_nonneg s]
    have hlo : t / 2 ≤ t + s := by linarith [neg_abs_le s]
    have hhi : t + s ≤ 2 * t := by linarith [le_abs_self s, abs_nonneg s]
    have h₁ := Real.log_le_log (show 0 < t / 2 by positivity) hlo
    have h₂ := Real.log_le_log (zero_lt_one.trans_le hs) hhi
    rw [Real.log_div (by positivity) two_ne_zero] at h₁
    rw [Real.log_mul two_ne_zero (by positivity)] at h₂
    have hshift : |Real.log (t + s) - Real.log t| ≤ Real.log 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hst := (gammaBracket_sub_log_le hs).trans (div_le_self (by norm_num)
      (show 1 ≤ (t + s)^2 by nlinarith [sq_nonneg (t + s - 1)]))
    have hsplit : |gammaBracket (t + s) - Real.log (t + s)| ≤ 20 + |Real.log (2 * Real.pi)| := by
      rw [show gammaBracket (t + s) - Real.log (t + s) =
        (gammaBracket (t + s) - Real.log (t + s) + Real.log (2 * Real.pi)) -
          Real.log (2 * Real.pi) by ring]
      exact (abs_sub _ _).trans (add_le_add hst le_rfl)
    have hcap : |gammaBracket (t + s) - Real.log t| ≤ C := by
      rw [← sub_add_sub_cancel (gammaBracket (t + s)) (Real.log (t + s)) (Real.log t)]
      exact (abs_add_le _ _).trans (add_le_add hsplit hshift)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hlog, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hcap (inv_nonneg.mpr hlog.le)
  have ht := hsmall.add_const 1
  rw [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [sub_div, div_self (Real.log_pos ht).ne', sub_add_cancel]

/-- The archimedean contribution has coefficient one against any fixed
integrable transform with an integrable logarithmic moment. -/
theorem integral_gammaBracket_shift_smul_div_log {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} (hf : Integrable f)
    (hlog : Integrable (fun u : ℝ => ‖f u‖ * Real.log (3 + |u|))) :
    Tendsto (fun t : ℝ => ∫ u : ℝ, (gammaBracket (t + u) / Real.log t) • f u)
      atTop (𝓝 (∫ u : ℝ, f u)) := by
  obtain ⟨C, hC, hg⟩ := gammaBracket_growth
  let bound := fun u : ℝ => (2 * C) * ‖f u‖ + C * (‖f u‖ * Real.log (3 + |u|))
  apply tendsto_integral_filter_of_dominated_convergence bound
  · exact Filter.Eventually.of_forall fun t => (((continuous_gammaBracket.comp (continuous_const.add continuous_id)).div_const
        (Real.log t)).aestronglyMeasurable).smul hf.aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (max 3 (Real.exp 1))] with t ht
    exact Filter.Eventually.of_forall fun u => by
      have ht₃ := (le_max_left _ _).trans ht
      have ht₀ : 0 ≤ t := by linarith
      have htL : 1 ≤ Real.log t := by
        simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans ht)
      have htLp : 0 < Real.log t := zero_lt_one.trans_le htL
      have hprod : 3 + |t + u| ≤ (3 + t) * (3 + |u|) := by
        have h₁ := abs_add_le t u
        rw [abs_of_nonneg ht₀] at h₁
        nlinarith [abs_nonneg u, mul_nonneg ht₀ (abs_nonneg u)]
      have hlogprod := Real.log_le_log (show 0 < 3 + |t + u| by positivity) hprod
      rw [Real.log_mul (by positivity) (by positivity)] at hlogprod
      have hL₂ : Real.log (3 + t) ≤ 2 * Real.log t := by
        have h : 3 + t ≤ t^2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr ht₃) ht₀]
        exact (Real.log_le_log (by positivity) h).trans_eq (by rw [Real.log_pow]; norm_num)
      have hlogu : 0 ≤ Real.log (3 + |u|) := Real.log_nonneg (by linarith [abs_nonneg u])
      have hbound : |gammaBracket (t + u)| / Real.log t ≤ C * (2 + Real.log (3 + |u|)) := by
        apply (div_le_iff₀ htLp).mpr
        calc
          _ ≤ C * (Real.log (3 + t) + Real.log (3 + |u|)) :=
            (hg _).trans (mul_le_mul_of_nonneg_left hlogprod hC.le)
          _ ≤ C * (2 * Real.log t + Real.log (3 + |u|) * Real.log t) := by
            apply mul_le_mul_of_nonneg_left _ hC.le
            exact add_le_add hL₂ (le_mul_of_one_le_right hlogu htL)
          _ = _ := by ring
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos htLp]
      exact (mul_le_mul_of_nonneg_right hbound (norm_nonneg (f u))).trans_eq (by dsimp [bound]; ring)
  · exact (hf.norm.const_mul (2 * C)).add (hlog.const_mul C)
  · exact Filter.Eventually.of_forall fun u => by
      simpa only [one_smul] using (gammaBracket_shift_div_log_tendsto_one u).smul
        (tendsto_const_nhds (x := f u))

/-- The archimedean contribution has coefficient one against any fixed
integrable real transform with an integrable logarithmic moment. -/
theorem integral_gammaBracket_shift_div_log {f : ℝ → ℝ} (hf : Integrable f)
    (hlog : Integrable (fun u : ℝ => |f u| * Real.log (3 + |u|))) :
    Tendsto (fun t : ℝ => ∫ u : ℝ, f u * (gammaBracket (t + u) / Real.log t))
      atTop (𝓝 (∫ u : ℝ, f u)) := by
  simpa only [smul_eq_mul, mul_comm] using integral_gammaBracket_shift_smul_div_log hf
    (by simpa only [Real.norm_eq_abs] using hlog)

end GoldbachZeros
