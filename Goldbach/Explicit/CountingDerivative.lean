import Goldbach.Explicit.CoefficientTail
import Goldbach.Explicit.CoefficientUniform
import Goldbach.Explicit.LogMoments

/-! An effective integral bound for the derivative in the zero-counting error. -/

open MeasureTheory Set Filter
open scoped Interval
noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum

/-- The positive-ordinate test in the Stieltjes comparison. -/
def logarithmicCoefficient (lam t : ℝ) : ℝ :=
  ‖coefficient lam t‖^2 * Real.log (t + 3)

private theorem logarithmicCoefficient_deriv (lam : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    deriv (logarithmicCoefficient lam) t =
      deriv (fun x => ‖coefficient lam x‖^2) t * Real.log (t + 3) +
        ‖coefficient lam t‖^2 / (t + 3) := by
  have h := ((contDiff_coefficient_sq lam).differentiable (by norm_num) t).hasDerivAt
  have hh := (Real.hasDerivAt_log (show t + 3 ≠ 0 by linarith)).comp t
    ((hasDerivAt_id t).add_const 3)
  have hp := (h.mul hh).deriv
  change deriv ((fun x => ‖coefficient lam x‖^2) * fun x => Real.log (x + 3)) t = _
  simpa only [Function.comp_def, id_eq, mul_one, div_eq_mul_inv] using hp

/-- The absolute differentiated test with its zero-counting envelope. -/
def countErrorIntegrand (lam t : ℝ) : ℝ :=
  Real.log (t + 2) * |deriv (logarithmicCoefficient lam) t|

private theorem counting_log_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.log (t + 3) :=
  Real.log_nonneg (by linarith)

private theorem countErrorIntegrand_le {lam t : ℝ} (ht : 0 ≤ t) :
    countErrorIntegrand lam t ≤
      |deriv (fun x => ‖coefficient lam x‖^2) t| * (Real.log (t + 3))^2 +
        (‖coefficient lam t‖^2 / (t + 3)) * Real.log (t + 3) := by
  have hlog := counting_log_nonneg ht
  have hlog₂ : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
  have hlogle := Real.log_le_log (show 0 < t + 2 by linarith) (show t + 2 ≤ t + 3 by linarith)
  let h := fun x : ℝ => ‖coefficient lam x‖^2
  have he := abs_add_le (deriv h t * Real.log (t + 3)) (h t / (t + 3))
  have hquot : 0 ≤ h t / (t + 3) := div_nonneg (sq_nonneg _) (by linarith)
  rw [abs_mul, abs_of_nonneg hlog, abs_of_nonneg hquot] at he
  unfold countErrorIntegrand
  rw [logarithmicCoefficient_deriv lam ht]
  change Real.log (t + 2) * |deriv h t * Real.log (t + 3) + h t / (t + 3)| ≤ _
  calc
    _ ≤ Real.log (t + 2) * (|deriv h t| * Real.log (t + 3) + h t / (t + 3)) :=
      mul_le_mul_of_nonneg_left he hlog₂
    _ ≤ Real.log (t + 3) * (|deriv h t| * Real.log (t + 3) + h t / (t + 3)) := by
      have hhn : 0 ≤ h t := sq_nonneg _
      exact mul_le_mul_of_nonneg_right hlogle (by positivity)
    _ = _ := by ring

private theorem countErrorIntegrand_measurable (lam : ℝ) : Measurable (countErrorIntegrand lam) :=
  ((measurable_id.add_const _).log).mul (measurable_deriv _).abs

private theorem exp_profile_width_bounds {lam : ℝ} (hlam : 0 < lam) (hlam₁ : lam ≤ 1 / 10) :
    Real.exp lam ≤ 2 ∧ Real.exp (lam / 2) ≤ 11 / 10 := by
  constructor
  · exact (Real.exp_bound_div_one_sub_of_interval hlam.le (by linarith)).trans
      ((div_le_iff₀ (by linarith : 0 < 1 - lam)).2 (by linarith))
  · exact (Real.exp_bound_div_one_sub_of_interval (by linarith : 0 ≤ lam / 2) (by linarith)).trans
      ((div_le_iff₀ (by linarith : 0 < 1 - lam / 2)).2 (by linarith))

private theorem log_add_compare {t U : ℝ} (hU : 3 ≤ U) (ht : 0 ≤ t) (h : t ≤ U) :
    Real.log (t + 3) ≤ Real.log U + 1 := by
  have hU₀ : 0 < U := by linarith
  have hp := Real.log_le_log (show 0 < t + 3 by linarith) (show t + 3 ≤ 2 * U by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hU₀.ne'] at hp
  linarith [Real.log_two_lt_d9]

private theorem small_count_error {lam : ℝ} (hlam : 0 < lam) (hlam₁ : lam ≤ 1 / 10) :
    let T := lam⁻¹
    let b := Real.log T + 1
    IntegrableOn (countErrorIntegrand lam) (Ioc 0 T) ∧
      (∫ t in Ioc 0 T, countErrorIntegrand lam t) ≤ 3 * lam^2 * b^2 := by
  let T := lam⁻¹
  let b := Real.log T + 1
  let r (t : ℝ) := Real.log (t + 3) / (t + 3)
  let H (t : ℝ) := 2 * lam^3 * b^2 + 2 * lam^2 * r t
  change IntegrableOn (countErrorIntegrand lam) (Ioc 0 T) ∧
    (∫ t in Ioc 0 T, countErrorIntegrand lam t) ≤ 3 * lam^2 * b^2
  have hT : 0 < T := inv_pos.mpr hlam
  have hT₃ : 3 ≤ T := by
    unfold T
    rw [← one_div]
    exact (le_div_iff₀ hlam).mpr (by linarith)
  have hb : 0 ≤ b := by
    have hL := Real.log_nonneg (show 1 ≤ T by linarith)
    unfold b
    linarith
  have hexp := (exp_profile_width_bounds hlam hlam₁).1
  have hri : IntervalIntegrable r volume 0 T := by
    refine ContinuousOn.intervalIntegrable_of_Icc hT.le ?_
    have h : Continuous (fun t : ℝ => t + 3) := by fun_prop
    have h₀ (t : ℝ) (ht : t ∈ Icc 0 T) : t + 3 ≠ 0 := by linarith [ht.1]
    exact (h.continuousOn.log h₀).div h.continuousOn h₀
  have hHi : IntervalIntegrable H volume 0 T :=
    intervalIntegrable_const.add (hri.const_mul _)
  have hpoint (t : ℝ) (ht : t ∈ Ioc 0 T) : countErrorIntegrand lam t ≤ H t := by
    have hlog := log_add_compare hT₃ ht.1.le ht.2
    have hlog₀ := counting_log_nonneg ht.1.le
    have hder := (coefficient_sq_uniform_deriv_le hlam.le t).trans
      (mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ lam^3))
    have hsq := (coefficient_sq_uniform_le hlam.le t).trans
      (mul_le_mul_of_nonneg_left hexp (sq_nonneg lam))
    have h₁ := mul_le_mul hder (pow_le_pow_left₀ hlog₀ hlog 2) (sq_nonneg _)
      (by positivity : 0 ≤ lam^3 * 2)
    have h₂ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsq
      (show 0 ≤ t + 3 by linarith [ht.1])) hlog₀
    apply (countErrorIntegrand_le ht.1.le).trans
    dsimp [H, r]
    simp only [div_eq_mul_inv] at h₂ ⊢
    nlinarith only [h₁, h₂]
  have hae := (ae_restrict_mem (μ := volume) (s := Ioc 0 T) measurableSet_Ioc).mono hpoint
  have hfi : IntegrableOn (countErrorIntegrand lam) (Ioc 0 T) := by
    refine hHi.1.mono' (countErrorIntegrand_measurable lam).aestronglyMeasurable ?_
    filter_upwards [hae, ae_restrict_mem (μ := volume) (s := Ioc 0 T) measurableSet_Ioc] with t ht hm
    have hn : 0 ≤ countErrorIntegrand lam t := mul_nonneg (Real.log_nonneg (by linarith [hm.1])) (abs_nonneg _)
    rwa [Real.norm_of_nonneg hn]
  refine ⟨hfi, (integral_mono_ae hfi hHi.1 hae).trans ?_⟩
  have hrEval : (∫ t in (0 : ℝ)..T, r t) =
      ((Real.log (T + 3))^2 - (Real.log 3)^2) / 2 := by
    have hd (t : ℝ) (ht : t ∈ uIcc 0 T) :
        HasDerivAt (fun v : ℝ => (Real.log (v + 3))^2 / 2) (r t) t := by
      rw [uIcc_of_le hT.le] at ht
      have h := (((Real.hasDerivAt_log (show t + 3 ≠ 0 by linarith [ht.1])).comp t
        ((hasDerivAt_id t).add_const 3)).pow 2).div_const 2
      convert h using 1 <;> first | rfl | (funext u; rfl) |
        (simp only [r, Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp_def, id_eq, mul_one]; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hri, zero_add]
    ring
  have hLogSq := pow_le_pow_left₀ (counting_log_nonneg hT.le) (log_add_compare hT₃ hT.le le_rfl) 2
  rw [← intervalIntegral.integral_of_le hT.le]
  unfold H
  rw [intervalIntegral.integral_add intervalIntegrable_const (hri.const_mul (2 * lam^2)),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hrEval]
  simp only [sub_zero, smul_eq_mul]
  have hwidth : T * (2 * lam^3 * b^2) = 2 * lam^2 * b^2 := by unfold T; field_simp [hlam.ne']
  rw [hwidth]
  nlinarith only [mul_le_mul_of_nonneg_left hLogSq (sq_nonneg lam),
    mul_nonneg (sq_nonneg lam) (sq_nonneg (Real.log 3))]

private theorem integrable_exp_square :
    IntegrableOn (fun s : ℝ => (1 + s)^2 * Real.exp (-s)) (Ioi (0 : ℝ)) ∧
      (∫ s in Ioi (0 : ℝ), (1 + s)^2 * Real.exp (-s)) = 5 := by
  have h₀ := exponential_moment 0
  have h₁ := exponential_moment 1
  have h₂ := exponential_moment 2
  norm_num [Nat.factorial] at h₀ h₁ h₂
  have he : (fun s : ℝ => (1 + s)^2 * Real.exp (-s)) =
      fun s => (Real.exp (-s) + 2 * (s * Real.exp (-s))) + s^2 * Real.exp (-s) := by
    funext s
    ring
  rw [he]
  have ha : IntegrableOn (fun s : ℝ => Real.exp (-s) + 2 * (s * Real.exp (-s))) (Ioi 0) :=
    h₀.1.add (h₁.1.const_mul 2)
  refine ⟨ha.add h₂.1, ?_⟩
  rw [integral_add ha h₂.1, integral_add h₀.1 (h₁.1.const_mul (2 : ℝ)), integral_const_mul,
    integral_exp_neg_Ioi_zero, h₁.2, h₂.2]
  norm_num

private theorem tail_count_error {lam : ℝ} (hlam : 0 < lam) (hlam₁ : lam ≤ 1 / 10) :
    let T := lam⁻¹
    let b := Real.log T + 1
    IntegrableOn (countErrorIntegrand lam) (Ioi T) ∧
      (∫ t in Ioi T, countErrorIntegrand lam t) ≤ 90 * lam^2 * b^2 := by
  let T := lam⁻¹
  let b := Real.log T + 1
  let E (s : ℝ) := T * Real.exp s
  let H (s : ℝ) := 18 * lam^2 * b^2 * ((1 + s)^2 * Real.exp (-s))
  change IntegrableOn (countErrorIntegrand lam) (Ioi T) ∧
    (∫ t in Ioi T, countErrorIntegrand lam t) ≤ 90 * lam^2 * b^2
  have hT : 0 < T := inv_pos.mpr hlam
  have hT₃ : 3 ≤ T := by
    unfold T
    rw [← one_div]
    exact (le_div_iff₀ hlam).mpr (by linarith)
  have hb : 1 ≤ b := by
    have hL := Real.log_nonneg (show 1 ≤ T by linarith)
    unfold b
    linarith
  have ht₀ (s : ℝ) : 0 < E s := mul_pos hT (Real.exp_pos s)
  have hE : InjOn E (Ioi (0 : ℝ)) := by
    intro u _ v _ h
    exact Real.exp_injective (mul_left_cancel₀ hT.ne' h)
  have hI : E '' Ioi (0 : ℝ) = Ioi T := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      have he := mul_lt_mul_of_pos_left (Real.one_lt_exp_iff.mpr hs) hT
      apply mem_Ioi.mpr
      simpa only [E, mul_one] using he
    · intro ht
      have ht' : 0 < t := hT.trans ht
      have hratio : 1 < t / T := (lt_div_iff₀ hT).2 (by simpa using ht)
      refine ⟨Real.log (t / T), Real.log_pos hratio, ?_⟩
      unfold E
      rw [Real.exp_log (div_pos ht' hT), mul_div_cancel₀ _ hT.ne']
  have hd (s : ℝ) (_ : s ∈ Ioi (0 : ℝ)) : HasDerivWithinAt E (E s) (Ioi 0) s :=
    ((Real.hasDerivAt_exp s).const_mul T).hasDerivWithinAt
  have hpoint (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      E s * countErrorIntegrand lam (E s) ≤ H s := by
    let t := E s
    let D := b * (1 + s)
    have ht : 0 < t := ht₀ s
    have hs₀ : 0 < s := hs
    have hTt : T ≤ t := by
      have hh := mul_le_mul_of_nonneg_left (Real.one_le_exp hs₀.le) hT.le
      simpa only [E, t, mul_one] using hh
    have hInv : t⁻¹ ≤ lam := by
      have h := inv_anti₀ hT hTt
      simpa only [T, inv_inv] using h
    have hlog : Real.log (t + 3) ≤ D := by
      have h₁ := log_add_compare (hT₃.trans hTt) ht.le le_rfl
      have h₂ : Real.log t = Real.log T + s := by
        dsimp [t, E]
        rw [Real.log_mul hT.ne' (Real.exp_pos _).ne', Real.log_exp]
      unfold D
      rw [h₂] at h₁
      unfold b at hb ⊢
      nlinarith only [h₁, mul_nonneg (show 0 ≤ Real.log T by linarith) hs₀.le]
    have hD : 1 ≤ D := by
      unfold D
      nlinarith only [hb, mul_nonneg (zero_le_one.trans hb) hs₀.le]
    have hDsq : D ≤ D^2 := by nlinarith [sq_nonneg (D - 1)]
    have hlog₀ := counting_log_nonneg ht.le
    have hder : |deriv (fun x => ‖coefficient lam x‖^2) t| ≤ 13 * lam / t^2 := by
      have hq := coefficient_sq_tail_deriv_le hlam.le (exp_profile_width_bounds hlam hlam₁).2 ht
      refine hq.trans ?_
      have he : 10 / t^3 = (10 / t^2) * t⁻¹ := by field_simp [ht.ne']
      rw [he]
      have hm := mul_le_mul_of_nonneg_left hInv (show 0 ≤ 10 / t^2 by positivity)
      simp only [div_eq_mul_inv] at hm ⊢
      nlinarith only [hm]
    have hb₅ : ‖coefficient lam t‖^2 / (t + 3) ≤ 5 * lam / t^2 := by
      calc
        _ ≤ (5 / t^2) / (t + 3) := div_le_div_of_nonneg_right
          (coefficient_sq_tail_le (exp_profile_width_bounds hlam hlam₁).2 ht) (by linarith)
        _ ≤ (5 / t^2) / t := div_le_div_of_nonneg_left (by positivity) ht (by linarith)
        _ ≤ _ := by
          rw [div_eq_mul_inv (5 / t^2) t]
          have h := mul_le_mul_of_nonneg_left hInv (show 0 ≤ 5 / t^2 by positivity)
          simpa only [div_eq_mul_inv, mul_assoc, mul_comm lam] using h
    have hcalc : countErrorIntegrand lam t ≤ 18 * lam / t^2 * D^2 := by
      have h₁ := mul_le_mul hder (pow_le_pow_left₀ hlog₀ hlog 2) (sq_nonneg _)
        (show 0 ≤ 13 * lam / t^2 by positivity)
      have h₂ := mul_le_mul hb₅ (hlog.trans hDsq) hlog₀
        (show 0 ≤ 5 * lam / t^2 by positivity)
      apply (countErrorIntegrand_le ht.le).trans
      simp only [div_eq_mul_inv] at h₁ h₂ ⊢
      nlinarith only [h₁, h₂]
    calc
      _ ≤ t * (18 * lam / t^2 * D^2) := mul_le_mul_of_nonneg_left hcalc ht.le
      _ = H s := by
        dsimp [H, D, t, E, T]
        rw [Real.exp_neg]
        field_simp [hlam.ne', (Real.exp_pos s).ne'] <;> ring
  have hf : Measurable (fun s => E s * countErrorIntegrand lam (E s)) :=
    (by unfold E; fun_prop : Measurable E).mul ((countErrorIntegrand_measurable lam).comp
      (by unfold E; fun_prop))
  have hHi : IntegrableOn H (Ioi (0 : ℝ)) := integrable_exp_square.1.const_mul _
  have hae := (ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi).mono hpoint
  have hfi : IntegrableOn (fun s => E s * countErrorIntegrand lam (E s)) (Ioi (0 : ℝ)) := by
    refine hHi.mono' hf.aestronglyMeasurable ?_
    filter_upwards [hae, ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi] with s hs hms
    have hn : 0 ≤ countErrorIntegrand lam (E s) :=
      mul_nonneg (Real.log_nonneg (by linarith [ht₀ s])) (abs_nonneg _)
    rwa [Real.norm_of_nonneg (mul_nonneg (ht₀ s).le hn)]
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hE
    (countErrorIntegrand lam)
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hE
    (countErrorIntegrand lam)
  simp only [hI, abs_of_pos (ht₀ _), smul_eq_mul] at hi he
  refine ⟨hi.mpr hfi, ?_⟩
  rw [he]
  refine (integral_mono_ae hfi hHi hae).trans_eq ?_
  unfold H
  rw [integral_const_mul, integrable_exp_square.2]
  ring

/-- Uniform counting-error integral. The coefficient 100 leaves slack in
both the finite interval and the exponentially transformed tail. -/
theorem counting_derivative_integral_le {lam : ℝ} (hlam : 0 < lam) (hlam₁ : lam ≤ 1 / 10) :
    IntegrableOn (countErrorIntegrand lam) (Ioi (0 : ℝ)) ∧
      (∫ t in Ioi (0 : ℝ), countErrorIntegrand lam t) ≤
        100 * lam^2 * (Real.log lam⁻¹ + 1)^2 := by
  let T := lam⁻¹
  have hT : 0 < T := inv_pos.mpr hlam
  have hsplit := Ioc_union_Ioi_eq_Ioi hT.le
  obtain ⟨hi, hsmall⟩ := small_count_error hlam hlam₁
  obtain ⟨hj, htail⟩ := tail_count_error hlam hlam₁
  change IntegrableOn (countErrorIntegrand lam) (Ioc 0 T) at hi
  change IntegrableOn (countErrorIntegrand lam) (Ioi T) at hj
  have hd : Disjoint (Ioc (0 : ℝ) T) (Ioi T) :=
    disjoint_left.mpr (fun _ hs ht => ht.not_ge hs.2)
  rw [← hsplit]
  refine ⟨hi.union hj, ?_⟩
  rw [setIntegral_union hd measurableSet_Ioi hi hj]
  nlinarith only [hsmall, htail, mul_nonneg (sq_nonneg lam) (sq_nonneg (Real.log lam⁻¹ + 1))]

end GoldbachExplicit
