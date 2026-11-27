import Goldbach.Explicit.EffectiveTheta
import Goldbach.Explicit.WeightMass
import Goldbach.Explicit.WeightedFirstMoment

/-! The lower bound for the explicit cosine-weighted variance. -/

open MeasureTheory Set
noncomputable section

namespace GoldbachExplicit

open GoldbachConcrete

/-- The left endpoint of the reflected interval, with `x = exp L`. -/
def trimmedEndpoint (L : ℝ) : ℝ := Real.exp L / L^2

/-- The normalized variance for the explicit Goldbach argument. -/
def weightedVariance (L : ℝ) : ℝ :=
  delta L ^ 2 * ∫ y in Icc (trimmedEndpoint L) (Real.exp L - trimmedEndpoint L),
    upperWeight (bandwidth L) (Real.exp L) y * (density (delta L) y - 1)^2

/-- The unnormalized weighted first-moment error on the explicit interval. -/
private theorem explicit_firstMoment_abs_le (hRH : RiemannHypothesis) {L : ℝ} (hL : 28 ≤ L) :
    |∫ y in Icc (trimmedEndpoint L) (Real.exp L - trimmedEndpoint L),
      reflectedWeight (bandwidth L) (Real.exp L) y * (density (delta L) y - 1)| ≤
        3 * Real.exp (3 * L / 4) := by
  let x := Real.exp L
  let A := trimmedEndpoint L
  let d := delta L
  let E := (3 / 2) * Real.exp (3 * L / 4)
  have hL₀ : 0 < L := by linarith
  have hx : 0 < x := Real.exp_pos _
  have hL₂ : 0 < L^2 := by positivity
  have hA₀ : 0 < A := div_pos hx hL₂
  have hAmin : 16 ≤ Real.log A := by
    change 16 ≤ Real.log (Real.exp L / L^2)
    rw [Real.log_div hx.ne' hL₂.ne', Real.log_exp, Real.log_pow]
    norm_cast
    linarith [log_le_sixth_of_ge_28 hL]
  have hA₂ : 2 ≤ A := calc
    _ ≤ Real.exp 16 := by linarith [Real.add_one_le_exp 16]
    _ ≤ Real.exp (Real.log A) := Real.exp_le_exp.mpr hAmin
    _ = _ := Real.exp_log hA₀
  have hAx : A ≤ x / 2 :=
    div_le_div_of_nonneg_left hx.le (by norm_num) (by nlinarith [sq_nonneg (L - 28)])
  have hd : 0 < d := delta_pos_of_pos hL₀
  have hdx : d * x = L^2 := by
    simp [d, delta, x, Real.exp_neg, (Real.exp_pos L).ne']
  have hp : L^4 ≤ x := by
    have he : Real.exp (4 * Real.log L) ≤ Real.exp L :=
      Real.exp_le_exp.mpr (by linarith [log_le_sixth_of_ge_28 hL])
    rwa [show (4 : ℝ) * Real.log L = (4 : ℕ) * Real.log L by norm_num,
      Real.exp_nat_mul, Real.exp_log hL₀] at he
  have hdA : d * x ≤ A := by
    change d * x ≤ x / L^2
    apply (le_div_iff₀ hL₂).2
    rw [hdx, ← pow_add]
    exact hp
  have hB : (1 + d) * (x - A) ≤ x := by
    nlinarith only [hdA, mul_nonneg hd.le hA₀.le]
  have hθ (t : ℝ) (ht : t ∈ Icc A ((1 + d) * (x - A))) : |Chebyshev.theta t - t| ≤ E := by
    have ht₀ : 0 < t := hA₀.trans_le ht.1
    have hlo := hAmin.trans (Real.log_le_log hA₀ ht.1)
    have hhi : Real.log t ≤ L := by
      rw [← Real.log_exp L]
      exact Real.log_le_log ht₀ (ht.2.trans hB)
    have h := theta_exp_error_le_three_halves hRH hlo
    rw [Real.exp_log ht₀] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  have hmoment := weighted_firstMoment_abs_le (bandwidth_pos_of_pos hL₀) hA₂ hAx hd
    (show 0 ≤ E by dsimp [E]; positivity) hθ
  simpa only [E, ← mul_assoc, show (2 : ℝ) * (3 / 2) = 3 by norm_num] using hmoment

theorem explicit_firstMoment_abs_lt (hRH : RiemannHypothesis) {L : ℝ} (hL : 42 ≤ L) :
    |∫ y in Icc (trimmedEndpoint L) (Real.exp L - trimmedEndpoint L),
      reflectedWeight (bandwidth L) (Real.exp L) y * (density (delta L) y - 1)| <
        trimmedEndpoint L / 2 := by
  refine (explicit_firstMoment_abs_le hRH (by linarith : 28 ≤ L)).trans_lt ?_
  change 3 * Real.exp (3 * L / 4) < Real.exp L / L^2 / 2
  have hp := Real.exp_pos (3 * L / 4)
  linarith only [first_moment_error_lt_trimmed_endpoint hL, hp]

private theorem explicit_variance_gt_of_firstMoment {L m c : ℝ} (hL : 28 ≤ L)
    (hmoment : |∫ y in Icc (trimmedEndpoint L) (Real.exp L - trimmedEndpoint L),
      reflectedWeight (bandwidth L) (Real.exp L) y * (density (delta L) y - 1)| <
        m * trimmedEndpoint L / 2)
    (hcoef : (6361 / 1000 : ℝ) + (2 + m) / L ≤ c)
    (hn : ¬ HasGoldbach (Real.exp L) (L^2)) :
    delta L * (L^2 - c * L) < weightedVariance L := by
  let x := Real.exp L
  let A := trimmedEndpoint L
  let d := delta L
  let V := bandwidth L
  let w := reflectedWeight V x
  let J := Icc A (x - A)
  let K := (Real.log 2)^2 + 2 * Real.log 2 + 2
  have hL₀ : 0 < L := by linarith
  have hx : 0 < x := Real.exp_pos _
  have hA₀ : 0 < A := div_pos hx (by positivity)
  have hAx : A ≤ x / 2 :=
    div_le_div_of_nonneg_left hx.le (by norm_num) (by nlinarith [sq_nonneg (L - 28)])
  have hd : 0 < d := delta_pos_of_pos hL₀
  have hV : 0 < V := bandwidth_pos_of_pos hL₀
  have hdx : d * x = L^2 := by
    simp [d, delta, x, Real.exp_neg, (Real.exp_pos L).ne']
  have hw : Measurable w :=
    (continuous_cosineWeight hV).measurable.comp
      ((measurable_const.div (measurable_id.min (measurable_const.sub measurable_id))).log)
  have hw_norm : ∀ᵐ y ∂volume.restrict J, ‖w y‖ ≤ 1 := by
    filter_upwards with y
    have hn₀ : 0 ≤ w y := cosineWeight_nonneg hV _
    rw [Real.norm_of_nonneg hn₀]
    exact cosineWeight_le_one hV _
  have hwi : IntegrableOn w J := by
    have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) J := integrableOn_const measure_Icc_lt_top.ne
    exact hc.mono' hw.aestronglyMeasurable (by simpa only [norm_one] using hw_norm)
  have hdi : IntegrableOn (fun y => w y * density d y) J :=
    (integrableOn_density hd hA₀).bdd_mul hw.aestronglyMeasurable hw_norm
  have hdiff : (∫ y in J, w y * (density d y - 1)) =
      (∫ y in J, w y * density d y) - ∫ y in J, w y := by
    simp_rw [mul_sub, mul_one]
    exact integral_sub hdi hwi
  change |∫ y in J, w y * (density d y - 1)| < m * A / 2 at hmoment
  rw [hdiff] at hmoment
  have hV₂ : V^2 = 3 * L := Real.sq_sqrt (by positivity)
  have hloss : Real.pi^2 / (2 * V^2) * (x * K) =
      (Real.pi^2 / 6 * K) / L * x := by
    rw [hV₂]
    field_simp [hL₀.ne']
    ring
  have hmass := reflected_weight_mass_ge hV hA₀ hAx
  change x - 2 * A - (Real.pi^2 / (2 * V^2)) * (x * K) ≤ ∫ y in J, w y at hmass
  rw [hloss] at hmass
  have hconst : (Real.pi^2 / 6 * K) / L * x ≤ (6361 / 1000 : ℝ) / L * x :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right cosine_loss_constant_lt.le hL₀.le) hx.le
  have hcompare : x - c * x / L ≤ x - (2 + m) * A - (6361 / 1000 : ℝ) / L * x := by
    have h := mul_le_mul_of_nonneg_right hcoef (div_pos hx hL₀).le
    have he : ((6361 / 1000 : ℝ) + (2 + m) / L) * (x / L) =
        (6361 / 1000 : ℝ) / L * x + (2 + m) * A := by
      change _ = (6361 / 1000 : ℝ) / L * x + (2 + m) * (x / L^2)
      field_simp [hL₀.ne']
    rw [he, ← mul_div_assoc] at h
    linarith only [h]
  have hn' : ¬ HasGoldbach x (d * x) := by simpa only [hdx] using hn
  have hreflect := weighted_reflection_of_no_goldbach hV hA₀ hd hn'
  change 2 * (∫ y in J, w y * density d y) - (∫ y in J, w y) ≤
    ∫ y in J, upperWeight V x y * (density d y - 1)^2 at hreflect
  have hmain : x - c * x / L < ∫ y in J, upperWeight V x y * (density d y - 1)^2 := by
    linarith only [hreflect, hcompare, hmass, hconst, (abs_lt.mp hmoment).1,
      show (2 + m) * A = 2 * A + m * A by ring]
  have hfactor : d^2 * (x - c * x / L) = d * (L^2 - c * L) := by
    calc
      _ = d * (d * x - c * (d * x) / L) := by ring
      _ = _ := by rw [hdx]; field_simp [hL₀.ne']
  change d * (L^2 - c * L) < d^2 * (∫ y in J, upperWeight V x y * (density d y - 1)^2)
  rw [← hfactor]
  exact mul_lt_mul_of_pos_left hmain (sq_pos_of_pos hd)

/-- The original lower variance bound. -/
theorem explicit_variance_gt_of_no_goldbach (hRH : RiemannHypothesis) {L : ℝ} (hL : 42 ≤ L)
    (hn : ¬ HasGoldbach (Real.exp L) (L^2)) :
    delta L * (L^2 - 7 * L) < weightedVariance L := by
  refine explicit_variance_gt_of_firstMoment (m := 1) (by linarith : 28 ≤ L)
    (by simpa only [one_mul] using explicit_firstMoment_abs_lt hRH hL) ?_ hn
  have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) (by norm_num) hL
  norm_num
  linarith

/-- The lower variance bound with the first-moment loss at the earlier cutoff. -/
theorem explicit_variance_gt_of_no_goldbach_of_ge_28 (hRH : RiemannHypothesis)
    {L : ℝ} (hL : 28 ≤ L) (hn : ¬ HasGoldbach (Real.exp L) (L^2)) :
    delta L * (L^2 - (53 / 8) * L) < weightedVariance L := by
  refine explicit_variance_gt_of_firstMoment (m := 5) hL
    ((explicit_firstMoment_abs_le hRH hL).trans_lt ?_) ?_ hn
  · change 3 * Real.exp (3 * L / 4) < 5 * (Real.exp L / L^2) / 2
    linarith only [first_moment_error_lt_five_trimmed hL]
  · have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 7) (by norm_num) hL
    norm_num
    linarith

end GoldbachExplicit
