import Goldbach.FirstMoment
import Goldbach.Gaussian

open Filter MeasureTheory Set
open scoped Topology

noncomputable section
namespace GoldbachConcrete

/-- The remaining sharp analytic estimate, in the Gaussian parameter
`b = 1/V²`. It is stated explicitly as a proposition. -/
def GaussianSecondMoment : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 / 2 → ∀ b : ℝ, 0 < b →
    ∀ c : ℝ, 1 < c → ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      (relativeWidth c x)^2 *
        (∫ y in Icc (a * x) ((1 - a) * x),
          GoldbachGaussian.weight b (Real.log (y / x)) * (density (relativeWidth c x) y - 1)^2)
      ≤ (1 + ε) * relativeWidth c x * (Real.log x)^2

private theorem weight_lower {a b m x y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hx : 0 < x) (hmin : b * (Real.log a)^2 ≤ -Real.log m)
    (hy : y ∈ Icc (a * x) ((1 - a) * x)) :
    m ≤ GoldbachGaussian.weight b (Real.log (y / x)) := by
  have hlo : a ≤ y / x := (le_div_iff₀ hx).mpr hy.1
  have hy0 := ha.trans_le hlo
  have hhi : y / x ≤ 1 := by
    apply (div_le_iff₀ hx).mpr
    nlinarith [hy.2, mul_nonneg ha.le hx.le]
  have hlog₁ := Real.log_le_log ha hlo
  have hlog₂ := Real.log_nonpos hy0.le hhi
  have hsq : (Real.log (y / x))^2 ≤ (Real.log a)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog₁)
      (show 0 ≤ -Real.log a - Real.log (y / x) by linarith)]
  rw [← Real.exp_log hm, GoldbachGaussian.weight]
  apply Real.exp_le_exp.mpr
  have h := (mul_le_mul_of_nonneg_left hsq hb.le).trans hmin
  linarith

private theorem gaussian_weighted_error_integrable {c x b : ℝ} (hb : 0 < b)
    (hd : 0 < relativeWidth c x) (ha : 0 < trim c * x) :
    Integrable (fun y => GoldbachGaussian.weight b (Real.log (y / x)) *
      (density (relativeWidth c x) y - 1)^2) (regionMeasure c x) := by
  have hi := integrableOn_density_error (v := (1 - trim c) * x) hd ha
  have hg : Measurable (fun y : ℝ => GoldbachGaussian.weight b (Real.log (y / x))) := by
    apply (show Continuous (GoldbachGaussian.weight b) by unfold GoldbachGaussian.weight; fun_prop).measurable.comp
    exact Real.measurable_log.comp (measurable_id.div_const x)
  refine hi.mono' (hg.mul (((measurable_density hd).sub measurable_const).pow_const 2)).aestronglyMeasurable ?_
  filter_upwards with y
  have hw₀ : 0 ≤ GoldbachGaussian.weight b (Real.log (y / x)) := (Real.exp_pos _).le
  have hw₁ : GoldbachGaussian.weight b (Real.log (y / x)) ≤ 1 := by
    unfold GoldbachGaussian.weight
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw₀ (sq_nonneg _))]
  exact mul_le_of_le_one_left (sq_nonneg _) hw₁

/-- Removal of the Gaussian on the trimmed interval and comparison with
the strict midpoint between the first and second moments. -/
theorem secondMomentInput_of_gaussian (hG : GaussianSecondMoment) : SecondMomentInput := by
  intro c hc
  let a := trim c
  let k := (1 - 2 * a + 1 / c) / 2
  obtain ⟨ha, hgap⟩ := trim_pos_and_gap hc
  have hc0 : 0 < c := zero_lt_one.trans hc
  have ha' : a < 1 / 2 := by
    have h : 0 < (1 : ℝ) / c := by positivity
    dsimp [a]
    linarith
  have hk : 1 / c < k := by
    dsimp [k, a]
    linarith
  have hkc : 1 < c * k := by
    have h := (div_lt_iff₀ hc0).mp hk
    linarith
  have hkc0 : 0 < c * k := zero_lt_one.trans hkc
  let m := (1 + 1 / (c * k)) / 2
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hm1 : m < 1 := by
    have h : (1 : ℝ) / (c * k) < 1 := (div_lt_iff₀ hkc0).mpr (by simpa using hkc)
    dsimp [m]
    linarith
  have hmck : 1 < m * (c * k) := by
    have h : m * (c * k) = (c * k + 1) / 2 := by
      dsimp only [m]
      rw [div_mul_eq_mul_div, add_mul, one_mul, div_mul_cancel₀ _ hkc0.ne']
    rw [h]
    linarith
  let ε := (m * (c * k) - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let b := -Real.log m / (1 + (Real.log a)^2)
  have hneg : 0 < -Real.log m := neg_pos.mpr (Real.log_neg hm0 hm1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbmin : b * (Real.log a)^2 ≤ -Real.log m := by
    dsimp [b]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 1 + (Real.log a)^2 by positivity)).mpr
    nlinarith only [hneg]
  apply eventually_atTop.mp
  filter_upwards [eventually_gt_atTop (1 : ℝ), hG a ha ha' b hb c hc ε hε] with x hx hg
  let d := relativeWidth c x
  let E := fun y => (density d y - 1)^2
  let μ := regionMeasure c x
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hd : 0 < d := relativeWidth_pos hc0 hx
  have hax : 0 < a * x := mul_pos ha hx0
  have hi : Integrable E μ := integrableOn_density_error hd hax
  have hw := gaussian_weighted_error_integrable hb hd hax
  have hcomp : m * (∫ y, E y ∂μ) ≤
      ∫ y, GoldbachGaussian.weight b (Real.log (y / x)) * E y ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hi.const_mul m) hw
    filter_upwards [ae_restrict_mem (μ := volume) (s := region c x) measurableSet_Icc] with y hy
    exact mul_le_mul_of_nonneg_right (weight_lower ha hb hm0 hx0 hbmin hy) (sq_nonneg _)
  have hscale : d * (Real.log x)^2 = d^2 * (x / c) := by
    dsimp [d, relativeWidth, window]
    field_simp [hc0.ne', hx0.ne']
  have hnorm : d^2 * (m * (∫ y, E y ∂μ)) ≤ d^2 * ((1 + ε) * (x / c)) := by
    calc
      _ ≤ d^2 * (∫ y, GoldbachGaussian.weight b (Real.log (y / x)) * E y ∂μ) :=
        mul_le_mul_of_nonneg_left hcomp (sq_nonneg _)
      _ ≤ (1 + ε) * d * (Real.log x)^2 := hg
      _ = _ := by rw [mul_assoc, hscale]; ring
  have hrest := le_of_mul_le_mul_left hnorm (sq_pos_of_pos hd)
  have hε' : 1 + ε ≤ m * (c * k) := by dsimp [ε]; linarith
  have hcmp : (1 + ε) / c ≤ m * k := (div_le_iff₀ hc0).mpr (by
    calc
      1 + ε ≤ m * (c * k) := hε'
      _ = m * k * c := by ring)
  have hlast : (∫ y, E y ∂μ) ≤ k * x := by
    apply le_of_mul_le_mul_left _ hm0
    calc
      _ ≤ (1 + ε) * (x / c) := hrest
      _ = ((1 + ε) / c) * x := by ring
      _ ≤ (m * k) * x := mul_le_mul_of_nonneg_right hcmp hx0.le
      _ = _ := by ring
  obtain ⟨herr, heq⟩ := errorIntegrand_integral (c := c) hax hd
  refine ⟨herr, ?_⟩
  rw [heq]
  change 2 * (∫ y, E y ∂μ) ≤ midpoint c x
  have hmid : midpoint c x = 2 * (k * x) := by dsimp [midpoint, k, a]; ring
  rw [hmid]
  exact mul_le_mul_of_nonneg_left hlast (by norm_num)

end GoldbachConcrete
