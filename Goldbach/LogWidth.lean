import Goldbach.FirstMoment

open Asymptotics Filter
open scoped Topology

noncomputable section
namespace GoldbachConcrete

/-- The additive width in the log coordinate. -/
def logWidth (c x : ℝ) : ℝ := Real.log (1 + relativeWidth c x)

theorem logWidth_div_relativeWidth_tendsto_one {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => logWidth c x / relativeWidth c x) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add (relativeWidth_tendsto_zero c)
  rw [add_zero] at h
  have hlo := (tendsto_const_nhds (x := (1 : ℝ))).div h one_ne_zero
  rw [div_one] at hlo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo (tendsto_const_nhds (x := (1 : ℝ))) ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    let d := relativeWidth c x
    have hd := relativeWidth_pos hc hx
    have hd₁ : 0 < 1 + d := by linarith
    have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hd₁)
    rw [Real.log_inv] at hlog
    change 1 / (1 + d) ≤ Real.log (1 + d) / d
    rw [le_div_iff₀ hd]
    have he : 1 - (1 + d)⁻¹ = 1 / (1 + d) * d := by
      field_simp [hd₁.ne']
      ring
    linarith
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    let d := relativeWidth c x
    have hd := relativeWidth_pos hc hx
    change Real.log (1 + d) / d ≤ 1
    rw [div_le_iff₀ hd, one_mul]
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + d by linarith)]

set_option maxHeartbeats 500000 in
theorem logWidth_log_inv_div_log_tendsto_one {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => Real.log (1 / logWidth c x) / Real.log x) atTop (𝓝 1) := by
  let D := relativeWidth c
  let L := logWidth c
  have hL := logWidth_div_relativeWidth_tendsto_one hc
  have hres : Tendsto (fun x => Real.log (L x / D x)) atTop (𝓝 0) := by
    have ht := (Real.continuousAt_log one_ne_zero).tendsto.comp hL
    simpa only [Function.comp_def, Real.log_one] using ht
  have hi : Tendsto (fun x => (Real.log x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hconst : Tendsto (fun x => Real.log c / Real.log x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul (Real.log c)
  have hloglog : Tendsto (fun x => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) := by
    have ht := (isLittleO_iff_tendsto (f := Real.log) (g := id) (fun x hx => by
      change x = 0 at hx
      simp [hx])).mp Real.isLittleO_log_id_atTop
    simpa only [Function.comp_def, id_eq] using ht.comp Real.tendsto_log_atTop
  have hresdiv : Tendsto (fun x => Real.log (L x / D x) / Real.log x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hres.mul hi
  have ht := (((tendsto_const_nhds (x := (1 : ℝ))).sub hconst).sub
    (hloglog.const_mul 2)).sub hresdiv
  simp only [sub_zero, mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 := zero_lt_one.trans hx
  have hg := Real.log_pos hx
  have hd : 0 < D x := relativeWidth_pos hc hx
  have hl : 0 < L x := Real.log_pos (by change 1 < 1 + D x; linarith)
  have he : Real.log (D x) = Real.log c + 2 * Real.log (Real.log x) - Real.log x := by
    change Real.log (c * (Real.log x)^2 / x) = _
    rw [Real.log_div (by positivity) hx0.ne', Real.log_mul hc.ne' (by positivity), Real.log_pow]
    norm_num
  change 1 - Real.log c / Real.log x - 2 * (Real.log (Real.log x) / Real.log x) -
    Real.log (L x / D x) / Real.log x = Real.log (1 / L x) / Real.log x
  rw [Real.log_div hl.ne' hd.ne', he, one_div, Real.log_inv]
  field_simp [hg.ne']
  ring

/-- The two normalizations of the sharp second moment have asymptotic ratio one. -/
theorem logWidth_scale_tendsto_one {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => logWidth c x * (Real.log (1 / logWidth c x))^2 /
      (relativeWidth c x * (Real.log x)^2)) atTop (𝓝 1) := by
  have h := (logWidth_div_relativeWidth_tendsto_one hc).mul
    ((logWidth_log_inv_div_log_tendsto_one hc).pow 2)
  simpa only [one_pow, mul_one, div_pow, div_mul_div_comm] using h

end GoldbachConcrete
