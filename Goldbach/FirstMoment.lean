import Goldbach.PrimeIntegral
import Zeta23.FromPNTPlus.MediumPNT

open Asymptotics Filter MeasureTheory
open scoped Topology

noncomputable section
namespace GoldbachConcrete

/-- The usual real-variable prime number theorem for Chebyshev's theta function. -/
theorem theta_div_tendsto_one :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  obtain ⟨C, hC, hPNT⟩ := MediumPNT
  have hrpow : Tendsto (fun x : ℝ => Real.log x ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 10)).comp Real.tendsto_log_atTop
  have hneg : Tendsto (fun x : ℝ => -C * Real.log x ^ ((1 : ℝ) / 10)) atTop atBot := by
    simpa only [Function.comp_def, neg_mul] using
      tendsto_neg_atTop_atBot.comp ((tendsto_const_mul_atTop_of_pos hC).mpr hrpow)
  have he := Real.tendsto_exp_atBot.comp hneg
  have hid : ∀ᶠ x : ℝ in atTop, id x ≠ 0 :=
    (eventually_gt_atTop 0).mono (fun _ hx => hx.ne')
  have he' : (fun x : ℝ => x * Real.exp (-C * Real.log x ^ ((1 : ℝ) / 10))) =o[atTop] id := by
    apply (isLittleO_iff_tendsto' (hid.mono (fun _ hn hh => (hn hh).elim))).mpr
    apply he.congr'
    filter_upwards [hid] with x hx
    change _ = x * _ / x
    field_simp [show x ≠ 0 from hx]
    rfl
  have hψ : Chebyshev.psi ~[atTop] (id : ℝ → ℝ) :=
    (hPNT.trans_isLittleO he').isEquivalent
  have hsqrt : Real.sqrt =o[atTop] (id : ℝ → ℝ) := by
    apply (isLittleO_iff_tendsto' (hid.mono (fun _ hn hh => (hn hh).elim))).mpr
    apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    change x ^ (-(1 / 2 : ℝ)) = Real.sqrt x / x
    rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, Real.sqrt_div_self]
  have hθ : Chebyshev.theta ~[atTop] (id : ℝ → ℝ) := by
    simpa only [sub_sub_cancel] using
      hψ.sub_isLittleO (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrt)
  exact (isEquivalent_iff_tendsto_one hid).mp hθ

theorem relativeWidth_tendsto_zero (c : ℝ) :
    Tendsto (relativeWidth c) atTop (𝓝 0) := by
  change Tendsto (fun x : ℝ => c * Real.log x ^ 2 / x) atTop (𝓝 0)
  simpa only [one_mul, add_zero, ← mul_div_assoc, mul_zero] using
    (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 2 one_ne_zero).const_mul c

theorem relativeWidth_pos {c x : ℝ} (hc : 0 < c) (hx : 1 < x) :
    0 < relativeWidth c x := by
  exact div_pos (mul_pos hc (sq_pos_of_pos (Real.log_pos hx))) (zero_lt_one.trans hx)

theorem trim_pos_and_gap {c : ℝ} (hc : 1 < c) :
    0 < trim c ∧ 1 / c < 1 - 2 * trim c := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have h : 1 / c < 1 := (div_lt_iff₀ hc0).mpr (by simpa using hc)
  unfold trim
  constructor <;> linarith

private theorem theta_scaled_tendsto {f : ℝ → ℝ} {a : ℝ}
    (hf : Tendsto f atTop atTop) (hscale : Tendsto (fun x => f x / x) atTop (𝓝 a)) :
    Tendsto (fun x => Chebyshev.theta (f x) / x) atTop (𝓝 a) := by
  have ht := (theta_div_tendsto_one.comp hf).mul hscale
  rw [one_mul] at ht
  apply ht.congr'
  filter_upwards [hf.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  change Chebyshev.theta (f x) / f x * (f x / x) = Chebyshev.theta (f x) / x
  rw [← mul_div_assoc, div_mul_cancel₀ _ hx.ne']

/-- The first moment required by the Goldbach reduction follows unconditionally
from the prime number theorem. -/
theorem firstMomentInput : FirstMomentInput := by
  intro c hc
  let a := trim c
  let b := 1 - a
  let d := relativeWidth c
  let f : ℝ → ℝ := fun x => (1 + d x) * (a * x)
  let g : ℝ → ℝ := fun x => b * x
  let k : ℝ := (3 * (b - a) + 1 / c) / 4
  obtain ⟨ha, hgap⟩ := trim_pos_and_gap hc
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hab : a < b := by
    have : 0 < (1 : ℝ) / c := by positivity
    dsimp [a, b]
    linarith
  have hb : 0 < b := ha.trans hab
  have hk : k < b - a := by
    dsimp [k, b, a]
    linarith
  have hax : Tendsto (fun x : ℝ => a * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos ha).2 tendsto_id
  have hg : Tendsto g atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hb).2 tendsto_id
  have hx1 : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
  have hdpos : ∀ᶠ x : ℝ in atTop, 0 < d x := hx1.mono (fun _ hx => relativeWidth_pos hc0 hx)
  have hf : Tendsto f atTop atTop := by
    apply tendsto_atTop_mono' _ _ hax
    filter_upwards [hdpos, hx1] with x hdx hx
    dsimp [f]
    nlinarith [mul_nonneg hdx.le (mul_pos ha (zero_lt_one.trans hx)).le]
  have hD : Tendsto (fun x : ℝ => 1 + d x) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (relativeWidth_tendsto_zero c)
  have hfs : Tendsto (fun x => f x / x) atTop (𝓝 a) := by
    have ht := hD.mul_const a
    rw [one_mul] at ht
    apply ht.congr'
    filter_upwards [hx1] with x hx
    dsimp [f]
    field_simp [(zero_lt_one.trans hx).ne']
  have hgs : Tendsto (fun x => g x / x) atTop (𝓝 b) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hx1] with x hx
    exact (mul_div_cancel_right₀ _ (zero_lt_one.trans hx).ne').symm
  have hlim : Tendsto
      (fun x => (Chebyshev.theta (g x) / x - Chebyshev.theta (f x) / x) / (1 + d x))
      atTop (𝓝 (b - a)) := by
    have ht := ((theta_scaled_tendsto hg hgs).sub (theta_scaled_tendsto hf hfs)).div hD one_ne_zero
    change Tendsto (fun x => (Chebyshev.theta (g x) / x - Chebyshev.theta (f x) / x) / (1 + d x))
      atTop (𝓝 ((b - a) / 1)) at ht
    simpa only [div_one] using ht
  have hevent : ∀ᶠ x : ℝ in atTop,
      Integrable (firstIntegrand c x) (regionMeasure c x) ∧
      midpoint c x < ∫ y, firstIntegrand c x y ∂regionMeasure c x := by
    filter_upwards [hx1, hdpos, hax.eventually (eventually_ge_atTop (2 : ℝ)),
        hfs.eventually (gt_mem_nhds hab), hlim.eventually (lt_mem_nhds hk)] with x hx hd hu huv hkx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hu' : f x ≤ g x := ((div_lt_iff₀ hx0).mp huv).le
    have hL := integral_density_lower_chebyshev hd hu hu'
    have hAx : 0 < a * x := mul_pos ha hx0
    have horder : a * x ≤ b * x := mul_le_mul_of_nonneg_right hab.le hx0.le
    obtain ⟨hi, hint⟩ := firstIntegrand_integral (c := c) hAx hd horder
    refine ⟨hi, ?_⟩
    have hk' : k * x < (Chebyshev.theta (g x) - Chebyshev.theta (f x)) / (1 + d x) := by
      calc
        _ < ((Chebyshev.theta (g x) / x - Chebyshev.theta (f x) / x) / (1 + d x)) * x :=
          mul_lt_mul_of_pos_right hkx hx0
        _ = _ := by rw [← sub_div, div_right_comm, div_mul_cancel₀ _ hx0.ne']
    have halg : 1 - 2 * trim c = b - a := by dsimp [a, b]; ring
    rw [hint, midpoint, halg]
    change (b - a + 1 / c) * x <
      4 * (∫ y in Set.Icc (a * x) (b * x), density (d x) y) - 2 * ((b - a) * x)
    change (Chebyshev.theta (g x) - Chebyshev.theta (f x)) / (1 + d x) ≤
      (∫ y in Set.Icc (a * x) (b * x), density (d x) y) at hL
    have hk_eq : 4 * (k * x) = 3 * ((b - a) * x) + (1 / c) * x := by
      dsimp [k]
      ring
    linarith
  exact eventually_atTop.mp hevent

end GoldbachConcrete
