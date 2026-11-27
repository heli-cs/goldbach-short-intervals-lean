import Goldbach.FirstMoment

open Asymptotics Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section
namespace GoldbachArithmetic

open ArithmeticFunction

/-- The contribution of higher prime powers to the sharp interval (y,(1+d)y]. -/
def primePowerIncrement (d y : ℝ) : ℝ :=
  (Chebyshev.psi ((1 + d) * y) - Chebyshev.theta ((1 + d) * y)) -
    (Chebyshev.psi y - Chebyshev.theta y)

private def primePowerWeight (n : ℕ) : ℝ :=
  if n.Prime then 0 else vonMangoldt n

private theorem primePowerWeight_nonneg (n : ℕ) : 0 ≤ primePowerWeight n := by
  unfold primePowerWeight
  split <;> simp [vonMangoldt_nonneg]

private theorem primePowerWeight_le_log (n : ℕ) :
    primePowerWeight n ≤ Real.log (n : ℝ) := by
  unfold primePowerWeight
  split
  · rename_i hp
    exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  · exact vonMangoldt_le_log

private theorem primePowerWeight_sum (z : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊z⌋₊, primePowerWeight n = Chebyshev.psi z - Chebyshev.theta z := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : n.Prime <;> simp [primePowerWeight, h]

private theorem primePowerIncrement_sum {d y : ℝ} (hd : 0 ≤ d) (hy : 0 ≤ y) :
    primePowerIncrement d y =
      ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊(1 + d) * y⌋₊, primePowerWeight n := by
  have hs : Finset.Ioc 0 ⌊y⌋₊ ⊆ Finset.Ioc 0 ⌊(1 + d) * y⌋₊ := by
    apply Finset.Ioc_subset_Ioc_right
    apply Nat.floor_mono
    nlinarith [mul_nonneg hd hy]
  have he : Finset.Ioc 0 ⌊(1 + d) * y⌋₊ \ Finset.Ioc 0 ⌊y⌋₊ =
      Finset.Ioc ⌊y⌋₊ ⌊(1 + d) * y⌋₊ := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Ioc]
    omega
  rw [primePowerIncrement, ← primePowerWeight_sum, ← primePowerWeight_sum, ← he]
  exact (eq_sub_of_add_eq (Finset.sum_sdiff hs)).symm

private theorem primePowerIncrement_nonneg {d y : ℝ} (hd : 0 ≤ d) (hy : 0 ≤ y) :
    0 ≤ primePowerIncrement d y := by
  rw [primePowerIncrement_sum hd hy]
  exact Finset.sum_nonneg (fun n _ => primePowerWeight_nonneg n)

private theorem upper_endpoint_le {d x y : ℝ} (hd : d ≤ 1) (hy : 0 ≤ y) (hyx : y ≤ x) :
    (1 + d) * y ≤ 2 * x :=
  (mul_le_mul_of_nonneg_right (show 1 + d ≤ 2 by linarith) hy).trans
    (mul_le_mul_of_nonneg_left hyx (by norm_num))

private theorem primePowerIncrement_le {d x y : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1)
    (hy : 0 ≤ y) (hyx : y ≤ x) (hx : 1 ≤ x) :
    primePowerIncrement d y ≤ (d * x + 1) * Real.log (2 * x) := by
  have hz : 0 ≤ (1 + d) * y := mul_nonneg (by linarith) hy
  have hfloor : ⌊y⌋₊ ≤ ⌊(1 + d) * y⌋₊ := Nat.floor_mono (by nlinarith [mul_nonneg hd hy])
  have hcard : ((Finset.Ioc ⌊y⌋₊ ⌊(1 + d) * y⌋₊).card : ℝ) ≤ d * x + 1 := by
    rw [Nat.card_Ioc, Nat.cast_sub hfloor]
    linarith [Nat.floor_le hz, Nat.sub_one_lt_floor y, mul_le_mul_of_nonneg_left hyx hd]
  rw [primePowerIncrement_sum hd hy]
  calc
    _ ≤ ∑ _n ∈ Finset.Ioc ⌊y⌋₊ ⌊(1 + d) * y⌋₊, Real.log (2 * x) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_Ioc.mp hn
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_le ⌊y⌋₊).trans_lt hn'.1
      have hnX := ((Nat.le_floor_iff hz).mp hn'.2).trans (upper_endpoint_le hd' hy hyx)
      exact (primePowerWeight_le_log n).trans (Real.log_le_log hn0 hnX)
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard (Real.log_nonneg (by linarith))

private def powerSupport (d : ℝ) (n : ℕ) : Set ℝ := Ico ((n : ℝ) / (1 + d)) (n : ℝ)

private theorem support_integral_le {d x u v : ℝ} {n : ℕ} (hd : 0 ≤ d)
    (hx : 0 ≤ x) (hn : n ≤ ⌊2 * x⌋₊) :
    (∫ y in Icc u v, (powerSupport d n).indicator (fun _ => primePowerWeight n) y)
      ≤ (2 * d * x) * primePowerWeight n := by
  have hD : 0 < 1 + d := by linarith
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hnX : (n : ℝ) ≤ 2 * x := (Nat.le_floor_iff (by positivity)).mp hn
  have hs : MeasurableSet (powerSupport d n) := measurableSet_Ico
  have hvol : volume (powerSupport d n) ≠ ⊤ := measure_Ico_lt_top.ne
  have horder : (n : ℝ) / (1 + d) ≤ n := div_le_self hn0 (by linarith)
  have hlength : (n : ℝ) - (n : ℝ) / (1 + d) ≤ 2 * d * x := by
    calc
      _ = d * (n : ℝ) / (1 + d) := by field_simp [hD.ne']; ring
      _ ≤ d * (n : ℝ) := div_le_self (mul_nonneg hd hn0) (by linarith)
      _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hnX hd]
  rw [integral_indicator hs, Measure.restrict_restrict hs]
  calc
    _ ≤ ∫ _y in powerSupport d n, primePowerWeight n := by
      apply setIntegral_mono_set (integrableOn_const hvol)
      · exact Filter.Eventually.of_forall (fun _ => primePowerWeight_nonneg n)
      · exact Filter.Eventually.of_forall (fun _ h => h.1)
    _ ≤ _ := by
      rw [setIntegral_const, smul_eq_mul]
      change volume.real (Ico ((n : ℝ) / (1 + d)) (n : ℝ)) * primePowerWeight n ≤ _
      rw [Real.volume_real_Ico_of_le horder]
      exact mul_le_mul_of_nonneg_right hlength (primePowerWeight_nonneg n)

private theorem primePowerIncrement_integral {d x u v : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1)
    (hx : 1 ≤ x) (hu : 0 ≤ u) (hv : v ≤ x) :
    IntegrableOn (primePowerIncrement d) (Icc u v) ∧
    (∫ y in Icc u v, primePowerIncrement d y) ≤ 2 * d * x *
      (Chebyshev.psi (2 * x) - Chebyshev.theta (2 * x)) := by
  let N := Finset.Ioc 0 ⌊2 * x⌋₊
  let term := fun n : ℕ => (powerSupport d n).indicator (fun _ => primePowerWeight n)
  let μ : Measure ℝ := volume.restrict (Icc u v)
  have hD : 0 < 1 + d := by linarith
  have hxi : 0 ≤ x := by linarith
  have hi : ∀ n ∈ N, Integrable (term n) μ := by
    intro n _
    exact (integrableOn_const (C := primePowerWeight n) (s := Icc u v) (μ := volume)
      measure_Icc_lt_top.ne).indicator measurableSet_Ico
  have he : (fun y => ∑ n ∈ N, term n y) =ᵐ[μ] primePowerIncrement d := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Icc u v) measurableSet_Icc] with y hy
    have hy0 := hu.trans hy.1
    have hz : 0 ≤ (1 + d) * y := mul_nonneg hD.le hy0
    have hzX := upper_endpoint_le hd' hy0 (hy.2.trans hv)
    rw [primePowerIncrement_sum hd hy0]
    simp only [term, Set.indicator]
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, N, powerSupport, Set.mem_Ico]
    rw [Nat.floor_lt hy0, Nat.le_floor_iff hz, div_le_iff₀ hD]
    constructor
    · rintro ⟨_, h, hn⟩
      exact ⟨hn, by simpa only [mul_comm] using h⟩
    · rintro ⟨hlo, hhi⟩
      exact ⟨⟨by exact_mod_cast hy0.trans_lt hlo,
        (Nat.le_floor_iff (by positivity)).mpr (hhi.trans hzX)⟩,
        by simpa only [mul_comm] using hhi, hlo⟩
  refine ⟨(integrable_finsetSum _ hi).congr he, ?_⟩
  calc
    _ = ∑ n ∈ N, ∫ y in Icc u v, term n y := by
      rw [← integral_congr_ae he, integral_finsetSum _ hi]
    _ ≤ ∑ n ∈ N, (2 * d * x) * primePowerWeight n := by
      exact Finset.sum_le_sum (fun _ hn => support_integral_le hd hxi (Finset.mem_Ioc.mp hn).2)
    _ = _ := by rw [← Finset.mul_sum, primePowerWeight_sum]

/-- A uniform local mean-square bound for the higher prime-power contribution. -/
theorem primePowerError_bound {a d v x : ℝ} (ha : 0 < a) (hd : 0 ≤ d) (hd' : d ≤ 1)
    (hx : 2 ≤ x) (hv : v ≤ x) :
    IntegrableOn (fun y => (primePowerIncrement d y)^2 / y^2) (Icc (a * x) v) ∧
    (∫ y in Icc (a * x) v, (primePowerIncrement d y)^2 / y^2) ≤
      (32 / a^2) * (d * (Real.log x)^2) * ((d * x + 1) / Real.sqrt x) := by
  have hx0 : 0 < x := by linarith
  have hax : 0 < a * x := mul_pos ha hx0
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog₂ : Real.log (2 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul two_ne_zero hx0.ne']
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx]
  have hsqrt₂ : Real.sqrt (2 * x) ≤ 2 * Real.sqrt x := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact (Real.sqrt_le_iff).mpr (by norm_num)
  obtain ⟨hi, hL⟩ := primePowerIncrement_integral hd hd' (by linarith) hax.le hv
  let M := (d * x + 1) * (2 * Real.log x) / (a * x)^2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let μ : Measure ℝ := volume.restrict (Icc (a * x) v)
  have hDom : ∀ᵐ y ∂μ, (primePowerIncrement d y)^2 / y^2 ≤ M * primePowerIncrement d y := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Icc (a * x) v) measurableSet_Icc] with y hy
    have hy0 := hax.trans_le hy.1
    have hP := primePowerIncrement_nonneg hd hy0.le
    have hPt := primePowerIncrement_le hd hd' hy0.le (hy.2.trans hv) (by linarith)
    have hPmax := hPt.trans (mul_le_mul_of_nonneg_left hlog₂ (by positivity))
    have hsq : (a * x)^2 ≤ y^2 := by gcongr; exact hy.1
    have hcoef : primePowerIncrement d y / y^2 ≤ M := by
      dsimp [M]
      exact div_le_div₀ (by positivity) hPmax (sq_pos_of_pos hax) hsq
    rw [pow_two, mul_div_assoc, mul_comm]
    exact mul_le_mul_of_nonneg_right hcoef hP
  have hJ : Integrable (fun y => (primePowerIncrement d y)^2 / y^2) μ := by
    have hbMeas : Measurable (fun y : ℝ => (y^2)⁻¹) := (measurable_id.pow_const 2).inv
    refine (hi.const_mul M).mono' ?_ ?_
    · rw [show (fun y : ℝ => (primePowerIncrement d y)^2 / y^2) =
          (primePowerIncrement d ^ 2) * (fun y : ℝ => (y^2)⁻¹) by
            funext y
            simp only [Pi.mul_apply, Pi.pow_apply, div_eq_mul_inv]]
      exact (hi.aestronglyMeasurable.pow 2).mul hbMeas.aestronglyMeasurable
    · filter_upwards [hDom] with y hy
      rwa [Real.norm_of_nonneg (by positivity)]
  refine ⟨hJ, ?_⟩
  have hG := Chebyshev.psi_sub_theta_le (x := 2 * x) (by linarith)
  have hG' : Chebyshev.psi (2 * x) - Chebyshev.theta (2 * x) ≤ 8 * Real.sqrt x * Real.log x := by
    apply hG.trans
    calc
      _ ≤ (2 * (2 * Real.sqrt x)) * (2 * Real.log x) := by
        gcongr
        exact Real.log_nonneg (by linarith)
      _ = _ := by ring
  calc
    _ ≤ ∫ y in Icc (a * x) v, M * primePowerIncrement d y :=
      integral_mono_ae hJ (hi.const_mul M) hDom
    _ ≤ M * (2 * d * x * (8 * Real.sqrt x * Real.log x)) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hL.trans (mul_le_mul_of_nonneg_left hG' (by positivity))) hM
    _ = _ := by
      dsimp [M]
      have hs := Real.sq_sqrt hx0.le
      field_simp [ha.ne', hx0.ne', (Real.sqrt_pos.2 hx0).ne']
      linear_combination (d * (Real.log x)^2 * 32) * hs

/-- The higher prime powers are negligible at the scale required by the
Gaussian second moment for the Goldbach interval. -/
theorem primePowerError_isLittleO {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (fun x => ∫ y in Icc (a * x) ((1 - a) * x),
        (primePowerIncrement (GoldbachConcrete.relativeWidth c x) y)^2 / y^2)
      =o[atTop] (fun x => GoldbachConcrete.relativeWidth c x * (Real.log x)^2) := by
  have hlog := isLittleO_log_rpow_rpow_atTop 2 (show 0 < (1 : ℝ) / 2 by norm_num)
  have hq : Tendsto (fun x : ℝ => (Real.log x)^2 / Real.sqrt x) atTop (𝓝 0) := by
    have ht := (isLittleO_iff_tendsto' (f := fun x : ℝ => Real.log x ^ (2 : ℝ))
      ((eventually_gt_atTop (0 : ℝ)).mono (fun x hx hz => ((Real.rpow_pos_of_pos hx _).ne' hz).elim))).mp hlog
    convert ht using 1
    funext x
    rw [← Real.sqrt_eq_rpow, ← Real.rpow_natCast]
    norm_num
  have hr : Tendsto (fun x : ℝ => 1 / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [one_div, Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 2)))
  have ht : Tendsto (fun x : ℝ => (32 / a^2) *
      ((GoldbachConcrete.relativeWidth c x * x + 1) / Real.sqrt x)) atTop (𝓝 0) := by
    have hz := (((hq.const_mul c).add hr).const_mul (32 / a^2))
    simp only [mul_zero, zero_add] at hz
    apply hz.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp [GoldbachConcrete.relativeWidth, GoldbachConcrete.window]
    rw [div_mul_cancel₀ _ hx.ne', add_div, mul_div_assoc]
  apply isLittleO_iff.mpr
  intro ε hε
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    (GoldbachConcrete.relativeWidth_tendsto_zero c).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    ht.eventually (gt_mem_nhds hε)] with x hx hd₁ hsmall
  let d := GoldbachConcrete.relativeWidth c x
  have hd : 0 ≤ d := (GoldbachConcrete.relativeWidth_pos hc (by linarith)).le
  have hv : (1 - a) * x ≤ x := by nlinarith [mul_nonneg ha.le (show 0 ≤ x by linarith)]
  have hbound := (primePowerError_bound ha hd hd₁.le hx hv).2
  have hnonneg : 0 ≤ ∫ y in Icc (a * x) ((1 - a) * x), (primePowerIncrement d y)^2 / y^2 :=
    integral_nonneg (fun _ => by positivity)
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (show 0 ≤ d * (Real.log x)^2 by positivity)]
  calc
    _ ≤ (32 / a^2) * (d * (Real.log x)^2) * ((d * x + 1) / Real.sqrt x) := hbound
    _ = (32 / a^2 * ((d * x + 1) / Real.sqrt x)) * (d * (Real.log x)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall.le (by positivity)


/-- The von Mangoldt weight restricted to higher prime powers. -/
abbrev higherPrimePowerWeight : ℕ → ℝ := primePowerWeight

theorem higherPrimePowerWeight_nonneg (n : ℕ) : 0 ≤ higherPrimePowerWeight n :=
  primePowerWeight_nonneg n

theorem higherPrimePowerWeight_ne_zero_iff (n : ℕ) :
    higherPrimePowerWeight n ≠ 0 ↔ ¬n.Prime ∧ IsPrimePow n := by
  classical
  by_cases hp : n.Prime
  · simp [higherPrimePowerWeight, primePowerWeight, hp]
  · simp [higherPrimePowerWeight, primePowerWeight, hp, vonMangoldt_ne_zero_iff]

theorem higherPrimePowerWeight_eq_vonMangoldt {n : ℕ} (hn : ¬n.Prime) :
    higherPrimePowerWeight n = vonMangoldt n := by
  simp [higherPrimePowerWeight, primePowerWeight, hn]

theorem sum_higherPrimePowerWeight (z : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊z⌋₊, higherPrimePowerWeight n = Chebyshev.psi z - Chebyshev.theta z :=
  primePowerWeight_sum z

theorem primePowerIncrement_eq_sum {d y : ℝ} (hd : 0 ≤ d) (hy : 0 ≤ y) :
    primePowerIncrement d y =
      ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊(1 + d) * y⌋₊, higherPrimePowerWeight n :=
  primePowerIncrement_sum hd hy

end GoldbachArithmetic
