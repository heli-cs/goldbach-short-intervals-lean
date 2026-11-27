import Goldbach.Explicit.PoleSum
import Goldbach.Explicit.Archimedean
import Zeta23.RvM.MainTerm

/-! An effective cumulative zero count under RH with a relaxed constant.
The count includes all multiplicities at its upper endpoint. -/

open Set Filter MeasureTheory Complex
open scoped Interval Topology
noncomputable section

namespace GoldbachExplicit

open GoldbachZeros Zeta23 Zeta23.RvM

private theorem four_good (hRH : RiemannHypothesis) : GoodHeight 4 := by
  intro ρ hz hh
  have h := ordinate_abs_gt_nine_halves hRH ⟨ρ, hz⟩
  change (9 / 2 : ℝ) < |ρ.im| at h
  rw [hh] at h
  norm_num at h

private theorem count_eq_zero_of_le_four (hRH : RiemannHypothesis) {t : ℝ} (ht : t ≤ 4) :
    Ncount 0 t = 0 := by
  have hh : zerosIn 0 t = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ρ hr
    obtain ⟨hz, hpos, htop⟩ := hr
    have h := ordinate_abs_gt_nine_halves hRH ⟨ρ, hz⟩
    change (9 / 2 : ℝ) < |ρ.im| at h
    rw [abs_of_pos hpos] at h
    linarith
  simp [Ncount, hh]

private theorem log_ratio_gt :
    (1 / 9 : ℝ) ≤ Real.log ((0.9 : ℝ) / 0.8) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8 / 9)
  have he : (8 / 9 : ℝ) = ((0.9 : ℝ) / 0.8)⁻¹ := by norm_num
  rw [he, Real.log_inv] at h
  norm_num at h ⊢
  linarith

private theorem upper_log_forty : Real.log 40 < 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 40)]
  have h : (27 / 10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h₄ := pow_lt_pow_left₀ h (by norm_num : (0 : ℝ) ≤ 27 / 10)
    (by norm_num : (4 : ℕ) ≠ 0)
  rw [← Real.exp_nat_mul] at h₄
  norm_num at h₄
  exact (by norm_num : (40 : ℝ) < 531441 / 10000).trans h₄

private theorem horizontal_le {T : ℝ} (hT : 4 ≤ T) (hg : GoodHeight T) :
    |(∫ σ in (1/2 : ℝ)..2, logDeriv riemannZeta ((σ : ℂ) + T * I)).im| ≤
      (122 * Real.pi) * Real.log T := by
  have h := backlund_horizontal_at T (max_le hT (by linarith)) hg
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hp : 0 < Real.log ((0.9 : ℝ) / 0.8) := by linarith [log_ratio_gt]
  have hi : 1 / Real.log ((0.9 : ℝ) / 0.8) ≤ 9 := by
    apply (div_le_iff₀ hp).mpr
    linarith [log_ratio_gt]
  have ha : 0 ≤ Real.log 40 := Real.log_nonneg (by norm_num)
  norm_num at h
  rw [abs_of_nonneg ha] at h
  apply h.trans
  have he : 1 / Real.log (9 / 8) ≤ (9 : ℝ) := by
    convert hi using 1 <;> norm_num
  have hk : 1 / Real.log (9 / 8) * (Real.log 40 + 2) ≤ (60 : ℝ) := by
    have hab : (0 : ℝ) ≤ Real.log 40 + 2 := by linarith
    have hi' := mul_le_mul he (show Real.log 40 + 2 ≤ 6 by linarith [upper_log_forty])
      hab (by norm_num : (0 : ℝ) ≤ 9)
    linarith
  have hm := mul_le_mul_of_nonneg_left (show
    1 / Real.log (9 / 8) * (Real.log 40 + 2) + 1 ≤ (61 : ℝ) by linarith)
    (show 0 ≤ 2 * Real.pi by positivity)
  have hm' : 2 * Real.pi * ((Real.log (9 / 8))⁻¹ * (Real.log 40 + 2) + 1) ≤ 122 * Real.pi := by
    rw [one_div] at hm
    linarith only [hm]
  exact mul_le_mul_of_nonneg_right hm' hlog

private def mainDensity (t : ℝ) : ℝ :=
  (Real.log t - Real.log (2 * Real.pi)) / (2 * Real.pi)

private def mainPrimitive (t : ℝ) : ℝ :=
  (t * Real.log t - t * (1 + Real.log (2 * Real.pi))) / (2 * Real.pi)

/-- The main term obtained by integrating the positive Stirling density
from $2π$, extended by zero to lower heights. -/
def zeroCountMain (t : ℝ) : ℝ :=
  mainPrimitive (max t (2 * Real.pi)) - mainPrimitive (2 * Real.pi)

private theorem continuous_zeroCountMain : Continuous zeroCountMain := by
  have h : Continuous (fun t : ℝ => max t (2 * Real.pi)) := continuous_id.max continuous_const
  have hlog : Continuous (fun t : ℝ => Real.log (max t (2 * Real.pi))) :=
    h.log (fun t => (lt_of_lt_of_le (by positivity : 0 < 2 * Real.pi) (le_max_right _ _)).ne')
  exact (((h.mul hlog).sub (h.mul continuous_const)).div_const _).sub continuous_const

private theorem primitive_deriv {t : ℝ} (h : 0 < t) :
    HasDerivAt mainPrimitive (mainDensity t) t := by
  have ht := Real.hasDerivAt_log h.ne'
  have he := ((((hasDerivAt_id t).mul ht).sub
    ((hasDerivAt_id t).mul_const (1 + Real.log (2 * Real.pi)))).div_const (2 * Real.pi))
  convert he using 1 <;> first | rfl | (simp only [id_eq, mainDensity]; field_simp [h.ne', Real.pi_ne_zero] <;> ring)

private theorem density_interval_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable mainDensity volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  unfold mainDensity
  apply ContinuousOn.div_const
  exact (continuousOn_id.log (fun t ht => (ha.trans_le ht.1).ne')).sub continuousOn_const

private theorem integral_mainDensity {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, mainDensity t) = mainPrimitive b - mainPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (density_interval_integrable ha hab)
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact primitive_deriv (ha.trans_le ht.1)

private theorem abs_mainPrimitive_sub_four {u : ℝ} (hlo : 4 ≤ u) (hhi : u ≤ 2 * Real.pi) :
    |mainPrimitive u - mainPrimitive 4| ≤ 1 := by
  rw [← integral_mainDensity (by norm_num : (0 : ℝ) < 4) hlo]
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_integral_norm hlo).trans ?_
  have hi : IntervalIntegrable mainDensity volume 4 u := density_interval_integrable (by norm_num) hlo
  have hπ : (6 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hπ' : 2 * Real.pi < (8 : ℝ) := by linarith [Real.pi_lt_d6]
  have hlog : Real.log (2 * Real.pi) - Real.log 4 ≤ 1 := by
    have he := Real.log_le_log (by positivity : 0 < 2 * Real.pi) hπ'.le
    have he' : Real.log 8 = Real.log 4 + Real.log 2 := by
      rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9]
  calc
    _ ≤ ∫ _ : ℝ in (4 : ℝ)..u, (1 / 6 : ℝ) := by
      apply intervalIntegral.integral_mono_on hlo hi.norm intervalIntegrable_const
      intro v hv
      have h₁ := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hv.1
      have h₂ := Real.log_le_log (by linarith [hv.1] : 0 < v) (hv.2.trans hhi)
      rw [Real.norm_eq_abs, mainDensity, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 6)).mpr
      rw [abs_of_nonpos (by linarith)]
      linarith
    _ ≤ 1 := by simp only [intervalIntegral.integral_const, smul_eq_mul]; linarith

private theorem abs_gamma_integral_sub_primitive {T : ℝ} (hT : 4 ≤ T) :
    |(∫ t in (4 : ℝ)..T, mu t) - (mainPrimitive T - mainPrimitive 4)| ≤ 1 := by
  have hμ : Continuous mu := Zeta23.mu_smooth.continuous
  have hmi := density_interval_integrable (by norm_num : (0 : ℝ) < 4) hT
  have hhi : IntervalIntegrable (fun t => 4 / t^2) volume 4 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (by linarith [ht.1]))
  rw [← integral_mainDensity (by norm_num : (0 : ℝ) < 4) hT,
    ← intervalIntegral.integral_sub (hμ.intervalIntegrable _ _) hmi]
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_integral_norm hT).trans ?_
  calc
    _ ≤ ∫ t in (4 : ℝ)..T, 4 / t^2 := by
      apply intervalIntegral.integral_mono_on hT ((hμ.intervalIntegrable _ _).sub hmi).norm hhi
      intro v hv
      have h := gammaBracket_sub_log_le (by linarith [hv.1] : 1 ≤ v)
      have hΓ : EF.gammaBracket v = (2 * Real.pi) * mu v := by
        unfold EF.gammaBracket mu
        field_simp [Real.pi_ne_zero]
      rw [hΓ] at h
      rw [Real.norm_eq_abs, mainDensity]
      have he : ((2 * Real.pi) * mu v - Real.log v + Real.log (2 * Real.pi)) / (2 * Real.pi) =
          mu v - (Real.log v - Real.log (2 * Real.pi)) / (2 * Real.pi) := by
        field_simp [Real.pi_ne_zero] <;> ring
      rw [← he, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
      refine h.trans ?_
      have hvp : 0 < v^2 := sq_pos_of_pos (by linarith [hv.1])
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hvp.le
      linarith [Real.pi_gt_three]
    _ = (-4 : ℝ) / T - (-4 : ℝ) / 4 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => -4 / t) ?_ hhi
      intro t ht
      rw [uIcc_of_le hT] at ht
      have ht' : t ≠ 0 := by linarith [ht.1]
      convert ((hasDerivAt_id t).inv ht').const_mul (-4) using 1
        <;> first | rfl | (simp only [id_eq]; ring)
    _ ≤ 1 := by
      have hh : (-4 : ℝ) / T ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)
      linarith

private theorem abs_contour_im_div_le {T : ℝ} (hT : 4 ≤ T)
    (h4 : GoodHeight 4) (hg : GoodHeight T) :
    |(1 / Real.pi) * (halfContour (logDeriv riemannZeta) 4 T).im| ≤
      244 * Real.log T + 1 := by
  have hb := horizontal_le (by norm_num : (4 : ℝ) ≤ 4) h4
  have he := horizontal_le hT hg
  have hv := vertical_two 4 T
  rw [intervalIntegral.integral_mul_const] at hv
  have hh : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have ht : 0 < Real.pi := Real.pi_pos
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi), one_div, ← div_eq_inv_mul]
  apply (div_le_iff₀ ht).mpr
  simp only [halfContour, Complex.sub_im, Complex.add_im]
  refine (abs_sub _ _).trans ?_
  have h := (abs_add_le _ _).trans (add_le_add hb hv)
  have h' := add_le_add h he
  have h'' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 122 * Real.pi)
  nlinarith only [h', h'']

private theorem count_at_good_height_le (hRH : RiemannHypothesis) {T : ℝ}
    (hT : 4 < T) (hg : GoodHeight T) :
    |(Ncount 0 T : ℝ) - zeroCountMain T| ≤ 250 * Real.log (T + 2) := by
  have h4 := four_good hRH
  have hcount := N_eq_halfContour_completedZeta (by norm_num : (1 : ℝ) ≤ 4) hT h4 hg
  rw [halfContour_completedZeta_split (by norm_num) hT h4 hg, Complex.add_im, mul_add,
    gamma_side (by norm_num) (by linarith)] at hcount
  have hN : Ncount 0 T = Ncount 4 T := by
    rw [Ncount_add (by norm_num : (0 : ℝ) ≤ 4) hT.le, count_eq_zero_of_le_four hRH le_rfl, zero_add]
  have hpr : |mainPrimitive T - mainPrimitive 4 - zeroCountMain T| ≤ 1 := by
    by_cases hh : T ≤ 2 * Real.pi
    · simpa [zeroCountMain, max_eq_right hh] using abs_mainPrimitive_sub_four hT.le hh
    · have ha : (4 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      have he : mainPrimitive T - mainPrimitive 4 - zeroCountMain T =
          mainPrimitive (2 * Real.pi) - mainPrimitive 4 := by
        rw [zeroCountMain, max_eq_left (le_of_not_ge hh)]
        ring
      rw [he]
      exact abs_mainPrimitive_sub_four ha le_rfl
  rw [hN, hcount]
  have hh := abs_contour_im_div_le hT.le h4 hg
  have hΓ := abs_gamma_integral_sub_primitive hT.le
  have he : Real.log T ≤ Real.log (T + 2) := Real.log_le_log (by linarith) (by linarith)
  have hlog : 1 ≤ Real.log (T + 2) := (Real.le_log_iff_exp_le (by linarith)).mpr
    (by linarith [Real.exp_one_lt_d9])
  set A := (1 / Real.pi) * (halfContour (logDeriv riemannZeta) 4 T).im
  set G := ∫ t in (4 : ℝ)..T, mu t
  set P := mainPrimitive T - mainPrimitive 4
  change |A + G - zeroCountMain T| ≤ _
  rw [show A + G - zeroCountMain T = A + (G - P) + (P - zeroCountMain T) by ring]
  have h₁ := abs_add_le (A + (G - P)) (P - zeroCountMain T)
  have h₂ := abs_add_le A (G - P)
  linarith only [h₁, h₂, hh, hΓ, hpr, he, hlog]

private theorem exists_goodHeight_between {a b : ℝ} (h : a < b) :
    ∃ t ∈ Ioo a b, GoodHeight t := by
  have hf : ((fun ρ : ℂ => ρ.im) '' zerosIn a b).Finite := (zerosIn_finite a b).image _
  obtain ⟨t, ht, hta⟩ := ((Ioo_infinite h).sdiff hf).nonempty
  refine ⟨t, ht, fun ρ hρ hr => hta ?_⟩
  exact ⟨ρ, ⟨hρ, by rw [hr]; exact ht.1, by rw [hr]; exact ht.2.le⟩, hr⟩

/-- Effective cumulative Riemann--von Mangoldt bound suitable for
Stieltjes integration. The relaxed constant avoids low-zero computation. -/
theorem cumulative_zero_count_le (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) :
    |(Ncount 0 T : ℝ) - zeroCountMain T| ≤ 250 * Real.log (T + 2) := by
  by_cases h : T ≤ 4
  · rw [count_eq_zero_of_le_four hRH h, Nat.cast_zero, zeroCountMain,
      max_eq_right (by linarith [Real.pi_gt_three]), sub_self, sub_zero, abs_zero]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have h₄ : 4 < T := lt_of_not_ge h
  have hshift : Continuous (fun t : ℝ => t + 2) := by fun_prop
  have hcLog : ContinuousAt (fun t : ℝ => Real.log (t + 2)) T :=
    hshift.continuousAt.log (by dsimp; linarith)
  have hc : ContinuousAt (fun t : ℝ => 250 * Real.log (t + 2)) T := continuousAt_const.mul hcLog
  have hcN : ContinuousAt (fun _ : ℝ => (Ncount 0 T : ℝ)) T := continuousAt_const
  have hm := continuous_zeroCountMain.continuousAt (x := T)
  rw [abs_sub_le_iff]
  constructor
  · by_contra! hn
    have hne := (hm.add hc).eventually_lt hcN
      (show zeroCountMain T + 250 * Real.log (T + 2) < (Ncount 0 T : ℝ) by linarith)
    obtain ⟨ε, hε, hdist⟩ := Metric.eventually_nhds_iff.mp hne
    obtain ⟨t, ht, hg⟩ := exists_goodHeight_between (show T < T + ε by linarith)
    have hdist' : dist t T < ε := by rw [Real.dist_eq, abs_of_pos (by linarith [ht.1])]; linarith [ht.2]
    have htN := (abs_sub_le_iff.mp (count_at_good_height_le hRH (h₄.trans ht.1) hg)).1
    have hn' : (Ncount 0 T : ℝ) ≤ (Ncount 0 t : ℝ) := by exact_mod_cast Ncount_mono le_rfl ht.1.le
    have hh := hdist hdist'
    change zeroCountMain t + 250 * Real.log (t + 2) < (Ncount 0 T : ℝ) at hh
    linarith only [htN, hn', hh]
  · by_contra! hn
    have hne := hcN.eventually_lt (hm.sub hc)
      (show (Ncount 0 T : ℝ) < zeroCountMain T - 250 * Real.log (T + 2) by linarith)
    obtain ⟨ε, hε, hdist⟩ := Metric.eventually_nhds_iff.mp hne
    obtain ⟨t, ht, hg⟩ := exists_goodHeight_between (max_lt h₄ (show T - ε < T by linarith))
    have ht4 := (le_max_left 4 (T - ε)).trans_lt ht.1
    have htε := (le_max_right 4 (T - ε)).trans_lt ht.1
    have hdist' : dist t T < ε := by rw [Real.dist_eq, abs_of_neg (by linarith [ht.2])]; linarith
    have htN := (abs_sub_le_iff.mp (count_at_good_height_le hRH ht4 hg)).2
    have hn' : (Ncount 0 t : ℝ) ≤ (Ncount 0 T : ℝ) := by exact_mod_cast Ncount_mono le_rfl ht.2.le
    have hh := hdist hdist'
    change (Ncount 0 T : ℝ) < zeroCountMain t - 250 * Real.log (t + 2) at hh
    linarith only [htN, hn', hh]


/-- The clipped counting main term has the stated Stirling-density integral. -/
theorem zeroCountMain_eq_integral (T : ℝ) :
    zeroCountMain T = ∫ t in (2 * Real.pi)..max T (2 * Real.pi),
      (Real.log t - Real.log (2 * Real.pi)) / (2 * Real.pi) := by
  exact (integral_mainDensity (by positivity) (le_max_right _ _)).symm

end GoldbachExplicit
