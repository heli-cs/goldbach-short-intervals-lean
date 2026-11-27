import Goldbach.Explicit.ChebyshevBounds
import Goldbach.Explicit.CosineFirstMoment
import Goldbach.Explicit.CosineEnergyBound
import Goldbach.LogIntegral

/-! An effective von Mangoldt square sum using Mathlib's Chebyshev bound. -/

open MeasureTheory Set
open scoped Interval
noncomputable section

namespace GoldbachExplicit

open ArithmeticFunction

private theorem exp_half_moment (k : ℕ) :
    IntegrableOn (fun s : ℝ => s^k * Real.exp (-s / 2)) (Ioi (0 : ℝ)) ∧
      (∫ s in Ioi (0 : ℝ), s^k * Real.exp (-s / 2)) = (2 : ℝ)^(k+1) * (k.factorial : ℝ) := by
  have he (s : ℝ) : -(1 / 2 : ℝ) * s = -s / 2 := by ring
  constructor
  · have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := 1 / 2)
      (show -1 < (k : ℝ) by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg _])
      (by norm_num) (by norm_num)
    simpa only [Real.rpow_one, Real.rpow_natCast, he] using hi
  · have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := 1 / 2)
      (by positivity) (by norm_num)
    have hp : (2 : ℝ)^((k : ℝ) + 1) = (2 : ℝ)^(k+1) := by
      rw [← Nat.cast_succ, Real.rpow_natCast]
    have hneg (s : ℝ) : -(1 / 2 * s) = -s / 2 := by ring
    simpa only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial,
      show (1 : ℝ) / (1 / 2) = 2 by norm_num, hp, hneg] using hi

private theorem integral_cosineAbel_weighted_le {V : ℝ} (hV : 0 < V) :
    (∫ s in (0 : ℝ)..V, cosineAbelWeight V s * (s * Real.exp (-s / 2))) ≤
      16 + 96 * (Real.pi^2 / V^2) := by
  let a := Real.pi^2 / V^2
  let G (s : ℝ) := s^2 * Real.exp (-s / 2) + a * (s^3 * Real.exp (-s / 2))
  have hG : IntegrableOn G (Ioi (0 : ℝ)) :=
    (exp_half_moment 2).1.add ((exp_half_moment 3).1.const_mul a)
  have hnon (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : 0 ≤ G s := by
    have hpos : 0 < s := hs
    dsimp [G, a]; positivity
  have hF : Continuous (fun s : ℝ => cosineAbelWeight V s * (s * Real.exp (-s / 2))) :=
    (continuous_cosineAbelWeight hV).mul (by fun_prop)
  rw [intervalIntegral.integral_of_le hV.le]
  calc
    _ ≤ ∫ s in Ioc (0 : ℝ) V, G s := by
      refine integral_mono_ae ((hF.intervalIntegrable 0 V).1)
        (hG.mono_set Ioc_subset_Ioi_self) ?_
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc (0 : ℝ) V) measurableSet_Ioc] with s hs
      have hm := mul_le_mul_of_nonneg_right (cosineAbelWeight_le_quadratic hV ⟨hs.1.le, hs.2⟩)
        (mul_nonneg hs.1.le (Real.exp_pos (-s / 2)).le)
      dsimp [G, a]
      nlinarith only [hm]
    _ ≤ ∫ s in Ioi (0 : ℝ), G s :=
      setIntegral_mono_set hG (ae_restrict_mem measurableSet_Ioi |>.mono hnon)
        (Filter.Eventually.of_forall fun _ hs => hs.1)
    _ = _ := by
      unfold G
      rw [integral_add (exp_half_moment 2).1 ((exp_half_moment 3).1.const_mul a), integral_const_mul,
        (exp_half_moment 2).2, (exp_half_moment 3).2]
      norm_num [Nat.factorial] <;> ring

/-- Effective finite prime and prime-power contribution from Abel summation. -/
private theorem weightedMangoldtSquares_le_of_psi_bound {V c d : ℝ} (hV : 1 ≤ V)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hψ : ∀ t : ℝ, 1 ≤ t →
      Chebyshev.psi t ≤ t * (c + d * (Real.log t * Real.exp (-Real.log t / 2)))) :
    weightedMangoldtSquares V ≤
      c * (V^2 / Real.pi^2 + 1 / 2) + d * (16 + 96 * (Real.pi^2 / V^2)) := by
  let E := Real.exp V
  let A (s : ℝ) := s * cosineWeight V s
  let S := cosineAbelWeight V
  let F (t : ℝ) := A (Real.log t) / t
  let Q (s : ℝ) := (c + d * (s * Real.exp (-s / 2))) * S s
  have hV₀ : 0 < V := zero_lt_one.trans_le hV
  have hE : 1 ≤ E := Real.one_le_exp hV₀.le
  have hA : ContDiff ℝ 2 A := contDiff_id.mul (contDiff_two_cosineWeight hV₀)
  have hS : Continuous S := continuous_cosineAbelWeight hV₀
  have hQ : Continuous Q := (by fun_prop : Continuous (fun s : ℝ =>
    c + d * (s * Real.exp (-s / 2)))).mul hS
  have hD (t : ℝ) (ht : 0 < t) :
      HasDerivAt F ((deriv A (Real.log t) - A (Real.log t)) / t^2) t := by
    have hd := (hA.differentiable (by norm_num) (Real.log t)).hasDerivAt
    have h := (hd.comp t (Real.hasDerivAt_log ht.ne')).div (hasDerivAt_id t) ht.ne'
    convert h using 1 <;> first | rfl | (funext u; rfl) |
      (simp only [id_eq, Function.comp_def]; field_simp [ht.ne'] <;> ring)
  have hDcont : ContinuousOn (deriv F) (Icc 1 E) := by
    have hl : ContinuousOn Real.log (Icc 1 E) :=
      continuousOn_id.log (fun t ht => (zero_lt_one.trans_le ht.1).ne')
    refine (((hA.continuous_deriv (by norm_num)).comp_continuousOn hl).sub
      (hA.continuous.comp_continuousOn hl)).div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero _ (zero_lt_one.trans_le ht.1).ne') |>.congr ?_
    intro t ht
    exact (hD t (zero_lt_one.trans_le ht.1)).deriv
  have hDint := hDcont.integrableOn_compact (μ := volume) isCompact_Icc
  have hFend : F E = 0 := by
    have he : Real.log E = V := Real.log_exp _
    simp [F, he, A, cosineWeight, abs_of_pos hV₀, hV₀.ne']
  have hΛ₀ : vonMangoldt 0 = 0 := by simp
  have hAbel := sum_mul_eq_sub_integral_mul₀ ArithmeticFunction.vonMangoldt
    hΛ₀ E (fun t ht => (hD t (zero_lt_one.trans_le ht.1)).differentiableAt) hDint
  simp only [← Chebyshev.psi_eq_sum_Icc, hFend, zero_mul, zero_sub] at hAbel
  have hsum : weightedMangoldtSquares V ≤
      ∑ n ∈ Finset.Icc 0 ⌊E⌋₊, F n * vonMangoldt n := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
    simp only [hΛ₀, mul_zero, zero_add]
    unfold weightedMangoldtSquares
    apply Finset.sum_le_sum
    intro n hn
    have hnp : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hn₀ := vonMangoldt_nonneg (n := n)
    have hbase := mul_le_mul_of_nonneg_left (vonMangoldt_le_log (n := n)) hn₀
    calc
      _ = (vonMangoldt n)^2 * (cosineWeight V (Real.log n) / n) := by ring
      _ ≤ (vonMangoldt n * Real.log n) * (cosineWeight V (Real.log n) / n) := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right hbase (div_nonneg (cosineWeight_nonneg hV₀ _) hnp.le)
      _ = _ := by unfold F A; ring
  have hDψ : IntegrableOn (fun t => deriv F t * Chebyshev.psi t) (Icc 1 E) := by
    have ht := integrableOn_mul_sum_Icc (m := 0) ArithmeticFunction.vonMangoldt
      (show (0 : ℝ) ≤ 1 by norm_num) hDint
    simpa only [← Chebyshev.psi_eq_sum_Icc] using ht
  have hQi : IntegrableOn (fun t => Q (Real.log t) / t) (Icc 1 E) := by
    refine ((hQ.comp_continuousOn (continuousOn_id.log (fun t ht =>
      (zero_lt_one.trans_le ht.1).ne'))).div continuousOn_id
      (fun t ht => (zero_lt_one.trans_le ht.1).ne')).integrableOn_compact isCompact_Icc
  have hmajor : (∫ t in Ioc 1 E, -(deriv F t * Chebyshev.psi t)) ≤
      ∫ t in Ioc 1 E, Q (Real.log t) / t := by
    refine integral_mono_ae ((hDψ.neg).mono_set Ioc_subset_Icc_self)
      (hQi.mono_set Ioc_subset_Icc_self) ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc 1 E) measurableSet_Ioc] with t ht
    have ht₀ : 0 < t := zero_lt_one.trans ht.1
    have hn : 0 ≤ S (Real.log t) := le_max_left _ _
    have hpos : 0 ≤ Chebyshev.psi t := Chebyshev.psi_nonneg _
    calc
      _ = (A (Real.log t) - deriv A (Real.log t)) / t^2 * Chebyshev.psi t := by
        rw [(hD t ht₀).deriv]
        ring
      _ ≤ S (Real.log t) / t^2 * Chebyshev.psi t :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg t)) hpos
      _ ≤ S (Real.log t) / t^2 * (t * (c + d *
          (Real.log t * Real.exp (-Real.log t / 2)))) :=
        mul_le_mul_of_nonneg_left (hψ t ht.1.le) (div_nonneg hn (sq_nonneg t))
      _ = _ := by unfold Q; field_simp [ht₀.ne']
  have hchange := GoldbachLogIntegral.integral_log_change
    (show 0 < (1 : ℝ) by norm_num) (Real.exp_pos V) Q
  change (∫ t in Icc (1 : ℝ) E, Q (Real.log t) / t) =
    ∫ s in Icc (Real.log 1) (Real.log (Real.exp V)), Q s at hchange
  rw [Real.log_one, Real.log_exp, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hV₀.le] at hchange
  rw [integral_neg, hchange] at hmajor
  have hInt : (∫ s in (0 : ℝ)..V, Q s) =
      c * (∫ s in (0 : ℝ)..V, S s) +
        d * (∫ s in (0 : ℝ)..V, S s * (s * Real.exp (-s / 2))) := by
    have he : Q = fun s => c * S s + d * (S s * (s * Real.exp (-s / 2))) := by
      funext s
      unfold Q
      ring
    have hSi : IntervalIntegrable S volume 0 V := hS.intervalIntegrable _ _
    have hSw : IntervalIntegrable (fun s => S s * (s * Real.exp (-s / 2))) volume 0 V :=
      (hS.mul (by fun_prop : Continuous (fun s : ℝ => s * Real.exp (-s / 2)))).intervalIntegrable _ _
    rw [he]
    change (∫ s in (0 : ℝ)..V, c * S s + d * (S s * (s * Real.exp (-s / 2)))) = _
    rw [intervalIntegral.integral_add (hSi.const_mul c) (hSw.const_mul d),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  exact hsum.trans (hAbel.le.trans (hmajor.trans (by
    rw [hInt]
    have h₁ := mul_le_mul_of_nonneg_left (integral_cosineAbelWeight_le hV) hc
    have h₂ := mul_le_mul_of_nonneg_left (integral_cosineAbel_weighted_le hV₀) hd
    dsimp [S]
    linarith only [h₁, h₂])))

theorem weightedMangoldtSquares_le {V : ℝ} (hV : 1 ≤ V) :
    weightedMangoldtSquares V ≤
      Real.log 4 * (V^2 / Real.pi^2 + 1 / 2) + 32 + 192 * (Real.pi^2 / V^2) := by
  have h := weightedMangoldtSquares_le_of_psi_bound hV
    (c := Real.log 4) (d := 2) (Real.log_nonneg (by norm_num)) (by norm_num) psi_le_log_envelope
  linarith only [h]

/-- The doubled prime contribution is at most (L+98) in the explicit range. -/
theorem twice_weightedMangoldtSquares_le {L : ℝ} (hL : 42 ≤ L) :
    2 * weightedMangoldtSquares (bandwidth L) ≤ L + 98 := by
  let V := bandwidth L
  have hV : 0 < V := bandwidth_pos hL
  have hV₁ : 1 ≤ V := Real.one_le_sqrt.mpr (by linarith)
  have hV₂ : V^2 = 3 * L := Real.sq_sqrt (by linarith)
  have hW := weightedMangoldtSquares_le hV₁
  have hl : Real.log 4 ≤ 3 / 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hπl : 9 ≤ Real.pi^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) Real.pi_gt_three.le 2
    norm_num at h ⊢
    exact h
  have hπu : Real.pi^2 ≤ 10 :=
    (pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 2).trans (by norm_num)
  have hratio : Real.pi^2 / V^2 ≤ 1 / 12 :=
    (div_le_iff₀ (sq_pos_of_pos hV)).2 (by rw [hV₂]; linarith)
  have hmain : Real.log 4 * (V^2 / Real.pi^2) ≤ L / 2 := by
    calc
      _ ≤ (3 / 2) * (V^2 / 9) :=
        mul_le_mul hl (div_le_div_of_nonneg_left (sq_nonneg V) (by norm_num) hπl)
          (by positivity) (by norm_num)
      _ = _ := by rw [hV₂]; ring
  change 2 * weightedMangoldtSquares V ≤ L + 98
  have hW' : weightedMangoldtSquares V ≤
      Real.log 4 * (V^2 / Real.pi^2) + Real.log 4 / 2 + 32 + 192 * (Real.pi^2 / V^2) := by
    linarith only [hW]
  linarith only [hW', hmain, hratio, hl]

/-- Absorb the Chebyshev error into a linear bound before integrating
the positive Abel weight. -/
theorem twice_weightedMangoldtSquares_le_of_ge_28 {L : ℝ} (hL : 28 ≤ L) :
    2 * weightedMangoldtSquares (bandwidth L) ≤ (11 / 6) * L + 3 := by
  let V := bandwidth L
  have hV : 1 ≤ V := Real.one_le_sqrt.mpr (by linarith)
  have hV₂ : V^2 = 3 * L := Real.sq_sqrt (by linarith)
  have hπ : (108 / 11 : ℝ) ≤ Real.pi^2 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3.14)
      (show (3.14 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_d6]) 2
    linarith only [hp, show (108 / 11 : ℝ) ≤ 3.14^2 by norm_num]
  have hv : 6 * (V^2 / Real.pi^2) ≤ (11 / 6) * L := by
    rw [← mul_div_assoc, hV₂]
    apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).2
    have h := mul_le_mul_of_nonneg_left hπ (show 0 ≤ (11 / 6 : ℝ) * L by positivity)
    nlinarith only [h]
  have hW : weightedMangoldtSquares V ≤ 3 * (V^2 / Real.pi^2 + 1 / 2) := by
    simpa only [zero_mul, add_zero] using
      weightedMangoldtSquares_le_of_psi_bound (c := 3) (d := 0) hV (by norm_num) (by norm_num)
        (fun t ht => by simpa only [zero_mul, add_zero, mul_comm t] using psi_le_three_mul t ht)
  linarith only [hW, hv]

end GoldbachExplicit
