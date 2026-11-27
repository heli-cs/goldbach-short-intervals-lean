import Mathlib

/-! A rational certificate for the constant in the reciprocal zero sum. -/

open Filter
open scoped Topology

noncomputable section

namespace GoldbachExplicit

/-- An upper harmonic enclosure with a first-order correction, valid at every index. -/
theorem eulerMascheroni_le_corrected_harmonic (n : ℕ) :
    Real.eulerMascheroniConstant ≤ (harmonic (n + 1) : ℝ) -
      Real.log ((n : ℝ) + 1) - 1 / (2 * ((n : ℝ) + 2)) := by
  let f (n : ℕ) : ℝ := (harmonic (n + 1) : ℝ) - Real.log ((n : ℝ) + 1) -
    1 / (2 * ((n : ℝ) + 2))
  have hmono : Antitone f := by
    apply antitone_nat_of_succ_le
    intro n
    let t : ℝ := (n : ℝ) + 1
    have ht : 0 < t := by dsimp [t]; positivity
    have hlog := Real.le_log_one_add_of_nonneg (x := 1 / t) (by positivity)
    have h₁ : 2 * (1 / t) / (1 / t + 2) = 2 / (2 * t + 1) := by
      field_simp [ht.ne', show 2 * t + 1 ≠ 0 by positivity, show 1 / t + 2 ≠ 0 by positivity] <;> ring
    rw [h₁] at hlog
    have h₂ : Real.log (t + 1) - Real.log t = Real.log (1 + 1 / t) := by
      rw [← Real.log_div (by positivity : t + 1 ≠ 0) ht.ne', add_div, div_self ht.ne']
    have h₃ : 2 / (2 * t + 1) - (1 / (t + 1) + 1 / (2 * (t + 1)) - 1 / (2 * (t + 2))) =
        3 / (2 * (2 * t + 1) * (t + 1) * (t + 2)) := by
      field_simp [show 2 * t + 1 ≠ 0 by positivity, show t + 1 ≠ 0 by positivity,
        show t + 2 ≠ 0 by positivity]
      <;> ring
    have h₄ : f (n + 1) - f n =
        1 / (t + 1) - (Real.log (t + 1) - Real.log t) -
          1 / (2 * (t + 2)) + 1 / (2 * (t + 1)) := by
      unfold f
      rw [harmonic_succ (n + 1)]
      push_cast
      dsimp [t]
      ring_nf
    rw [← sub_nonpos, h₄, h₂]
    linarith [show 0 ≤ 3 / (2 * (2 * t + 1) * (t + 1) * (t + 2)) by positivity]
  have h₀ := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hDen : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 2)) atTop atTop := by
    refine tendsto_atTop.2 fun x =>
      ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop x)).mono fun n hn => ?_
    change x ≤ (n : ℝ) at hn
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hlim : Tendsto f atTop (𝓝 Real.eulerMascheroniConstant) := by
    simpa only [f, Function.comp_def, Nat.cast_add, Nat.cast_one, one_div, sub_zero] using
      h₀.sub (tendsto_inv_atTop_zero.comp hDen)
  exact hmono.le_of_tendsto hlim n

theorem eulerMascheroni_lt_5777 :
    Real.eulerMascheroniConstant < (5777 / 10000 : ℝ) := by
  have h := eulerMascheroni_le_corrected_harmonic 31
  have hlog : Real.log 32 = 5 * Real.log 2 := by
    simpa only [show (2 : ℝ)^5 = 32 by norm_num, Nat.cast_ofNat] using Real.log_pow (2 : ℝ) 5
  norm_num [harmonic, Finset.sum_range_succ] at h
  rw [hlog] at h
  linarith [Real.log_two_gt_d9]

theorem log_four_pi_gt_25309 : (25309 / 10000 : ℝ) < Real.log (4 * Real.pi) := by
  have hsum := Real.sum_range_le_log_div (x := (2283 / 10283 : ℝ)) (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hsum
  have hlog : Real.log (6283 / 500) = 3 * Real.log 2 + Real.log (6283 / 4000) := by
    have hp : Real.log ((2 : ℝ)^3) = (3 : ℝ) * Real.log 2 := by simpa using Real.log_pow (2 : ℝ) 3
    rw [← hp, ← Real.log_mul (by norm_num : (2 : ℝ)^3 ≠ 0)
      (by norm_num : (6283 / 4000 : ℝ) ≠ 0)]
    norm_num
  have hval : (25309 / 10000 : ℝ) < Real.log (6283 / 500) := by
    rw [hlog]
    linarith [Real.log_two_gt_d9, hsum]
  exact hval.trans_le (Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_d4]))

theorem reciprocal_zero_constant_lt :
    2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) < (47 / 1000 : ℝ) := by
  linarith [eulerMascheroni_lt_5777, log_four_pi_gt_25309]

end GoldbachExplicit
