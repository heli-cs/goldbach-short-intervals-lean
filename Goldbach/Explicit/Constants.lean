import Mathlib

/-! Lean enclosures for two constants checked separately by the Arb script. -/

noncomputable section

namespace GoldbachExplicit

theorem prime_coefficient_lt :
    (624 / 100 : ℝ) / Real.pi^2 < 633 / 1000 := by
  apply (div_lt_iff₀ (by positivity : 0 < Real.pi^2)).mpr
  have hp : (3.14159 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  have h := pow_lt_pow_left₀ hp (by norm_num : (0 : ℝ) ≤ 3.14159) (by norm_num : (2 : ℕ) ≠ 0)
  linarith only [h]

private theorem log_two_pi_lt : Real.log (2 * Real.pi) < (19 / 10 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have hp : (2 * Real.pi)^10 ≤ (32 / 5 : ℝ)^10 :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.pi_lt_d6]) 10
  have he : (27 / 10 : ℝ)^19 < (Real.exp 1)^19 :=
    pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9])
      (by norm_num) (by norm_num : (19 : ℕ) ≠ 0)
  have hbase : (32 / 5 : ℝ)^10 < (27 / 10 : ℝ)^19 := by norm_num
  have hpower : (Real.exp 1)^19 = (Real.exp (19 / 10))^10 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  have h := hp.trans_lt (hbase.trans (he.trans_eq hpower))
  by_contra! hn
  exact (not_lt_of_ge (pow_le_pow_left₀ (Real.exp_pos _).le hn 10)) h

theorem rational_tail_integral_coefficient_lt :
    ((Real.log (2 * Real.pi))^2 + 2 * Real.log (2 * Real.pi) + 2) / Real.pi^2 < 1 := by
  apply (div_lt_iff₀ (by positivity : 0 < Real.pi^2)).mpr
  have hlog₀ : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    linarith [Real.pi_gt_three]
  have hlog := log_two_pi_lt
  have hpow := pow_le_pow_left₀ hlog₀ hlog.le 2
  have hp : (3.1 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  have hp₂ := pow_lt_pow_left₀ hp (by norm_num : (0 : ℝ) ≤ 3.1) (by norm_num : (2 : ℕ) ≠ 0)
  linarith only [hlog, hpow, hp₂]

end GoldbachExplicit
