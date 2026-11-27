import Goldbach.LogIntegral

open MeasureTheory Set

noncomputable section
namespace GoldbachArithmetic

/-- The trivial-zero term in the symmetric explicit formula for ψ. -/
def trivialZeroTerm (y : ℝ) : ℝ := -(1 / 2 : ℝ) * Real.log (1 - (y ^ 2)⁻¹)

/-- A local bound for the difference of the trivial-zero terms,
with the short relative width retained. -/
theorem trivialZeroTerm_sub_le {d y : ℝ} (hd : 0 ≤ d) (hy : 2 ≤ y) :
    |trivialZeroTerm ((1 + d) * y) - trivialZeroTerm y| ≤ 2 * d / y^2 := by
  let a := (y^2)⁻¹
  let A := 1 - a
  let B := 1 - (((1 + d) * y)^2)⁻¹
  have hY : 0 < y := by linarith
  have hd₁ : 0 < 1 + d := by linarith
  have ha₀ : 0 ≤ a := by dsimp [a]; positivity
  have ha₁ : a ≤ 1 / 2 := by
    dsimp [a]
    rw [inv_eq_one_div, div_le_div_iff₀ (sq_pos_of_pos hY) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [sq_nonneg (y - 2)]
  have hA : 0 < A := by dsimp [A]; linarith
  have hAhalf : 1 / 2 ≤ A := by dsimp [A]; linarith
  have hp : 1 ≤ (1 + d)^2 := by nlinarith [sq_nonneg d]
  have hB_eq : B = 1 - a / (1 + d)^2 := by
    dsimp [a, B]
    rw [mul_pow, mul_inv, div_eq_mul_inv, mul_comm]
  have hAB : A ≤ B := by
    rw [hB_eq]
    dsimp [A]
    exact sub_le_sub_left (div_le_self ha₀ hp) _
  have hB := hA.trans_le hAB
  have hδ : 1 - 1 / (1 + d)^2 ≤ 2 * d := by
    have hp0 : 0 < (1 + d)^2 := sq_pos_of_pos hd₁
    have h : 1 - 2 * d ≤ 1 / (1 + d)^2 := (le_div_iff₀ hp0).mpr
      (by nlinarith [sq_nonneg d, mul_nonneg hd (sq_nonneg d)])
    linarith
  have hdiff : B - A ≤ 2 * d * a := by
    rw [hB_eq]
    have he : 1 - a / (1 + d)^2 - A = a * (1 - 1 / (1 + d)^2) := by dsimp [A]; ring
    rw [he, mul_comm]
    exact mul_le_mul_of_nonneg_right hδ ha₀
  have hlogs : Real.log A ≤ Real.log B := Real.log_le_log hA hAB
  have hval : trivialZeroTerm ((1 + d) * y) - trivialZeroTerm y =
      -((Real.log B - Real.log A) / 2) := by
    dsimp [trivialZeroTerm, A, B, a]
    ring
  rw [hval, abs_neg, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hlogs) (by norm_num)),
    ← Real.log_div hB.ne' hA.ne']
  have hquot : B / A - 1 ≤ 4 * d * a := by
    rw [← div_self hA.ne', ← sub_div, div_le_iff₀ hA]
    have hm : 2 * d * a ≤ (4 * d * a) * A := by
      have hl := mul_le_mul_of_nonneg_left hAhalf (show 0 ≤ 4 * d * a by positivity)
      linarith
    exact hdiff.trans hm
  have hlog := (Real.log_le_sub_one_of_pos (div_pos hB hA)).trans hquot
  calc
    _ ≤ (4 * d * a) / 2 := div_le_div_of_nonneg_right hlog (by norm_num)
    _ = _ := by dsimp [a]; ring

/-- Two distinct integer powers of a common exponent at least two are
separated by at least the square root of the smaller power. -/
theorem sqrt_le_pow_gap {m n k : ℕ} (hm : 1 ≤ m) (hmn : m < n) (hk : 2 ≤ k) :
    Real.sqrt ((m : ℝ)^k) ≤ (n : ℝ)^k - (m : ℝ)^k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm₀ : (0 : ℝ) ≤ m := by positivity
  have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hmn)
  have hroot : Real.sqrt ((m : ℝ)^(2 + j)) ≤ (m : ℝ)^(j + 1) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [← pow_mul]
    exact pow_le_pow_right₀ hm₁ (by omega)
  have hbase : (m : ℝ) ^ (j + 1) ≤ ((m : ℝ) + 1) ^ (j + 1) :=
    pow_le_pow_left₀ hm₀ (by linarith) _
  have hstep : (m : ℝ)^(2 + j) + (m : ℝ)^(j + 1) ≤ ((m : ℝ) + 1)^(2 + j) := by
    rw [show 2 + j = (j + 1) + 1 by omega, pow_succ (m : ℝ) (j + 1),
      pow_succ ((m : ℝ) + 1) (j + 1)]
    simpa only [mul_add, mul_one, add_comm] using
      mul_le_mul_of_nonneg_right hbase (show 0 ≤ (m : ℝ) + 1 by positivity)
  have htop : ((m : ℝ) + 1)^(2 + j) ≤ (n : ℝ)^(2 + j) :=
    pow_le_pow_left₀ (by positivity) hmn' _
  linarith

end GoldbachArithmetic
