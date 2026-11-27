import Mathlib

/-! Exact support and diagonal computations for the second spectral test. -/

open scoped ArithmeticFunction.vonMangoldt Chebyshev
noncomputable section

namespace GoldbachExplicit

def inverseTest (lam u : ℝ) : ℝ :=
  if |u| ≤ lam then Real.exp (|u| / 2) * (Real.exp (lam - |u|) - 1) else 0

@[simp] theorem inverseTest_zero {lam : ℝ} (hlam : 0 ≤ lam) :
    inverseTest lam 0 = Real.exp lam - 1 := by simp [inverseTest, hlam]

theorem inverseTest_eq_zero_of_lt_abs {lam u : ℝ} (h : lam < |u|) :
    inverseTest lam u = 0 := by simp [inverseTest, h.not_ge]

private theorem one_div_add_one_le_log_gap {n : ℕ} (hn : 0 < n) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn₁ : 0 < (n : ℝ) + 1 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hn' hn₁)
  have hd : (n : ℝ) / (n + 1) - 1 = -(1 / (n + 1 : ℝ)) := by
    field_simp [hn₁.ne'] <;> ring
  rw [Real.log_div hn'.ne' hn₁.ne', hd] at h
  linarith

theorem log_locations_separated {lam : ℝ} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≠ n)
    (hsep : lam * ((n : ℝ) + 1) < 1) :
    lam < |Real.log m - Real.log n| := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have h₀ : lam < 1 / ((n : ℝ) + 1) := (lt_div_iff₀ (by positivity)).2 hsep
  rcases lt_or_gt_of_ne hmn with h | h
  · have hcast : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h
    have he := Real.log_le_log (show 0 < (m : ℝ) + 1 by positivity) hcast
    have hc : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
      (show 0 < (m : ℝ) + 1 by positivity) (show (m : ℝ) + 1 ≤ (n : ℝ) + 1 by linarith)
    have hh := one_div_add_one_le_log_gap hm
    rw [abs_of_nonpos (by linarith [Real.log_le_log hm' (show (m : ℝ) ≤ n by linarith)])]
    linarith
  · have hcast : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h
    have he := Real.log_le_log (show 0 < (n : ℝ) + 1 by positivity) hcast
    have hh := one_div_add_one_le_log_gap hn
    rw [abs_of_nonneg (by linarith [Real.log_le_log hn' (show (n : ℝ) ≤ m by linarith)])]
    linarith

/-- The inverse Fourier support gives exactly one prime term for the
second Weil test. The statement applies to all integers, including
prime powers. -/
theorem translated_inverseTest_diagonal {lam : ℝ} {n m : ℕ}
    (hlam : 0 ≤ lam) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hsep : lam * ((n : ℝ) + 1) < 1) :
    (inverseTest lam (Real.log m - Real.log n) +
      inverseTest lam (Real.log m + Real.log n)) / 2 =
      if m = n then (Real.exp lam - 1) / 2 else 0 := by
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : lam < 1 / 3 := by
    have h := mul_le_mul_of_nonneg_left (show (3 : ℝ) ≤ (n : ℝ) + 1 by linarith) hlam
    linarith
  have hplus : lam < |Real.log m + Real.log n| := by
    have h₁ := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hm₂
    have h₂ := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn₂
    linarith [le_abs_self (Real.log m + Real.log n), Real.log_two_gt_d9]
  rw [inverseTest_eq_zero_of_lt_abs hplus, add_zero]
  by_cases he : m = n
  · subst m
    simp [hlam]
  · rw [if_neg he, inverseTest_eq_zero_of_lt_abs
      (log_locations_separated (by omega : 0 < n) (by omega : 0 < m) he hsep), zero_div]

/-- A Chebyshev increment supported on one positive integer is exactly
the von Mangoldt weight of that integer. -/
theorem psi_sub_eq_vonMangoldt {a b : ℝ} {n : ℕ} (hn : 0 < n)
    (ha₀ : 0 ≤ a) (ha : (n : ℝ) - 1 ≤ a) (han : a < n)
    (hnb : (n : ℝ) ≤ b) (hb : b < (n : ℝ) + 1) :
    Chebyshev.psi b - Chebyshev.psi a = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hb₀ : 0 ≤ b := ha₀.trans (han.le.trans hnb)
  have hal : k ≤ ⌊a⌋₊ := (Nat.le_floor_iff ha₀).2 (by
    push_cast at ha
    linarith)
  have hau : ⌊a⌋₊ < k + 1 := (Nat.floor_lt ha₀).2 (by exact_mod_cast han)
  have hbl : k + 1 ≤ ⌊b⌋₊ := (Nat.le_floor_iff hb₀).2 (by exact_mod_cast hnb)
  have hbu : ⌊b⌋₊ < k + 1 + 1 := (Nat.floor_lt hb₀).2 (by exact_mod_cast hb)
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc,
    show ⌊a⌋₊ = k by omega, show ⌊b⌋₊ = k + 1 by omega]
  rw [Finset.sum_Icc_succ_top (by omega : 0 ≤ k + 1)]
  ring

end GoldbachExplicit
