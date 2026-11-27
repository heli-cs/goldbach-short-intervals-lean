import Goldbach.Explicit.LargeRange

/-! The finite premise and the bridge for the coefficient-one Goldbach interval. -/

/-- Even arguments needed to take the next even integer for all real
`5 ≤ x < Real.exp 42`. -/
def FiniteGoldbachExplicitRange : Prop :=
  ∀ n : ℕ, 6 ≤ n → (n : ℝ) < Real.exp 42 + 2 → Even n →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧ p + q = n

private theorem two_le_log_sq {x : ℝ} (hx : 5 ≤ x) :
    (2 : ℝ) ≤ (Real.log x)^2 := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ)^2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hlogRatio := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 5 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), hlog4] at hlogRatio
  have hlog5 : (3 / 2 : ℝ) ≤ Real.log 5 := by
    linarith [Real.log_two_gt_d9]
  have hlogx := hlog5.trans (Real.log_le_log (by norm_num) hx)
  calc
    (2 : ℝ) ≤ (3 / 2 : ℝ)^2 := by norm_num
    _ ≤ (Real.log x)^2 := pow_le_pow_left₀ (by norm_num) hlogx _

/-- The finite premise gives a Goldbach number in the required interval for
each real argument below the analytic cutoff. -/
theorem goldbach_short_interval_finite_of_finite
    (hfin : FiniteGoldbachExplicitRange) {x : ℝ}
    (hx : 5 ≤ x) (hcut : x < Real.exp 42) :
    GoldbachConcrete.HasGoldbach x ((Real.log x)^2) := by
  let k := ⌊x / 2⌋₊ + 1
  let n := 2 * k
  have hklt : x / 2 < (k : ℝ) := by
    simpa [k] using Nat.lt_floor_add_one (x / 2)
  have hkle : (k : ℝ) ≤ x / 2 + 1 := by
    have hfloor := Nat.floor_le (show 0 ≤ x / 2 by linarith)
    simpa [k] using add_le_add_right hfloor 1
  have hncast : (n : ℝ) = 2 * (k : ℝ) := by simp [n]
  have hxlt : x < (n : ℝ) := by linarith
  have hxle : (n : ℝ) ≤ x + 2 := by linarith
  have hn6 : 6 ≤ n := by
    have h5 : (5 : ℝ) < (n : ℝ) := hx.trans_lt hxlt
    exact_mod_cast h5
  have hneven : Even n := ⟨k, two_mul k⟩
  obtain ⟨p, q, hp, hq, hpo, hqo, hpq⟩ :=
    hfin n hn6 (by linarith) hneven
  have hpqReal : (p : ℝ) + (q : ℝ) = (n : ℝ) := by exact_mod_cast hpq
  exact ⟨p, q, hp, hq, hpo, hqo, hpqReal.symm ▸ hxlt,
    hpqReal.symm ▸ hxle.trans (add_le_add_right (two_le_log_sq hx) x)⟩

/-- The all-range coefficient-one statement from RH and the exact finite premise. -/
theorem goldbach_short_interval_explicit_of_finite
    (hRH : RiemannHypothesis) (hfin : FiniteGoldbachExplicitRange) :
    ∀ x : ℝ, 5 ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + (Real.log x)^2 := by
  intro x hx
  by_cases hcut : x < Real.exp 42
  · exact goldbach_short_interval_finite_of_finite hfin hx hcut
  · exact goldbach_short_interval_explicit_large hRH x (le_of_not_gt hcut)

/-- Prime representations below the published computation bound would supply
the finite premise. Parity forces both summands to be odd for even `n ≥ 6`. -/
theorem finiteGoldbachExplicitRange_of_prime_representations
    (hcomputed : ∀ n : ℕ, 6 ≤ n → n < 4000000000000000000 → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) :
    FiniteGoldbachExplicitRange := by
  have hcut : Real.exp 42 + 2 < (4000000000000000000 : ℝ) := by
    have hbase : Real.exp 1 ≤ 272 / 100 := by linarith [Real.exp_one_lt_d9]
    calc
      Real.exp 42 + 2 = (Real.exp 1)^42 + 2 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (272 / 100 : ℝ)^42 + 2 :=
        add_le_add_left (pow_le_pow_left₀ (Real.exp_pos 1).le hbase 42) 2
      _ < _ := by norm_num
  intro n hn hnbound heven
  have hncert : n < 4000000000000000000 := by
    exact_mod_cast hnbound.trans hcut
  obtain ⟨p, q, hp, hq, hsum⟩ := hcomputed n hn hncert heven
  obtain ⟨k, hk⟩ := heven
  have hpp := hp.eq_two_or_odd
  have hqp := hq.eq_two_or_odd
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  exact ⟨p, q, hp, hq, hp.odd_of_ne_two hp2, hq.odd_of_ne_two hq2, hsum⟩
