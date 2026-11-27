import Goldbach.Explicit.FiniteRange
import Goldbach.Explicit.IntervalCertificate

/-! The exact real-interval premise for a sparse finite certificate. -/

/-- The finite real-interval coverage needed below the analytic cutoff. -/
def FiniteGoldbachIntervalCoverage : Prop :=
  ∀ x : ℝ, 5 ≤ x → x < Real.exp 42 → GoldbachConcrete.HasGoldbach x ((Real.log x)^2)

/-- With an even left endpoint, checking the even arguments in a half-open
block suffices. The witness at `n` is even and at least `n + 2`, so it also
works strictly to the right of every real argument in `[n, n + 2)`. -/
theorem goldbach_log_sq_real_cover_iff_even {a : ℕ} {b : ℝ} (ha : 1 ≤ a) (heven : Even a) :
    (∀ x : ℝ, (a : ℝ) ≤ x → x < b → GoldbachConcrete.HasGoldbach x ((Real.log x)^2)) ↔
    ∀ n : ℕ, a ≤ n → (n : ℝ) < b → Even n →
      GoldbachConcrete.HasGoldbach n ((Real.log (n : ℝ))^2) := by
  constructor
  · intro h n han hnb _
    exact h n (by exact_mod_cast han) hnb
  · intro h x hax hxb
    have hax₁ : 1 ≤ x := (show (1 : ℝ) ≤ (a : ℝ) by exact_mod_cast ha).trans hax
    have hx₀ : 0 ≤ x / 2 := by linarith
    let n := 2 * ⌊x / 2⌋₊
    have hnx : (n : ℝ) ≤ x := by
      push_cast [n]
      linarith [Nat.floor_le hx₀]
    have hxn : x < (n : ℝ) + 2 := by
      push_cast [n]
      linarith [Nat.lt_floor_add_one (x / 2)]
    have han : a ≤ n := by
      obtain ⟨k, hk⟩ := heven
      have hka : (k : ℝ) ≤ x / 2 := by
        rw [hk, Nat.cast_add] at hax
        linarith
      have hkfloor := (Nat.le_floor_iff hx₀).2 hka
      dsimp [n]
      omega
    obtain ⟨p, q, hp, hq, hpo, hqo, hlo, hhi⟩ :=
      h n han (hnx.trans_lt hxb) ⟨⌊x / 2⌋₊, two_mul _⟩
    have hnlt : n < p + q := by exact_mod_cast hlo
    obtain ⟨k, hk⟩ := hpo.add_odd hqo
    have hn₂ : n + 2 ≤ p + q := by
      dsimp [n] at *
      omega
    have hlo' : x < (p : ℝ) + (q : ℝ) :=
      hxn.trans_le (by exact_mod_cast hn₂)
    have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast ha.trans han
    have hlog := Real.log_le_log (zero_lt_one.trans_le hn₁) hnx
    have hsquare := pow_le_pow_left₀ (Real.log_nonneg hn₁) hlog 2
    exact ⟨p, q, hp, hq, hpo, hqo, hlo', hhi.trans (add_le_add hnx hsquare)⟩

theorem finiteGoldbachIntervalCoverage_of_finite
    (h : FiniteGoldbachExplicitRange) : FiniteGoldbachIntervalCoverage :=
  fun _ hx hcut => goldbach_short_interval_finite_of_finite h hx hcut

/-- A certificate that covers the real intervals suffices for the exact
coefficient-one conclusion from five onwards. -/
theorem goldbach_short_interval_explicit_of_interval_coverage
    (hRH : RiemannHypothesis) (hcover : FiniteGoldbachIntervalCoverage) :
    ∀ x : ℝ, 5 ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + (Real.log x)^2 := by
  intro x hx
  by_cases hcut : x < Real.exp 42
  · exact hcover x hx hcut
  · exact goldbach_short_interval_explicit_large hRH x (le_of_not_gt hcut)
