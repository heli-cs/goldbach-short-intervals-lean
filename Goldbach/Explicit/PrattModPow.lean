import Goldbach.Explicit.PrattCertificate

/-! Kernel evaluation of the modular powers in a Lucas certificate. -/

namespace GoldbachExplicit

/-- Binary modular exponentiation with an explicit bound on the exponent's bit length. -/
def prattModPow (base modulus : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % modulus
  | fuel + 1, exponent =>
    let half := prattModPow base modulus fuel (exponent / 2)
    let square := (half * half) % modulus
    if exponent % 2 = 0 then square else (square * base) % modulus

theorem prattModPow_eq {base modulus fuel exponent : ℕ} (h : exponent < 2 ^ fuel) :
    prattModPow base modulus fuel exponent = base ^ exponent % modulus := by
  induction fuel generalizing exponent with
  | zero =>
    have he : exponent = 0 := by simpa using h
    simp [he, prattModPow]
  | succ fuel ih =>
    rw [pow_succ] at h
    have hh : exponent / 2 < 2 ^ fuel := by omega
    have he : exponent = exponent / 2 + exponent / 2 + exponent % 2 := by omega
    have hpow : base ^ exponent = base ^ (exponent / 2) * base ^ (exponent / 2) *
        base ^ (exponent % 2) := by
      rw [← pow_add, ← pow_add, ← he]
    rw [prattModPow, ih hh, hpow]
    by_cases hb : exponent % 2 = 0
    · simp only [hb, if_pos, pow_zero, mul_one, Nat.mod_mul_mod, Nat.mul_mod_mod]
    · have hb' : exponent % 2 = 1 := by omega
      simp only [hb', Nat.one_ne_zero, if_false, pow_one, Nat.mod_mul_mod, Nat.mul_mod_mod]

private theorem zmod_pow_eq_one_iff_prattModPow {n base fuel exponent : ℕ}
    (hn : 1 < n) (hfuel : exponent < 2 ^ fuel) :
    (base : ZMod n) ^ exponent = 1 ↔ prattModPow base n fuel exponent = 1 := by
  rw [prattModPow_eq hfuel, ← Nat.cast_pow, ← Nat.cast_one (R := ZMod n),
    ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hn]

/-- The primality and modular power checks for the factors of `n - 1`. -/
def PrattModularTests (n base fuel : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | (p, _) :: rest => p.Prime ∧ prattModPow base n fuel ((n - 1) / p) ≠ 1 ∧
    PrattModularTests n base fuel rest

private theorem lucasFactorTests_of_modular {n base fuel : ℕ} (hn : 1 < n)
    (hfuel : n - 1 < 2 ^ fuel) {factors : List (ℕ × ℕ)}
    (htests : PrattModularTests n base fuel factors) : LucasFactorTests n base factors := by
  induction factors with
  | nil => trivial
  | cons row rest ih =>
    obtain ⟨p, exp⟩ := row
    obtain ⟨hp, hm, hrest⟩ := htests
    have he := (Nat.div_le_self (n - 1) p).trans_lt hfuel
    exact ⟨hp, fun h => hm ((zmod_pow_eq_one_iff_prattModPow hn he).mp h), ih hrest⟩

/-- A Lucas certificate with its exponentiations evaluated using only natural arithmetic. -/
theorem prime_of_pratt_modular {n base fuel : ℕ} {factors : List (ℕ × ℕ)}
    (hn : 1 < n) (hfuel : n - 1 < 2 ^ fuel)
    (hprod : (factors.map fun r => r.1 ^ r.2).prod = n - 1)
    (hbase : prattModPow base n fuel (n - 1) = 1)
    (htests : PrattModularTests n base fuel factors) : n.Prime :=
  prime_of_lucas_factorization hprod ((zmod_pow_eq_one_iff_prattModPow hn hfuel).mpr hbase)
    (lucasFactorTests_of_modular hn hfuel htests)

end GoldbachExplicit
