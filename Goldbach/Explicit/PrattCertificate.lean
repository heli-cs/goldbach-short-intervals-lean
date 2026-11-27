import Mathlib.NumberTheory.LucasPrimality

/-! Primality from checked Pratt certificates. -/

namespace GoldbachExplicit

/-- The checks for the prime factors of `n - 1`. The exponents in the
factorization are accounted for by the separate product equality. -/
def LucasFactorTests (n base : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | (p, _) :: rest =>
      p.Prime ∧ (base : ZMod n) ^ ((n - 1) / p) ≠ 1 ∧ LucasFactorTests n base rest

private theorem factor_test_of_mem {n base : ℕ} {factors : List (ℕ × ℕ)}
    (h : LucasFactorTests n base factors) {r : ℕ × ℕ} (hr : r ∈ factors) :
    r.1.Prime ∧ (base : ZMod n) ^ ((n - 1) / r.1) ≠ 1 := by
  induction factors with
  | nil => simp at hr
  | cons f factors ih =>
      obtain ⟨p, k⟩ := f
      rcases List.mem_cons.mp hr with rfl | hmem
      · exact ⟨h.1, h.2.1⟩
      · exact ih h.2.2 hmem

private theorem exists_factor_of_prime_dvd_product {p : ℕ} (hp : p.Prime)
    (factors : List (ℕ × ℕ)) (h : p ∣ (factors.map fun r => r.1 ^ r.2).prod) :
    ∃ r ∈ factors, p ∣ r.1 := by
  induction factors with
  | nil =>
      exact (hp.not_dvd_one (by simpa only [List.map_nil, List.prod_nil] using h)).elim
  | cons r factors ih =>
      rw [List.map_cons, List.prod_cons] at h
      rcases hp.dvd_mul.mp h with h | h
      · exact ⟨r, List.mem_cons_self, hp.dvd_of_dvd_pow h⟩
      · obtain ⟨q, hq, hdiv⟩ := ih h
        exact ⟨q, List.mem_cons_of_mem _ hq, hdiv⟩

/-- The product and the modular power identities are checked in Lean. Every
prime divisor of `n - 1` occurs in the supplied complete factorization. -/
theorem prime_of_lucas_factorization {n base : ℕ} {factors : List (ℕ × ℕ)}
    (hprod : (factors.map fun r => r.1 ^ r.2).prod = n - 1)
    (hbase : (base : ZMod n) ^ (n - 1) = 1) (htests : LucasFactorTests n base factors) :
    n.Prime := by
  apply lucas_primality n (base : ZMod n) hbase
  intro p hp hdiv
  rw [← hprod] at hdiv
  obtain ⟨r, hr, hpr⟩ := exists_factor_of_prime_dvd_product hp factors hdiv
  obtain ⟨hprime, hne⟩ := factor_test_of_mem htests hr
  rwa [(Nat.prime_dvd_prime_iff_eq hp hprime).mp hpr]

end GoldbachExplicit
