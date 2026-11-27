import Goldbach.Concrete
import Goldbach.Explicit.PrattCertificate

/-! Finite certificates for fixed-width windows over real half-open intervals. -/

namespace GoldbachExplicit

private def checkWidthCover {α : Type} (value : α → ℕ)
    (width right : ℕ) : ℕ → List α → Bool
  | left, [] => decide (right ≤ left)
  | left, row :: rest =>
      decide (left < value row ∧ value row ≤ left + width) &&
        checkWidthCover value width right (value row) rest

private theorem witness_of_checkWidthCover {α : Type}
    {value : α → ℕ} {width left right : ℕ} {rows : List α}
    (h : checkWidthCover value width right left rows = true) {x : ℝ}
    (hx : (left : ℝ) ≤ x) (hxright : x < (right : ℝ)) :
    ∃ row : α, x < (value row : ℝ) ∧ (value row : ℝ) ≤ x + width := by
  induction rows generalizing left with
  | nil =>
      simp only [checkWidthCover, decide_eq_true_eq] at h
      have hright : (right : ℝ) ≤ (left : ℝ) := by exact_mod_cast h
      exact (not_lt_of_ge (hright.trans hx) hxright).elim
  | cons row rest ih =>
      simp only [checkWidthCover, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨_, hgap⟩, hrest⟩ := h
      by_cases hxs : x < (value row : ℝ)
      · have hgap' : (value row : ℝ) ≤ (left : ℝ) + (width : ℝ) := by exact_mod_cast hgap
        exact ⟨row, hxs, hgap'.trans (add_le_add_left hx _)⟩
      · exact ih hrest (le_of_not_gt hxs)

/-- The value and the kernel-checked primality and parity proof of a witness. -/
structure CertifiedOddPrime where
  number : ℕ
  prime : number.Prime
  odd : Odd number

/-- Both summands of a certified Goldbach number. -/
structure PairCertificate where
  left : CertifiedOddPrime
  right : CertifiedOddPrime

def PairCertificate.sum (pair : PairCertificate) : ℕ :=
  pair.left.number + pair.right.number

/-- The sums increase, with each step at most the allowed width. The last
sum must reach the right endpoint. -/
def checkIntervalCover (width right left : ℕ) (rows : List PairCertificate) : Bool :=
  checkWidthCover PairCertificate.sum width right left rows

/-- Each checked sum covers the real inputs before that sum. -/
theorem interval_cover_of_check {width left right : ℕ} {rows : List PairCertificate}
    (h : checkIntervalCover width right left rows = true) :
    ∀ x : ℝ, (left : ℝ) ≤ x → x < (right : ℝ) →
      GoldbachConcrete.HasGoldbach x (width : ℝ) := by
  intro x hx hxright
  obtain ⟨row, hlo, hhi⟩ := witness_of_checkWidthCover h hx hxright
  have hsum : (row.sum : ℝ) = (row.left.number : ℝ) + (row.right.number : ℝ) := by
    simp [PairCertificate.sum]
  rw [hsum] at hlo hhi
  exact ⟨_, _, row.left.prime, row.right.prime, row.left.odd, row.right.odd, hlo, hhi⟩

/-- An odd prime in the real interval `(x, x + width]`. -/
def HasOddPrime (x width : ℝ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ Odd p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x + width

def checkPrimeIntervalCover (width right left : ℕ) (rows : List CertifiedOddPrime) : Bool :=
  checkWidthCover CertifiedOddPrime.number width right left rows

/-- Interpret a checked ladder of odd primes as a real interval cover. -/
theorem prime_interval_cover_of_check {width left right : ℕ} {rows : List CertifiedOddPrime}
    (h : checkPrimeIntervalCover width right left rows = true) :
    ∀ x : ℝ, (left : ℝ) ≤ x → x < (right : ℝ) → HasOddPrime x (width : ℝ) := by
  intro x hx hxright
  obtain ⟨row, hlo, hhi⟩ := witness_of_checkWidthCover h hx hxright
  exact ⟨_, row.prime, row.odd, hlo, hhi⟩

/-- Glue two Goldbach covers at a common endpoint. The right block includes the seam. -/
theorem join_goldbach_interval_covers {a b c : ℝ} {H : ℝ → ℝ}
    (h₁ : ∀ x : ℝ, a ≤ x → x < b → GoldbachConcrete.HasGoldbach x (H x))
    (h₂ : ∀ x : ℝ, b ≤ x → x < c → GoldbachConcrete.HasGoldbach x (H x)) :
    ∀ x : ℝ, a ≤ x → x < c → GoldbachConcrete.HasGoldbach x (H x) := by
  intro x hx hx'
  by_cases h : x < b
  · exact h₁ x hx h
  · exact h₂ x (le_of_not_gt h) hx'

theorem join_prime_interval_covers {a b c width : ℝ}
    (h₁ : ∀ x : ℝ, a ≤ x → x < b → HasOddPrime x width)
    (h₂ : ∀ x : ℝ, b ≤ x → x < c → HasOddPrime x width) :
    ∀ x : ℝ, a ≤ x → x < c → HasOddPrime x width := by
  intro x hx hx'
  by_cases h : x < b
  · exact h₁ x hx h
  · exact h₂ x (le_of_not_gt h) hx'

/-- A fixed width gives the logarithmic-square width if it suffices at the left endpoint. -/
theorem log_sq_cover_of_width {a b width : ℝ} (ha : 1 ≤ a)
    (hw : width ≤ (Real.log a)^2)
    (h : ∀ x : ℝ, a ≤ x → x < b → GoldbachConcrete.HasGoldbach x width) :
    ∀ x : ℝ, a ≤ x → x < b → GoldbachConcrete.HasGoldbach x ((Real.log x)^2) := by
  intro x hx hx'
  obtain ⟨p, q, hp, hq, hpo, hqo, hlo, hhi⟩ := h x hx hx'
  have hlog := Real.log_le_log (zero_lt_one.trans_le ha) hx
  have hwidth := hw.trans (pow_le_pow_left₀ (Real.log_nonneg ha) hlog 2)
  exact ⟨p, q, hp, hq, hpo, hqo, hlo, hhi.trans (add_le_add_right hwidth x)⟩

/-- A fixed odd prime translates a prime cover into a Goldbach cover. -/
theorem goldbach_interval_of_prime_shift {p : ℕ} {a b width : ℝ}
    (hp : p.Prime) (hop : Odd p)
    (h : ∀ y : ℝ, a ≤ y → y < b → HasOddPrime y width) :
    ∀ x : ℝ, a + p ≤ x → x < b + p → GoldbachConcrete.HasGoldbach x width := by
  intro x hx hx'
  obtain ⟨q, hq, hoq, hlo, hhi⟩ := h (x - p) (by linarith) (by linarith)
  exact ⟨p, q, hp, hq, hop, hoq, by linarith, by linarith⟩

/-- The outer ladder can have gaps as large as the length of the inner
covered interval. Each anchor translates the same inner prime cover. -/
theorem goldbach_interval_of_two_prime_covers {a b c d width : ℝ}
    (inner : ∀ y : ℝ, a ≤ y → y < b → HasOddPrime y width)
    (outer : ∀ z : ℝ, c ≤ z → z < d → HasOddPrime z (b - a)) :
    ∀ x : ℝ, b + c ≤ x → x < b + d → GoldbachConcrete.HasGoldbach x width := by
  intro x hx hx'
  obtain ⟨p, hp, hop, hlo, hhi⟩ := outer (x - b) (by linarith) (by linarith)
  obtain ⟨q, hq, hoq, hql, hqh⟩ := inner (x - p) (by linarith) (by linarith)
  exact ⟨p, q, hp, hq, hop, hoq, by linarith, by linarith⟩

end GoldbachExplicit
