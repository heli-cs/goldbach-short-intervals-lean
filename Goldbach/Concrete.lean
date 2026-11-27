import Mathlib

/-! Concrete odd-prime density and the reflection reduction. -/

open MeasureTheory
open scoped BigOperators

namespace GoldbachConcrete

/-- A sum of two odd primes in (x,x+H]. -/
def HasGoldbach (x H : ℝ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
    x < (p : ℝ) + (q : ℝ) ∧ (p : ℝ) + (q : ℝ) ≤ x + H

noncomputable def primeWeight (d y : ℝ) (p : ℕ) : ℝ := by
  classical
  exact if Nat.Prime p ∧ Odd p ∧ y < (p : ℝ) ∧
      (p : ℝ) ≤ (1 + d) * y then Real.log (p : ℝ) else 0

/-- Concrete odd-prime Chebyshev density on (y,(1+d)y]. -/
noncomputable def density (d y : ℝ) : ℝ :=
  (∑ p ∈ Finset.range (Nat.ceil ((1 + d) * y) + 1),
    primeWeight d y p) / (d * y)

/-- A nonzero finite weighted prime count gives an actual prime witness. -/
theorem density_witness (d y : ℝ) (hF : density d y ≠ 0) :
    ∃ p : ℕ, Nat.Prime p ∧ Odd p ∧ y < (p : ℝ) ∧
      (p : ℝ) ≤ (1 + d) * y := by
  classical
  by_contra h
  apply hF
  unfold density
  have hz : (∑ p ∈ Finset.range (Nat.ceil ((1 + d) * y) + 1),
      primeWeight d y p) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    have hn : ¬ (Nat.Prime p ∧ Odd p ∧ y < (p : ℝ) ∧
        (p : ℝ) ≤ (1 + d) * y) := fun hp => h ⟨p, hp⟩
    simp [primeWeight, hn]
  rw [hz, zero_div]

theorem no_pair (x d y : ℝ) (hn : ¬ HasGoldbach x (d * x)) :
    density d y * density d (x - y) = 0 := by
  by_cases h₁ : density d y = 0
  · simp [h₁]
  by_cases h₂ : density d (x - y) = 0
  · simp [h₂]
  obtain ⟨p, hp, hop, hp₁, hp₂⟩ := density_witness d y h₁
  obtain ⟨q, hq, hoq, hq₁, hq₂⟩ := density_witness d (x - y) h₂
  exfalso
  apply hn
  refine ⟨p, q, hp, hq, hop, hoq, ?_, ?_⟩
  · linarith
  · calc
      (p : ℝ) + (q : ℝ) ≤ (1 + d) * y + (1 + d) * (x - y) :=
        add_le_add hp₂ hq₂
      _ = x + d * x := by ring

theorem pair_deficit (A B : ℝ) (hz : A * B = 0) :
    2 * (A + B - 1) ≤ (A - 1)^2 + (B - 1)^2 := by
  nlinarith only [hz, sq_nonneg (A + B - 2)]

noncomputable def window (c x : ℝ) : ℝ := c * (Real.log x)^2
noncomputable def relativeWidth (c x : ℝ) : ℝ := window c x / x
noncomputable def trim (c : ℝ) : ℝ := (1 - 1 / c) / 4
noncomputable def region (c x : ℝ) : Set ℝ :=
  Set.Icc (trim c * x) ((1 - trim c) * x)
noncomputable def regionMeasure (c x : ℝ) : Measure ℝ :=
  volume.restrict (region c x)

noncomputable def firstIntegrand (c x y : ℝ) : ℝ :=
  2 * (density (relativeWidth c x) y +
    density (relativeWidth c x) (x - y) - 1)

noncomputable def errorIntegrand (c x y : ℝ) : ℝ :=
  (density (relativeWidth c x) y - 1)^2 +
    (density (relativeWidth c x) (x - y) - 1)^2

noncomputable def midpoint (c x : ℝ) : ℝ :=
  (1 - 2 * trim c + 1 / c) * x

/-- First-moment proposition proved in Goldbach.FirstMoment.
Expected first integral is asymptotic to 2*(1-2*trim c)*x. -/
def FirstMomentInput : Prop :=
  ∀ c : ℝ, 1 < c → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
    Integrable (firstIntegrand c x) (regionMeasure c x) ∧
    midpoint c x < (∫ y, firstIntegrand c x y ∂regionMeasure c x)

/-- Second-moment proposition for the Gaussian-kernel argument,
prime-power removal, reflection, and integrability. Expected upper bound
is (2/c+o(1))*x, strictly below the chosen midpoint for c>1. -/
def SecondMomentInput : Prop :=
  ∀ c : ℝ, 1 < c → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
    Integrable (errorIntegrand c x) (regionMeasure c x) ∧
    (∫ y, errorIntegrand c x y ∂regionMeasure c x) ≤ midpoint c x

/-- The actual mathematical statement to be proved. Uses Mathlib's RH. -/
def Target : Prop :=
  RiemannHypothesis → ∀ c : ℝ, 1 < c → ∃ X : ℝ, ∀ x : ℝ,
    X ≤ x → HasGoldbach x (window c x)

/-- A concrete contradiction, with analytic estimates as explicit inputs. -/
theorem pointwise_conclusion (c x : ℝ) (hx : 0 < x)
    (hfi : Integrable (firstIntegrand c x) (regionMeasure c x))
    (hei : Integrable (errorIntegrand c x) (regionMeasure c x))
    (hfirst : midpoint c x <
      (∫ y, firstIntegrand c x y ∂regionMeasure c x))
    (hsecond : (∫ y, errorIntegrand c x y ∂regionMeasure c x) ≤
      midpoint c x) : HasGoldbach x (window c x) := by
  by_contra hn
  have hw : relativeWidth c x * x = window c x := by
    unfold relativeWidth
    exact div_mul_cancel₀ _ (ne_of_gt hx)
  have hn' : ¬ HasGoldbach x (relativeWidth c x * x) := by
    rw [hw]
    exact hn
  have hp : ∀ y, firstIntegrand c x y ≤ errorIntegrand c x y := by
    intro y
    exact pair_deficit _ _ (no_pair x (relativeWidth c x) y hn')
  have hi := integral_mono hfi hei hp
  exact (not_lt_of_ge (le_trans hi hsecond)) hfirst

/-- Reflection reduces the target to the stated first and second moments. -/
theorem conditional_target (hFirst : FirstMomentInput)
    (hSecond : RiemannHypothesis → SecondMomentInput) : Target := by
  intro hRH c hc
  obtain ⟨X₁, h₁⟩ := hFirst c hc
  obtain ⟨X₂, h₂⟩ := hSecond hRH c hc
  refine ⟨max 1 (max X₁ X₂), ?_⟩
  intro x hx
  have hx₀ : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_trans (le_max_left _ _) hx)
  have hx₁ : X₁ ≤ x := le_trans (le_max_left X₁ X₂)
    (le_trans (le_max_right 1 (max X₁ X₂)) hx)
  have hx₂ : X₂ ≤ x := le_trans (le_max_right X₁ X₂)
    (le_trans (le_max_right 1 (max X₁ X₂)) hx)
  obtain ⟨hfi, hf⟩ := h₁ x hx₁
  obtain ⟨hei, he⟩ := h₂ x hx₂
  exact pointwise_conclusion c x hx₀ hfi hei hf he

#print axioms density_witness
#print axioms no_pair
#print axioms pair_deficit
#print axioms pointwise_conclusion
#print axioms conditional_target
#check Target

end GoldbachConcrete
