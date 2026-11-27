import Mathlib

/-! Finite Schur inequalities for the Gaussian-kernel method. -/

open scoped BigOperators

namespace GoldbachSchur

 theorem pair_bound (k a b : ℝ) (hk : 0 ≤ k) :
    2 * (k * (a * b)) ≤ k * a ^ 2 + k * b ^ 2 := by
  have h : 0 ≤ k * (a - b)^2 := mul_nonneg hk (sq_nonneg _)
  nlinarith only [h]

 theorem finite_schur {ι : Type*} (s : Finset ι)
    (K : ι → ι → ℝ) (a : ι → ℝ)
    (hK : ∀ i j, 0 ≤ K i j)
    (hSym : ∀ i j, K i j = K j i) :
    (∑ i ∈ s, ∑ j ∈ s, K i j * (a i * a j)) ≤
      ∑ i ∈ s, a i ^ 2 * (∑ j ∈ s, K i j) := by
  classical
  have hpoint : ∀ i j, 2 * (K i j * (a i * a j)) ≤
      K i j * a i ^ 2 + K i j * a j ^ 2 :=
    fun i j => pair_bound (K i j) (a i) (a j) (hK i j)
  have hsum : (∑ i ∈ s, ∑ j ∈ s, 2 * (K i j * (a i * a j))) ≤
      ∑ i ∈ s, ∑ j ∈ s, (K i j * a i ^ 2 + K i j * a j ^ 2) := by
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpoint i j))
  have hleft : (∑ i ∈ s, ∑ j ∈ s, K i j * a i ^ 2) =
      ∑ i ∈ s, a i ^ 2 * (∑ j ∈ s, K i j) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_mul, mul_comm]
  have hright : (∑ i ∈ s, ∑ j ∈ s, K i j * a j ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, K i j * a i ^ 2 := by
    calc
      (∑ i ∈ s, ∑ j ∈ s, K i j * a j ^ 2) =
          ∑ j ∈ s, ∑ i ∈ s, K i j * a j ^ 2 := Finset.sum_comm
      _ = ∑ i ∈ s, ∑ j ∈ s, K i j * a i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hSym j i]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  rw [hright, hleft] at hsum
  linarith

/-- Finite Schur estimate with a nonnegative mass attached to each index. -/
theorem finite_schur_weighted {ι : Type*} (s : Finset ι)
    (K : ι → ι → ℝ) (m a : ι → ℝ)
    (hm : ∀ i, 0 ≤ m i)
    (hK : ∀ i j, 0 ≤ K i j)
    (hSym : ∀ i j, K i j = K j i) :
    (∑ i ∈ s, ∑ j ∈ s, m i * m j * K i j * (a i * a j)) ≤
      ∑ i ∈ s, m i * a i ^ 2 * (∑ j ∈ s, m j * K i j) := by
  have h := finite_schur s (fun i j => m i * m j * K i j) a
    (fun i j => mul_nonneg (mul_nonneg (hm i) (hm j)) (hK i j))
    (fun i j => by rw [hSym i j, mul_comm (m i) (m j)])
  refine h.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc (m i), ← Finset.mul_sum]
  ring

#print axioms pair_bound
#print axioms finite_schur

end GoldbachSchur
