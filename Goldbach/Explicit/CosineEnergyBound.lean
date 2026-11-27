import Goldbach.Explicit.CompactVariance
import Goldbach.Explicit.PrimeTrace

/-! Separation of the archimedean, pole, and prime contributions to the Schur bound. -/

noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum GoldbachZeros
open ArithmeticFunction

/-- The positive logarithmic envelope for the archimedean contribution. -/
def archimedeanZeroSum (lam : ℝ) : ℝ :=
  ∑' ρ : Zeros, multiplicity ρ * ‖sharpCoefficient lam ρ‖^2 * Real.log (|ordinate ρ| + 3)

/-- The finite von Mangoldt square sum against the cosine weight. -/
def weightedMangoldtSquares (V : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊Real.exp V⌋₊, (vonMangoldt n)^2 / n * cosineWeight V (Real.log n)

private theorem bandwidth_ge_two_pi {L : ℝ} (hL : 28 ≤ L) : 2 * Real.pi ≤ bandwidth L := by
  change 2 * Real.pi ≤ Real.sqrt (3 * L)
  apply (Real.le_sqrt (by positivity) (by linarith)).mpr
  have h := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 2
  nlinarith only [h, hL]

/-- In the explicit range, the full cosine energy is summable. Its pole
part costs at most δ and its prime part costs at most the stated finite
weighted von Mangoldt square sum. -/
theorem cosine_energy_le_of_ge_28 (hRH : RiemannHypothesis) {L : ℝ} (hL : 28 ≤ L) :
    Summable (cosineEnergy (bandwidth L) (logWidth L)) ∧
      (∑' ρ : Zeros, cosineEnergy (bandwidth L) (logWidth L) ρ) <
        archimedeanZeroSum (logWidth L) + delta L +
          2 * delta L * weightedMangoldtSquares (bandwidth L) := by
  let V := bandwidth L
  let lam := logWidth L
  let d := delta L
  let S := Finset.Ioc 0 ⌊Real.exp V⌋₊
  let H (ρ : Zeros) := multiplicity ρ * ‖sharpCoefficient lam ρ‖^2
  let G (ρ : Zeros) := H ρ * Real.log (|ordinate ρ| + 3)
  let P (n : ℕ) := cosinePrimeWeight V n
  let T (n : ℕ) (ρ : Zeros) := H ρ * Real.cos (ordinate ρ * Real.log n)
  let C (n : ℕ) := ∑' ρ : Zeros, T n ρ
  have hL₀ : 0 < L := by linarith
  have hV : 0 < V := bandwidth_pos_of_pos hL₀
  have hVπ : 2 * Real.pi ≤ V := bandwidth_ge_two_pi hL
  have hd : 0 < d := delta_pos_of_pos hL₀
  have hds : d < 1 / 10^8 := delta_lt_of_ge_28 hL
  have hl : 0 < lam := logWidth_pos_of_pos hL₀
  have hl₁ : lam ≤ 1 := (logWidth_le_delta_of_pos hL₀).trans (by linarith)
  have hlE : Real.exp lam = 1 + d := Real.exp_log (by linarith)
  have hH₀ (ρ : Zeros) : 0 ≤ H ρ := mul_nonneg (multiplicity_nonneg ρ) (sq_nonneg _)
  have hG : Summable G := sharp_coefficient_log_summable hl.le hl₁
  have hH : Summable H := by
    refine (hG.mul_left (2 : ℝ)).of_nonneg_of_le hH₀ (fun ρ => ?_)
    have hlog : 1 / 2 ≤ Real.log (|ordinate ρ| + 3) := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (show (2 : ℝ) ≤ |ordinate ρ| + 3 by linarith [abs_nonneg (ordinate ρ)])
      linarith [Real.log_two_gt_d9]
    have hmul := mul_le_mul_of_nonneg_left hlog (hH₀ ρ)
    change H ρ ≤ 2 * G ρ
    unfold G
    nlinarith only [hmul]
  have hT (n : ℕ) : Summable (T n) := by
    refine hH.of_norm_bounded (fun ρ => ?_)
    unfold T
    rw [norm_mul, Real.norm_of_nonneg (hH₀ ρ), Real.norm_eq_abs]
    exact mul_le_of_le_one_right (hH₀ ρ) (Real.abs_cos_le_one _)
  have hP₀ (n : ℕ) : 0 ≤ P n := by
    unfold P cosinePrimeWeight
    exact mul_nonneg (div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)) (cosineWeight_nonneg hV _)
  obtain ⟨hPole, hPoleBound⟩ := pole_contribution_lt_delta_of_ge_28 hRH hL
  let U (ρ : Zeros) := ∑ n ∈ S, P n * T n ρ
  have hU : Summable U := by
    exact summable_sum (s := S) (fun n _ => (hT n).mul_left (P n))
  have hmajor := (hPole.add hG).sub (hU.mul_left 2)
  have hterm (ρ : Zeros) :
      cosineEnergy V lam ρ ≤ poleTerm L ρ + G ρ - 2 * U ρ := by
    have h := mul_le_mul_of_nonneg_left (cosine_row_le hRH hVπ (ordinate ρ)) (hH₀ ρ)
    have hu : U ρ = H ρ * ∑ n ∈ S, P n * Real.cos (ordinate ρ * Real.log n) := by
      unfold U T
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    change H ρ * cosineRow V (ordinate ρ) ≤ _
    rw [hu, show poleTerm L ρ = H ρ * ‖polePair V (ordinate ρ)‖ from rfl]
    change _ ≤ _ + H ρ * Real.log (|ordinate ρ| + 3) - _
    change H ρ * cosineRow V (ordinate ρ) ≤ H ρ * (‖polePair V (ordinate ρ)‖ +
      Real.log (|ordinate ρ| + 3) - 2 * ∑ n ∈ S, P n * Real.cos (ordinate ρ * Real.log n)) at h
    nlinarith only [h]
  have hE : Summable (cosineEnergy V lam) := hmajor.of_nonneg_of_le (cosineEnergy_nonneg hV lam) hterm
  refine ⟨hE, ?_⟩
  have hsum := hE.tsum_le_tsum hterm hmajor
  rw [(hPole.add hG).tsum_sub (hU.mul_left _), hPole.tsum_add hG, tsum_mul_left] at hsum
  have hswap : (∑' ρ, U ρ) = ∑ n ∈ S, P n * C n := by
    unfold U
    rw [Summable.tsum_finsetSum (fun n _ => (hT n).mul_left (P n))]
    exact Finset.sum_congr rfl (fun n _ => tsum_mul_left)
  rw [hswap] at hsum
  have hdiag (n : ℕ) (hn : n ∈ S) :
      -d * ((vonMangoldt n)^2 / n * cosineWeight V (Real.log n)) ≤ P n * C n := by
    have hp : 0 < n := (Finset.mem_Ioc.mp hn).1
    by_cases hn₁ : n = 1
    · simp [hn₁, P, cosinePrimeWeight, vonMangoldt_apply_one]
    have hn₂ : 2 ≤ n := by omega
    have hnP : 0 < (n : ℝ) := by exact_mod_cast hp
    have hnV := (Nat.le_floor_iff (Real.exp_pos V).le).mp (Finset.mem_Ioc.mp hn).2
    have hsep : (Real.exp lam - 1) * (n : ℝ) < 1 := by
      rw [hlE, add_sub_cancel_left]
      exact (mul_le_mul_of_nonneg_left hnV hd.le).trans_lt
        ((delta_exp_bandwidth_lt_of_ge_28 hL).trans (by norm_num))
    have ht := prime_trace_lower hRH hl hl₁ hn₂ (by linarith) hsep
    change -(Real.exp lam - 1) * vonMangoldt n * Real.exp (-Real.log n / 2) ≤ C n at ht
    rw [hlE, add_sub_cancel_left] at ht
    have hs : Real.sqrt (n : ℝ) = Real.exp (Real.log n / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnP]
      congr 1
      ring
    have hexp : Real.exp (-Real.log n / 2) = (Real.sqrt (n : ℝ))⁻¹ := by
      rw [neg_div, Real.exp_neg, hs]
    have he :
        P n * (-d * vonMangoldt n * (Real.sqrt (n : ℝ))⁻¹) =
          -d * ((vonMangoldt n)^2 / n * cosineWeight V (Real.log n)) := by
      let z := Real.sqrt (n : ℝ)
      unfold P cosinePrimeWeight
      change (vonMangoldt n / z * cosineWeight V (Real.log n)) *
        (-d * vonMangoldt n * z⁻¹) = _
      calc
        _ = -d * ((vonMangoldt n)^2 / z^2 * cosineWeight V (Real.log n)) := by
          field_simp [(Real.sqrt_pos.2 hnP).ne']
        _ = _ := by rw [show z^2 = (n : ℝ) from Real.sq_sqrt hnP.le]
    rw [hexp] at ht
    exact (le_of_eq he.symm).trans (mul_le_mul_of_nonneg_left ht (hP₀ n))
  have hprime := Finset.sum_le_sum hdiag
  rw [← Finset.mul_sum] at hprime
  change -d * weightedMangoldtSquares V ≤ ∑ n ∈ S, P n * C n at hprime
  change (∑' ρ, cosineEnergy V lam ρ) < archimedeanZeroSum lam + d + 2 * d * weightedMangoldtSquares V
  change (∑' ρ, cosineEnergy V lam ρ) < (∑' ρ, G ρ) + d + 2 * d * weightedMangoldtSquares V
  change (∑' ρ, poleTerm L ρ) < d at hPoleBound
  nlinarith only [hsum, hprime, hPoleBound]

theorem cosine_energy_le (hRH : RiemannHypothesis) {L : ℝ} (hL : 42 ≤ L) :
    Summable (cosineEnergy (bandwidth L) (logWidth L)) ∧
      (∑' ρ : Zeros, cosineEnergy (bandwidth L) (logWidth L) ρ) <
        archimedeanZeroSum (logWidth L) + delta L +
          2 * delta L * weightedMangoldtSquares (bandwidth L) :=
  cosine_energy_le_of_ge_28 hRH (by linarith)

end GoldbachExplicit
