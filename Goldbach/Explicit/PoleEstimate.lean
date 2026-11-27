import Goldbach.Explicit.CosineDecay
import Goldbach.Explicit.NumericalBounds
import Goldbach.Explicit.PoleSum
import Goldbach.Coefficient

/-! The quantitative pole contribution in the explicit spectral bound. -/

open scoped Interval
noncomputable section

namespace GoldbachExplicit

open GoldbachZeros GoldbachSpectrum

private theorem coefficient_sq_le_width {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) :
    ‖coefficient lam t‖^2 ≤ lam^2 * Real.exp lam := by
  have hI : Continuous (fun s : ℝ => Complex.exp (exponent 1 t * (s : ℂ))) := by fun_prop
  have h : ‖coefficient lam t‖ ≤ lam * Real.exp (lam / 2) := by
    unfold coefficient
    calc
      _ ≤ ∫ s in (0 : ℝ)..lam, ‖Complex.exp (exponent 1 t * (s : ℂ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm hlam
      _ ≤ ∫ _ : ℝ in (0 : ℝ)..lam, Real.exp (lam / 2) := by
        apply intervalIntegral.integral_mono_on hlam (hI.norm.intervalIntegrable _ _) intervalIntegrable_const
        intro s hs
        rw [norm_exp_exponent_mul]
        apply Real.exp_le_exp.mpr
        linarith [hs.2]
      _ = _ := by simp [intervalIntegral.integral_const, smul_eq_mul]
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, ← Real.exp_nat_mul] at hs
  rw [show (2 : ℕ) * (lam / 2) = lam by push_cast; ring] at hs
  exact hs

def polePair (V t : ℝ) : ℂ :=
  cosineTransform V ((t : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I) +
    cosineTransform V ((t : ℂ) + ((-1 / 2 : ℝ) : ℂ) * Complex.I)

def poleTerm (L : ℝ) (ρ : Zeros) : ℝ :=
  multiplicity ρ * ‖coefficient (logWidth L) (ordinate ρ)‖^2 *
    ‖polePair (bandwidth L) (ordinate ρ)‖

private theorem norm_polePair_le {V : ℝ} (hV : 0 < V) (t : ℝ) :
    ‖polePair V t‖ ≤ (16 * Real.exp (V / 2) / V) / (1 / 4 + t^2) := by
  unfold polePair
  have h₁ := norm_cosineTransform_pole_le hV t (1 / 2) (by norm_num)
  have h₂ := norm_cosineTransform_pole_le hV t (-1 / 2) (by norm_num)
  refine (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq ?_)
  have h : 1 / (4 : ℝ) + t^2 ≠ 0 := by positivity
  field_simp [hV.ne', h]
  ring

/-- Absolute summability and the manuscript's strict bound by δ for
the entire pole contribution, with both signs and multiplicities. -/
theorem pole_contribution_lt_delta_of_ge_28 (hRH : RiemannHypothesis) {L : ℝ} (hL : 28 ≤ L) :
    Summable (poleTerm L) ∧ (∑' ρ : Zeros, poleTerm L ρ) < delta L := by
  let V := bandwidth L
  let d := delta L
  let lam := logWidth L
  let C := (16 * Real.exp (V / 2) / V) * (lam^2 * Real.exp lam)
  have hL₀ : 0 < L := by linarith
  have hV : 0 < V := bandwidth_pos_of_pos hL₀
  have hV₁ : 1 ≤ V := by
    change 1 ≤ Real.sqrt (3 * L)
    exact Real.one_le_sqrt.mpr (by linarith)
  have hd : 0 < d := delta_pos_of_pos hL₀
  have hd₁ : d ≤ 1 := (delta_lt_of_ge_28 hL).le.trans (by norm_num)
  have hlam : 0 < lam := logWidth_pos_of_pos hL₀
  have hld : lam ≤ d := logWidth_le_delta_of_pos hL₀
  have hexp : Real.exp lam ≤ 2 := by
    have he : Real.exp lam = 1 + d := Real.exp_log (by linarith)
    linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hterm (ρ : Zeros) : poleTerm L ρ ≤ C * reciprocalZeroTerm ρ := by
    let t := ordinate ρ
    have hb := coefficient_sq_le_width hlam.le t
    have hp := norm_polePair_le hV t
    have hm := multiplicity_nonneg ρ
    have hp₀ : 0 ≤ (16 * Real.exp (V / 2) / V) / (1 / 4 + t^2) := by positivity
    unfold poleTerm reciprocalZeroTerm
    change multiplicity ρ * ‖coefficient lam t‖^2 * ‖polePair V t‖ ≤
      C * (multiplicity ρ / (1 / 4 + t^2))
    calc
      _ ≤ (multiplicity ρ * (lam^2 * Real.exp lam)) *
          ((16 * Real.exp (V / 2) / V) / (1 / 4 + t^2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hb hm) hp (norm_nonneg _) (by positivity)
      _ = _ := by unfold C; ring
  have hs := (reciprocal_zero_sum hRH).1.mul_left C
  have hS := hs.of_nonneg_of_le (fun ρ =>
    mul_nonneg (mul_nonneg (multiplicity_nonneg ρ) (sq_nonneg _)) (norm_nonneg _)) hterm
  refine ⟨hS, (hS.tsum_le_tsum hterm hs).trans_lt ?_⟩
  rw [tsum_mul_left]
  have hsum : (∑' ρ : Zeros, reciprocalZeroTerm ρ) ≤ 1 :=
    (reciprocal_zero_sum_lt hRH).le.trans (by norm_num)
  have hl : lam^2 ≤ d^2 := pow_le_pow_left₀ hlam.le hld 2
  have hv : 16 * Real.exp (V / 2) / V ≤ 16 * Real.exp (V / 2) := div_le_self (by positivity) hV₁
  calc
    _ ≤ C := mul_le_of_le_one_right hC hsum
    _ ≤ (16 * Real.exp (V / 2)) * (d^2 * 2) := by
      unfold C
      gcongr
    _ = d * (32 * (d * Real.exp (V / 2))) := by ring
    _ < d := by
      apply mul_lt_of_lt_one_right hd
      have hh : d * Real.exp (V / 2) < 1 / 32 :=
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hd.le).trans_lt
          (delta_exp_bandwidth_lt_of_ge_28 hL)
      linarith

theorem pole_contribution_lt_delta (hRH : RiemannHypothesis) {L : ℝ} (hL : 42 ≤ L) :
    Summable (poleTerm L) ∧ (∑' ρ : Zeros, poleTerm L ρ) < delta L :=
  pole_contribution_lt_delta_of_ge_28 hRH (by linarith)

end GoldbachExplicit
