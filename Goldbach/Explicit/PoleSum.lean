import Goldbach.Explicit.PoleConstant
import Goldbach.Zeros
import Zeta23.XiPrime.ExplicitFormula.ZeroFree

/-! Exact and numerical pole sums, deduced from the verified logarithmic
derivative of the xi function. -/

noncomputable section
namespace GoldbachExplicit

open GoldbachZeros Zeta23

def reciprocalZeroTerm (ρ : Zeros) : ℝ :=
  multiplicity ρ / (1 / 4 + ordinate ρ^2)

private theorem reciprocalZeroTerm_nonneg (ρ : Zeros) :
    0 ≤ reciprocalZeroTerm ρ := div_nonneg (multiplicity_nonneg ρ) (by positivity)

private theorem logDeriv_xi_one :
    logDeriv XiPrime.xi 1 = completedRiemannZeta₀ 1 := by
  have hv := (hasDerivAt_id (1 : ℂ)).sub_const (1 : ℂ)
  have hpoly := (((hasDerivAt_id (1 : ℂ)).mul hv).div_const (2 : ℂ))
  have hh := (hpoly.mul (differentiable_completedZeta₀ (1 : ℂ)).hasDerivAt).add_const (1 / 2 : ℂ)
  have h : HasDerivAt XiPrime.xi (completedRiemannZeta₀ 1 / 2) 1 := by
    change HasDerivAt (fun s : ℂ => s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2) _ _
    convert hh using 1 <;> first | rfl | (simp [div_eq_mul_inv, mul_comm]) | (dsimp; ring)
  rw [logDeriv_apply, h.deriv, XiPrime.xi_one]
  ring

private theorem real_part_xi_term_eq (hRH : RiemannHypothesis) (ρ : Zeros) :
    2 * ((zeroMult ρ : ℝ) * (((1 : ℂ).re - (ρ : ℂ).re) /
      Complex.normSq ((1 : ℂ) - ρ))) = reciprocalZeroTerm ρ := by
  have hr : (ρ : ℂ).re = 1 / 2 := RH_implies_on_line hRH ρ.property
  have hm : (zeroMult (ρ : ℂ) : ℝ) = multiplicity ρ := by rfl
  rw [reciprocalZeroTerm, hm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, hr]
  unfold ordinate
  have he : (1 - (1 / 2 : ℝ)) * (1 - 1 / 2) +
      (0 - (ρ : ℂ).im) * (0 - (ρ : ℂ).im) = 1 / 4 + (ρ : ℂ).im ^ 2 := by ring
  rw [he]
  ring

/-- The Hadamard zero-sum value follows under RH from the pinned
Hadamard-free xi logarithmic derivative formula. The sum includes both signs. -/
theorem reciprocal_zero_sum (hRH : RiemannHypothesis) :
    Summable reciprocalZeroTerm ∧
      (∑' ρ : Zeros, reciprocalZeroTerm ρ) =
        2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  have hxi : XiPrime.xi (1 : ℂ) ≠ 0 := by rw [XiPrime.xi_one]; norm_num
  have h := XiPrime.ZeroFree.summable_re_one_div hxi
  have hsum := XiPrime.ZeroFree.re_logDeriv_xi_eq_tsum hxi
  refine ⟨(h.mul_left 2).congr (real_part_xi_term_eq hRH), ?_⟩
  simp_rw [← real_part_xi_term_eq hRH]
  rw [tsum_mul_left, ← hsum, logDeriv_xi_one, completedRiemannZeta₀_one]
  have hlog : Complex.log (4 * (Real.pi : ℂ)) = (Real.log (4 * Real.pi) : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
      (Complex.ofReal_log (by positivity : 0 ≤ 4 * Real.pi)).symm
  rw [hlog]
  simp
  ring

theorem reciprocal_zero_sum_lt (hRH : RiemannHypothesis) :
    (∑' ρ : Zeros, reciprocalZeroTerm ρ) < (47 / 1000 : ℝ) := by
  rw [(reciprocal_zero_sum hRH).2]
  exact reciprocal_zero_constant_lt

/-- The reciprocal sum provides the low-height exclusion needed for
an inverse-ordinate bound. -/
theorem ordinate_abs_gt_nine_halves (hRH : RiemannHypothesis) (ρ : Zeros) :
    (9 / 2 : ℝ) < |ordinate ρ| := by
  have hm : (1 : ℝ) ≤ multiplicity ρ := by
    change (1 : ℝ) ≤ (zeroMult (ρ : ℂ) : ℝ)
    exact_mod_cast (zetaSeam.one_le_mult (ρ : ℂ) ρ.property)
  have hterm := ((reciprocal_zero_sum hRH).1.le_tsum ρ
      (fun σ _ => reciprocalZeroTerm_nonneg σ)).trans_lt (reciprocal_zero_sum_lt hRH)
  by_contra! ht
  have hs : ordinate ρ^2 ≤ (9 / 2 : ℝ)^2 := sq_le_sq.mpr (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 9 / 2)]; exact ht)
  have hden : 0 < 1 / 4 + ordinate ρ^2 := by positivity
  have h := (div_lt_iff₀ hden).mp hterm
  nlinarith [h, hs]

theorem inverse_square_zero_sum_lt (hRH : RiemannHypothesis) :
    Summable (fun ρ : Zeros => multiplicity ρ / ordinate ρ^2) ∧
      (∑' ρ : Zeros, multiplicity ρ / ordinate ρ^2) < (48 / 1000 : ℝ) := by
  have hscale : ∀ ρ : Zeros, multiplicity ρ / ordinate ρ^2 ≤
      (82 / 81 : ℝ) * reciprocalZeroTerm ρ := by
    intro ρ
    have hρ := ordinate_abs_gt_nine_halves hRH ρ
    have hs : (81 / 4 : ℝ) ≤ ordinate ρ^2 := by
      have h := (sq_le_sq).mpr (show |(9 / 2 : ℝ)| ≤ |ordinate ρ| by rw [abs_of_pos (by norm_num : (0 : ℝ) < 9 / 2)]; exact hρ.le)
      norm_num at h
      exact h
    have hγ : 0 < ordinate ρ^2 := by linarith
    have hp : 0 < 1 / 4 + ordinate ρ^2 := by positivity
    unfold reciprocalZeroTerm
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hγ hp).mpr
    have h := mul_le_mul_of_nonneg_right hs (multiplicity_nonneg ρ)
    nlinarith only [h]
  have hm := ((reciprocal_zero_sum hRH).1.mul_left (82 / 81 : ℝ))
  have hs := hm.of_nonneg_of_le
    (fun ρ => div_nonneg (multiplicity_nonneg ρ) (sq_nonneg _)) hscale
  refine ⟨hs, (hs.tsum_le_tsum hscale hm).trans_lt ?_⟩
  rw [tsum_mul_left]
  linarith [reciprocal_zero_sum_lt hRH]

end GoldbachExplicit
