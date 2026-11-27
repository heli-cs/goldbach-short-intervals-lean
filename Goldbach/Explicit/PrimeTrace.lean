import Goldbach.Explicit.AveragedPsi
import Goldbach.Explicit.PrimeDiagonal

/-! A prime-diagonal trace from the common-height sharp explicit formula. -/

open Filter MeasureTheory Set
open scoped Interval ComplexConjugate
noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum GoldbachGaussian GoldbachZeros GoldbachArithmetic

private theorem coefficient_neg (lam t : ℝ) :
    coefficient lam (-t) = conj (coefficient lam t) := by
  have h : exponent 1 (-t) = conj (exponent 1 t) := by
    unfold exponent
    simp only [map_mul, map_add, map_div₀, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
      Complex.ofReal_neg]
    ring
  rw [coefficient_formula, coefficient_formula, h]
  rw [map_div₀, map_sub, map_one, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]

private theorem integral_reflected_wave {lam : ℝ} (hlam : 0 ≤ lam) (v t : ℝ) :
    (∫ u in Icc (v - lam) v, (Real.exp ((v - u) / 2) : ℂ) * wave t u) =
      wave t v * coefficient lam (-t) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (sub_le_self v hlam)]
  have hs := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := lam)
    (fun u => (Real.exp ((v - u) / 2) : ℂ) * wave t u) v
  simp only [sub_zero, sub_sub_cancel] at hs
  rw [← hs, coefficient, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  change (Real.exp (s / 2) : ℂ) * wave t (v - s) = wave t v * _
  simp only [Complex.ofReal_exp, wave, ← Complex.exp_add]
  congr 1
  unfold exponent
  push_cast
  ring

private theorem linear_trivialZero_mono :
    MonotoneOn (fun y : ℝ => y + trivialZeroTerm y) (Ici (3 / 2)) := by
  have hd (y : ℝ) (hy : 3 / 2 ≤ y) :
      HasDerivAt (fun z : ℝ => z + trivialZeroTerm z)
        (1 - 1 / (y * (y^2 - 1))) y := by
    have hy₀ : 0 < y := by linarith
    have hsq : 1 < y^2 := by nlinarith [sq_nonneg (y - 3 / 2)]
    have hp := sub_pos.mpr (inv_lt_one_of_one_lt₀ hsq)
    have hi := (hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_pow 2 y).inv (by positivity))
    unfold trivialZeroTerm
    convert (hasDerivAt_id y).add ((hi.log hp.ne').const_mul (-(1 / 2))) using 1 <;>
      first | rfl | (funext z; rfl) | (simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one,
        zero_sub, Pi.sub_apply, Pi.inv_apply]; field_simp [hy₀.ne', hsq.ne', hp.ne'] <;> ring)
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · exact fun y hy => (hd y hy).continuousAt.continuousWithinAt
  · exact fun y hy => (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    have hy' : 3 / 2 ≤ y := interior_subset hy
    rw [(hd y hy').deriv]
    have hsq : 5 / 4 ≤ y^2 - 1 := by nlinarith [sq_nonneg (y - 3 / 2)]
    have hprod : 1 ≤ y * (y^2 - 1) :=
      (by norm_num : (1 : ℝ) ≤ 3 / 2 * (5 / 4)).trans <|
        mul_le_mul hy' hsq (by norm_num) (by linarith)
    have hpos : 0 < y * (y^2 - 1) := zero_lt_one.trans_le hprod
    exact sub_nonneg.mpr ((div_le_iff₀ hpos).2 (by simpa only [one_mul] using hprod))

private theorem reflected_exponential_integral {lam : ℝ} (hlam : 0 ≤ lam) (v : ℝ) :
    (∫ u in Icc (v - lam) v, Real.exp (v / 2 - u)) =
      (Real.exp lam - 1) * Real.exp (-v / 2) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (sub_le_self v hlam),
    intervalIntegral.integral_comp_sub_left Real.exp, integral_exp,
    show v / 2 - (v - lam) = -v / 2 + lam by ring,
    show v / 2 - v = -v / 2 by ring, Real.exp_add]
  ring

/-- The sharp spectral test at an isolated integer has a single exact
von Mangoldt term. The linear and trivial-zero terms together have
nonnegative contribution. -/
theorem prime_trace_lower (hRH : RiemannHypothesis) {lam : ℝ} {n : ℕ}
    (hlam : 0 < lam) (hlam₁ : lam ≤ 1) (hn : 2 ≤ n)
    (hlamExp : Real.exp lam ≤ 4 / 3) (hsep : (Real.exp lam - 1) * (n : ℝ) < 1) :
    -(Real.exp lam - 1) * ArithmeticFunction.vonMangoldt n *
        Real.exp (-Real.log n / 2) ≤
      ∑' ρ : Zeros, multiplicity ρ * ‖sharpCoefficient lam ρ‖^2 *
        Real.cos (ordinate ρ * Real.log n) := by
  let v := Real.log (n : ℝ)
  let a := v - lam
  let W (u : ℝ) : ℂ := (Real.exp ((v - u) / 2) : ℂ)
  let P (u : ℝ) := Real.exp ((v - u) / 2) * sharpSpectralValue lam u
  let μ := volume.restrict (Icc a v)
  let C (ρ : Zeros) : ℂ := (((multiplicity ρ) * ‖sharpCoefficient lam ρ‖^2 : ℝ) : ℂ) *
    wave (ordinate ρ) v
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hv : Real.exp v = n := Real.exp_log hn₀
  have hav : a ≤ v := sub_le_self v hlam.le
  have haexp : Real.exp a = (n : ℝ) / Real.exp lam := by
    simp only [a, Real.exp_sub, hv]
  have haBound : 3 / 2 ≤ Real.exp a := by
    rw [haexp, le_div_iff₀ (Real.exp_pos lam)]
    linarith
  have ha : 0 < a := Real.one_lt_exp_iff.mp (by linarith)
  have hW : Continuous W := by unfold W; fun_prop
  have hW₂ : MemLp W 2 μ :=
    (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).2
      ((hW.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  have hterm (ρ : Zeros) :
      (multiplicity ρ : ℂ) * sharpCoefficient lam ρ *
        (∫ u in Icc a v, W u * wave (ordinate ρ) u) = C ρ := by
    rw [show (∫ u in Icc a v, W u * wave (ordinate ρ) u) =
        wave (ordinate ρ) v * coefficient lam (-ordinate ρ) from
      integral_reflected_wave hlam.le v (ordinate ρ)]
    unfold C sharpCoefficient
    rw [coefficient_neg, show ∀ c w m : ℂ, m * c * (w * conj c) = m * (c * conj c) * w
      from fun c w m => by ring, Complex.mul_conj']
    norm_cast
  have hC : Summable C := by
    let K := (1 + Real.exp (lam / 2))^2
    have hmajor := (inverse_square_zero_sum_lt hRH).1.mul_left K
    apply hmajor.of_norm_bounded
    intro ρ
    let g := ordinate ρ
    have hg : 0 < |g| := (by norm_num : (0 : ℝ) < 9 / 2).trans
      (ordinate_abs_gt_nine_halves hRH ρ)
    have hc := pow_le_pow_left₀ (norm_nonneg _) (coefficient_norm_le_inv_ordinate lam g hg) 2
    rw [div_pow, sq_abs] at hc
    have hm := multiplicity_nonneg ρ
    unfold C
    rw [norm_mul, norm_wave, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ multiplicity ρ * (K / g^2) := mul_le_mul_of_nonneg_left hc hm
      _ = _ := by unfold g; ring
  have hseries := hC.congr (fun ρ => (hterm ρ).symm)
  have htest := sharp_spectral_integral_eq_tsum hRH hlam hlam₁ ha hav hW₂ hseries
  simp_rw [hterm] at htest
  have hint : (∫ u, P u ∂μ) = ∑' ρ : Zeros, multiplicity ρ * ‖sharpCoefficient lam ρ‖^2 *
      Real.cos (ordinate ρ * v) := by
    have hL : (∫ u in Icc a v, W u * (sharpSpectralValue lam u : ℂ)) =
        ((∫ u, P u ∂μ : ℝ) : ℂ) := by
      simp only [W, P, μ, ← Complex.ofReal_mul, integral_complex_ofReal]
    rw [hL] at htest
    have h := congrArg Complex.re htest
    rw [Complex.ofReal_re, Complex.re_tsum hC] at h
    simpa only [C, Complex.re_ofReal_mul, wave, Complex.exp_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      zero_mul, add_zero, sub_zero, zero_add, Real.exp_zero, one_mul] using h
  have hPi : Integrable P μ := by
    have hi := hW₂.integrable_mul (sharpSpectralValue_memLp hRH hlam hlam₁ ha hav)
    have hi' := Complex.reCLM.integrable_comp hi
    simpa only [Function.comp_def, Pi.mul_apply, W, ← Complex.ofReal_mul, Complex.reCLM_apply,
      Complex.ofReal_re, P] using hi'
  have hm : ∀ᵐ u ∂μ, -(ArithmeticFunction.vonMangoldt n) * Real.exp (v / 2 - u) ≤ P u := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Icc a v) measurableSet_Icc,
      μ.ae_ne v] with u hu huv
    have hlt : u < v := lt_of_le_of_ne hu.2 huv
    have hnLower : (n : ℝ) - 1 ≤ Real.exp a := by
      rw [haexp, le_div_iff₀ (Real.exp_pos lam)]
      nlinarith only [hsep, Real.one_le_exp_iff.mpr hlam.le]
    have hlow : 3 / 2 ≤ Real.exp u := haBound.trans (Real.exp_le_exp.mpr hu.1)
    have hNat : Chebyshev.psi (Real.exp (u + lam)) - Chebyshev.psi (Real.exp u) =
        ArithmeticFunction.vonMangoldt n := by
      apply psi_sub_eq_vonMangoldt (by omega : 0 < n) (Real.exp_pos _).le
      · exact hnLower.trans (Real.exp_le_exp.mpr hu.1)
      · rw [← hv]
        exact Real.exp_lt_exp.mpr hlt
      · rw [← hv]
        exact Real.exp_le_exp.mpr (by linarith [hu.1])
      · rw [Real.exp_add]
        have htop := mul_lt_mul_of_pos_right (Real.exp_lt_exp.mpr hlt) (Real.exp_pos lam)
        rw [hv] at htop
        nlinarith only [htop, hsep]
    have hstep : Real.exp u ≤ Real.exp (u + lam) := Real.exp_le_exp.mpr (by linarith)
    have hmono := linear_trivialZero_mono (mem_Ici.mpr hlow)
      (mem_Ici.mpr (hlow.trans hstep)) hstep
    unfold P sharpSpectralValue
    rw [hNat, ← mul_assoc, ← Real.exp_add, show (v - u) / 2 + -u / 2 = v / 2 - u by ring]
    nlinarith only [mul_nonneg (Real.exp_pos (v / 2 - u)).le
      (sub_nonneg.mpr hmono)]
  have hE : IntegrableOn (fun u => Real.exp (v / 2 - u)) (Icc a v) :=
    (by fun_prop : Continuous (fun u => Real.exp (v / 2 - u))).continuousOn.integrableOn_compact
      isCompact_Icc
  have h := integral_mono_ae (hE.const_mul (-(ArithmeticFunction.vonMangoldt n))) hPi hm
  rw [integral_const_mul, hint] at h
  change -(ArithmeticFunction.vonMangoldt n) *
    (∫ u in Icc (v - lam) v, Real.exp (v / 2 - u)) ≤ _ at h
  rw [reflected_exponential_integral hlam.le v] at h
  convert h using 1
  ring

end GoldbachExplicit
