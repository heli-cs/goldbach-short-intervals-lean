import Goldbach.Explicit.SpectralLinear
import Goldbach.Explicit.PoleSum

/-! A logarithmically integrated explicit formula for Chebyshev's psi.
Averaging supplies an extra inverse power of the zero ordinate. -/

open MeasureTheory Set
open scoped Interval
noncomputable section

namespace GoldbachExplicit

open GoldbachSpectrum GoldbachGaussian GoldbachZeros GoldbachArithmetic

/-- The discrepancy with the trivial-zero term included, in log coordinates. -/
def logPsiError (u : ℝ) : ℝ :=
  Real.exp u + trivialZeroTerm (Real.exp u) - Chebyshev.psi (Real.exp u)

/-- Integrating the log-coordinate discrepancy over a starting window. -/
def averagedLogPsiError (eps u : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..eps, logPsiError (u + s)

private def averagedMode (eps u : ℝ) (ρ : Zeros) : ℂ :=
  (multiplicity ρ : ℂ) *
    (coefficient eps (ordinate ρ) / exponent 1 (ordinate ρ)) *
    Complex.exp (exponent 1 (ordinate ρ) * (u : ℂ))

private theorem exponent_ne (t : ℝ) : exponent 1 t ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num [exponent_re] at hr

private theorem abs_le_norm_exponent (t : ℝ) : |t| ≤ ‖exponent 1 t‖ := by
  simpa only [exponent_im] using Complex.abs_im_le_norm (exponent 1 t)

/-- A sharp-window coefficient decays inversely with the nonzero frequency. -/
theorem coefficient_norm_le_inv_ordinate (e g : ℝ) (hg : 0 < |g|) :
    ‖coefficient e g‖ ≤ (1 + Real.exp (e / 2)) / |g| := by
  have ht := norm_sub_le (Complex.exp (exponent 1 g * (e : ℂ))) (1 : ℂ)
  rw [norm_one, norm_exp_exponent_mul, one_mul, add_comm] at ht
  rw [coefficient_formula, norm_div]
  exact (div_le_div_of_nonneg_right ht (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) hg (abs_le_norm_exponent g))

private theorem norm_averagedMode_le (hRH : RiemannHypothesis) (eps u : ℝ) (ρ : Zeros) :
    ‖averagedMode eps u ρ‖ ≤
      ((1 + Real.exp (eps / 2)) * Real.exp (u / 2)) * (multiplicity ρ / ordinate ρ^2) := by
  let g := ordinate ρ
  have hg : 0 < |g| := (by norm_num : (0 : ℝ) < 9 / 2).trans
    (ordinate_abs_gt_nine_halves hRH ρ)
  have hm := multiplicity_nonneg ρ
  have hd : ‖coefficient eps g / exponent 1 g‖ ≤ (1 + Real.exp (eps / 2)) / g^2 := by
    rw [norm_div]
    calc
      _ ≤ ((1 + Real.exp (eps / 2)) / |g|) / ‖exponent 1 g‖ :=
        div_le_div_of_nonneg_right (coefficient_norm_le_inv_ordinate eps g hg) (norm_nonneg _)
      _ ≤ ((1 + Real.exp (eps / 2)) / |g|) / |g| :=
        div_le_div_of_nonneg_left (by positivity) hg (abs_le_norm_exponent g)
      _ = _ := by rw [div_div, ← pow_two, sq_abs]
  unfold averagedMode
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hm, norm_exp_exponent_mul, one_mul]
  calc
    _ ≤ multiplicity ρ * ((1 + Real.exp (eps / 2)) / g^2) * Real.exp (u / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hm) (Real.exp_pos _).le
    _ = _ := by unfold g; ring

private theorem averagedMode_summable (hRH : RiemannHypothesis) (eps u : ℝ) :
    Summable (averagedMode eps u) :=
  (((inverse_square_zero_sum_lt hRH).1).mul_left
    ((1 + Real.exp (eps / 2)) * Real.exp (u / 2))).of_norm_bounded
      (norm_averagedMode_le hRH eps u)

theorem logPsiError_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable logPsiError volume a b := by
  have hψ : Monotone (fun u => Chebyshev.psi (Real.exp u)) :=
    Chebyshev.psi_mono.comp Real.exp_monotone
  have hg : ContinuousOn (fun u => trivialZeroTerm (Real.exp u)) (uIcc a b) := by
    have hi : ContinuousOn (fun u : ℝ => ((Real.exp u) ^ 2)⁻¹) (uIcc a b) :=
      (Real.continuous_exp.continuousOn.pow 2).inv₀
        (fun u _ => pow_ne_zero _ (Real.exp_pos u).ne')
    unfold trivialZeroTerm
    refine continuousOn_const.mul ((continuousOn_const.sub hi).log ?_)
    intro u hu
    rw [uIcc_of_le hab] at hu
    have h₁ : 1 < Real.exp u := Real.one_lt_exp_iff.mpr (ha.trans_le hu.1)
    have h₂ : 1 < (Real.exp u)^2 := by nlinarith
    exact (sub_pos.mpr ((inv_lt_one₀ (by positivity)).2 h₂)).ne'
  exact ((Real.continuous_exp.intervalIntegrable _ _).add hg.intervalIntegrable).sub
    hψ.intervalIntegrable

private theorem integral_averaged_wave (g u eps : ℝ) (heps : 0 ≤ eps) :
    (∫ t in Icc u (u + eps), (Real.exp (t / 2) : ℂ) * wave g t) =
      Complex.exp (exponent 1 g * (u : ℂ)) * coefficient eps g := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : u ≤ u + eps)]
  have hwave (t : ℝ) :
      (Real.exp (t / 2) : ℂ) * wave g t = Complex.exp (exponent 1 g * (t : ℂ)) := by
    rw [Complex.ofReal_exp, wave, ← Complex.exp_add]
    congr 1
    unfold exponent
    push_cast
    ring
  simp_rw [hwave]
  rw [integral_exp_mul_complex (exponent_ne g), coefficient_formula]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

private theorem logPsiError_integral_eq_averaged_sub {u eps lam : ℝ}
    (hu : 0 < u) (heps : 0 ≤ eps) (hlam : 0 < lam) :
    (∫ t in Icc u (u + eps), (Real.exp (t / 2) : ℂ) * (sharpSpectralValue lam t : ℂ)) =
      ((averagedLogPsiError eps (u + lam) - averagedLogPsiError eps u : ℝ) : ℂ) := by
  have he (t : ℝ) : (Real.exp (t / 2) : ℂ) * (sharpSpectralValue lam t : ℂ) =
      ((logPsiError (t + lam) - logPsiError t : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    unfold sharpSpectralValue logPsiError
    rw [← mul_assoc, ← Real.exp_add, show t / 2 + -t / 2 = 0 by ring, Real.exp_zero, one_mul]
    ring
  simp_rw [he]
  rw [integral_complex_ofReal]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : u ≤ u + eps)]
  have h₀ : IntervalIntegrable logPsiError volume u (u + eps) :=
    logPsiError_intervalIntegrable hu (by linarith)
  have h₁ : IntervalIntegrable logPsiError volume (u + lam) (u + eps + lam) :=
    logPsiError_intervalIntegrable (by linarith) (by linarith)
  have hshift : IntervalIntegrable (fun t => logPsiError (t + lam)) volume u (u + eps) := by
    simpa only [add_sub_cancel_right] using h₁.comp_add_right lam
  rw [intervalIntegral.integral_sub hshift h₀, intervalIntegral.integral_comp_add_right logPsiError lam]
  unfold averagedLogPsiError
  have hx (z : ℝ) : (∫ s in (0 : ℝ)..eps, logPsiError (z + s)) =
      ∫ t in z..(z + eps), logPsiError t := by
    simpa only [zero_add, add_comm z] using intervalIntegral.integral_comp_add_right
      (a := (0 : ℝ)) (b := eps) logPsiError z
  rw [hx, hx, show u + eps + lam = u + lam + eps by ring]

private theorem local_averagedLogPsiError_sub (hRH : RiemannHypothesis) {eps u lam : ℝ}
    (heps : 0 ≤ eps) (hu : 0 < u) (hlam : 0 < lam) (hlam₁ : lam ≤ 1) :
    averagedLogPsiError eps (u + lam) - averagedLogPsiError eps u =
      (∑' ρ, averagedMode eps (u + lam) ρ).re - (∑' ρ, averagedMode eps u ρ).re := by
  let W (t : ℝ) : ℂ := (Real.exp (t / 2) : ℂ)
  have hW : Continuous W := by unfold W; fun_prop
  have hW₂ : MemLp W 2 (volume.restrict (Icc u (u + eps))) := by
    apply (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).2
    exact (hW.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hterm (ρ : Zeros) :
      (multiplicity ρ : ℂ) * sharpCoefficient lam ρ *
        (∫ t in Icc u (u + eps), W t * wave (ordinate ρ) t) =
        averagedMode eps (u + lam) ρ - averagedMode eps u ρ := by
    let g := ordinate ρ
    rw [show (∫ t in Icc u (u + eps), W t * wave g t) =
        Complex.exp (exponent 1 g * (u : ℂ)) * coefficient eps g from
      integral_averaged_wave g u eps heps]
    unfold sharpCoefficient averagedMode
    change (multiplicity ρ : ℂ) * coefficient lam g * _ =
      (multiplicity ρ : ℂ) * (coefficient eps g / exponent 1 g) *
        Complex.exp (exponent 1 g * ((u + lam : ℝ) : ℂ)) -
      (multiplicity ρ : ℂ) * (coefficient eps g / exponent 1 g) *
        Complex.exp (exponent 1 g * (u : ℂ))
    rw [coefficient_formula lam]
    push_cast
    rw [mul_add, Complex.exp_add]
    ring
  have hSm := (averagedMode_summable hRH eps (u + lam)).sub (averagedMode_summable hRH eps u)
  have htermSum : Summable (fun ρ : Zeros => (multiplicity ρ : ℂ) * sharpCoefficient lam ρ *
      (∫ t in Icc u (u + eps), W t * wave (ordinate ρ) t)) :=
    hSm.congr (fun ρ => (hterm ρ).symm)
  have h := sharp_spectral_integral_eq_tsum hRH hlam hlam₁ hu (by linarith : u ≤ u + eps)
    hW₂ htermSum
  simp_rw [hterm] at h
  rw [logPsiError_integral_eq_averaged_sub hu heps hlam,
    (averagedMode_summable hRH eps (u + lam)).tsum_sub (averagedMode_summable hRH eps u)] at h
  simpa only [Complex.ofReal_re, Complex.sub_re] using congrArg Complex.re h

private theorem averagedLogPsiError_sub_eq (hRH : RiemannHypothesis) {eps a u : ℝ}
    (heps : 0 ≤ eps) (ha : 0 < a) (hau : a ≤ u) :
    averagedLogPsiError eps u - averagedLogPsiError eps a =
      (∑' ρ, averagedMode eps u ρ).re - (∑' ρ, averagedMode eps a ρ).re := by
  let F (u : ℝ) := averagedLogPsiError eps u - (∑' ρ, averagedMode eps u ρ).re
  have hstep {u t : ℝ} (hu : 0 < u) (ht : 0 < t) (ht₁ : t ≤ 1) : F (u + t) = F u := by
    have h := local_averagedLogPsiError_sub hRH heps hu ht ht₁
    dsimp only [F]
    linarith
  have hind (n : ℕ) : ∀ u, a ≤ u → u ≤ a + n → F u = F a := by
    induction n with
    | zero =>
      intro u hau hu
      have he : u = a := le_antisymm (by simpa using hu) hau
      rw [he]
    | succ n ih =>
      intro u hau hu
      by_cases hn : u ≤ a + n
      · exact ih u hau hn
      have hs : 0 < u - (a + n) := sub_pos.mpr (lt_of_not_ge hn)
      have hs₁ : u - (a + n) ≤ 1 := by
        push_cast at hu
        linarith
      have he := hstep (u := a + n) (by positivity) hs hs₁
      rw [show a + (n : ℝ) + (u - (a + n)) = u by ring] at he
      exact he.trans (ih (a + n) (le_add_of_nonneg_right (Nat.cast_nonneg _)) le_rfl)
  obtain ⟨n, hn⟩ := exists_nat_ge (u - a)
  have hh := hind n u hau (by linarith)
  dsimp only [F] at hh
  linarith

/-- Uniform bound for the change in the averaged log-coordinate discrepancy
from any positive starting point. Its constant comes from the verified
two-sided inverse-square zero sum. -/
theorem averagedLogPsiError_sub_abs_le (hRH : RiemannHypothesis) {eps a u : ℝ}
    (heps : 0 ≤ eps) (heps₁ : eps ≤ 1) (ha : 0 < a) (hau : a ≤ u) :
    |averagedLogPsiError eps u - averagedLogPsiError eps a| ≤
      (3 / 20 : ℝ) * (Real.exp (u / 2) + Real.exp (a / 2)) := by
  have hhalf : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      norm_num
    nlinarith [Real.exp_one_lt_d9, sq_nonneg (Real.exp (1 / 2 : ℝ) - 2)]
  have hExp : 1 + Real.exp (eps / 2) ≤ 3 := by
    have h := Real.exp_le_exp.mpr (show eps / 2 ≤ 1 / 2 by linarith)
    linarith
  have hnorm (v : ℝ) : |(∑' ρ, averagedMode eps v ρ).re| ≤ (3 / 20 : ℝ) * Real.exp (v / 2) := by
    have hS := ((inverse_square_zero_sum_lt hRH).1).mul_left
      ((1 + Real.exp (eps / 2)) * Real.exp (v / 2))
    have hdom := norm_averagedMode_le hRH eps v
    have hnormS := hS.of_nonneg_of_le (fun _ => norm_nonneg _) hdom
    have hnum : (∑' ρ : Zeros, multiplicity ρ / ordinate ρ^2) ≤ (1 / 20 : ℝ) :=
      (inverse_square_zero_sum_lt hRH).2.le.trans (by norm_num)
    calc
      _ ≤ ‖∑' ρ, averagedMode eps v ρ‖ := Complex.abs_re_le_norm _
      _ ≤ ∑' ρ, ‖averagedMode eps v ρ‖ := norm_tsum_le_tsum_norm hnormS
      _ ≤ ∑' ρ : Zeros, ((1 + Real.exp (eps / 2)) * Real.exp (v / 2)) *
          (multiplicity ρ / ordinate ρ^2) := hnormS.tsum_le_tsum hdom hS
      _ ≤ _ := by
        rw [tsum_mul_left]
        calc
          _ ≤ ((1 + Real.exp (eps / 2)) * Real.exp (v / 2)) * (1 / 20 : ℝ) :=
            mul_le_mul_of_nonneg_left hnum (by positivity)
          _ ≤ (3 * Real.exp (v / 2)) * (1 / 20 : ℝ) := by gcongr
          _ = _ := by ring
  rw [averagedLogPsiError_sub_eq hRH heps ha hau]
  exact (abs_sub _ _).trans (by linarith [hnorm a, hnorm u])

end GoldbachExplicit
