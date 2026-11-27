import Goldbach.Explicit.CompactSchur
import Goldbach.Explicit.CosineRegularity
import Goldbach.Explicit.GammaConvolution
import Goldbach.Explicit.PoleEstimate

/-! The first Weil formula for the compact cosine zero row. -/

open MeasureTheory Set
noncomputable section

namespace GoldbachExplicit

open GoldbachGaussian GoldbachZeros Zeta23

/-- The multiplicity-weighted cosine row at the given real ordinate. -/
def cosineRow (V t : ℝ) : ℝ :=
  ∑' ρ : Zeros, multiplicity ρ * cosineKernel V (t - ordinate ρ)

/-- The archimedean part of the cosine row. -/
def cosineArchimedean (V t : ℝ) : ℝ :=
  ∫ s : ℝ, cosineKernel V s / (2 * Real.pi) * EF.gammaBracket (t + s)

/-- The nonnegative von Mangoldt weights appearing in a cosine row. -/
def cosinePrimeWeight (V : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n * cosineWeight V (Real.log n)

private theorem cosineTransform_even (V : ℝ) (z : ℂ) :
    cosineTransform V (-z) = cosineTransform V z :=
  Taper.paperFT_neg_of_even (cosineWeight_even V) z

private theorem cosineTransform_ofReal (V s : ℝ) :
    cosineTransform V (s : ℂ) = (cosineKernel V s : ℂ) :=
  Taper.paperFT_ofReal_eq_re (cosineWeight_even V) s

/-- The first Weil identity, with the two poles, convolution of the gamma
factor, and the exact finite prime sum. -/
theorem cosine_row_formula (hRH : RiemannHypothesis) {V : ℝ} (hV : 0 < V) (t : ℝ) :
    Summable (fun ρ : Zeros => multiplicity ρ * cosineKernel V (t - ordinate ρ)) ∧
      cosineRow V t = (polePair V t).re + cosineArchimedean V t -
        2 * ∑ n ∈ Finset.Ioc 0 ⌊Real.exp V⌋₊,
          cosinePrimeWeight V n * Real.cos (t * Real.log n) := by
  let k (u : ℝ) : ℂ := (cosineWeight V u : ℂ) * wave (-t) u
  let S := Finset.Ioc 0 ⌊Real.exp V⌋₊
  have hk : ContDiff ℝ 2 k := by
    have hcast : ContDiff ℝ 2 (fun u : ℝ => ((-t * u : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
    unfold k wave
    exact (Complex.ofRealCLM.contDiff.comp (contDiff_two_cosineWeight hV)).mul
      ((hcast.mul contDiff_const).cexp)
  have hkc : HasCompactSupport k :=
    ((cosineWeight_hasCompactSupport V).comp_left Complex.ofReal_zero).mul_right
  have hks : tsupport k ⊆ Icc (-V) V := by
    apply closure_minimal _ isClosed_Icc
    intro u hu
    apply abs_le.mp
    by_contra! h
    exact hu (by simp [k, cosineWeight_zero_of_lt_abs h])
  have hshift (z : ℂ) : paperFT k z = cosineTransform V (z - (t : ℂ)) := by
    unfold paperFT k cosineTransform wave
    apply integral_congr_ae
    filter_upwards with u
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have h := weil_explicit_on_line hRH k hk hkc
  have hterm (ρ : Zeros) : (multiplicity ρ : ℂ) * paperFT k (ordinate ρ) =
      ((multiplicity ρ * cosineKernel V (t - ordinate ρ) : ℝ) : ℂ) := by
    have he : cosineKernel V (ordinate ρ - t) = cosineKernel V (t - ordinate ρ) := by
      rw [← neg_sub (ordinate ρ) t, cosineKernel_even V]
    rw [hshift, ← Complex.ofReal_sub, cosineTransform_ofReal, he, Complex.ofReal_mul]
  refine ⟨Complex.summable_ofReal.mp (h.1.congr hterm), ?_⟩
  have hp : paperFT k (Complex.I / 2) + paperFT k (-Complex.I / 2) = polePair V t := by
    calc
      _ = cosineTransform V (-((t : ℂ) + ((-1 / 2 : ℝ) : ℂ) * Complex.I)) +
          cosineTransform V (-((t : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I)) := by
        rw [hshift, hshift]
        congr 2 <;> push_cast <;> ring
      _ = _ := by simp only [cosineTransform_even, polePair, add_comm]
  have hg : (1 / (2 * Real.pi) : ℂ) *
      (∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ)) = (cosineArchimedean V t : ℂ) := by
    rw [← integral_const_mul]
    have hf (r : ℝ) : (1 / (2 * Real.pi) : ℂ) *
        (paperFT k (r : ℂ) * (EF.gammaBracket r : ℂ)) =
        ((cosineKernel V (r - t) / (2 * Real.pi) * EF.gammaBracket r : ℝ) : ℂ) := by
      rw [hshift, ← Complex.ofReal_sub, cosineTransform_ofReal]
      push_cast
      ring
    simp_rw [hf, integral_complex_ofReal]
    congr 1
    unfold cosineArchimedean
    simpa only [show ∀ r : ℝ, t + (r - t) = r from fun r => by ring] using
      integral_sub_right_eq_self (fun s => cosineKernel V s / (2 * Real.pi) * EF.gammaBracket (t + s)) t
  have hr (u : ℝ) : (k u + k (-u)).re = 2 * cosineWeight V u * Real.cos (t * u) := by
    have hw (v : ℝ) : (wave (-t) v).re = Real.cos (t * v) := by
      unfold wave
      simp [Complex.exp_re, Complex.mul_re, Complex.mul_im, neg_mul]
    unfold k
    simp only [Complex.add_re, Complex.re_ofReal_mul, hw, mul_neg, Real.cos_neg]
    rw [cosineWeight_even V u]
    ring
  have hprime :
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))) =
        ∑ n ∈ S, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
          (k (Real.log n) + k (-Real.log n)) :=
    tsum_eq_sum (s := S) (fun n hn => EF.prime_summand_eq_zero hks hn)
  have he := h.2
  simp_rw [hterm] at he
  rw [EF.literatureRHS, hp, hprime, hg, ← Complex.ofReal_tsum] at he
  have hreal := congrArg Complex.re he
  simp only [Complex.ofReal_re, Complex.add_re, Complex.sub_re, Complex.re_sum,
    Complex.re_ofReal_mul, hr] at hreal
  unfold cosineRow
  rw [hreal]
  rw [Finset.mul_sum]
  have hsum : (∑ n ∈ S, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      (2 * cosineWeight V (Real.log n) * Real.cos (t * Real.log n))) =
      ∑ n ∈ S, 2 * (cosinePrimeWeight V n * Real.cos (t * Real.log n)) := by
    exact Finset.sum_congr rfl (fun n _ => by unfold cosinePrimeWeight; ring)
  rw [hsum]
  ring

/-- Upper bound for a cosine row using the verified gamma envelope. -/
theorem cosine_row_le (hRH : RiemannHypothesis) {V : ℝ} (hV : 2 * Real.pi ≤ V) (t : ℝ) :
    cosineRow V t ≤ ‖polePair V t‖ + Real.log (|t| + 3) -
      2 * ∑ n ∈ Finset.Ioc 0 ⌊Real.exp V⌋₊,
        cosinePrimeWeight V n * Real.cos (t * Real.log n) := by
  have hpV : 0 < V := (by positivity : (0 : ℝ) < 2 * Real.pi).trans_le hV
  rw [(cosine_row_formula hRH hpV t).2]
  have hGamma : cosineArchimedean V t ≤ Real.log (|t| + 3) := (cosine_gamma_average_le hV t).2
  linarith only [Complex.re_le_norm (polePair V t), hGamma]

end GoldbachExplicit
