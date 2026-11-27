import Goldbach.SharpSpectrum
import Goldbach.SpectralAsymptotic
import Goldbach.LogWidth
import Goldbach.Target

open Filter MeasureTheory Set
open scoped Topology

noncomputable section
namespace GoldbachConcrete

open GoldbachSpectrum GoldbachZeros GoldbachGaussian GoldbachArithmetic

private def trivialError (d y : ℝ) : ℝ :=
  (trivialZeroTerm ((1 + d) * y) - trivialZeroTerm y) / y

private theorem trivialError_measurable (d : ℝ) : Measurable (trivialError d) := by
  have hg : Measurable trivialZeroTerm := by unfold trivialZeroTerm; fun_prop
  unfold trivialError
  exact ((hg.comp (measurable_const.mul measurable_id)).sub hg).div measurable_id

private theorem trivialError_norm_le {d u y : ℝ} (hd : 0 ≤ d) (hu : 2 ≤ u) (hy : u ≤ y) :
    ‖trivialError d y‖ ≤ 2 * d / u^3 := by
  have hu₀ : 0 < u := by linarith
  have hy₀ : 0 < y := hu₀.trans_le hy
  unfold trivialError
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hy₀]
  calc
    _ ≤ (2 * d / y^2) / y := div_le_div_of_nonneg_right (trivialZeroTerm_sub_le hd (hu.trans hy)) hy₀.le
    _ = 2 * d / y^3 := by rw [div_div, show y ^ 2 * y = y ^ 3 by ring]
    _ ≤ 2 * d / u^3 := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hu₀.le hy 3)

private theorem logWidth_pos {c x : ℝ} (hc : 0 < c) (hx : 1 < x) : 0 < logWidth c x := by
  unfold logWidth
  exact Real.log_pos (by linarith [relativeWidth_pos hc hx])

private theorem logWidth_tendsto_zero {c : ℝ} :
    Tendsto (logWidth c) atTop (𝓝 0) := by
  have h := (relativeWidth_tendsto_zero c).const_add 1
  rw [add_zero] at h
  have h' := (Real.continuousAt_log one_ne_zero).tendsto.comp h
  change Tendsto (fun x => Real.log (1 + relativeWidth c x)) atTop (𝓝 0)
  simpa only [Function.comp_def, Real.log_one] using h'

private def widthScale (c x : ℝ) : ℝ :=
  relativeWidth c x * (Real.log x)^2

private def spectralMass (b lam : ℝ) : ℝ :=
  ∑' ρ : Zeros, diagonalEnergy b (sharpCoefficient lam) ρ

private theorem spectralMass_ratio_tendsto (hRH : RiemannHypothesis) {b c : ℝ}
    (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun x => spectralMass b (logWidth c x) / widthScale c x) atTop (𝓝 1) := by
  have hp : Tendsto (logWidth c) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨logWidth_tendsto_zero,
      (eventually_gt_atTop (1 : ℝ)).mono (fun _ hx => logWidth_pos hc hx)⟩
  have h := ((weighted_spectral_asymptotic hRH hb).comp hp).mul (logWidth_scale_tendsto_one hc)
  rw [mul_one] at h
  apply h.congr'
  have hsmall := (logWidth_tendsto_zero (c := c)).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_gt_atTop (1 : ℝ), hsmall] with x hx hlam₁
  have hl := logWidth_pos hc hx
  have hlog : 0 < Real.log (1 / logWidth c x) := Real.log_pos ((one_lt_div hl).mpr hlam₁)
  have hs : 0 < widthScale c x := mul_pos (relativeWidth_pos hc hx) (sq_pos_of_pos (Real.log_pos hx))
  change (spectralMass b (logWidth c x) / (logWidth c x * (Real.log (1 / logWidth c x))^2)) *
      (logWidth c x * (Real.log (1 / logWidth c x))^2 / widthScale c x) = _
  field_simp [hl.ne', hlog.ne', hs.ne']

private theorem corrected_variance_le (hRH : RiemannHypothesis)
    {d b x u v : ℝ} (hb : 0 < b) (hd : 0 < d) (hx : 0 < x) (hu : 2 ≤ u) (hv : 0 < v)
    (hlam₁ : Real.log (1 + d) ≤ 1) :
    (∫ y in Icc u v, weight b (Real.log (y / x)) * (psiError d y - trivialError d y)^2) ≤
      spectralMass b (Real.log (1 + d)) := by
  let A (y : ℝ) := Chebyshev.psi ((1 + d) * y) - Chebyshev.psi y - d * y -
      (trivialZeroTerm ((1 + d) * y) - trivialZeroTerm y)
  have hA (y : ℝ) : psiError d y - trivialError d y = A y / y := by
    unfold psiError trivialError A
    exact (sub_div _ _ _).symm
  let lam := Real.log (1 + d)
  have hl : 0 < lam := Real.log_pos (by linarith)
  have hu₀ : 0 < u := by linarith
  have hpos : Icc (Real.log u) (Real.log v) ⊆ Ioi (0 : ℝ) := fun t ht =>
    (Real.log_pos (by linarith : 1 < u)).trans_le ht.1
  have hlog := GoldbachLogIntegral.integral_normalized_error (z := Real.log x) hu₀ hv (weight b) A
  have he (t : ℝ) : A (Real.exp t) / Real.sqrt (Real.exp t) = -sharpSpectralValue lam t := by
    have hw : Real.exp (t + lam) = (1 + d) * Real.exp t := by
      rw [Real.exp_add, show Real.exp lam = 1 + d from Real.exp_log (by linarith), mul_comm]
    unfold sharpSpectralValue A
    rw [sqrt_exp_eq, div_eq_mul_inv, ← Real.exp_neg, show -(t / 2) = -t / 2 by ring, hw]
    ring
  calc
    _ = ∫ y in Icc u v, weight b (Real.log y - Real.log x) * (A y)^2 / y^2 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      have hy₀ := hu₀.trans_le hy.1
      change weight b (Real.log (y / x)) * (psiError d y - trivialError d y)^2 =
        weight b (Real.log y - Real.log x) * (A y)^2 / y^2
      rw [hA, Real.log_div hy₀.ne' hx.ne', div_pow, mul_div_assoc]
    _ = ∫ t in Icc (Real.log u) (Real.log v), weight b (t - Real.log x) * (A (Real.exp t) / Real.sqrt (Real.exp t))^2 := hlog
    _ = ∫ t in Icc (Real.log u) (Real.log v), weight b (t - Real.log x) * (sharpSpectralValue lam t)^2 := by
      simp_rw [he, neg_sq]
    _ ≤ _ := (local_sharp_spectral_mean_square hRH hb hl hlam₁ (Real.log x) _
      measurableSet_Icc hpos).2

private theorem variance_arithmetic_remainder {a x d : ℝ}
    (ha : 0 < a) (hx : 2 ≤ x)
    (hd : 0 ≤ d) (hd₁ : d ≤ 1) (hlogx : 1 ≤ Real.log x) :
    x * (2 * d / (a * x)^3)^2 ≤ (4 / a^6 * x⁻¹) * (d * (Real.log x)^2) := by
  have hx₀ : 0 < x := by linarith
  have hx₄ : 1 ≤ x^4 := one_le_pow₀ (by linarith)
  have hdsq : d^2 ≤ d := by nlinarith [mul_nonneg hd (sub_nonneg.mpr hd₁)]
  have hlogs : 1 ≤ (Real.log x)^2 := by nlinarith [sq_nonneg (Real.log x - 1)]
  calc
    _ = (4 / a^6 * x⁻¹) * (d^2 / x^4) := by field_simp [ha.ne', hx₀.ne']; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (div_le_self (sq_nonneg _) hx₄).trans (hdsq.trans (le_mul_of_one_le_right hd hlogs))

/-- The sharp local Chebyshev variance with the coefficient required by the
Goldbach reduction. The only analytic hypothesis is RH. -/
theorem gaussianPsiSecondMoment_of_RH (hRH : RiemannHypothesis) : GaussianPsiSecondMoment := by
  intro a ha ha' b hb c hc ε hε
  let η := min (ε / 8) 1
  have hη : 0 < η := lt_min (by positivity) zero_lt_one
  have hη₁ : η ≤ 1 := min_le_right _ _
  have hηε : η ≤ ε / 8 := min_le_left _ _
  let K := 1 + η⁻¹
  have hK : 0 < K := by unfold K; positivity
  have hscale : (1 + η) * (1 + η) ≤ 1 + ε / 2 := by
    have hηsq : η^2 ≤ η := by nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hη₁)]
    nlinarith
  have hc₀ : 0 < c := by linarith
  have hspec := (spectralMass_ratio_tendsto hRH hb hc₀).eventually
    (gt_mem_nhds (show (1 : ℝ) < 1 + η by linarith))
  have htriv := ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).const_mul
    (4 / a^6))
  rw [mul_zero] at htriv
  have htriv' := htriv.eventually (gt_mem_nhds (show 0 < ε / 2 / K by positivity))
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (2 / a),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    (relativeWidth_tendsto_zero c).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    logWidth_tendsto_zero (c := c) |>.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hspec, htriv'] with x hx hxa hlogx hd₁ hl₁ hs ht
  let d := relativeWidth c x
  let u := a * x
  let v := (1 - a) * x
  let J := Icc u v
  let W (y : ℝ) := weight b (Real.log (y / x))
  let E (y : ℝ) := psiError d y
  let G (y : ℝ) := trivialError d y
  let C := 2 * d / u^3
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 < x := by linarith
  have hu₂ : 2 ≤ u := by
    simpa only [u, mul_comm] using (div_le_iff₀ ha).mp hxa
  have hu₀ : 0 < u := by linarith
  have huv : u ≤ v := by
    unfold u v
    exact mul_le_mul_of_nonneg_right (by linarith) hx₀.le
  have hv₀ : 0 < v := hu₀.trans_le huv
  have hlen : v - u ≤ x := by
    unfold u v
    nlinarith [mul_nonneg ha.le hx₀.le]
  have hd : 0 < d := relativeWidth_pos hc₀ hx₁
  have hS : 0 < widthScale c x := mul_pos hd (sq_pos_of_pos (Real.log_pos hx₁))
  have hM : spectralMass b (logWidth c x) ≤ (1 + η) * widthScale c x :=
    (div_lt_iff₀ hS).mp hs |>.le
  have hw (y : ℝ) : 0 ≤ W y := (Real.exp_pos _).le
  have hw₁ (y : ℝ) : W y ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) (sq_nonneg _))
  have hwM : Measurable W := by
    apply (show Continuous (weight b) by unfold weight; fun_prop).measurable.comp
    exact Real.measurable_log.comp (measurable_id.div_const x)
  have hG (y : ℝ) (hy : y ∈ J) : ‖G y‖ ≤ C := trivialError_norm_le hd.le hu₂ hy.1
  let M := (Chebyshev.psi ((1 + d) * v) + Chebyshev.psi v + d * v) / u
  have hE (y : ℝ) (hy : y ∈ J) : ‖E y‖ ≤ M := by
    have hy₀ : 0 < y := hu₀.trans_le hy.1
    have hdy₀ : 0 ≤ d * y := mul_nonneg hd.le hy₀.le
    have hl := (abs_sub (Chebyshev.psi ((1 + d) * y) - Chebyshev.psi y) (d * y)).trans
      (add_le_add (abs_sub (Chebyshev.psi ((1 + d) * y)) (Chebyshev.psi y)) (le_refl |d * y|))
    have hψ₁ := Chebyshev.psi_nonneg ((1 + d) * y)
    have hψ₂ := Chebyshev.psi_nonneg y
    rw [abs_of_nonneg hψ₁, abs_of_nonneg hψ₂, abs_of_nonneg hdy₀] at hl
    unfold E psiError M
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hy₀]
    refine div_le_div₀ (by positivity) (hl.trans ?_) hu₀ hy.1
    exact add_le_add (add_le_add (Chebyshev.psi_mono (mul_le_mul_of_nonneg_left hy.2 (by positivity)))
      (Chebyshev.psi_mono hy.2)) (mul_le_mul_of_nonneg_left hy.2 hd.le)
  have hi (f : ℝ → ℝ) (hfm : Measurable f) (B : ℝ) (hB : ∀ y ∈ J, ‖f y‖ ≤ B) :
      IntegrableOn (fun y => W y * (f y)^2) J := by
    refine (integrable_const (μ := volume.restrict J) (B^2)).mono'
      (hwM.mul (hfm.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := J) measurableSet_Icc] with y hy
    rw [Real.norm_of_nonneg (mul_nonneg (hw y) (sq_nonneg _))]
    refine (mul_le_of_le_one_left (sq_nonneg _) (hw₁ y)).trans ?_
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) (hB y hy) 2
  have hEI := hi E (psiError_measurable d) M hE
  have hGI := hi G (trivialError_measurable d) C hG
  have hAI := hi (fun y => E y - G y) ((psiError_measurable d).sub (trivialError_measurable d))
    (M + C) (fun y hy => (norm_sub_le _ _).trans (add_le_add (hE y hy) (hG y hy)))
  have hcorrect : (∫ y in J, W y * (E y - G y)^2) ≤ (1 + η) * widthScale c x :=
    (corrected_variance_le hRH hb hd hx₀ hu₂ hv₀ hl₁.le).trans hM
  have hrem : (∫ y in J, W y * (G y)^2) ≤ (ε / 2 / K) * widthScale c x := by
    calc
      _ ≤ ∫ _ in J, C^2 := by
        apply setIntegral_mono_on hGI (integrable_const _) measurableSet_Icc
        intro y hy
        refine (mul_le_of_le_one_left (sq_nonneg _) (hw₁ y)).trans ?_
        simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) (hG y hy) 2
      _ ≤ x * C^2 := by
        rw [setIntegral_const, smul_eq_mul]
        change volume.real (Icc u v) * C^2 ≤ _
        rw [Real.volume_real_Icc_of_le huv]
        exact mul_le_mul_of_nonneg_right hlen (sq_nonneg _)
      _ ≤ (4 / a^6 * x⁻¹) * widthScale c x :=
        variance_arithmetic_remainder ha hx hd.le hd₁.le hlogx
      _ ≤ _ := mul_le_mul_of_nonneg_right ht.le hS.le
  have hpoint (y : ℝ) : W y * (E y)^2 ≤
      (1 + η) * (W y * (E y - G y)^2) + K * (W y * (G y)^2) := by
    have h := sq_sub_le hη (E y - G y) (-G y)
    rw [neg_sq, sub_neg_eq_add, sub_add_cancel] at h
    unfold K
    exact (mul_le_mul_of_nonneg_left h (hw y)).trans_eq (by ring)
  have hIcomb : IntegrableOn (fun y => (1 + η) * (W y * (E y - G y)^2) + K * (W y * (G y)^2)) J :=
    (hAI.const_mul (1 + η)).add (hGI.const_mul K)
  calc
    _ ≤ ∫ y in J, (1 + η) * (W y * (E y - G y)^2) + K * (W y * (G y)^2) :=
      setIntegral_mono_on hEI hIcomb measurableSet_Icc (fun y _ => hpoint y)
    _ = (1 + η) * (∫ y in J, W y * (E y - G y)^2) + K * (∫ y in J, W y * (G y)^2) := by
      rw [integral_add (hAI.const_mul (1 + η)) (hGI.const_mul K), integral_const_mul, integral_const_mul]
    _ ≤ (1 + η) * ((1 + η) * widthScale c x) + K * ((ε / 2 / K) * widthScale c x) :=
      add_le_add (mul_le_mul_of_nonneg_left hcorrect (by positivity)) (mul_le_mul_of_nonneg_left hrem hK.le)
    _ ≤ (1 + ε) * widthScale c x := by
      have hKε : K * (ε / 2 / K) = ε / 2 := by field_simp [hK.ne']
      rw [← mul_assoc K, hKε, ← mul_assoc, ← add_mul]
      apply mul_le_mul_of_nonneg_right _ hS.le
      linarith
    _ = _ := by unfold widthScale; ring

end GoldbachConcrete

/-- Under RH, every sufficiently large interval of length c (log x)²,
with c > 1, contains a sum of two odd primes. -/
theorem goldbach_short_interval (hRH : RiemannHypothesis) :
    ∀ c : ℝ, 1 < c → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < (p : ℝ) + (q : ℝ) ∧
        (p : ℝ) + (q : ℝ) ≤ x + c * (Real.log x)^2 :=
  goldbach_short_interval_of_psi GoldbachConcrete.gaussianPsiSecondMoment_of_RH hRH
