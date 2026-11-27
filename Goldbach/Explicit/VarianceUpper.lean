import Goldbach.Explicit.MainZeroSum
import Goldbach.Explicit.PrimePowerVariance
import Goldbach.Explicit.TrivialZeroVariance
import Goldbach.ChebyshevTransfer

/-! Transfer of the explicit spectral bound to the odd-prime variance. -/

open MeasureTheory Set
noncomputable section

namespace GoldbachExplicit

open GoldbachConcrete GoldbachArithmetic GoldbachSpectrum

private def trivialDifference (d y : ℝ) : ℝ :=
  trivialZeroTerm ((1 + d) * y) - trivialZeroTerm y

private def spectralNumerator (d y : ℝ) : ℝ :=
  d * y + trivialDifference d y - (Chebyshev.psi ((1 + d) * y) - Chebyshev.psi y)

private theorem sharpSpectralValue_eq_normalized {d : ℝ} (hd : 0 < 1 + d) (u : ℝ) :
    spectralNumerator d (Real.exp u) / Real.sqrt (Real.exp u) =
      sharpSpectralValue (Real.log (1 + d)) u := by
  have hroot : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp]
    congr 1
    ring
  have harg : Real.exp (u + Real.log (1 + d)) = (1 + d) * Real.exp u := by
    rw [Real.exp_add, Real.exp_log hd, mul_comm]
  unfold spectralNumerator sharpSpectralValue trivialDifference
  rw [hroot, div_eq_mul_inv, ← Real.exp_neg, harg, show -(u / 2) = -u / 2 by ring]
  ring

/-- The complete spectral component of the explicit variance, in the
original moving interval and with the reciprocal-square normalization. -/
private theorem explicit_spectral_variance_lt_of_energy (hRH : RiemannHypothesis)
    {L K : ℝ} (hL : 28 ≤ L) (hE : Summable (cosineEnergy (bandwidth L) (logWidth L)))
    (hEbound : (∑' ρ, cosineEnergy (bandwidth L) (logWidth L) ρ) < delta L * K) :
    let x := Real.exp L
    let A := trimmedEndpoint L
    let d := delta L
    (∫ y in Icc A (x - A),
      upperWeight (bandwidth L) x y * (spectralNumerator d y)^2 / y^2) <
        d * K := by
  let x := Real.exp L
  let A := trimmedEndpoint L
  let B := x - A
  let d := delta L
  let V := bandwidth L
  let lam := logWidth L
  let I := Icc A B
  have hx : 0 < x := Real.exp_pos _
  have hL₀ : 0 < L := by linarith
  have hd : 0 < d := delta_pos_of_pos hL₀
  have hL₂ : 2 ≤ L^2 := by nlinarith [sq_nonneg (L - 28)]
  have hAx : A ≤ x / 2 := div_le_div_of_nonneg_left hx.le (by norm_num) hL₂
  have hAB : A ≤ B := by dsimp [B]; linarith
  have hA₂ : 2 ≤ A := (explicit_interval_endpoints_of_ge_28 hL ⟨le_rfl, hAB⟩).1
  have hA : 0 < A := by linarith
  have hB : 0 < B := hA.trans_le hAB
  have hV : 0 < V := bandwidth_pos_of_pos hL₀
  have hl : 0 < lam := logWidth_pos_of_pos hL₀
  have hl₁ : lam ≤ 1 := (logWidth_le_delta_of_pos hL₀).trans
    ((delta_lt_of_ge_28 hL).le.trans (by norm_num))
  have hlo : 0 < Real.log A := Real.log_pos (by linarith)
  have hhi : Real.log A ≤ Real.log B := Real.log_le_log hA hAB
  have hS := cosine_sharp_meanSquare_le hRH hl hl₁ hlo hhi hV L hE
  have hLog (y : ℝ) (hy : y ∈ I) :
      upperWeight V x y = cosineWeight V (Real.log y - L) := by
    have hy₀ := hA.trans_le hy.1
    unfold upperWeight
    rw [Real.log_div hx.ne' hy₀.ne', show Real.log x = L from Real.log_exp _,
      show L - Real.log y = -(Real.log y - L) by ring, cosineWeight_even V]
  change (∫ y in I, upperWeight V x y * (spectralNumerator d y)^2 / y^2) < _
  calc
    _ = ∫ y in I, cosineWeight V (Real.log y - L) * (spectralNumerator d y)^2 / y^2 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      change upperWeight V x y * (spectralNumerator d y)^2 / y^2 = _
      rw [hLog y hy]
    _ = ∫ u in Icc (Real.log A) (Real.log B),
        cosineWeight V (u - L) * (spectralNumerator d (Real.exp u) / Real.sqrt (Real.exp u))^2 :=
      GoldbachLogIntegral.integral_normalized_error hA hB _ _
    _ = ∫ u in Icc (Real.log A) (Real.log B),
        cosineWeight V (u - L) * ‖(sharpSpectralValue lam u : ℂ)‖^2 := by
      simp_rw [sharpSpectralValue_eq_normalized (show 0 < 1 + d by linarith)]
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, lam, logWidth, d]
    _ ≤ _ := hS
    _ < _ := hEbound

theorem explicit_spectral_variance_lt (hRH : RiemannHypothesis) {L : ℝ} (hL : 42 ≤ L) :
    let x := Real.exp L
    let A := trimmedEndpoint L
    let d := delta L
    (∫ y in Icc A (x - A),
      upperWeight (bandwidth L) x y * (spectralNumerator d y)^2 / y^2) <
        d * ((L - 2 * Real.log L)^2 + (11 / 3) * L + 104) := by
  obtain ⟨hE, hEbound⟩ := cosine_energy_explicit_le hRH hL
  exact explicit_spectral_variance_lt_of_energy hRH (by linarith) hE hEbound

private theorem explicit_variance_lt_of_bounds {L K η ζ e : ℝ} (hL : 28 ≤ L)
    (hη : 0 < η) (hζ : 0 < ζ) (hK : K ≤ L^2)
    (hSpectral :
      let x := Real.exp L
      let A := trimmedEndpoint L
      let d := delta L
      (∫ y in Icc A (x - A),
        upperWeight (bandwidth L) x y * (spectralNumerator d y)^2 / y^2) < d * K)
    (hPrimePower :
      let x := Real.exp L
      let A := trimmedEndpoint L
      let d := delta L
      IntegrableOn (fun y => (primePowerIncrement d y)^2 / y^2) (Icc A (x - A)) ∧
        (∫ y in Icc A (x - A), (primePowerIncrement d y)^2 / y^2) < d * e) :
    weightedVariance L <
      delta L * (K + η * L^2 + (1 + η⁻¹) * ((1 + ζ⁻¹) / 10^6 + (1 + ζ) * e)) := by
  let x := Real.exp L
  let a := trimmedEndpoint L
  let d := delta L
  let V := bandwidth L
  let I := Icc a (x - a)
  let μ := volume.restrict I
  let W := upperWeight V x
  let B (y : ℝ) := d * (density d y - 1)
  let S (y : ℝ) := spectralNumerator d y / y
  let R (y : ℝ) := trivialDifference d y / y
  let P (y : ℝ) := primePowerIncrement d y / y
  have hL₀ : 0 < L := by linarith
  have hd : 0 < d := delta_pos_of_pos hL₀
  have hV : 0 < V := bandwidth_pos_of_pos hL₀
  have ha : 0 < a := div_pos (Real.exp_pos _) (sq_pos_of_pos hL₀)
  have hW₀ (y : ℝ) : 0 ≤ W y := cosineWeight_nonneg hV _
  have hW₁ (y : ℝ) : W y ≤ 1 := cosineWeight_le_one hV _
  have hWm : Measurable W :=
    (continuous_cosineWeight hV).measurable.comp (measurable_const.div measurable_id).log
  have hWb : ∀ᵐ y ∂μ, ‖W y‖ ≤ 1 := Filter.Eventually.of_forall (fun y => by
    rw [Real.norm_of_nonneg (hW₀ y)]
    exact hW₁ y)
  have hrel (y : ℝ) (hy : y ∈ I) : B y = -S y + R y - P y := by
    have hy₂ := (explicit_interval_endpoints_of_ge_28 hL hy).1
    have hy₀ : 0 < y := by linarith
    unfold B S R P spectralNumerator primePowerIncrement
    rw [density_eq_theta_sub hd hy₂]
    field_simp [hd.ne', hy₀.ne']
    ring
  have hBI : Integrable (fun y => W y * (B y)^2) μ := by
    have hh : Integrable (fun y => (B y)^2) μ := by
      simpa only [B, mul_pow] using
        (integrableOn_density_error (v := x - a) hd ha).const_mul (d^2)
    exact hh.bdd_mul hWm.aestronglyMeasurable hWb
  obtain ⟨hR₀, hRb⟩ := explicit_trivialZero_error_lt_of_ge_28 hL
  have hRI : Integrable (fun y => W y * (R y)^2) μ := by
    simpa only [R, div_pow, ← mul_div_assoc, trivialDifference, μ, I, a, x, W, V, d,
      IntegrableOn] using hR₀
  have hR : (∫ y, W y * (R y)^2 ∂μ) < d / 10^6 := by
    simpa only [R, div_pow, ← mul_div_assoc, trivialDifference] using hRb
  obtain ⟨hP₀, hPb⟩ := hPrimePower
  have hPI : Integrable (fun y => (P y)^2) μ := by
    simpa only [P, div_pow, μ, I, a, x, d, IntegrableOn] using hP₀
  have hPIW : Integrable (fun y => W y * (P y)^2) μ :=
    hPI.bdd_mul hWm.aestronglyMeasurable hWb
  have hP : (∫ y, W y * (P y)^2 ∂μ) < d * e :=
    (integral_mono hPIW hPI (fun y => mul_le_of_le_one_left (sq_nonneg _) (hW₁ y))).trans_lt
      (by simpa only [P, div_pow] using hPb)
  have hSm : Measurable S := by
    have hψ := Chebyshev.psi_mono.measurable
    have hArg : Measurable (fun y : ℝ => (1 + d) * y) := by fun_prop
    have hR' : Measurable (trivialDifference d) := by unfold trivialDifference trivialZeroTerm; fun_prop
    exact (((measurable_const.mul measurable_id).add hR').sub
      ((hψ.comp hArg).sub hψ)).div measurable_id
  have hSI : Integrable (fun y => W y * (S y)^2) μ := by
    refine (((hBI.const_mul 3).add (hRI.const_mul 3)).add (hPIW.const_mul 3)).mono'
      (hWm.mul (hSm.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := I) measurableSet_Icc] with y hy
    have hs : S y = -B y + R y - P y := by linarith only [hrel y hy]
    have he : (S y)^2 ≤ 3 * ((B y)^2 + (R y)^2 + (P y)^2) := by
      rw [hs]
      nlinarith only [sq_nonneg (B y + R y), sq_nonneg (B y - P y), sq_nonneg (R y + P y)]
    have hh := mul_le_mul_of_nonneg_left he (hW₀ y)
    rw [Real.norm_of_nonneg (mul_nonneg (hW₀ y) (sq_nonneg _))]
    change _ ≤ 3 * (W y * (B y)^2) + 3 * (W y * (R y)^2) + 3 * (W y * (P y)^2)
    nlinarith only [hh]
  have hS : (∫ y, W y * (S y)^2 ∂μ) < d * K := by
    simpa only [S, div_pow, ← mul_div_assoc] using hSpectral
  have hcmp : (∫ y, W y * (B y)^2 ∂μ) ≤
      (1 + η) * (∫ y, W y * (S y)^2 ∂μ) +
        (1 + η⁻¹) * ((1 + ζ⁻¹) * (∫ y, W y * (R y)^2 ∂μ) +
          (1 + ζ) * (∫ y, W y * (P y)^2 ∂μ)) := by
    let Q (y : ℝ) := (1 + ζ⁻¹) * (W y * (R y)^2) + (1 + ζ) * (W y * (P y)^2)
    have hRI' := hRI.const_mul (1 + ζ⁻¹)
    have hPI' := hPIW.const_mul (1 + ζ)
    have hQI : Integrable Q μ := hRI'.add hPI'
    have hQ : (∫ y, Q y ∂μ) =
        (1 + ζ⁻¹) * (∫ y, W y * (R y)^2 ∂μ) +
          (1 + ζ) * (∫ y, W y * (P y)^2 ∂μ) := by
      unfold Q
      rw [integral_add hRI' hPI', integral_const_mul, integral_const_mul]
    rw [← hQ, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hSI.const_mul (1 + η)) (hQI.const_mul (1 + η⁻¹))]
    apply integral_mono_ae hBI ((hSI.const_mul (1 + η)).add (hQI.const_mul (1 + η⁻¹)))
    filter_upwards [ae_restrict_mem (μ := volume) (s := I) measurableSet_Icc] with y hy
    have hb : (B y)^2 = (S y - (R y - P y))^2 := by rw [hrel y hy]; ring
    have hp := mul_le_mul_of_nonneg_left (sq_sub_le hη (S y) (R y - P y)) (hW₀ y)
    have hc : (R y - P y)^2 ≤ (1 + ζ) * (P y)^2 + (1 + ζ⁻¹) * (R y)^2 := by
      rw [show (R y - P y)^2 = (P y - R y)^2 by ring]
      exact sq_sub_le hζ (P y) (R y)
    have hrc := mul_le_mul_of_nonneg_left hc
      (mul_nonneg (hW₀ y) (show 0 ≤ 1 + η⁻¹ by positivity))
    change W y * (B y)^2 ≤ (1 + η) * (W y * (S y)^2) +
      (1 + η⁻¹) * Q y
    rw [hb]
    unfold Q
    nlinarith only [hp, hrc]
  have hJ : weightedVariance L = ∫ y, W y * (B y)^2 ∂μ := by
    change d^2 * (∫ y, W y * (density d y - 1)^2 ∂μ) = _
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    unfold B
    ring
  have hmain : (1 + η) * (∫ y, W y * (S y)^2 ∂μ) < d * (K + η * L^2) := by
    have h₁ := mul_lt_mul_of_pos_left hS (show 0 < 1 + η by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hK (show 0 ≤ η * d by positivity)
    nlinarith only [h₁, h₂]
  have hErrR := mul_le_mul_of_nonneg_left hR.le (show 0 ≤ 1 + ζ⁻¹ by positivity)
  have hErrP := mul_le_mul_of_nonneg_left hP.le (show 0 ≤ 1 + ζ by positivity)
  have hErr := mul_le_mul_of_nonneg_left (add_le_add hErrR hErrP)
    (show 0 ≤ 1 + η⁻¹ by positivity)
  change _ < d * (K + η * L^2 + (1 + η⁻¹) * ((1 + ζ⁻¹) / 10^6 + (1 + ζ) * e))
  rw [hJ]
  nlinarith only [hcmp, hmain, hErr]

/-- The original upper odd-prime variance estimate. -/
theorem explicit_variance_lt (hRH : RiemannHypothesis) {L : ℝ} (hL : 42 ≤ L) :
    weightedVariance L < delta L * ((L - 2 * Real.log L)^2 + 4 * L + 105) := by
  let K := (L - 2 * Real.log L)^2 + (11 / 3) * L + 104
  have hL₀ : 0 < L := by linarith
  have hK : K ≤ L^2 := by
    unfold K
    linarith only [alternative_upper_lt_lower hL, hL]
  have hP := explicit_primePower_error_lt hL
  have h := explicit_variance_lt_of_bounds (η := 1 / (5 * L)) (ζ := 1) (e := 1 / 100)
    (by linarith : 28 ≤ L) (by positivity) (by norm_num) hK (explicit_spectral_variance_lt hRH hL)
    (by simpa only [mul_one_div] using hP)
  refine h.trans_le (mul_le_mul_of_nonneg_left ?_ (delta_pos hL).le)
  simp only [one_div, inv_inv]
  rw [show (5 * L)⁻¹ * L^2 = L / 5 by field_simp [hL₀.ne']]
  unfold K
  linarith only [hL]

/-- The tightened upper variance estimate, with both arithmetic corrections. -/
theorem explicit_variance_lt_of_ge_28 (hRH : RiemannHypothesis) {L : ℝ} (hL : 28 ≤ L) :
    weightedVariance L < delta L * ((L - 2 * Real.log L)^2 + (21 / 4) * L - 7) := by
  let K := (L - 2 * Real.log L)^2 + (9 / 2) * L - 8
  have hL₀ : 0 < L := by linarith
  have hK : K ≤ L^2 := by
    unfold K
    linarith only [alternative_upper_lt_lower_of_ge_28 hL, hL]
  obtain ⟨hE, hEbound⟩ := cosine_energy_explicit_le_of_ge_28 hRH hL
  have h := explicit_variance_lt_of_bounds (η := 1 / (3 * L)) (ζ := 1 / 10) (e := 11 / 100)
    hL (by positivity) (by norm_num) hK
    (explicit_spectral_variance_lt_of_energy hRH hL hE hEbound)
    (explicit_primePower_error_lt_of_ge_28 hL)
  refine h.trans_le (mul_le_mul_of_nonneg_left ?_ (delta_pos_of_pos hL₀).le)
  simp only [one_div, inv_inv]
  rw [show (3 * L)⁻¹ * L^2 = L / 3 by field_simp [hL₀.ne']]
  unfold K
  linarith only [hL]

end GoldbachExplicit
