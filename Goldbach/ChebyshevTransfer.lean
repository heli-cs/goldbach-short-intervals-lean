import Goldbach.PrimePowerError
import Goldbach.SecondMoment

open Asymptotics Filter MeasureTheory Set
open scoped Topology

noncomputable section
namespace GoldbachConcrete

open GoldbachArithmetic

/-- The normalized increment of Chebyshev's ψ after subtracting its main term. -/
def psiError (d y : ℝ) : ℝ :=
  (Chebyshev.psi ((1 + d) * y) - Chebyshev.psi y - d * y) / y

/-- A sharp weighted bound for the normalized Chebyshev ψ error would
suffice for the existence theorem. -/
def GaussianPsiSecondMoment : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 / 2 → ∀ b : ℝ, 0 < b →
    ∀ c : ℝ, 1 < c → ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      (∫ y in Icc (a * x) ((1 - a) * x),
        GoldbachGaussian.weight b (Real.log (y / x)) * (psiError (relativeWidth c x) y)^2)
      ≤ (1 + ε) * relativeWidth c x * (Real.log x)^2

theorem psiError_measurable (d : ℝ) : Measurable (psiError d) := by
  have hp := Chebyshev.psi_mono.measurable
  unfold psiError
  exact (((hp.comp (measurable_const.mul measurable_id)).sub hp).sub
    (measurable_const.mul measurable_id)).div measurable_id

private theorem psiError_eq {d y : ℝ} (hd : 0 < d) (hy : 2 ≤ y) :
    psiError d y = d * (density d y - 1) + primePowerIncrement d y / y := by
  have hy0 : y ≠ 0 := by linarith
  rw [density_eq_theta_sub hd hy]
  unfold psiError primePowerIncrement
  field_simp [hd.ne', hy0]
  ring

theorem sq_sub_le {η : ℝ} (hη : 0 < η) (A B : ℝ) :
    (A - B)^2 ≤ (1 + η) * A^2 + (1 + η⁻¹) * B^2 := by
  have h := mul_nonneg hη.le (sq_nonneg (A + η⁻¹ * B))
  have he : η * (A + η⁻¹ * B)^2 = η * A^2 + 2 * A * B + η⁻¹ * B^2 := by
    field_simp [hη.ne']
    ring
  rw [he] at h
  nlinarith only [h]

/-- Removing higher prime powers preserves the unit leading coefficient in
the Gaussian estimate. -/
theorem gaussianSecondMoment_of_psi (hψ : GaussianPsiSecondMoment) : GaussianSecondMoment := by
  intro a ha ha' b hb c hc ε hε
  have hc0 : 0 < c := zero_lt_one.trans hc
  let η := min (ε / 8) 1
  have hη : 0 < η := lt_min (by positivity) zero_lt_one
  have hη₁ : η ≤ 1 := min_le_right _ _
  have hηε : η ≤ ε / 8 := min_le_left _ _
  let K := 1 + η⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  have hpow := isLittleO_iff.mp (primePowerError_isLittleO ha hc0)
    (show 0 < ε / 2 / K by positivity)
  have hscale : (1 + η) * (1 + η) ≤ 1 + ε / 2 := by
    have hηsq : η^2 ≤ η := by nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hη₁)]
    nlinarith
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (2 / a),
    (relativeWidth_tendsto_zero c).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hψ a ha ha' b hb c hc η hη, hpow] with x hx hxa hd₁ hψx hpowx
  let d := relativeWidth c x
  let I := Icc (a * x) ((1 - a) * x)
  let μ : Measure ℝ := volume.restrict I
  let W : ℝ → ℝ := fun y => GoldbachGaussian.weight b (Real.log (y / x))
  let A := psiError d
  let B : ℝ → ℝ := fun y => d * (density d y - 1)
  let P : ℝ → ℝ := fun y => primePowerIncrement d y / y
  have hd : 0 < d := relativeWidth_pos hc0 (by linarith)
  have hax : 0 < a * x := mul_pos ha (by linarith)
  have ha₂ : 2 ≤ a * x := by
    have h := (div_le_iff₀ ha).mp hxa
    linarith
  have hv : (1 - a) * x ≤ x := by nlinarith [mul_nonneg ha.le (show 0 ≤ x by linarith)]
  have hW₀ (y : ℝ) : 0 ≤ W y := (Real.exp_pos _).le
  have hW₁ (y : ℝ) : W y ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  have hWM : Measurable W := by
    apply (show Continuous (GoldbachGaussian.weight b) by unfold GoldbachGaussian.weight; fun_prop).measurable.comp
    exact Real.measurable_log.comp (measurable_id.div_const x)
  have hBI : Integrable (fun y => (B y)^2) μ := by
    simpa only [B, mul_pow] using
      (integrableOn_density_error (v := (1 - a) * x) hd hax).const_mul (d^2)
  have hPI : Integrable (fun y => (P y)^2) μ := by
    simpa only [P, div_pow, μ, I, IntegrableOn] using (primePowerError_bound ha hd.le hd₁.le hx hv).1
  have hEq : ∀ᵐ y ∂μ, A y = B y + P y := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := I) measurableSet_Icc] with y hy
    exact psiError_eq hd (ha₂.trans hy.1)
  have hAI : Integrable (fun y => (A y)^2) μ := by
    refine ((hBI.const_mul 2).add (hPI.const_mul 2)).mono'
      ((psiError_measurable d).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hEq] with y hy
    rw [Real.norm_of_nonneg (sq_nonneg _), hy]
    change (B y + P y)^2 ≤ 2 * (B y)^2 + 2 * (P y)^2
    nlinarith only [sq_nonneg (B y - P y)]
  have weighted {f : ℝ → ℝ} (hi : Integrable (fun y => (f y)^2) μ) :
      Integrable (fun y => W y * (f y)^2) μ := by
    refine hi.mono' (hWM.aestronglyMeasurable.mul hi.aestronglyMeasurable) ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (mul_nonneg (hW₀ y) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (hW₁ y)
  have hPI' : (∫ y, W y * (P y)^2 ∂μ) ≤ ∫ y, (P y)^2 ∂μ :=
    integral_mono (weighted hPI) hPI (fun y => mul_le_of_le_one_left (sq_nonneg _) (hW₁ y))
  have hpoint : ∀ᵐ y ∂μ, W y * (B y)^2 ≤
      (1 + η) * (W y * (A y)^2) + K * (W y * (P y)^2) := by
    filter_upwards [hEq] with y hy
    have hB : B y = A y - P y := by linarith
    calc
      _ ≤ W y * ((1 + η) * (A y)^2 + K * (P y)^2) := by
        apply mul_le_mul_of_nonneg_left _ (hW₀ y)
        rw [hB]
        exact sq_sub_le hη (A y) (P y)
      _ = _ := by ring
  have hcomp : (∫ y, W y * (B y)^2 ∂μ) ≤
      (1 + η) * (∫ y, W y * (A y)^2 ∂μ) + K * (∫ y, W y * (P y)^2 ∂μ) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((weighted hAI).const_mul (1 + η)) ((weighted hPI).const_mul K)]
    exact integral_mono_ae (weighted hBI)
      (((weighted hAI).const_mul (1 + η)).add ((weighted hPI).const_mul K)) hpoint
  let s := d * (Real.log x)^2
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hPow : (∫ y, (P y)^2 ∂μ) ≤ (ε / 2 / K) * s := by
    have hLI : 0 ≤ ∫ y in I, (primePowerIncrement d y)^2 / y^2 :=
      integral_nonneg (fun _ => by positivity)
    change ‖∫ y in I, (primePowerIncrement d y)^2 / y^2‖ ≤ (ε / 2 / K) * ‖s‖ at hpowx
    rw [Real.norm_of_nonneg hLI, Real.norm_of_nonneg hs] at hpowx
    simpa only [P, div_pow] using hpowx
  have hψx' : (∫ y, W y * (A y)^2 ∂μ) ≤ (1 + η) * s := by
    simpa only [W, A, d, μ, I, s, mul_assoc] using hψx
  have htheta : d^2 * (∫ y in I, W y * (density d y - 1)^2) =
      ∫ y, W y * (B y)^2 ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    dsimp only [B]
    ring
  rw [mul_assoc (1 + ε) (relativeWidth c x)]
  change d^2 * (∫ y in I, W y * (density d y - 1)^2) ≤ (1 + ε) * s
  rw [htheta]
  apply hcomp.trans
  calc
    _ ≤ (1 + η) * ((1 + η) * s) + K * ((ε / 2 / K) * s) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hψx' (by positivity))
        (mul_le_mul_of_nonneg_left (hPI'.trans hPow) hK.le)
    _ = ((1 + η) * (1 + η)) * s + (ε / 2) * s := by
      field_simp [hK.ne']
    _ ≤ _ := by
      have hL := mul_le_mul_of_nonneg_right hscale hs
      linarith

end GoldbachConcrete
