import Mathlib
import Zeta23.ExplicitFormula.Bridge

open Filter MeasureTheory Set
open scoped Topology ContDiff
noncomputable section

namespace GoldbachZeros

open Zeta23

private def planeWave (r : ℝ) (u : ℝ) : ℂ := Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))

private theorem planeWave_norm (r u : ℝ) : ‖planeWave r u‖ = 1 := by
  unfold planeWave
  rw [norm_cexp_I_mul]
  simp

private theorem integrable_mul_planeWave {k : ℝ → ℂ} (hk : Integrable k) (r : ℝ) :
    Integrable (fun u => k u * planeWave r u) := by
  have hw : Continuous (planeWave r) := by unfold planeWave; fun_prop
  exact hk.mul_bdd hw.aestronglyMeasurable (Eventually.of_forall fun u => (planeWave_norm r u).le)

private theorem paperFT_real_deriv {k : ℝ → ℂ} (hk : Differentiable ℝ k)
    (hki : Integrable k) (hdi : Integrable (deriv k)) (r : ℝ) :
    paperFT (deriv k) (r : ℂ) = -(Complex.I * (r : ℂ)) * paperFT k (r : ℂ) := by
  let c : ℂ := Complex.I * (r : ℂ)
  have hv (u : ℝ) : HasDerivAt (planeWave r) (c * planeWave r u) u := by
    unfold planeWave
    simpa [c, mul_comm] using (((hasDerivAt_id u).ofReal_comp).const_mul c).cexp
  have hki' := integrable_mul_planeWave hki r
  have hm : Integrable (fun u => k u * (c * planeWave r u)) := by
    refine (hki'.const_mul c).congr (Eventually.of_forall fun u => ?_)
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := k) (u' := deriv k) (v := planeWave r) (v' := fun u => c * planeWave r u)
    (fun u _ => (hk u).hasDerivAt) (fun u _ => hv u) hm (integrable_mul_planeWave hdi r) hki'
  have hs :
      (∫ u, k u * (c * planeWave r u)) = c * paperFT k (r : ℂ) := by
    change (∫ u, k u * (c * planeWave r u)) = c * (∫ u, k u * planeWave r u)
    rw [← Zeta23.integral_const_mul_C c (fun u => k u * planeWave r u)]
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  rw [hs] at h
  change c * paperFT k (r : ℂ) = -paperFT (deriv k) (r : ℂ) at h
  simpa only [neg_neg, neg_mul, c] using (congrArg Neg.neg h).symm

private theorem paperFT_real_norm_le {k : ℝ → ℂ} (hki : Integrable k) (r : ℝ) :
    ‖paperFT k (r : ℂ)‖ ≤ ∫ u, ‖k u‖ := by
  change ‖∫ u, k u * planeWave r u‖ ≤ _
  exact norm_integral_le_of_norm_le hki.norm (Eventually.of_forall fun u => by
    rw [norm_mul, planeWave_norm, mul_one])

/-- Real-frequency Fourier decay from two integrable derivatives. -/
theorem paperFT_real_norm_le_quadratic {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hki : Integrable k) (hdi : Integrable (deriv k)) (hddi : Integrable (deriv (deriv k)))
    (r : ℝ) :
    ‖paperFT k (r : ℂ)‖ ≤ ((∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖) / (1 + r^2) := by
  have hd : ContDiff ℝ 1 (deriv k) := hk.deriv'
  have h := paperFT_real_deriv (hd.differentiable (by norm_num)) hdi hddi r
  rw [paperFT_real_deriv (hk.differentiable (by norm_num)) hki hdi r] at h
  have hn := paperFT_real_norm_le (k := deriv (deriv k)) hddi r
  rw [h] at hn
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at hn
  rw [← mul_assoc, ← pow_two, sq_abs] at hn
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = ‖paperFT k (r : ℂ)‖ + r^2 * ‖paperFT k (r : ℂ)‖ := by ring
    _ ≤ _ := add_le_add (paperFT_real_norm_le hki r) hn

private def cutoffBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, by norm_num⟩

private def cutoffBase (x : ℝ) : ℂ := (cutoffBump x : ℂ)

private theorem cutoffBase_smooth (n : ℕ) : ContDiff ℝ n cutoffBase :=
  Complex.ofRealCLM.contDiff.comp cutoffBump.contDiff

private theorem cutoffBase_compact : HasCompactSupport cutoffBase := by
  have he : Function.support cutoffBase = Function.support cutoffBump := by
    ext x
    simp [cutoffBase, Function.mem_support]
  unfold HasCompactSupport tsupport
  rw [he]
  exact cutoffBump.hasCompactSupport

private theorem cutoffBase_one {x : ℝ} (hx : |x| ≤ 1) : cutoffBase x = 1 := by
  have h : x ∈ Metric.closedBall (0 : ℝ) cutoffBump.rIn := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, cutoffBump] using hx
  simp [cutoffBase, cutoffBump.one_of_mem_closedBall h]

private def cutoffError (a : ℝ) (x : ℝ) : ℂ := cutoffBase (a * x) - 1

private theorem cutoffError_smooth (n : ℕ) (a : ℝ) : ContDiff ℝ n (cutoffError a) :=
  ((cutoffBase_smooth n).comp (contDiff_const.mul contDiff_id)).sub contDiff_const

private theorem cutoffError_small (a x : ℝ) : ‖cutoffError a x‖ ≤ 1 := by
  unfold cutoffError cutoffBase
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr cutoffBump.le_one)]
  linarith [cutoffBump.nonneg' (a * x)]

private theorem bounded_of_compact_support {f : ℝ → ℂ} (hc : Continuous f)
    (hs : HasCompactSupport f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖f x‖ ≤ C := by
  obtain ⟨B, hB⟩ := hs.isCompact.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max 0 B, le_max_left _ _, fun x => ?_⟩
  by_cases hx : f x = 0
  · simp [hx]
  · exact (hB x (subset_tsupport _ hx)).trans (le_max_right _ _)

private theorem cutoffError_deriv_bounds :
    ∃ B₁ B₂ : ℝ, 0 ≤ B₁ ∧ 0 ≤ B₂ ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ x : ℝ,
      ‖deriv (cutoffError a) x‖ ≤ B₁ ∧ ‖deriv (deriv (cutoffError a)) x‖ ≤ B₂ := by
  have hc₁ : ContDiff ℝ 1 (deriv cutoffBase) := (cutoffBase_smooth 2).deriv'
  obtain ⟨B₁, hB₁, h₁⟩ := bounded_of_compact_support hc₁.continuous cutoffBase_compact.deriv
  obtain ⟨B₂, hB₂, h₂⟩ := bounded_of_compact_support (hc₁.continuous_deriv le_rfl)
    cutoffBase_compact.deriv.deriv
  refine ⟨B₁, B₂, hB₁, hB₂, fun a ha ha₁ x => ?_⟩
  have hD {n : ℕ} (hn : 0 < n) :
      iteratedDeriv n (cutoffError a) = fun x => a^n • iteratedDeriv n cutoffBase (a*x) := by
    have hh : deriv (cutoffError a) = deriv (fun x => cutoffBase (a * x)) := by
      ext x
      exact deriv_sub_const 1
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    calc
      _ = iteratedDeriv (j+1) (fun x => cutoffBase (a*x)) := by
        simp only [iteratedDeriv_succ', hh]
      _ = _ := iteratedDeriv_comp_const_smul (cutoffBase_smooth (j+1)) a
  have he₁ (x : ℝ) := congrFun (hD (n := 1) (by norm_num)) x
  have he₂ (x : ℝ) := congrFun (hD (n := 2) (by norm_num)) x
  simp only [iteratedDeriv_one, pow_one] at he₁
  simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_zero] at he₂
  constructor
  · rw [he₁, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left (h₁ _) ha).trans (mul_le_of_le_one_left hB₁ ha₁)
  · rw [he₂, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
    exact (mul_le_mul_of_nonneg_left (h₂ _) (sq_nonneg a)).trans
      (mul_le_of_le_one_left hB₂ (pow_le_one₀ ha ha₁))

private def scale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

private theorem scale_pos (n : ℕ) : 0 < scale n := by unfold scale; positivity

private theorem scale_le_one (n : ℕ) : scale n ≤ 1 := by
  unfold scale
  rw [inv_eq_one_div, div_le_one (by positivity)]
  exact le_add_of_nonneg_left (Nat.cast_nonneg n)

private theorem scale_tendsto : Tendsto scale atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, one_div] using
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)

private theorem eventually_cutoffError_zero (k : ℝ → ℂ) (x : ℝ) (j : ℕ) :
    ∀ᶠ n : ℕ in atTop, iteratedDeriv j (fun y => cutoffError (scale n) y * k y) x = 0 := by
  have hx : Tendsto (fun n : ℕ => |scale n * x|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, zero_mul, abs_zero] using (scale_tendsto.mul_const x).norm
  filter_upwards [hx.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
  have hc : Continuous (fun y : ℝ => |scale n * y|) := (continuous_const.mul continuous_id).abs
  have hloc : (fun y => cutoffError (scale n) y * k y) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [hc.continuousAt.tendsto.eventually (gt_mem_nhds hn)] with y hy
    simp [cutoffError, cutoffBase_one (le_of_lt hy)]
  rw [hloc.iteratedDeriv_eq j]
  simp

private theorem second_derivative_mul {f k : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hk : ContDiff ℝ 2 k) (x : ℝ) :
    deriv (deriv (fun y => f y * k y)) x =
      f x * deriv (deriv k) x + 2 * deriv f x * deriv k x + deriv (deriv f) x * k x := by
  have h := iteratedDeriv_fun_mul (hf.contDiffAt (x := x)) (hk.contDiffAt (x := x))
  norm_num [Finset.sum_range_succ, iteratedDeriv_succ, iteratedDeriv_one] at h
  linear_combination h

private theorem integral_error_tendsto_zero {F : ℕ → ℝ → ℂ} {majorant : ℝ → ℝ}
    (hm : Integrable majorant) (hc : ∀ n, Continuous (F n))
    (hb : ∀ n x, ‖F n x‖ ≤ majorant x) (hz : ∀ x, ∀ᶠ n in atTop, F n x = 0) :
    Tendsto (fun n : ℕ => ∫ u : ℝ, ‖F n u‖) atTop (𝓝 0) := by
  simpa using tendsto_integral_filter_of_dominated_convergence (f := fun _ : ℝ => (0 : ℝ))
    majorant (Eventually.of_forall fun n => (hc n).norm.aestronglyMeasurable)
    (Eventually.of_forall fun n => Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact hb n x)
    hm (Eventually.of_forall fun x => tendsto_const_nhds.congr'
      ((hz x).mono fun _ h => by simp [h]))

private theorem paperFT_sub_real {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
    paperFT (fun x => f x - g x) (r : ℂ) =
      paperFT f (r : ℂ) - paperFT g (r : ℂ) := by
  change (∫ u, (f u - g u) * planeWave r u) = _
  simp_rw [sub_mul]
  exact integral_sub (integrable_mul_planeWave hf r) (integrable_mul_planeWave hg r)

/-- Smooth compact cutoffs approximate the real Fourier transform in the
reciprocal-quadratic weighted sup norm. The value at the origin is preserved. -/
theorem exists_compact_paperFT_approx {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hki : Integrable k) (hdi : Integrable (deriv k)) (hddi : Integrable (deriv (deriv k)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ g 0 = k 0 ∧
      ∀ r : ℝ, ‖paperFT g (r : ℂ) - paperFT k (r : ℂ)‖ ≤ ε / (1 + r^2) := by
  obtain ⟨B₁, B₂, hB₁, hB₂, hcut⟩ := cutoffError_deriv_bounds
  let E (n : ℕ) (x : ℝ) := cutoffError (scale n) x * k x
  have hE (n : ℕ) : ContDiff ℝ 2 (E n) := (cutoffError_smooth 2 _).mul hk
  have hE0 (n : ℕ) (x : ℝ) : ‖E n x‖ ≤ ‖k x‖ := by
    dsimp only [E]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (cutoffError_small _ _)
  have hE1 (n : ℕ) (x : ℝ) :
      ‖deriv (E n) x‖ ≤ B₁ * ‖k x‖ + ‖deriv k x‖ := by
    have hh := hcut (scale n) (scale_pos n).le (scale_le_one n) x
    have hc₀ := (cutoffError_smooth 2 (scale n)).differentiable (by norm_num) x
    dsimp only [E]
    rw [deriv_fun_mul hc₀ (hk.differentiable (by norm_num) x)]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right hh.1 (norm_nonneg _))
      (mul_le_of_le_one_left (norm_nonneg _) (cutoffError_small _ _))
  have hE2 (n : ℕ) (x : ℝ) :
      ‖deriv (deriv (E n)) x‖ ≤
        ‖deriv (deriv k) x‖ + (2 * B₁) * ‖deriv k x‖ + B₂ * ‖k x‖ := by
    have hh := hcut (scale n) (scale_pos n).le (scale_le_one n) x
    dsimp only [E]
    rw [second_derivative_mul (cutoffError_smooth 2 _) hk]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_)
    · simp only [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
      exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) (cutoffError_small _ _))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh.1 (by norm_num)) (norm_nonneg _))
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hh.2 (norm_nonneg _)
  have hc₂ (n : ℕ) : Continuous (deriv (deriv (E n))) :=
    ((hE n).deriv' : ContDiff ℝ 1 (deriv (E n))).continuous_deriv le_rfl
  have hm₁ := (hki.norm.const_mul B₁).add hdi.norm
  have hm₂ := (hddi.norm.add (hdi.norm.const_mul (2 * B₁))).add (hki.norm.const_mul B₂)
  have ht₀ := integral_error_tendsto_zero hki.norm (fun n => (hE n).continuous) hE0
    (fun x => by simpa only [iteratedDeriv_zero] using eventually_cutoffError_zero k x 0)
  have ht₂ := integral_error_tendsto_zero hm₂ hc₂ hE2
    (fun x => by
      simpa only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_zero, E] using
        eventually_cutoffError_zero k x 2)
  have ht := ht₀.add ht₂
  rw [zero_add] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  let g : ℝ → ℂ := fun x => cutoffBase (scale n * x) * k x
  have hgc : ContDiff ℝ 2 g := ((cutoffBase_smooth 2).comp (contDiff_const.mul contDiff_id)).mul hk
  obtain ⟨Λ, hΛ⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport cutoffBase_compact
  have hgS : HasCompactSupport g := by
    apply Zeta23.hasCompactSupport_of_support_subset_abs (Λ := Λ / scale n)
    intro x hx
    have hb : cutoffBase (scale n * x) ≠ 0 := fun h => hx (by simp [g, h])
    have h := hΛ _ hb
    rw [abs_mul, abs_of_pos (scale_pos n)] at h
    exact (le_div_iff₀ (scale_pos n)).mpr (by linarith)
  have hgI := hgc.continuous.integrable_of_hasCompactSupport (μ := volume) hgS
  refine ⟨g, hgc, hgS, by simp [g, cutoffBase_one (by norm_num : |(0 : ℝ)| ≤ 1)], fun r => ?_⟩
  have heq : (fun x => g x - k x) = E n := by
    funext x
    unfold g E cutoffError
    ring
  have ei := hki.norm.mono' (hE n).continuous.aestronglyMeasurable (Eventually.of_forall (hE0 n))
  have ed := hm₁.mono' ((hE n).continuous_deriv (by norm_num)).aestronglyMeasurable
    (Eventually.of_forall (hE1 n))
  have edd := hm₂.mono' (hc₂ n).aestronglyMeasurable (Eventually.of_forall (hE2 n))
  rw [← paperFT_sub_real hgI hki, heq]
  exact (paperFT_real_norm_le_quadratic (hE n) ei ed edd r).trans
    (div_le_div_of_nonneg_right hn.le (by positivity))

end GoldbachZeros
