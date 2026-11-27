import Goldbach.Explicit.PrimePowerMass

/-! The effective higher-prime-power variance at the moving endpoint. -/

open MeasureTheory Set
noncomputable section

namespace GoldbachExplicit

open GoldbachArithmetic

private theorem quartic_exp_antitoneOn :
    AntitoneOn (fun L : ℝ => L^4 * Real.exp (-L / 2)) (Ici 28) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact (by fun_prop : Continuous (fun L : ℝ => L^4 * Real.exp (-L / 2))).continuousOn
  · exact (by fun_prop : Differentiable ℝ (fun L : ℝ => L^4 * Real.exp (-L / 2))).differentiableOn
  · intro L hL
    have hL' : 28 ≤ L := interior_subset hL
    have hpos : 0 ≤ L := by linarith
    have hd : HasDerivAt (fun t : ℝ => t^4 * Real.exp (-t / 2))
        (L^3 * Real.exp (-L / 2) * (4 - L / 2)) L := by
      convert (hasDerivAt_pow 4 L).mul (((hasDerivAt_id L).neg.div_const 2).exp) using 1 <;>
        first | rfl | (simp only [Pi.neg_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub]; ring)
    rw [hd.deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

private theorem primePower_allowance_lt {L : ℝ} (hL : 42 ≤ L) :
    4 * L^4 * Real.exp (-L / 2) < 1 / 100 := by
  have he := quartic_exp_antitoneOn (by norm_num : (42 : ℝ) ∈ Ici 28)
    (show 28 ≤ L by linarith) hL
  have hs := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ 4 by norm_num)
  calc
    _ ≤ 4 * (42 : ℝ)^4 * Real.exp (-(42 : ℝ) / 2) := by simpa only [mul_assoc] using hs
    _ < _ := by
      rw [show -(42 : ℝ) / 2 = -21 by norm_num, Real.exp_neg, ← div_eq_mul_inv]
      apply (div_lt_iff₀ (Real.exp_pos _)).2
      have hExp := exp_nat_gt_lower (n := 21) (by decide)
      norm_num at hExp ⊢
      linarith

private theorem explicit_primePower_error_le {L : ℝ} (hL : 28 ≤ L) :
    let x := Real.exp L
    let A := trimmedEndpoint L
    let d := delta L
    IntegrableOn (fun y => (primePowerIncrement d y)^2 / y^2) (Icc A (x - A)) ∧
      (∫ y in Icc A (x - A), (primePowerIncrement d y)^2 / y^2) ≤
        d * (6 * L^3 * Real.exp (-L / 2)) := by
  let x := Real.exp L
  let A := trimmedEndpoint L
  let d := delta L
  let J := Icc A (x - A)
  let D := primePowerIncrement d
  let B := (3 / 4 : ℝ) * L^2
  change IntegrableOn (fun y => (D y)^2 / y^2) J ∧
    (∫ y in J, (D y)^2 / y^2) ≤ d * (6 * L^3 * Real.exp (-L / 2))
  have hL₀ : 0 < L := by linarith
  have hx : 0 < x := Real.exp_pos _
  have hd : 0 < d := delta_pos_of_pos hL₀
  have hL₂ : 2 ≤ L^2 := by nlinarith [sq_nonneg (L - 28)]
  have hA : 0 < A := div_pos hx (sq_pos_of_pos hL₀)
  have hAx : A ≤ x / 2 := div_le_div_of_nonneg_left hx.le (by norm_num) hL₂
  have hJ : A ≤ x - A := by linarith
  have hA₁ : 1 ≤ A := by
    exact (by norm_num : (1 : ℝ) ≤ 2).trans
      (explicit_interval_endpoints_of_ge_28 hL ⟨le_rfl, hJ⟩).1
  have hBx : (1 + d) * (x - A) ≤ x :=
    (explicit_interval_endpoints_of_ge_28 hL ⟨hJ, le_rfl⟩).2
  obtain ⟨hI, hMass⟩ := primePowerIncrement_integral_div_sq_le hd.le hA hBx
  change IntegrableOn (fun y => D y / y^2) J at hI
  have hD : Measurable D := by
    have hψ := Chebyshev.psi_mono.measurable
    have hθ := Chebyshev.theta_mono.measurable
    have harg : Measurable (fun y : ℝ => (1 + d) * y) := by fun_prop
    exact ((hψ.comp harg).sub (hθ.comp harg)).sub (hψ.sub hθ)
  have hDom (y : ℝ) (hy : y ∈ J) : (D y)^2 / y^2 ≤ B * (D y / y^2) := by
    obtain ⟨h₀, h₁⟩ := explicit_primePowerIncrement_le_of_ge_28 hL hy
    have hh := mul_le_mul_of_nonneg_right h₁ h₀
    rw [← mul_div_assoc, pow_two]
    exact div_le_div_of_nonneg_right hh (sq_nonneg _)
  have hae := (ae_restrict_mem (μ := volume) (s := J) measurableSet_Icc).mono hDom
  have hIi : IntegrableOn (fun y => (D y)^2 / y^2) J := by
    refine (hI.const_mul B).mono' ((hD.pow_const 2).div (measurable_id.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [hae] with y hy
    rwa [Real.norm_of_nonneg (by positivity)]
  refine ⟨hIi, ?_⟩
  have hU := integral_mono_ae hIi (hI.const_mul B) hae
  rw [integral_const_mul] at hU
  have hAmin : 16 ≤ Real.log A := by
    change 16 ≤ Real.log (Real.exp L / L^2)
    rw [Real.log_div hx.ne' (sq_pos_of_pos hL₀).ne', Real.log_exp, Real.log_pow]
    norm_num
    linarith [log_le_sixth_of_ge_28 hL]
  have hS := reciprocal_higherPrimePowerWeight_le_of_log_ge_16 hA₁
    (show A ≤ x by linarith) hAmin
  have hsqrt : Real.sqrt A = Real.exp (L / 2) / L := by
    change Real.sqrt (Real.exp L / L^2) = _
    rw [Real.sqrt_div hx.le, Real.sqrt_sq hL₀.le]
    have he : Real.exp (L / 2)^2 = Real.exp L := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    change Real.sqrt (Real.exp L) / L = _
    rw [← he, Real.sqrt_sq (Real.exp_pos _).le]
  calc
    _ ≤ B * (∫ y in J, D y / y^2) := hU
    _ ≤ B * (d * (8 / Real.sqrt A)) :=
      mul_le_mul_of_nonneg_left (hMass.trans (mul_le_mul_of_nonneg_left hS hd.le))
        (by unfold B; positivity)
    _ = d * (6 * L^3 * Real.exp (-L / 2)) := by
      rw [hsqrt, show -L / 2 = -(L / 2) by ring, Real.exp_neg]
      unfold B
      field_simp [hL₀.ne', (Real.exp_pos (L / 2)).ne'] <;> ring

/-- The original reciprocal-square error allowance. -/
theorem explicit_primePower_error_lt {L : ℝ} (hL : 42 ≤ L) :
    let x := Real.exp L
    let A := trimmedEndpoint L
    let d := delta L
    IntegrableOn (fun y => (primePowerIncrement d y)^2 / y^2) (Icc A (x - A)) ∧
      (∫ y in Icc A (x - A), (primePowerIncrement d y)^2 / y^2) < d / 100 := by
  obtain ⟨hi, h⟩ := explicit_primePower_error_le (by linarith : 28 ≤ L)
  have hwide : 6 * L^3 * Real.exp (-L / 2) ≤ 4 * L^4 * Real.exp (-L / 2) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hn : 0 ≤ (4 * L - 6) * L^3 :=
      mul_nonneg (by linarith) (pow_nonneg (by linarith) _)
    nlinarith only [hn]
  have hbound := mul_lt_mul_of_pos_left (hwide.trans_lt (primePower_allowance_lt hL)) (delta_pos hL)
  refine ⟨hi, h.trans_lt ?_⟩
  simpa only [mul_one_div] using hbound

/-- The reciprocal-square error allowance at the earlier cutoff. -/
theorem explicit_primePower_error_lt_of_ge_28 {L : ℝ} (hL : 28 ≤ L) :
    let x := Real.exp L
    let A := trimmedEndpoint L
    let d := delta L
    IntegrableOn (fun y => (primePowerIncrement d y)^2 / y^2) (Icc A (x - A)) ∧
      (∫ y in Icc A (x - A), (primePowerIncrement d y)^2 / y^2) < d * (11 / 100) := by
  obtain ⟨hi, h⟩ := explicit_primePower_error_le hL
  have hmono := quartic_exp_antitoneOn (by simp : (28 : ℝ) ∈ Ici 28)
    (show L ∈ Ici (28 : ℝ) from hL) hL
  have hbase : 6 * (28 : ℝ)^3 * Real.exp (-28 / 2) < 11 / 100 := by
    rw [show (-28 : ℝ) / 2 = -14 by norm_num, Real.exp_neg, ← div_eq_mul_inv]
    have he := exp_nat_gt_lower (n := 14) (by decide)
    apply (div_lt_iff₀ (Real.exp_pos _)).2
    norm_num at he ⊢
    linarith
  have hL₀ : 0 < L := by linarith
  have hfactor (t : ℝ) (ht : 0 < t) :
      6 * t^3 * Real.exp (-t / 2) = (6 / t) * (t^4 * Real.exp (-t / 2)) := by
    field_simp [ht.ne'] <;> ring
  have hcomparison : 6 * L^3 * Real.exp (-L / 2) ≤ 6 * (28 : ℝ)^3 * Real.exp (-28 / 2) := by
    rw [hfactor L hL₀, hfactor 28 (by norm_num)]
    exact mul_le_mul (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL)
      hmono (by positivity) (by norm_num)
  have hb := hcomparison.trans_lt hbase
  exact ⟨hi, h.trans_lt (mul_lt_mul_of_pos_left hb (delta_pos_of_pos (by linarith)))⟩

end GoldbachExplicit
