import Goldbach.Explicit.LowerVariance
import Goldbach.ArithmeticError

/-! The effective trivial-zero correction on the full moving interval. -/

open MeasureTheory Set
noncomputable section

namespace GoldbachExplicit

open GoldbachArithmetic

/-- The squared normalized trivial-zero correction is strictly below one
millionth of the relative width on the explicit interval. -/
theorem explicit_trivialZero_error_lt_of_ge_28 {L : ℝ} (hL : 28 ≤ L) :
    let x := Real.exp L
    let A := trimmedEndpoint L
    let d := delta L
    let W := upperWeight (bandwidth L) x
    let r (y : ℝ) := trivialZeroTerm ((1 + d) * y) - trivialZeroTerm y
    IntegrableOn (fun y => W y * r y^2 / y^2) (Icc A (x - A)) ∧
      (∫ y in Icc A (x - A), W y * r y^2 / y^2) < d / 10^6 := by
  dsimp only
  let x := Real.exp L
  let A := trimmedEndpoint L
  let d := delta L
  let W := upperWeight (bandwidth L) x
  let r (y : ℝ) := trivialZeroTerm ((1 + d) * y) - trivialZeroTerm y
  let J := Icc A (x - A)
  let C := 4 * d^2 / A^6
  let f (y : ℝ) := W y * r y^2 / y^2
  change IntegrableOn f J ∧ (∫ y in J, f y) < d / 10^6
  have hx : 0 < x := Real.exp_pos _
  have hL₀ : 0 < L := by linarith
  have hL₂ : 0 < L^2 := sq_pos_of_pos hL₀
  have hd : 0 < d := delta_pos_of_pos hL₀
  have hV := bandwidth_pos_of_pos hL₀
  have hA : 0 < A := div_pos hx hL₂
  have hC : 0 ≤ C := by unfold C; positivity
  have hL₂big : 720 ≤ L^2 := by nlinarith [sq_nonneg (L - 28)]
  have hp := Real.pow_div_factorial_le_exp L hL₀.le 6
  norm_num [Nat.factorial] at hp
  have hpow : L^4 ≤ x := by
    apply le_trans ?_ hp
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 720)).mpr
    have h := mul_le_mul_of_nonneg_right hL₂big (pow_nonneg hL₀.le 4)
    nlinarith only [h]
  have hsmall : L^2 ≤ A := by
    change L^2 ≤ x / L^2
    apply (le_div_iff₀ hL₂).mpr
    rw [← pow_add]
    exact hpow
  have hA₂ : 2 ≤ A := (by linarith : 2 ≤ L^2).trans hsmall
  have hAB : A ≤ x - A := by
    have he : A ≤ x / 2 := div_le_div_of_nonneg_left hx.le (by norm_num) (by linarith)
    linarith
  have hW : Measurable W :=
    (continuous_cosineWeight hV).measurable.comp ((measurable_const.div measurable_id).log)
  have hr : Measurable r := by
    unfold r trivialZeroTerm
    fun_prop
  have hf : Measurable f := (hW.mul (hr.pow_const 2)).div (measurable_id.pow_const 2)
  have hnon (y : ℝ) : 0 ≤ f y :=
    div_nonneg (mul_nonneg (cosineWeight_nonneg hV _) (sq_nonneg _)) (sq_nonneg _)
  have hpoint (y : ℝ) (hy : y ∈ J) : f y ≤ C := by
    have hR := trivialZeroTerm_sub_le hd.le (hA₂.trans hy.1)
    change |r y| ≤ 2 * d / y^2 at hR
    have hysq := pow_le_pow_left₀ hA.le hy.1 2
    have hRC : |r y| ≤ 2 * d / A^2 :=
      hR.trans (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hA) hysq)
    have hSq := pow_le_pow_left₀ (abs_nonneg _) hRC 2
    rw [sq_abs] at hSq
    have hWle : W y ≤ 1 := cosineWeight_le_one hV _
    have hmul := (mul_le_of_le_one_left (sq_nonneg (r y)) hWle).trans hSq
    calc
      f y ≤ (2 * d / A^2)^2 / A^2 :=
        div_le_div₀ (by positivity) hmul (sq_pos_of_pos hA) hysq
      _ = C := by dsimp [C]; field_simp [hA.ne']; ring
  have hcI : IntegrableOn (fun _ : ℝ => C) J := integrableOn_const measure_Icc_lt_top.ne
  have hae := (ae_restrict_mem (μ := volume) (s := J) measurableSet_Icc).mono hpoint
  have hfI : IntegrableOn f J := by
    refine hcI.mono' hf.aestronglyMeasurable ?_
    filter_upwards [hae] with y hy
    rw [Real.norm_of_nonneg (hnon y)]
    exact hy
  refine ⟨hfI, ?_⟩
  have hi : (∫ y in J, f y) ≤ ∫ _y in J, C := integral_mono_ae hfI hcI hae
  rw [setIntegral_const, smul_eq_mul] at hi
  change _ ≤ volume.real (Icc A (x - A)) * C at hi
  rw [Real.volume_real_Icc_of_le hAB] at hi
  have hi' : (∫ y in J, f y) ≤ x * C :=
    hi.trans (mul_le_mul_of_nonneg_right (by linarith) hC)
  have hdx : d * x = L^2 := by
    simp [d, delta, x, Real.exp_neg, (Real.exp_pos L).ne']
  have hnormalize : x * C = d * (4 * L^2 / A^6) := by
    unfold C
    rw [← hdx]
    ring
  have hden : L^12 ≤ A^6 := by
    have h := pow_le_pow_left₀ hL₂.le hsmall 6
    rwa [← pow_mul] at h
  have hratio : 4 * L^2 / A^6 < 1 / 10^6 := by
    calc
      _ ≤ 4 * L^2 / L^12 := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 4 / L^10 := by field_simp [hL₀.ne']
      _ ≤ 4 / 28^10 := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 28) hL 10)
      _ < _ := by norm_num
  rw [hnormalize] at hi'
  exact hi'.trans_lt (by simpa only [mul_one_div] using mul_lt_mul_of_pos_left hratio hd)

theorem explicit_trivialZero_error_lt {L : ℝ} (hL : 42 ≤ L) :
    let x := Real.exp L
    let A := trimmedEndpoint L
    let d := delta L
    let W := upperWeight (bandwidth L) x
    let f (y : ℝ) := W y * (trivialZeroTerm ((1 + d) * y) - trivialZeroTerm y)^2 / y^2
    IntegrableOn f (Icc A (x - A)) ∧ (∫ y in Icc A (x - A), f y) < d / 10^6 :=
  explicit_trivialZero_error_lt_of_ge_28 (by linarith)

end GoldbachExplicit
