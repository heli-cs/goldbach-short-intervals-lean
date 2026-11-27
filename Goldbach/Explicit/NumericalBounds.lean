import Mathlib

/-! Rational enclosures and parameter bounds for the explicit Goldbach range. -/

open Filter Set
open scoped Topology

noncomputable section

namespace GoldbachExplicit

def margin (L : ℝ) : ℝ :=
  4 * L * Real.log L - 4 * (Real.log L)^2 - 10 * L - 7

private theorem log_twenty_one_sixteen_lower :
    (2719 / 10000 : ℝ) < Real.log (21 / 16) := by
  have h := Real.sum_range_le_log_div (x := (5 / 37 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem log_twenty_one_sixteen_upper :
    Real.log (21 / 16) < (272 / 1000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (5 / 37 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_forty_two_bounds :
    (37375 / 10000 : ℝ) < Real.log 42 ∧ Real.log 42 < 4 := by
  have h42 : Real.log 42 = 5 * Real.log 2 + Real.log (21 / 16) := by
    have hp : Real.log ((2 : ℝ)^5) = (5 : ℝ) * Real.log 2 := by simpa using Real.log_pow (2 : ℝ) 5
    rw [← hp, ← Real.log_mul (by norm_num : (2 : ℝ)^5 ≠ 0) (by norm_num : (21 / 16 : ℝ) ≠ 0)]
    norm_num
  rw [h42]
  constructor
  · linarith [Real.log_two_gt_d9, log_twenty_one_sixteen_lower]
  · linarith [Real.log_two_lt_d9, log_twenty_one_sixteen_upper]

theorem margin_at_forty_two : 145 < margin 42 := by
  obtain ⟨hl, hu⟩ := log_forty_two_bounds
  have h := mul_pos (sub_pos.mpr hl)
    (show 0 < 168 - 4 * (Real.log 42 + 37375 / 10000) by linarith)
  unfold margin
  nlinarith only [h]

private theorem margin_hasDerivAt {L : ℝ} (hL : 0 < L) :
    HasDerivAt margin (4 * (1 - 2 / L) * Real.log L - 6) L := by
  have hlog := Real.hasDerivAt_log hL.ne'
  have h := (((((hasDerivAt_id L).const_mul (4 : ℝ)).mul hlog).sub
    ((hlog.pow 2).const_mul (4 : ℝ))).sub
      ((hasDerivAt_id L).const_mul (10 : ℝ))).sub_const (7 : ℝ)
  convert h using 1 <;> first | rfl | (simp only [id_eq]; field_simp [hL.ne'] <;> ring)

theorem margin_strictMonoOn : StrictMonoOn margin (Ici 42) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · exact fun L hL => (margin_hasDerivAt (by linarith [hL.out])).continuousAt.continuousWithinAt
  · intro L hL
    have hL' : 42 ≤ L := interior_subset hL
    have hp : 0 < L := by linarith
    rw [(margin_hasDerivAt hp).deriv]
    have hlog : 3 < Real.log L :=
      (by linarith [log_forty_two_bounds.1] : 3 < Real.log 42).trans_le (Real.log_le_log (by norm_num) hL')
    have hfrac : (2 : ℝ) / L ≤ 1 / 2 := (div_le_iff₀ hp).2 (by linarith)
    nlinarith only [hlog, hfrac, mul_nonneg
      (show 0 ≤ 1 / 2 - 2 / L by linarith) (show 0 ≤ Real.log L by linarith)]

theorem margin_gt_145 {L : ℝ} (hL : 42 ≤ L) : 145 < margin L :=
  margin_at_forty_two.trans_le (margin_strictMonoOn.monotoneOn (by simp) hL hL)

theorem upper_expression_lt_lower_expression {L : ℝ} (hL : 42 ≤ L) :
    (L - 2 * Real.log L)^2 + 3 * L + 7 < L^2 - 7 * L := by
  have h := margin_gt_145 hL
  unfold margin at h
  nlinarith only [h]

/-- The coefficient in the integrated quadratic loss for the cosine kernel. -/
theorem cosine_loss_constant_lt :
    Real.pi^2 / 6 * ((Real.log 2)^2 + 2 * Real.log 2 + 2) < 6361 / 1000 := by
  have hπ : Real.pi ≤ (3.141593 : ℝ) := Real.pi_lt_d6.le
  have hl : Real.log 2 ≤ (693147181 / 1000000000 : ℝ) := by
    linarith [Real.log_two_lt_d9]
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    _ ≤ (3.141593 : ℝ)^2 / 6 *
        ((693147181 / 1000000000 : ℝ)^2 + 2 * (693147181 / 1000000000 : ℝ) + 2) := by
      gcongr
    _ < _ := by norm_num

private theorem square_mul_exp_antitoneOn {a k : ℝ} (hk : 0 < k) (hbase : 2 ≤ k * a)
    (ha : 0 ≤ a) :
    AntitoneOn (fun L : ℝ => L^2 * Real.exp (-k * L)) (Ici a) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact (by fun_prop : Continuous (fun L : ℝ => L^2 * Real.exp (-k * L))).continuousOn
  · exact (by fun_prop : Differentiable ℝ (fun L : ℝ => L^2 * Real.exp (-k * L))).differentiableOn
  · intro L hL
    have hL' : a ≤ L := interior_subset hL
    have hderiv : HasDerivAt (fun L : ℝ => L^2 * Real.exp (-k * L))
        (L * Real.exp (-k * L) * (2 - k * L)) L := by
      convert (hasDerivAt_pow 2 L).mul (((hasDerivAt_id L).const_mul (-k)).exp) using 1
        <;> first | rfl | (simp only [id_eq]; ring)
    rw [hderiv.deriv]
    apply mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (ha.trans hL') (Real.exp_pos _).le)
    exact sub_nonpos.mpr (hbase.trans (mul_le_mul_of_nonneg_left hL' hk.le))

def delta (L : ℝ) : ℝ := L^2 * Real.exp (-L)

def logWidth (L : ℝ) : ℝ := Real.log (1 + delta L)

def bandwidth (L : ℝ) : ℝ := Real.sqrt (3 * L)

def trim (L : ℝ) : ℝ := (L^2)⁻¹

theorem bandwidth_pos_of_pos {L : ℝ} (hL : 0 < L) : 0 < bandwidth L := by
  unfold bandwidth
  positivity

theorem bandwidth_pos {L : ℝ} (hL : 42 ≤ L) : 0 < bandwidth L :=
  bandwidth_pos_of_pos (by linarith)

theorem bandwidth_le_third_of_ge_twenty_seven {L : ℝ} (hL : 27 ≤ L) : bandwidth L ≤ L / 3 := by
  have h := mul_nonneg (show 0 ≤ L by linarith) (show 0 ≤ L - 27 by linarith)
  exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith only [h]⟩

theorem bandwidth_le_third {L : ℝ} (hL : 42 ≤ L) : bandwidth L ≤ L / 3 :=
  bandwidth_le_third_of_ge_twenty_seven (by linarith)

theorem delta_pos_of_pos {L : ℝ} (hL : 0 < L) : 0 < delta L := by
  unfold delta
  exact mul_pos (sq_pos_of_pos hL) (Real.exp_pos _)

theorem delta_pos {L : ℝ} (hL : 42 ≤ L) : 0 < delta L :=
  delta_pos_of_pos (by linarith)

theorem logWidth_pos_of_pos {L : ℝ} (hL : 0 < L) : 0 < logWidth L :=
  Real.log_pos (by linarith [delta_pos_of_pos hL])

theorem logWidth_pos {L : ℝ} (hL : 42 ≤ L) : 0 < logWidth L :=
  logWidth_pos_of_pos (by linarith)

theorem logWidth_le_delta_of_pos {L : ℝ} (hL : 0 < L) : logWidth L ≤ delta L := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + delta L by linarith [delta_pos_of_pos hL])
  simpa [logWidth] using h

theorem logWidth_le_delta {L : ℝ} (hL : 42 ≤ L) : logWidth L ≤ delta L :=
  logWidth_le_delta_of_pos (by linarith)

private theorem square_mul_exp_at_forty_two (k : ℝ) (n : ℕ) (hn : k * 42 = n) (hn' : 0 < n) :
    (42 : ℝ)^2 * Real.exp (-k * 42) < 1764 / ((27 / 10 : ℝ)^n) := by
  have he : (27 / 10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  rw [neg_mul, hn, Real.exp_neg, show (n : ℝ) = (n : ℝ) * 1 by ring, Real.exp_nat_mul]
  rw [show (42 : ℝ)^2 = 1764 by norm_num, div_eq_mul_inv]
  exact mul_lt_mul_of_pos_left (inv_strictAnti₀ (by positivity)
    (pow_lt_pow_left₀ he (by norm_num) (Nat.ne_of_gt hn'))) (by norm_num)

theorem delta_lt {L : ℝ} (hL : 42 ≤ L) : delta L < (2 / 10^15 : ℝ) := by
  calc
    _ ≤ delta 42 := by
      simpa [delta] using square_mul_exp_antitoneOn (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by simp)
        (show L ∈ Ici (42 : ℝ) from hL) hL
    _ < 1764 / ((27 / 10 : ℝ)^42) := by
      simpa [delta] using square_mul_exp_at_forty_two 1 42 (by norm_num) (by norm_num)
    _ < _ := by norm_num

theorem delta_exp_bandwidth_lt {L : ℝ} (hL : 42 ≤ L) :
    delta L * Real.exp (bandwidth L) < (1 / 10^8 : ℝ) := by
  calc
    _ = L^2 * Real.exp (-L + bandwidth L) := by simp [delta, Real.exp_add, mul_assoc]
    _ ≤ L^2 * Real.exp (-(2 / 3 : ℝ) * L) := by
      gcongr
      linarith [bandwidth_le_third hL]
    _ ≤ (42 : ℝ)^2 * Real.exp (-(2 / 3 : ℝ) * 42) :=
      square_mul_exp_antitoneOn (by norm_num) (by norm_num) (by norm_num) (by simp)
        (show L ∈ Ici (42 : ℝ) from hL) hL
    _ < 1764 / ((27 / 10 : ℝ)^28) := square_mul_exp_at_forty_two (2 / 3) 28 (by norm_num) (by norm_num)
    _ < _ := by norm_num

theorem delta_exp_half_bandwidth_lt {L : ℝ} (hL : 42 ≤ L) :
    delta L * Real.exp (bandwidth L / 2) < (1 / 10^11 : ℝ) := by
  calc
    _ = L^2 * Real.exp (-L + bandwidth L / 2) := by simp [delta, Real.exp_add, mul_assoc]
    _ ≤ L^2 * Real.exp (-(5 / 6 : ℝ) * L) := by
      gcongr
      linarith [bandwidth_le_third hL]
    _ ≤ (42 : ℝ)^2 * Real.exp (-(5 / 6 : ℝ) * 42) :=
      square_mul_exp_antitoneOn (by norm_num) (by norm_num) (by norm_num) (by simp)
        (show L ∈ Ici (42 : ℝ) from hL) hL
    _ < 1764 / ((27 / 10 : ℝ)^35) := square_mul_exp_at_forty_two (5 / 6) 35 (by norm_num) (by norm_num)
    _ < _ := by norm_num


/-- The pointwise theta error, with the factor from the two weighted
first moments, is smaller than the trimmed left endpoint. -/
theorem first_moment_error_lt_trimmed_endpoint {L : ℝ} (hL : 42 ≤ L) :
    16 * Real.exp (3 * L / 4) < Real.exp L / L^2 := by
  have hbase : (16 : ℝ) * 42^2 < Real.exp ((1 / 4 : ℝ) * 42) := by
    have he : (27 / 10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h₁ := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 27 / 10) (by decide : (10 : ℕ) ≠ 0)
    have h₂ : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by linarith [Real.add_one_le_exp (1 / 2)]
    rw [show (1 / 4 : ℝ) * 42 = (10 : ℕ) * 1 + 1 / 2 by norm_num,
      Real.exp_add, Real.exp_nat_mul]
    calc
      _ < (27 / 10 : ℝ)^10 * (3 / 2) := by norm_num
      _ ≤ _ := mul_le_mul h₁.le h₂ (by norm_num) (by positivity)
  have h₄₂ : (16 : ℝ) * (42^2 * Real.exp (-(1 / 4 : ℝ) * 42)) < 1 := by
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, ← mul_div_assoc]
    exact (div_lt_iff₀ (Real.exp_pos _)).2 (by simpa only [one_mul] using hbase)
  have hmono := square_mul_exp_antitoneOn (k := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
    (show (42 : ℝ) ∈ Ici 42 by simp) (show L ∈ Ici (42 : ℝ) from hL) hL
  have hb : (16 : ℝ) * (L^2 * Real.exp (-(1 / 4 : ℝ) * L)) < 1 :=
    (mul_le_mul_of_nonneg_left hmono (by norm_num)).trans_lt h₄₂
  have he : Real.exp (-(1 / 4 : ℝ) * L) * Real.exp L = Real.exp (3 * L / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (lt_div_iff₀ (by positivity : 0 < L^2)).2
  calc
    _ = (16 * (L^2 * Real.exp (-(1 / 4 : ℝ) * L))) * Real.exp L := by rw [← he]; ring
    _ < _ := by simpa only [one_mul] using mul_lt_mul_of_pos_right hb (Real.exp_pos L)

theorem exp_nat_gt_lower {n : ℕ} (hn : n ≠ 0) :
    (2718 / 1000 : ℝ)^n < Real.exp n := by
  rw [show (n : ℝ) = (n : ℝ) * 1 by ring, Real.exp_nat_mul]
  exact pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9]) (by norm_num) hn

theorem log_twenty_eight_lower : (83 / 25 : ℝ) ≤ Real.log 28 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 / 7 by norm_num)
  rw [show (28 : ℝ) = 2^5 * (8 / 7)⁻¹ by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_inv]
  norm_num
  linarith [Real.log_two_gt_d9]

theorem log_le_sixth_of_ge_28 {L : ℝ} (hL : 28 ≤ L) : Real.log L ≤ L / 6 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < L / 42 by positivity)
  rw [Real.log_div (by linarith : L ≠ 0) (by norm_num)] at h
  linarith [log_forty_two_bounds.2]

theorem delta_lt_of_ge_28 {L : ℝ} (hL : 28 ≤ L) : delta L < 1 / 10^8 := by
  have hm := square_mul_exp_antitoneOn (a := 28) (k := 1) (by norm_num)
    (by norm_num) (by norm_num) (by simp) (show L ∈ Ici (28 : ℝ) from hL) hL
  have he := exp_nat_gt_lower (n := 28) (by decide)
  unfold delta
  calc
    _ ≤ (28 : ℝ)^2 * Real.exp (-28) := by simpa only [neg_mul, one_mul] using hm
    _ = (28 : ℝ)^2 / Real.exp 28 := by rw [Real.exp_neg, div_eq_mul_inv]
    _ < _ := (div_lt_iff₀ (Real.exp_pos _)).2 (by norm_num at he ⊢; linarith)

theorem delta_exp_bandwidth_lt_of_ge_28 {L : ℝ} (hL : 28 ≤ L) :
    delta L * Real.exp (bandwidth L) < 1 / 32 := by
  have hm := square_mul_exp_antitoneOn (a := 28) (k := 2 / 3) (by norm_num)
    (by norm_num) (by norm_num) (by simp) (show L ∈ Ici (28 : ℝ) from hL) hL
  have he : (2718 / 1000 : ℝ)^18 < Real.exp ((2 / 3 : ℝ) * 28) :=
    (exp_nat_gt_lower (n := 18) (by decide)).trans_le (Real.exp_le_exp.mpr (by norm_num))
  calc
    _ = L^2 * Real.exp (-L + bandwidth L) := by simp [delta, Real.exp_add, mul_assoc]
    _ ≤ L^2 * Real.exp (-(2 / 3 : ℝ) * L) := by
      gcongr
      linarith [bandwidth_le_third_of_ge_twenty_seven (L := L) (by linarith : 27 ≤ L)]
    _ ≤ (28 : ℝ)^2 * Real.exp (-(2 / 3 : ℝ) * 28) := hm
    _ = (28 : ℝ)^2 / Real.exp ((2 / 3 : ℝ) * 28) := by
      simp only [neg_mul, Real.exp_neg, div_eq_mul_inv]
    _ < _ := (div_lt_iff₀ (Real.exp_pos _)).2 (by linarith only [he,
      show (28 : ℝ)^2 < (1 / 32) * (2718 / 1000)^18 by norm_num])

theorem first_moment_error_lt_five_trimmed {L : ℝ} (hL : 28 ≤ L) :
    6 * Real.exp (3 * L / 4) < 5 * (Real.exp L / L^2) := by
  have he : (2718 / 1000 : ℝ)^7 < Real.exp ((1 / 4 : ℝ) * 28) := by
    rw [show (1 / 4 : ℝ) * 28 = (7 : ℕ) by norm_num]
    exact exp_nat_gt_lower (n := 7) (by decide)
  have hbase : (6 : ℝ) * (28^2 * Real.exp (-(1 / 4 : ℝ) * 28)) < 5 := by
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, ← mul_div_assoc]
    exact (div_lt_iff₀ (Real.exp_pos _)).2
      (by linarith only [he, show (6 : ℝ) * 28^2 < 5 * (2718 / 1000)^7 by norm_num])
  have hm := square_mul_exp_antitoneOn (a := 28) (k := 1 / 4) (by norm_num)
    (by norm_num) (by norm_num) (by simp) (show L ∈ Ici (28 : ℝ) from hL) hL
  have h := (mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ 6 by norm_num)).trans_lt hbase
  have hE : Real.exp (-(1 / 4 : ℝ) * L) * Real.exp L = Real.exp (3 * L / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hL₂ : 0 < L^2 := sq_pos_of_pos (by linarith)
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hL₂).2
  have hh := mul_lt_mul_of_pos_right h (Real.exp_pos L)
  rw [show 6 * (L^2 * Real.exp (-(1 / 4 : ℝ) * L)) * Real.exp L =
    6 * Real.exp (3 * L / 4) * L^2 by rw [← hE]; ring] at hh
  simpa only [mul_comm (5 : ℝ) (Real.exp L)] using hh

theorem delta_mul_square_le_of_ge_28 {L : ℝ} (hL : 28 ≤ L) :
    delta L * (L + 1)^2 < 1 / 10^6 := by
  have hm := square_mul_exp_antitoneOn (a := 28) (k := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by simp) (show L ∈ Ici (28 : ℝ) from hL) hL
  simp only [neg_mul, one_div, inv_mul_eq_div] at hm
  have hquad : (L + 1)^2 ≤ 2 * L^2 := by nlinarith [sq_nonneg (L - 2)]
  have hform (u : ℝ) : delta u * (2 * u^2) = 2 * (u^2 * Real.exp (-(u / 2)))^2 := by
    rw [mul_pow, ← Real.exp_nat_mul, show (2 : ℕ) * -(u / 2) = -u by push_cast; ring]
    unfold delta
    ring
  have he := exp_nat_gt_lower (n := 28) (by decide)
  calc
    _ ≤ delta L * (2 * L^2) :=
      mul_le_mul_of_nonneg_left hquad (delta_pos_of_pos (by linarith)).le
    _ ≤ delta 28 * (2 * 28^2) := by
      rw [hform, hform]
      gcongr
    _ = 2 * (28 : ℝ)^4 / Real.exp 28 := by
      unfold delta
      rw [Real.exp_neg]
      simp only [div_eq_mul_inv]
      ring
    _ < _ := (div_lt_iff₀ (Real.exp_pos _)).2 (by norm_num at he ⊢; linarith)

end GoldbachExplicit
