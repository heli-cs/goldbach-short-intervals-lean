import Goldbach.Explicit.LowerVariance
import Goldbach.ArithmeticError
import Goldbach.PrimePowerError

/-! Pointwise control of higher prime powers in the moving explicit interval. -/

open MeasureTheory Set
noncomputable section

namespace GoldbachExplicit

open ArithmeticFunction GoldbachArithmetic

/-- One full interval width is short compared with the square root of
the moving lower endpoint. -/
theorem sq_lt_sqrt_trimmedEndpoint_of_ge_28 {L : ℝ} (hL : 28 ≤ L) :
    L^2 < Real.sqrt (trimmedEndpoint L) := by
  have hL₀ : 0 < L := by linarith
  have hpow : (Nat.factorial 14 : ℝ) < L^8 :=
    (show (Nat.factorial 14 : ℝ) < 28^8 by norm_num [Nat.factorial]).trans_le
      (pow_le_pow_left₀ (by norm_num) hL 8)
  have hfact : 0 < (Nat.factorial 14 : ℝ) := by positivity
  have hlarge : L^6 < Real.exp L := calc
    _ < L^6 * (L^8 / (Nat.factorial 14 : ℝ)) := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left
        ((one_lt_div hfact).2 hpow) (pow_pos hL₀ _)
    _ = L^14 / (Nat.factorial 14 : ℝ) := by rw [← mul_div_assoc, ← pow_add]
    _ ≤ _ := Real.pow_div_factorial_le_exp L hL₀.le 14
  apply (Real.lt_sqrt (sq_nonneg L)).2
  change (L^2)^2 < Real.exp L / L^2
  apply (lt_div_iff₀ (sq_pos_of_pos hL₀)).2
  rw [← pow_mul, ← pow_add]
  exact hlarge

theorem sq_lt_sqrt_trimmedEndpoint {L : ℝ} (hL : 42 ≤ L) :
    L^2 < Real.sqrt (trimmedEndpoint L) :=
  sq_lt_sqrt_trimmedEndpoint_of_ge_28 (by linarith)

/-- Both Chebyshev arguments lie below the original right endpoint
throughout the moving interval. -/
theorem explicit_interval_endpoints_of_ge_28 {L y : ℝ} (hL : 28 ≤ L)
    (hy : y ∈ Icc (trimmedEndpoint L) (Real.exp L - trimmedEndpoint L)) :
    2 ≤ y ∧ (1 + delta L) * y ≤ Real.exp L := by
  let A := trimmedEndpoint L
  let x := Real.exp L
  let d := delta L
  have hAs := sq_lt_sqrt_trimmedEndpoint_of_ge_28 hL
  have hA₀ : 0 < A := by unfold A trimmedEndpoint; positivity
  have hA₄ : L^4 < A := by
    have h := (Real.lt_sqrt (sq_nonneg L)).1 hAs
    rwa [← pow_mul] at h
  have hLA : L^2 ≤ A := by
    refine le_trans ?_ hA₄.le
    have h : 1 ≤ L^2 := by nlinarith [sq_nonneg (L - 28)]
    rw [show L^4 = (L^2)^2 by ring]
    nlinarith [sq_nonneg (L^2 - 1)]
  have hdx : d * x = L^2 := by
    simp [d, delta, x, Real.exp_neg, (Real.exp_pos L).ne']
  have hd : 0 < d := delta_pos_of_pos (by linarith)
  have hB : (1 + d) * (x - A) ≤ x := by
    nlinarith only [hLA, hdx, mul_nonneg hd.le hA₀.le]
  refine ⟨(show 2 ≤ A by nlinarith [sq_nonneg (L - 28)]).trans hy.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left hy.2 (by positivity)).trans hB

theorem explicit_interval_endpoints {L y : ℝ} (hL : 42 ≤ L)
    (hy : y ∈ Icc (trimmedEndpoint L) (Real.exp L - trimmedEndpoint L)) :
    2 ≤ y ∧ (1 + delta L) * y ≤ Real.exp L :=
  explicit_interval_endpoints_of_ge_28 (by linarith) hy

/-- The finite higher-prime-power increment is bounded by the original
additive width throughout the trimmed interval. -/
theorem explicit_primePowerIncrement_le_of_ge_28 {L y : ℝ} (hL : 28 ≤ L)
    (hy : y ∈ Icc (trimmedEndpoint L) (Real.exp L - trimmedEndpoint L)) :
    0 ≤ primePowerIncrement (delta L) y ∧
      primePowerIncrement (delta L) y ≤ (3 / 4) * L^2 := by
  classical
  let x := Real.exp L
  let A := trimmedEndpoint L
  let d := delta L
  let J := Finset.Ioc ⌊y⌋₊ ⌊(1 + d) * y⌋₊
  let S := J.filter (fun n => higherPrimePowerWeight n ≠ 0)
  let k (n : ℕ) := n.factorization n.minFac
  have hA₀ : 0 < A := by unfold A trimmedEndpoint; positivity
  have hd : 0 < d := delta_pos_of_pos (by linarith)
  obtain ⟨hy₂, hxy⟩ := explicit_interval_endpoints_of_ge_28 hL hy
  have hy₀ : 0 ≤ y := by linarith
  have hy'₀ : 0 ≤ (1 + d) * y := by positivity
  have hdx : d * x = L^2 := by
    simp [d, delta, x, Real.exp_neg, (Real.exp_pos L).ne']
  have hwidth : d * y ≤ L^2 := by
    rw [← hdx]
    exact mul_le_mul_of_nonneg_left (by linarith [hy.2]) hd.le
  have hmembers (n : ℕ) (hn : n ∈ S) :
      y < (n : ℝ) ∧ (n : ℝ) ≤ (1 + d) * y ∧ ¬n.Prime ∧ IsPrimePow n := by
    obtain ⟨hJ, hP⟩ := Finset.mem_filter.mp hn
    obtain ⟨h₁, h₂⟩ := Finset.mem_Ioc.mp hJ
    obtain ⟨hnot, hpow⟩ := (higherPrimePowerWeight_ne_zero_iff n).mp hP
    exact ⟨(Nat.floor_lt hy₀).1 h₁, (Nat.le_floor_iff hy'₀).1 h₂, hnot, hpow⟩
  have hrep (n : ℕ) (hn : n ∈ S) : n.minFac.Prime ∧ 2 ≤ k n ∧ n.minFac ^ k n = n := by
    obtain ⟨_, _, hnot, hpow⟩ := hmembers n hn
    have hP := Nat.minFac_prime hpow.ne_one
    have he : n.minFac ^ k n = n := hpow.minFac_pow_factorization_eq
    have hk : 2 ≤ k n := by
      by_contra! h
      rcases (show k n = 0 ∨ k n = 1 by omega) with h₀ | h₁
      · rw [h₀, pow_zero] at he
        exact hpow.ne_one he.symm
      · rw [h₁, pow_one] at he
        exact hnot (he ▸ hP)
    exact ⟨hP, hk, he⟩
  have hlogs (n : ℕ) (hn : n ∈ S) :
      (k n : ℝ) * Real.log (n.minFac : ℝ) ≤ L ∧ Real.log 2 ≤ Real.log (n.minFac : ℝ) := by
    obtain ⟨hp, _, he⟩ := hrep n hn
    have hp₂ : (2 : ℝ) ≤ n.minFac := by exact_mod_cast hp.two_le
    have hneq : (n.minFac : ℝ) ^ k n = (n : ℝ) := by exact_mod_cast he
    have hn₀ : 0 < (n : ℝ) := by linarith [(hmembers n hn).1]
    have hlog := Real.log_le_log hn₀ ((hmembers n hn).2.1.trans hxy)
    rw [← hneq, Real.log_pow, Real.log_exp] at hlog
    exact ⟨hlog, Real.log_le_log (by norm_num) hp₂⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let E := Finset.Ioc 0 ⌊L / Real.log 2⌋₊
  have hMap : Set.MapsTo k (S : Set ℕ) (E : Set ℕ) := by
    intro n hns
    have hn : n ∈ S := hns
    have hKo := (hrep n hn).2.1
    have he : (k n : ℝ) * Real.log 2 ≤ L :=
      (mul_le_mul_of_nonneg_left (hlogs n hn).2 (Nat.cast_nonneg _)).trans (hlogs n hn).1
    exact Finset.mem_Ioc.mpr ⟨by omega,
      (Nat.le_floor_iff (div_nonneg (by linarith) hlog2.le)).2 ((le_div_iff₀ hlog2).2 he)⟩
  have hNo {n m : ℕ} (hn : n ∈ S) (hm : m ∈ S) (he : k n = k m)
      (hlt : n.minFac < m.minFac) : False := by
    obtain ⟨hp, hk, hnPow⟩ := hrep n hn
    obtain ⟨_, _, hmPow⟩ := hrep m hm
    have hgap := sqrt_le_pow_gap (m := n.minFac) (n := m.minFac)
      (by have h := hp.two_le; omega) hlt hk
    have hrn : (n.minFac : ℝ)^k n = (n : ℝ) := by exact_mod_cast hnPow
    have hrm : (m.minFac : ℝ)^k n = (m : ℝ) := by
      rw [he]
      exact_mod_cast hmPow
    rw [hrn, hrm] at hgap
    have hAlo : A ≤ (n : ℝ) := hy.1.trans (hmembers n hn).1.le
    have hlo := (sq_lt_sqrt_trimmedEndpoint_of_ge_28 hL).trans_le (Real.sqrt_le_sqrt hAlo)
    linarith only [hgap, hlo, hwidth, (hmembers n hn).1, (hmembers m hm).2.1]
  have hInj : Set.InjOn k (S : Set ℕ) := by
    intro n hn m hm he
    have hn' : n ∈ S := hn
    have hm' : m ∈ S := hm
    rcases lt_trichotomy n.minFac m.minFac with hl | hl | hl
    · exact (hNo hn' hm' he hl).elim
    · rw [← (hrep n hn').2.2, ← (hrep m hm').2.2, hl, he]
    · exact (hNo hm' hn' he.symm hl).elim
  have hc : (S.card : ℝ) ≤ L / Real.log 2 := by
    have hc := Finset.card_le_card_of_injOn k hMap hInj
    have hce : E.card = ⌊L / Real.log 2⌋₊ := by unfold E; rw [Nat.card_Ioc, Nat.sub_zero]
    rw [hce] at hc
    exact (show (S.card : ℝ) ≤ (⌊L / Real.log 2⌋₊ : ℝ) by exact_mod_cast hc).trans
      (Nat.floor_le (div_nonneg (by linarith) hlog2.le))
  have hterm (n : ℕ) (hn : n ∈ S) : higherPrimePowerWeight n ≤ L / 2 := by
    obtain ⟨hp, hk, he⟩ := hrep n hn
    rw [higherPrimePowerWeight_eq_vonMangoldt (hmembers n hn).2.2.1, ← he,
      vonMangoldt_apply_pow (by omega : k n ≠ 0), vonMangoldt_apply_prime hp]
    have hk' : (2 : ℝ) ≤ k n := by exact_mod_cast hk
    have hh := mul_le_mul_of_nonneg_right hk' (hlog2.le.trans (hlogs n hn).2)
    linarith only [hh, (hlogs n hn).1]
  have hs : (∑ n ∈ S, higherPrimePowerWeight n) = ∑ n ∈ J, higherPrimePowerWeight n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hns
    by_contra h
    exact hns (Finset.mem_filter.mpr ⟨hn, h⟩)
  change 0 ≤ primePowerIncrement d y ∧ primePowerIncrement d y ≤ (3 / 4) * L^2
  rw [primePowerIncrement_eq_sum hd.le hy₀]
  change 0 ≤ (∑ n ∈ J, higherPrimePowerWeight n) ∧ _ ≤ (3 / 4) * L^2
  refine ⟨Finset.sum_nonneg (fun n _ => higherPrimePowerWeight_nonneg n), ?_⟩
  rw [← hs]
  calc
    _ ≤ ∑ _n ∈ S, L / 2 := Finset.sum_le_sum hterm
    _ ≤ (L / Real.log 2) * (L / 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ (3 / 4) * L^2 := by
      have hlog : 2 / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      apply (mul_le_mul_of_nonneg_right
        (show L / Real.log 2 ≤ (3 / 2) * L from (div_le_iff₀ hlog2).2 (by
          nlinarith [mul_nonneg (show 0 ≤ L by linarith) (sub_nonneg.mpr hlog)]))
        (show 0 ≤ L / 2 by positivity)).trans_eq
      ring

theorem explicit_primePowerIncrement_le {L y : ℝ} (hL : 42 ≤ L)
    (hy : y ∈ Icc (trimmedEndpoint L) (Real.exp L - trimmedEndpoint L)) :
    0 ≤ primePowerIncrement (delta L) y ∧ primePowerIncrement (delta L) y ≤ L^2 := by
  obtain ⟨h₀, h₁⟩ := explicit_primePowerIncrement_le_of_ge_28 (by linarith : 28 ≤ L) hy
  exact ⟨h₀, h₁.trans (mul_le_of_le_one_left (sq_nonneg _) (by norm_num))⟩

end GoldbachExplicit
