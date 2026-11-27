import Mathlib

/-! Translation control for a compact unimodal weight, including jumps. -/

open MeasureTheory Set
open scoped Interval
noncomputable section

namespace GoldbachExplicit

private theorem monotone_increment_integral {g : ℝ → ℝ} {a b c d : ℝ}
    (hg : Monotone g) (hab : a ≤ b) (hd : 0 ≤ d)
    (ha : ∀ s ≤ a, g s = 0) (hb : ∀ s, b ≤ s → g s = c) :
    Integrable (fun s => g s - g (s - d)) ∧
    (∫ s, g s - g (s - d)) = d * c := by
  have hbd : a ≤ b + d := by linarith
  have hshift : Monotone (fun s => g (s - d)) :=
    fun _ _ h => hg (sub_le_sub_right h d)
  have hi : IntervalIntegrable (fun s => g s - g (s - d)) volume a (b + d) :=
    hg.intervalIntegrable.sub hshift.intervalIntegrable
  have hzero (s : ℝ) (hs : s ∉ Ioc a (b + d)) : g s - g (s - d) = 0 := by
    by_cases hs₁ : s ≤ a
    · rw [ha s hs₁, ha (s - d) (by linarith), sub_self]
    · have hs₂ : b + d < s := lt_of_not_ge (fun h => hs ⟨lt_of_not_ge hs₁, h⟩)
      rw [hb s (by linarith), hb (s - d) (by linarith), sub_self]
  have he : (fun s => g s - g (s - d)) =
      (Ioc a (b + d)).indicator (fun s => g s - g (s - d)) := by
    funext s
    by_cases hs : s ∈ Ioc a (b + d)
    · rw [indicator_of_mem hs]
    · rw [indicator_of_notMem hs, hzero s hs]
  constructor
  · rw [he, integrable_indicator_iff measurableSet_Ioc]
    exact hi.1
  · rw [show (∫ s, g s - g (s - d)) =
        ∫ s in Ioc a (b + d), g s - g (s - d) by
      symm
      exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
      ← intervalIntegral.integral_of_le hbd]
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable (μ := volume)) (hshift.intervalIntegrable (μ := volume)),
      intervalIntegral.integral_comp_sub_right g d, add_sub_cancel_right]
    have h₁ := intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (μ := volume) (a := a) (b := b)) (hg.intervalIntegrable (μ := volume) (a := b) (b := b + d))
    have h₂ := intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (μ := volume) (a := a - d) (b := a)) (hg.intervalIntegrable (μ := volume) (a := a) (b := b))
    have ht : (∫ s in b..(b + d), g s) = d * c := by
      trans ∫ _ : ℝ in b..(b + d), c
      · apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by linarith : b ≤ b + d)] at hs
        exact hb s hs.1
      · simp [intervalIntegral.integral_const, smul_eq_mul]
    have hbot : (∫ s in (a - d)..a, g s) = 0 := by
      trans ∫ _ : ℝ in (a - d)..a, (0 : ℝ)
      · apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by linarith : a - d ≤ a)] at hs
        exact ha s hs.2
      · simp
    linarith only [h₁, h₂, ht, hbot]

/-- A nonnegative unimodal compact weight bounded by one has translation
cost at most twice the translation length in L¹. The proof works even when
the weight jumps at a support endpoint. -/
theorem integral_abs_sub_translate_le {q : ℝ → ℝ} {a b c d : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (hd : 0 ≤ d)
    (hleft : MonotoneOn q (Iic c)) (hright : AntitoneOn q (Ici c))
    (ha : ∀ s ≤ a, q s = 0) (hb : ∀ s, b ≤ s → q s = 0) (hqc : q c ≤ 1) :
    Integrable (fun s => |q (s - d) - q s|) ∧
      (∫ s, |q (s - d) - q s|) ≤ 2 * d := by
  let g₁ (s : ℝ) := q (min s c)
  let g₂ (s : ℝ) := q c - q (max s c)
  have hm₁ : Monotone g₁ :=
    fun _ _ h => hleft (mem_Iic.mpr (min_le_right _ _)) (mem_Iic.mpr (min_le_right _ _)) (min_le_min_right _ h)
  have hm₂ : Monotone g₂ :=
    fun _ _ h => sub_le_sub_left (hright (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _)) (max_le_max_right _ h)) _
  have h₁ := monotone_increment_integral hm₁ (hac.trans hcb) hd
      (fun s hs => by unfold g₁; rw [min_eq_left (hs.trans hac), ha s hs])
      (fun s hs => by unfold g₁; rw [min_eq_right (hcb.trans hs)])
  have h₂ := monotone_increment_integral hm₂ (hac.trans hcb) hd
      (fun s hs => by unfold g₂; rw [max_eq_right (hs.trans hac), sub_self])
      (fun s hs => by unfold g₂; rw [max_eq_left (hcb.trans hs), hb s hs, sub_zero])
  have he (s : ℝ) : q s = g₁ s - g₂ s := by
    rcases le_total s c with h | h
    · simp [g₁, g₂, min_eq_left h, max_eq_right h]
    · simp [g₁, g₂, min_eq_right h, max_eq_left h]
  let D₁ (s : ℝ) := g₁ s - g₁ (s - d)
  let D₂ (s : ℝ) := g₂ s - g₂ (s - d)
  have hD (s : ℝ) : q (s - d) - q s = D₂ s - D₁ s := by
    rw [he (s - d), he s]
    dsimp [D₁, D₂]
    ring
  have hD₁ : Integrable D₁ := h₁.1
  have hD₂ : Integrable D₂ := h₂.1
  have hq : Integrable (fun s => |q (s - d) - q s|) := by
    simp_rw [hD]
    exact (hD₂.sub hD₁).abs
  refine ⟨hq, ?_⟩
  have hd₁ (s : ℝ) : 0 ≤ D₁ s := sub_nonneg.mpr (hm₁ (sub_le_self s hd))
  have hd₂ (s : ℝ) : 0 ≤ D₂ s := sub_nonneg.mpr (hm₂ (sub_le_self s hd))
  have hb₁ := integral_mono hq (hD₁.add hD₂) (fun s => by
    rw [hD]
    exact (abs_sub _ _).trans_eq (by
      change |D₂ s| + |D₁ s| = D₁ s + D₂ s
      rw [abs_of_nonneg (hd₁ s), abs_of_nonneg (hd₂ s)]
      exact add_comm _ _))
  change (∫ s, |q (s - d) - q s|) ≤ ∫ s, D₁ s + D₂ s at hb₁
  rw [integral_add hD₁ hD₂, h₁.2, h₂.2] at hb₁
  nlinarith only [hb₁, mul_le_mul_of_nonneg_left hqc hd]

end GoldbachExplicit
