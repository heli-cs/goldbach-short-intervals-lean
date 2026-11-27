import Goldbach.Zeros

open Filter Asymptotics Set
open scoped Topology

noncomputable section
namespace GoldbachZeros

/-- The cumulative Riemann–von Mangoldt main term. A bounded constant
term is immaterial in the error estimate below. -/
def countMain (t : ℝ) : ℝ := t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1)

private theorem main_diff (t : ℝ) (ht : 0 < t) :
    countMain (2 * t) - countMain t = t / (2 * Real.pi) * Zeta23.ell1 t := by
  unfold countMain Zeta23.ell1 Zeta23.l
  rw [show 2 * t / (2 * Real.pi) = 2 * (t / (2 * Real.pi)) by ring,
    Real.log_mul (by norm_num) (div_pos ht (by positivity)).ne']
  ring

/-- The dyadic formula implies the cumulative formula with an
square-root error, by induction on the integer part of the height. -/
theorem cumulative_count_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 1 ≤ t →
      |(Zeta23.Ncount 0 t : ℝ) - countMain t| ≤ K * Real.sqrt t := by
  obtain ⟨C, T₀, hcount⟩ := riemannVonMangoldt.main
  let T := max 1 T₀
  have hT₁ : 1 ≤ T := le_max_left _ _
  let E := fun t : ℝ => (Zeta23.Ncount 0 t : ℝ) - countMain t
  have hcont : ContinuousOn (fun x : ℝ => |countMain x|) (Icc 1 (2 * T)) := by
    apply ContinuousOn.abs
    unfold countMain
    apply (continuousOn_id.div_const _).mul
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.log (continuousOn_id.div_const _)
    intro x hx
    exact (div_pos (zero_lt_one.trans_le hx.1) (by positivity)).ne'
  obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  let K := max ((Zeta23.Ncount 0 (2 * T) : ℝ) + max 0 B) (8 * |C|)
  have hK : 0 ≤ K := (mul_nonneg (by norm_num) (abs_nonneg C)).trans (le_max_right _ _)
  have hKc : 8 * |C| ≤ K := le_max_right _ _
  have hd (t : ℝ) (ht : T ≤ t) : |E (2 * t)| ≤ |E t| + |C| * 2 * Real.sqrt t := by
    have ht₁ := hT₁.trans ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht₁
    have hz := hcount t ((le_max_right 1 T₀).trans ht)
    rw [Zeta23.zetaZeroConfig_N] at hz
    have hsplit : E (2 * t) = E t +
        ((Zeta23.Ncount t (2 * t) : ℝ) - t / (2 * Real.pi) * Zeta23.ell1 t) := by
      dsimp [E]
      rw [Zeta23.Ncount_add ht0.le (by linarith), Nat.cast_add, ← main_diff t ht0]
      ring
    have hlog := Real.log_le_rpow_div ht0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at hlog
    have hlog0 := Real.log_nonneg ht₁
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add_right (hz.trans ?_) _)
    calc
      _ ≤ |C| * Real.log t := mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
      _ ≤ |C| * (Real.sqrt t / (1 / 2)) :=
        mul_le_mul_of_nonneg_left hlog (abs_nonneg C)
      _ = _ := by ring
  have hAll : ∀ n : ℕ, ∀ t : ℝ, 1 ≤ t → ⌊t⌋₊ = n → |E t| ≤ K * Real.sqrt t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t ht hn
      by_cases hlarge : 2 * T ≤ t
      · have hhalf : T ≤ t / 2 := by linarith
        have hh : 1 ≤ t / 2 := hT₁.trans hhalf
        have hfloor : ⌊t / 2⌋₊ < n := by
          rw [← hn]
          apply (Nat.floor_lt (show 0 ≤ t / 2 by linarith)).mpr
          have ht₂ : 2 ≤ t := by linarith
          linarith [Nat.lt_floor_add_one t]
        have hi := ih ⌊t / 2⌋₊ hfloor (t / 2) hh rfl
        have heq : 2 * (t / 2) = t := by ring
        have hstep := hd (t / 2) hhalf
        rw [heq] at hstep
        have hsqrt : Real.sqrt (t / 2) ≤ (3 / 4) * Real.sqrt t := by
          apply Real.sqrt_le_iff.mpr
          refine ⟨by positivity, ?_⟩
          rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ t)]
          linarith
        have hCoef : (K + 2 * |C|) * (3 / 4) ≤ K := by linarith
        calc
          _ ≤ K * Real.sqrt (t / 2) + |C| * 2 * Real.sqrt (t / 2) :=
            hstep.trans (add_le_add_left hi _)
          _ = (K + 2 * |C|) * Real.sqrt (t / 2) := by ring
          _ ≤ (K + 2 * |C|) * ((3 / 4) * Real.sqrt t) :=
            mul_le_mul_of_nonneg_left hsqrt (by positivity)
          _ = ((K + 2 * |C|) * (3 / 4)) * Real.sqrt t := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hCoef (Real.sqrt_nonneg _)
      · have hupper : t ≤ 2 * T := le_of_not_ge hlarge
        have hB' : |countMain t| ≤ B := hB ⟨t, ⟨ht, hupper⟩, rfl⟩
        have hn' : (Zeta23.Ncount 0 t : ℝ) ≤ Zeta23.Ncount 0 (2 * T) := by
          exact_mod_cast Zeta23.Ncount_mono (a := 0) (c := 0) le_rfl hupper
        have hmono : |E t| ≤ (Zeta23.Ncount 0 (2 * T) : ℝ) + max 0 B := by
          dsimp [E]
          refine (abs_sub _ _).trans ?_
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
          exact add_le_add hn' (hB'.trans (le_max_right _ _))
        exact (hmono.trans (le_max_left _ _)).trans
          (le_mul_of_one_le_right hK (Real.one_le_sqrt.mpr ht))
  exact ⟨K, hK, fun t ht => hAll ⌊t⌋₊ t ht rfl⟩

/-- The positive-ordinate counting asymptotic needed for the scaled
zero measure. Zeros are counted with their analytic multiplicities. -/
theorem cumulative_count_tendsto :
    Tendsto (fun t : ℝ => (Zeta23.Ncount 0 t : ℝ) / (t * Real.log t))
      atTop (𝓝 (1 / (2 * Real.pi))) := by
  obtain ⟨K, hK, herror⟩ := cumulative_count_error
  let E := fun t : ℝ => (Zeta23.Ncount 0 t : ℝ) - countMain t
  have hE : E =O[atTop] Real.sqrt := by
    apply isBigO_iff.mpr
    refine ⟨K, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using herror t ht
  have hne : ∀ᶠ t : ℝ in atTop, id t ≠ 0 :=
    (eventually_gt_atTop 0).mono (fun _ ht => ht.ne')
  have hsqrt : Real.sqrt =o[atTop] (id : ℝ → ℝ) := by
    apply (isLittleO_iff_tendsto' (hne.mono (fun _ hn h => (hn h).elim))).mpr
    apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    change t ^ (-(1 / 2 : ℝ)) = Real.sqrt t / t
    rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow, Real.sqrt_div_self]
  have hE₁ := (hE.trans_isLittleO hsqrt).tendsto_div_nhds_zero
  have hL := Real.tendsto_log_atTop.inv_tendsto_atTop
  have hE₂ : Tendsto (fun t : ℝ => E t / (t * Real.log t)) atTop (𝓝 0) := by
    have ht := hE₁.mul hL
    rw [zero_mul] at ht
    apply ht.congr'
    exact Eventually.of_forall (fun t => by
      change E t / t * (Real.log t)⁻¹ = E t / (t * Real.log t)
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_assoc])
  have hM : Tendsto (fun t : ℝ => countMain t / (t * Real.log t))
      atTop (𝓝 (1 / (2 * Real.pi))) := by
    have ht := ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (hL.const_mul (Real.log (2 * Real.pi) + 1))).const_mul (1 / (2 * Real.pi))
    simp only [mul_zero, sub_zero, mul_one] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 := zero_lt_one.trans ht
    have hπ : (2 * Real.pi) ≠ 0 := (by positivity : 0 < 2 * Real.pi).ne'
    unfold countMain
    rw [Real.log_div ht0.ne' hπ]
    dsimp
    field_simp [ht0.ne', hπ, (Real.log_pos ht).ne']
    ring
  have ht := hE₂.add hM
  rw [zero_add] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun t => by
    change E t / (t * Real.log t) + countMain t / (t * Real.log t) = _
    rw [← add_div]
    congr 1
    dsimp [E]
    ring)


/-- The natural scaled mass on a fixed positive interval. With
`T = 1/lam` this is the positive-annulus counting limit. -/
theorem scaled_positive_window_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun T : ℝ => (Zeta23.Ncount (a * T) (b * T) : ℝ) / (T * Real.log T))
      atTop (𝓝 ((b - a) / (2 * Real.pi))) := by
  have scaled (d : ℝ) (hd : 0 < d) :
      Tendsto (fun T : ℝ => (Zeta23.Ncount 0 (d * T) : ℝ) / (T * Real.log T))
        atTop (𝓝 (d / (2 * Real.pi))) := by
    have h := cumulative_count_tendsto.comp ((tendsto_const_mul_atTop_of_pos hd).2 tendsto_id)
    have hf : Tendsto (fun T : ℝ => d * (1 + Real.log d * (Real.log T)⁻¹))
        atTop (𝓝 d) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add
        (Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul (Real.log d))).const_mul d
    have ht := h.mul hf
    have hscale : (1 / (2 * Real.pi)) * d = d / (2 * Real.pi) := by ring
    rw [hscale] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop 1,
        ((tendsto_const_mul_atTop_of_pos hd).2 (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)).eventually
          (eventually_gt_atTop (1 : ℝ))] with T hT hDT
    have hT0 := zero_lt_one.trans hT
    change 1 < d * T at hDT
    have hprod : 0 < d * T := mul_pos hd hT0
    change ((Zeta23.Ncount 0 (d * T) : ℝ) / ((d * T) * Real.log (d * T))) *
      (d * (1 + Real.log d * (Real.log T)⁻¹)) = _
    have hq : d * (1 + Real.log d * (Real.log T)⁻¹) =
        ((d * T) * Real.log (d * T)) / (T * Real.log T) := by
      rw [Real.log_mul hd.ne' hT0.ne']
      field_simp [hT0.ne', (Real.log_pos hT).ne']
      ring
    rw [hq, ← mul_div_assoc, div_mul_cancel₀ _ (mul_pos hprod (Real.log_pos hDT)).ne']
  have h := (scaled b (ha.trans_le hab)).sub (scaled a ha)
  rw [← sub_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [← sub_div, Zeta23.Ncount_add (mul_nonneg ha.le hT)
    (mul_le_mul_of_nonneg_right hab hT), Nat.cast_add, add_sub_cancel_left]

end GoldbachZeros
