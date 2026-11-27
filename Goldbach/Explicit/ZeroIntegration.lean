import Goldbach.LocalDensity

/-! Exact integration by parts for the finite cumulative ordinate count. -/

open Set MeasureTheory
open scoped Interval BigOperators
noncomputable section

namespace GoldbachExplicit
open GoldbachZeros Zeta23

/-- Positive-ordinate Stieltjes summation at finite height. All zeros
at the upper endpoint occur with multiplicity in the boundary term. -/
theorem zero_window_integration_by_parts {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) :
    (∑ ρ ∈ zeroWindow a b, multiplicity ρ * f (ordinate ρ)) =
      f b * (Ncount a b : ℝ) - ∫ t in Ioc a b, deriv f t * (Ncount a t : ℝ) := by
  classical
  let W := zeroWindow a b
  let Q (t : ℝ) : ℝ := Ncount a t
  let H (ρ : Zeros) := (Ici (ordinate ρ)).indicator (deriv f)
  have hc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hi : IntegrableOn (deriv f) (Ioc a b) :=
    (hc.continuousOn.integrableOn_compact (μ := volume) isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hterm (ρ : Zeros) : IntegrableOn (fun t => multiplicity ρ * H ρ t) (Ioc a b) :=
    (hi.indicator measurableSet_Ici).const_mul _
  have hsum (t : ℝ) (ht : t ∈ Ioc a b) :
      deriv f t * Q t = ∑ ρ ∈ W, multiplicity ρ * H ρ t := by
    have he : zeroWindow a t = W.filter (fun ρ => ordinate ρ ≤ t) := by
      ext ρ
      simp only [Finset.mem_filter, W, mem_zeroWindow]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨⟨h₁, h₂.trans ht.2⟩, h₂⟩
      · rintro ⟨⟨h₁, _⟩, h₂⟩
        exact ⟨h₁, h₂⟩
    dsimp only [Q]
    rw [Ncount_eq_sum_zeroWindow, he, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ _
    by_cases hz : ordinate ρ ≤ t
    · simp only [if_pos hz, H, indicator_of_mem (mem_Ici.mpr hz)]
      ring
    · simp only [if_neg hz, H, indicator_of_notMem (show t ∉ Ici (ordinate ρ) from hz), mul_zero]
  have hterm_eval (ρ : Zeros) (hρ : ρ ∈ W) :
      (∫ t in Ioc a b, multiplicity ρ * H ρ t) =
        multiplicity ρ * (f b - f (ordinate ρ)) := by
    obtain ⟨h₁, h₂⟩ := mem_zeroWindow.mp hρ
    have hset : Ici (ordinate ρ) ∩ Ioc a b = Icc (ordinate ρ) b := by
      ext u
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h₁.trans_le h.1, h.2⟩⟩
    dsimp only [H]
    rw [integral_const_mul, integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici, hset, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le h₂]
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun y _ => hf.differentiable (by norm_num) y) (hc.intervalIntegrable _ _)]
  have hI : (∫ t in Ioc a b, deriv f t * Q t) =
      (∑ ρ ∈ W, multiplicity ρ) * f b - ∑ ρ ∈ W, multiplicity ρ * f (ordinate ρ) := by
    calc
      _ = ∫ t in Ioc a b, ∑ ρ ∈ W, multiplicity ρ * H ρ t :=
        setIntegral_congr_fun measurableSet_Ioc hsum
      _ = ∑ ρ ∈ W, ∫ t in Ioc a b, multiplicity ρ * H ρ t :=
        integral_finsetSum W (fun ρ _ => hterm ρ)
      _ = ∑ ρ ∈ W, multiplicity ρ * (f b - f (ordinate ρ)) :=
        Finset.sum_congr rfl hterm_eval
      _ = _ := by simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  change _ = f b * (Ncount a b : ℝ) - ∫ t in Ioc a b, deriv f t * Q t
  rw [hI, Ncount_eq_sum_zeroWindow]
  change (∑ ρ ∈ W, multiplicity ρ * f (ordinate ρ)) =
    f b * (∑ ρ ∈ W, multiplicity ρ) -
      ((∑ ρ ∈ W, multiplicity ρ) * f b - ∑ ρ ∈ W, multiplicity ρ * f (ordinate ρ))
  ring

end GoldbachExplicit
