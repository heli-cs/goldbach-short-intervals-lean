import Goldbach.Gaussian
import Zeta23.GammaFacts.Complete
import Zeta23.RvM.Statement
import Zeta23.WeilEF.Main

open Zeta23
open scoped BigOperators ComplexConjugate

noncomputable section
namespace GoldbachZeros

/-- The carrier consists of distinct nontrivial zeros. Each sum below
uses the analytic multiplicity as a weight. -/
abbrev Zeros := zetaZeroConfig.carrier

def ordinate (ρ : Zeros) : ℝ := (ρ : ℂ).im

def multiplicity (ρ : Zeros) : ℝ := zetaZeroConfig.mult ρ

theorem multiplicity_nonneg (ρ : Zeros) : 0 ≤ multiplicity ρ := Nat.cast_nonneg _

theorem gammaOf_eq_ordinate (hRH : RiemannHypothesis) (ρ : Zeros) :
    gammaOf (ρ : ℂ) = (ordinate ρ : ℂ) := by
  have hr : (ρ : ℂ).re = 1 / 2 := RH_implies_on_line hRH ρ.property
  apply Complex.ext
  · simp [WeilEF.gammaOf_re, ordinate]
  · simp [WeilEF.gammaOf_im, hr]

theorem riemannVonMangoldt : RiemannVonMangoldt zetaZeroConfig :=
  RvM.riemannVonMangoldt gammaFacts

/-- Smooth Weil explicit formula on the actual zeta zeros. The RH
specialization uses their real ordinates and retains analytic multiplicities. -/
theorem weil_explicit_on_line (hRH : RiemannHypothesis) (k : ℝ → ℂ)
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : Zeros => (multiplicity ρ : ℂ) * paperFT k (ordinate ρ)) ∧
      ∑' ρ : Zeros, (multiplicity ρ : ℂ) * paperFT k (ordinate ρ) = EF.literatureRHS k := by
  have h := WeilEF.EF_lit_zetaZeroConfig k hk hkc
  have heq (ρ : Zeros) :
      (zetaZeroConfig.mult (ρ : ℂ) : ℂ) * paperFT k (gammaOf (ρ : ℂ)) =
        (multiplicity ρ : ℂ) * paperFT k (ordinate ρ) := by
    rw [gammaOf_eq_ordinate hRH ρ]
    simp [multiplicity]
  exact ⟨h.1.congr heq, (tsum_congr heq).symm.trans h.2⟩

def row (b t : ℝ) : ℝ :=
  ∑' ρ : Zeros, multiplicity ρ * GoldbachGaussian.kernel b (t - ordinate ρ)

private theorem log_window_le (t n : ℝ) :
    Real.log (|t + n| + 3) ≤
      (2 / Real.log 3) * (Real.log (|t| + 3) * Real.log (|n| + 3)) := by
  have ht : 0 < |t| + 3 := by positivity
  have hn : 0 < |n| + 3 := by positivity
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have htL := Real.log_le_log (show (0 : ℝ) < 3 by norm_num)
    (show (3 : ℝ) ≤ |t| + 3 by linarith [abs_nonneg t])
  have hnL := Real.log_le_log (show (0 : ℝ) < 3 by norm_num)
    (show (3 : ℝ) ≤ |n| + 3 by linarith [abs_nonneg n])
  have hmul : |t + n| + 3 ≤ (|t| + 3) * (|n| + 3) := by
    nlinarith [abs_add_le t n, abs_nonneg t, abs_nonneg n, mul_nonneg (abs_nonneg t) (abs_nonneg n)]
  calc
    _ ≤ Real.log ((|t| + 3) * (|n| + 3)) :=
      Real.log_le_log (by positivity) hmul
    _ = Real.log (|t| + 3) + Real.log (|n| + 3) := Real.log_mul ht.ne' hn.ne'
    _ ≤ (Real.log (|t| + 3) * Real.log (|n| + 3) +
        Real.log (|t| + 3) * Real.log (|n| + 3)) / Real.log 3 := by
      apply (le_div_iff₀ hL).mpr
      nlinarith [mul_le_mul_of_nonneg_left htL (hL.le.trans hnL),
        mul_le_mul_of_nonneg_left hnL (hL.le.trans htL)]
    _ = _ := by ring

/-- Absolute summability and a uniform logarithmic row bound follow from the
two-sided unit-window count. This applies even without RH. -/
theorem row_summable_and_bound {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      Summable (fun ρ : Zeros => multiplicity ρ * GoldbachGaussian.kernel b (t - ordinate ρ)) ∧
        row b t ≤ C * Real.log (|t| + 3) := by
  classical
  obtain ⟨A, hA, hlocal⟩ := riemannVonMangoldt.local_count
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hLC := Tail.LocalCount.ofWindowCount zetaZeroConfig hA hlocal
  let B := Real.sqrt (Real.pi / b) * max 1 (4 * b)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let w := fun n : ℤ => Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)
  have hw : Summable w := WeilEF.summable_weight
  have hw₀ (n : ℤ) : 0 ≤ w n :=
    div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)
  let D : ℝ := 4 * B * A * (2 / Real.log 3)
  have hD : 0 ≤ D := by
    have : 0 < Real.log 3 := Real.log_pos (by norm_num)
    dsimp [D]
    positivity
  refine ⟨D * ∑' n, w n, mul_nonneg hD (tsum_nonneg hw₀), fun t => ?_⟩
  let key : Zeros → ℤ := fun ρ => WeilEF.key (ordinate ρ - t)
  let f : Zeros → ℝ := fun ρ => multiplicity ρ * GoldbachGaussian.kernel b (t - ordinate ρ)
  have hf₀ (ρ : Zeros) : 0 ≤ f ρ :=
    mul_nonneg (multiplicity_nonneg ρ) (GoldbachGaussian.kernel_nonneg _ _)
  have hlog : 0 ≤ Real.log (|t| + 3) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  have hfin (s : Finset Zeros) :
      (∑ ρ ∈ s, f ρ) ≤ (D * ∑' n, w n) * Real.log (|t| + 3) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := key) (t := s.image key)
      (fun ρ hρ => Finset.mem_image_of_mem key hρ)]
    have hfiber (n : ℤ) :
        (∑ ρ ∈ s with key ρ = n, f ρ) ≤ D * Real.log (|t| + 3) * w n := by
      have hwin (ρ : Zeros) (hρ : ρ ∈ s.filter (fun ρ => key ρ = n)) :
          (n : ℝ) < ordinate ρ - t ∧ ordinate ρ - t ≤ (n : ℝ) + 1 := by
        have hn : WeilEF.key (ordinate ρ - t) = n := (Finset.mem_filter.mp hρ).2
        rw [← hn]
        exact ⟨WeilEF.key_lt _, WeilEF.le_key_add_one _⟩
      have hcnt := hLC.window (t + (n : ℝ)) (s.filter (fun ρ => key ρ = n))
        (fun ρ hρ => by
          obtain ⟨h₁, h₂⟩ := hwin ρ hρ
          change t + (n : ℝ) < ordinate ρ ∧ ordinate ρ ≤ t + (n : ℝ) + 1
          exact ⟨by linarith, by linarith⟩)
      have hpt (ρ : Zeros) (hρ : ρ ∈ s.filter (fun ρ => key ρ = n)) :
          f ρ ≤ (4 * B / (1 + (n : ℝ) ^ 2)) * multiplicity ρ := by
        obtain ⟨h₁, h₂⟩ := hwin ρ hρ
        have hq := WeilEF.one_add_sq_ge h₁ h₂
        have hk := GoldbachGaussian.kernel_le_inv_sq hb (t - ordinate ρ)
        have hbound : B / (1 + (t - ordinate ρ) ^ 2) ≤ 4 * B / (1 + (n : ℝ) ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hq' : 1 + (n : ℝ) ^ 2 ≤ 4 * (1 + (t - ordinate ρ) ^ 2) := by nlinarith
          nlinarith only [mul_le_mul_of_nonneg_left hq' hB]
        calc
          f ρ ≤ multiplicity ρ * (B / (1 + (t - ordinate ρ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hk (multiplicity_nonneg ρ)
          _ ≤ multiplicity ρ * (4 * B / (1 + (n : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hbound (multiplicity_nonneg ρ)
          _ = _ := mul_comm _ _
      calc
        _ ≤ ∑ ρ ∈ s with key ρ = n, (4 * B / (1 + (n : ℝ) ^ 2)) * multiplicity ρ :=
          Finset.sum_le_sum hpt
        _ = (4 * B / (1 + (n : ℝ) ^ 2)) * ∑ ρ ∈ s with key ρ = n, multiplicity ρ := by
          rw [Finset.mul_sum]
        _ ≤ (4 * B / (1 + (n : ℝ) ^ 2)) * (A * Real.log (|t + (n : ℝ)| + 3)) :=
          mul_le_mul_of_nonneg_left hcnt (by positivity)
        _ ≤ (4 * B / (1 + (n : ℝ) ^ 2)) *
            (A * ((2 / Real.log 3) * (Real.log (|t| + 3) * Real.log (|(n : ℝ)| + 3)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (log_window_le _ _) hA0) (by positivity)
        _ = _ := by dsimp [D, w]; ring
    calc
      _ ≤ ∑ n ∈ s.image key, D * Real.log (|t| + 3) * w n :=
        Finset.sum_le_sum (fun n _ => hfiber n)
      _ = (D * Real.log (|t| + 3)) * ∑ n ∈ s.image key, w n := by rw [Finset.mul_sum]
      _ ≤ (D * Real.log (|t| + 3)) * ∑' n, w n :=
        mul_le_mul_of_nonneg_left (hw.sum_le_tsum _ (fun n _ => hw₀ n)) (mul_nonneg hD hlog)
      _ = _ := by ring
  have hf : Summable f := summable_of_sum_le hf₀ hfin
  exact ⟨hf, hf.tsum_le_of_sum_le hfin⟩


private theorem zero_ne_one (ρ : Zeros) : (ρ : ℂ) ≠ 1 := by
  intro h
  have hr := ρ.property.2.2
  rw [h, Complex.one_re] at hr
  exact lt_irrefl _ hr

private def conjZero (ρ : Zeros) : Zeros := by
  refine ⟨conj (ρ : ℂ), ?_⟩
  change Zeta23.IsNontrivialZero (conj (ρ : ℂ))
  obtain ⟨hzero, hlo, hhi⟩ := ρ.property
  refine ⟨?_, ?_, ?_⟩
  · rw [Zeta23.riemannZeta_conj (zero_ne_one ρ), hzero, map_zero]
  · simpa only [Complex.conj_re] using hlo
  · simpa only [Complex.conj_re] using hhi

/-- Conjugation reverses the ordinate and preserves the analytic weight. -/
def conjugation : Zeros ≃ Zeros where
  toFun := conjZero
  invFun := conjZero
  left_inv ρ := Subtype.ext (Complex.conj_conj (ρ : ℂ))
  right_inv ρ := Subtype.ext (Complex.conj_conj (ρ : ℂ))

@[simp] theorem ordinate_conjugation (ρ : Zeros) :
    ordinate (conjugation ρ) = -ordinate ρ := Complex.conj_im _

@[simp] theorem multiplicity_conjugation (ρ : Zeros) :
    multiplicity (conjugation ρ) = multiplicity ρ := by
  change ((analyticOrderAt riemannZeta (conj (ρ : ℂ))).toNat : ℝ) =
    ((analyticOrderAt riemannZeta (ρ : ℂ)).toNat : ℝ)
  rw [Zeta23.analyticOrderAt_zeta_conj (zero_ne_one ρ)]

theorem row_even (b t : ℝ) : row b (-t) = row b t := by
  unfold row
  rw [← conjugation.tsum_eq (fun ρ => multiplicity ρ * GoldbachGaussian.kernel b (-t - ordinate ρ))]
  apply tsum_congr
  intro ρ
  rw [multiplicity_conjugation, ordinate_conjugation,
    show -t - -ordinate ρ = -(t - ordinate ρ) by ring, GoldbachGaussian.kernel_even]

end GoldbachZeros
