import Goldbach.Coefficient
import Goldbach.LocalSpectrum

open Filter
open scoped BigOperators

noncomputable section
namespace GoldbachSpectrum

private theorem log_sq_weight_le (n : ℤ) (hn : n ≠ 0) :
    (Real.log (|(n : ℝ)| + 3))^2 / (1 + (n : ℝ)^2)
      ≤ 256 * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  let z := |(n : ℝ)|
  have hz₁ : 1 ≤ z := by dsimp [z]; exact_mod_cast Int.one_le_abs hn
  have hz : 0 < z := zero_lt_one.trans_le hz₁
  have hlog₀ : 0 ≤ Real.log (z + 3) := Real.log_nonneg (by linarith)
  have hlog : Real.log (z + 3) ≤ 16 * z^((1 : ℝ) / 4) := by
    have hpow : (z + 3)^((1 : ℝ) / 4) ≤ (4 * z)^((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have h4 : (4 : ℝ)^((1 : ℝ) / 4) ≤ 4 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
        (by norm_num : (1 : ℝ) / 4 ≤ 1)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hz.le] at hpow
    calc
      _ ≤ (z + 3)^((1 : ℝ) / 4) / (1 / 4) :=
        Real.log_le_rpow_div (by positivity) (by norm_num)
      _ ≤ (4 * z^((1 : ℝ) / 4)) / (1 / 4) := by
        exact div_le_div_of_nonneg_right
          (hpow.trans (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hz.le _))) (by norm_num)
      _ = _ := by ring
  have hsquare : (Real.log (z + 3))^2 ≤ 256 * z^((1 : ℝ) / 2) := by
    calc
      _ ≤ (16 * z^((1 : ℝ) / 4))^2 := pow_le_pow_left₀ hlog₀ hlog _
      _ = _ := by
        rw [mul_pow, show (1 / 2 : ℝ) = (1 / 4 : ℝ) * (2 : ℕ) by norm_num,
          Real.rpow_mul hz.le, Real.rpow_natCast]
        norm_num
  have hinv : 1 / (1 + (n : ℝ)^2) ≤ z ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hz.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, show z^2 = (n : ℝ)^2 by exact sq_abs _, one_div]
    exact inv_anti₀ (by positivity) (by linarith)
  calc
    _ = (Real.log (z + 3))^2 * (1 / (1 + (n : ℝ)^2)) := by dsimp [z]; ring
    _ ≤ (256 * z^((1 : ℝ) / 2)) * z^(-2 : ℝ) :=
      mul_le_mul hsquare hinv (by positivity) (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hz]; norm_num [z]

private theorem summable_log_sq_weight :
    Summable (fun n : ℤ => (Real.log (|(n : ℝ)| + 3))^2 / (1 + (n : ℝ)^2)) := by
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow (show (1 : ℝ) < 3 / 2 by norm_num)).mul_left 256) ?_
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact log_sq_weight_le n hn

/-- The local zero count allows one extra logarithm in the reciprocal
quadratic summability bound. -/
theorem summable_log_over_ordinates :
    Summable (fun ρ : GoldbachZeros.Zeros =>
      GoldbachZeros.multiplicity ρ * Real.log (|GoldbachZeros.ordinate ρ| + 3) /
        (1 + (GoldbachZeros.ordinate ρ)^2)) := by
  classical
  obtain ⟨A, hA, hlocal⟩ := GoldbachZeros.riemannVonMangoldt.local_count
  have hA₀ := zero_le_one.trans hA
  have hLC := Zeta23.Tail.LocalCount.ofWindowCount Zeta23.zetaZeroConfig hA hlocal
  let w := fun n : ℤ => (Real.log (|(n : ℝ)| + 3))^2 / (1 + (n : ℝ)^2)
  let f := fun ρ : GoldbachZeros.Zeros =>
    GoldbachZeros.multiplicity ρ * Real.log (|GoldbachZeros.ordinate ρ| + 3) /
      (1 + (GoldbachZeros.ordinate ρ)^2)
  let key := fun ρ : GoldbachZeros.Zeros => Zeta23.WeilEF.key (GoldbachZeros.ordinate ρ)
  have hf (ρ : GoldbachZeros.Zeros) : 0 ≤ f ρ := by
    dsimp [f]
    exact div_nonneg (mul_nonneg (GoldbachZeros.multiplicity_nonneg _)
      (Real.log_nonneg (by linarith [abs_nonneg (GoldbachZeros.ordinate ρ)]))) (by positivity)
  refine summable_of_sum_le (c := (8 * A) * ∑' n, w n) hf (fun s => ?_)
  rw [← Finset.sum_fiberwise_of_maps_to (g := key) (t := s.image key)
    (fun ρ hρ => Finset.mem_image_of_mem key hρ)]
  have hwin (n : ℤ) (ρ : GoldbachZeros.Zeros) (hρ : ρ ∈ s.filter (fun ρ => key ρ = n)) :
      (n : ℝ) < GoldbachZeros.ordinate ρ ∧ GoldbachZeros.ordinate ρ ≤ (n : ℝ) + 1 := by
    have hn : Zeta23.WeilEF.key (GoldbachZeros.ordinate ρ) = n := (Finset.mem_filter.mp hρ).2
    rw [← hn]
    exact ⟨Zeta23.WeilEF.key_lt _, Zeta23.WeilEF.le_key_add_one _⟩
  have hpoint (n : ℤ) (ρ : GoldbachZeros.Zeros) (hρ : ρ ∈ s.filter (fun ρ => key ρ = n)) :
      f ρ ≤ (8 * Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ)^2)) * GoldbachZeros.multiplicity ρ := by
    let y := GoldbachZeros.ordinate ρ
    obtain ⟨h₁, h₂⟩ := hwin n ρ hρ
    have hm := GoldbachZeros.multiplicity_nonneg ρ
    have hdiff : |y - (n : ℝ)| ≤ 1 := by
      apply abs_le.mpr
      change (n : ℝ) < y at h₁
      change y ≤ (n : ℝ) + 1 at h₂
      constructor <;> linarith
    have habs : |y| ≤ |(n : ℝ)| + 1 := by
      have h := abs_add_le (n : ℝ) (y - (n : ℝ))
      rw [add_sub_cancel] at h
      linarith
    have hL : Real.log (|y| + 3) ≤ 2 * Real.log (|(n : ℝ)| + 3) := by
      have hb : |y| + 3 ≤ (|(n : ℝ)| + 3)^2 := by
        nlinarith [habs, abs_nonneg (n : ℝ), sq_nonneg |(n : ℝ)|]
      exact (Real.log_le_log (by positivity) hb).trans_eq (by rw [Real.log_pow]; norm_num)
    have hq := Zeta23.WeilEF.one_add_sq_ge h₁ h₂
    have hinv : 1 / (1 + y^2) ≤ 4 / (1 + (n : ℝ)^2) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by dsimp [y]; linarith)
    calc
      f ρ = GoldbachZeros.multiplicity ρ * (Real.log (|y| + 3) * (1 / (1 + y^2))) := by
        dsimp [f, y]; ring
      _ ≤ GoldbachZeros.multiplicity ρ * ((2 * Real.log (|(n : ℝ)| + 3)) * (4 / (1 + (n : ℝ)^2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hL hinv (by positivity)
            (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])))) hm
      _ = _ := by ring
  have hsum (n : ℤ) :
      (∑ ρ ∈ s with key ρ = n, f ρ) ≤ (8 * A) * w n := by
    have hcount := hLC.window n (s.filter (fun ρ => key ρ = n)) (hwin n)
    calc
      _ ≤ ∑ ρ ∈ s with key ρ = n,
          (8 * Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ)^2)) * GoldbachZeros.multiplicity ρ :=
        Finset.sum_le_sum (hpoint n)
      _ = (8 * Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ)^2)) *
          ∑ ρ ∈ s with key ρ = n, GoldbachZeros.multiplicity ρ := by rw [Finset.mul_sum]
      _ ≤ (8 * Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ)^2)) *
          (A * Real.log (|(n : ℝ)| + 3)) :=
        mul_le_mul_of_nonneg_left hcount
          (div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])))
            (by positivity))
      _ = _ := by dsimp [w]; ring
  calc
    _ ≤ ∑ n ∈ s.image key, (8 * A) * w n := Finset.sum_le_sum (fun n _ => hsum n)
    _ = (8 * A) * ∑ n ∈ s.image key, w n := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (summable_log_sq_weight.sum_le_tsum _ (fun n _ => by dsimp [w]; positivity)) (by positivity)

theorem coefficient_sq_le {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (γ : ℝ) :
    ‖coefficient lam γ‖^2 ≤ (Real.exp 1 + (1 + Real.exp (1 / 2))^2) / (1 + γ^2) := by
  have hnorm : ‖coefficient lam γ‖^2 ≤ Real.exp 1 := by
    rw [coefficient_sq_scale hlam₀]
    have hsq : lam^2 ≤ 1 := by nlinarith [mul_nonneg hlam₀ (sub_nonneg.mpr hlam₁)]
    exact (mul_le_mul_of_nonneg_left (profile_le_exp_one hlam₀ hlam₁ _) (sq_nonneg _)).trans
      (mul_le_of_le_one_left (Real.exp_pos _).le hsq)
  have htail : γ^2 * ‖coefficient lam γ‖^2 ≤ (1 + Real.exp (1 / 2))^2 := by
    rw [coefficient_sq_scale hlam₀]
    convert sq_mul_profile_le hlam₀ hlam₁ (lam * γ) using 1
    ring
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [hnorm, htail]

/-- The full Schur diagonal is a genuine summable series for every
fixed coefficient width in the range used in the manuscript. -/
theorem diagonalEnergy_summable {b lam : ℝ} (hb : 0 < b) (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) :
    Summable (diagonalEnergy b (fun ρ => coefficient lam (GoldbachZeros.ordinate ρ))) := by
  obtain ⟨C, hC, hrow⟩ := GoldbachZeros.row_summable_and_bound hb
  let D := Real.exp 1 + (1 + Real.exp (1 / 2))^2
  refine Summable.of_norm_bounded (summable_log_over_ordinates.mul_left (C * D)) (fun ρ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (energy_nonneg _ _ _)]
  let y := GoldbachZeros.ordinate ρ
  let m := GoldbachZeros.multiplicity ρ
  have hm := GoldbachZeros.multiplicity_nonneg ρ
  have hlog : 0 ≤ Real.log (|y| + 3) := Real.log_nonneg (by linarith [abs_nonneg y])
  have hcap := coefficient_sq_le hlam₀ hlam₁ y
  calc
    _ = m * (‖coefficient lam y‖^2 * GoldbachZeros.row b y) := by dsimp [diagonalEnergy, m, y]; ring
    _ ≤ m * ((D / (1 + y^2)) * (C * Real.log (|y| + 3))) := by
      apply mul_le_mul_of_nonneg_left _ hm
      exact mul_le_mul hcap (hrow y).2
        (tsum_nonneg (fun ρ' => mul_nonneg (GoldbachZeros.multiplicity_nonneg _)
          (GoldbachGaussian.kernel_nonneg _ _))) (by dsimp [D]; positivity)
    _ = _ := by dsimp [m, y]; ring

end GoldbachSpectrum
