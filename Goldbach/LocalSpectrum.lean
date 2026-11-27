import Goldbach.FiniteSpectrum
import Goldbach.Zeros

open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section
namespace GoldbachSpectrum

private theorem zero_cutoff_finite (T : ℝ) :
    {ρ : GoldbachZeros.Zeros | |GoldbachZeros.ordinate ρ| ≤ T}.Finite := by
  have h := Zeta23.zetaZeroConfig.finite_window (-T - 1) T
  refine (h.preimage (f := Subtype.val) Subtype.val_injective.injOn).subset ?_
  intro ρ hρ
  change |GoldbachZeros.ordinate ρ| ≤ T at hρ
  have h₁ := (abs_le.mp hρ).1
  have h₂ := (abs_le.mp hρ).2
  exact ⟨ρ.property, (by change -T - 1 < GoldbachZeros.ordinate ρ; linarith), h₂⟩

/-- Symmetric height truncation. A zero with ordinate exactly `-T`
or `T` is included with its multiplicity in the associated sum. -/
def zerosUpTo (T : ℝ) : Finset GoldbachZeros.Zeros :=
  (zero_cutoff_finite T).toFinset

@[simp] theorem mem_zerosUpTo (T : ℝ) (ρ : GoldbachZeros.Zeros) :
    ρ ∈ zerosUpTo T ↔ |GoldbachZeros.ordinate ρ| ≤ T := by
  rw [zerosUpTo, Set.Finite.mem_toFinset]
  rfl

def partialSum (a : GoldbachZeros.Zeros → ℂ) (T u : ℝ) : ℂ :=
  ∑ ρ ∈ zerosUpTo T, (GoldbachZeros.multiplicity ρ : ℂ) * a ρ *
    GoldbachGaussian.wave (GoldbachZeros.ordinate ρ) u

def diagonalEnergy (b : ℝ) (a : GoldbachZeros.Zeros → ℂ)
    (ρ : GoldbachZeros.Zeros) : ℝ :=
  GoldbachZeros.multiplicity ρ * ‖a ρ‖^2 * GoldbachZeros.row b (GoldbachZeros.ordinate ρ)

theorem energy_nonneg (b : ℝ) (a : GoldbachZeros.Zeros → ℂ) (ρ : GoldbachZeros.Zeros) :
    0 ≤ diagonalEnergy b a ρ := by
  unfold diagonalEnergy GoldbachZeros.row
  exact mul_nonneg (mul_nonneg (GoldbachZeros.multiplicity_nonneg _) (sq_nonneg _))
    (tsum_nonneg fun z => mul_nonneg (GoldbachZeros.multiplicity_nonneg _)
      (GoldbachGaussian.kernel_nonneg _ _))

private theorem finite_subset_mean_square {b : ℝ} (hb : 0 < b) (z : ℝ)
    (s : Finset GoldbachZeros.Zeros) (a : GoldbachZeros.Zeros → ℂ) :
    (∫ u, GoldbachGaussian.weight b (u - z) *
      ‖∑ ρ ∈ s, (GoldbachZeros.multiplicity ρ : ℂ) * a ρ *
        GoldbachGaussian.wave (GoldbachZeros.ordinate ρ) u‖^2) ≤
      ∑ ρ ∈ s, diagonalEnergy b a ρ := by
  obtain ⟨_, _, hrow⟩ := GoldbachZeros.row_summable_and_bound hb
  apply (GoldbachGaussian.integral_norm_sq_le_schur s hb z
    GoldbachZeros.ordinate GoldbachZeros.multiplicity a GoldbachZeros.multiplicity_nonneg).trans
  apply Finset.sum_le_sum
  intro ρ _
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (GoldbachZeros.multiplicity_nonneg _) (sq_nonneg _))
  exact (hrow (GoldbachZeros.ordinate ρ)).1.sum_le_tsum _
    (fun ρ' _ => mul_nonneg (GoldbachZeros.multiplicity_nonneg _)
      (GoldbachGaussian.kernel_nonneg _ _))

theorem finite_zero_sum_mean_square {b : ℝ} (hb : 0 < b) (z T : ℝ)
    (a : GoldbachZeros.Zeros → ℂ) :
    (∫ u, GoldbachGaussian.weight b (u - z) * ‖partialSum a T u‖ ^ 2) ≤
      ∑ ρ ∈ zerosUpTo T, diagonalEnergy b a ρ :=
  finite_subset_mean_square hb z (zerosUpTo T) a

private theorem zerosUpTo_mono : Monotone zerosUpTo := by
  intro T U hTU ρ hρ
  exact (mem_zerosUpTo U ρ).mpr (((mem_zerosUpTo T ρ).mp hρ).trans hTU)

/-- The mean square of a difference of symmetric truncations is bounded by
the diagonal energy on just the newly included zeros. -/
theorem partialSum_sub_mean_square {b : ℝ} (hb : 0 < b) (z : ℝ)
    {T U : ℝ} (hTU : T ≤ U) (a : GoldbachZeros.Zeros → ℂ) :
    (∫ u, GoldbachGaussian.weight b (u - z) * ‖partialSum a U u - partialSum a T u‖^2) ≤
      ∑ ρ ∈ zerosUpTo U \ zerosUpTo T, diagonalEnergy b a ρ := by
  classical
  have he (u : ℝ) : partialSum a U u - partialSum a T u =
      ∑ ρ ∈ zerosUpTo U \ zerosUpTo T, (GoldbachZeros.multiplicity ρ : ℂ) * a ρ *
        GoldbachGaussian.wave (GoldbachZeros.ordinate ρ) u := by
    unfold partialSum
    exact (eq_sub_of_add_eq (Finset.sum_sdiff (zerosUpTo_mono hTU))).symm
  simp_rw [he]
  exact finite_subset_mean_square hb z _ a

theorem zerosUpTo_tendsto_atTop : Tendsto zerosUpTo atTop atTop := by
  apply tendsto_atTop.mpr
  intro s
  filter_upwards [eventually_ge_atTop (∑ ρ ∈ s, |GoldbachZeros.ordinate ρ|)] with T hT
  intro ρ hρ
  apply (mem_zerosUpTo T ρ).mpr
  exact (Finset.single_le_sum (fun _ _ => abs_nonneg _) hρ).trans hT

/-- A summable diagonal controls the full tails in Gaussian weighted mean
square, independently of any explicit formula for the limit. -/
theorem eventually_partialSum_sub_mean_square_le {b : ℝ} (hb : 0 < b) (z : ℝ)
    (a : GoldbachZeros.Zeros → ℂ) (hE : Summable (diagonalEnergy b a))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ U : ℝ, T ≤ U →
      (∫ u, GoldbachGaussian.weight b (u - z) * ‖partialSum a U u - partialSum a T u‖^2) ≤ ε := by
  classical
  have hS : Tendsto (fun T : ℝ => ∑ ρ ∈ zerosUpTo T, diagonalEnergy b a ρ) atTop
      (𝓝 (∑' ρ, diagonalEnergy b a ρ)) := hE.hasSum.comp zerosUpTo_tendsto_atTop
  let B := ∑' ρ, diagonalEnergy b a ρ
  filter_upwards [hS.eventually (lt_mem_nhds (show B - ε < B by linarith))] with T hT
  intro U hTU
  calc
    _ ≤ ∑ ρ ∈ zerosUpTo U \ zerosUpTo T, diagonalEnergy b a ρ :=
      partialSum_sub_mean_square hb z hTU a
    _ = (∑ ρ ∈ zerosUpTo U, diagonalEnergy b a ρ) -
        (∑ ρ ∈ zerosUpTo T, diagonalEnergy b a ρ) :=
      eq_sub_of_add_eq (Finset.sum_sdiff (zerosUpTo_mono hTU))
    _ ≤ B - (∑ ρ ∈ zerosUpTo T, diagonalEnergy b a ρ) :=
      sub_le_sub_right (hE.sum_le_tsum _ (fun ρ _ => energy_nonneg b a ρ)) _
    _ ≤ ε := by linarith

private theorem integrable_finite_weighted_square {b : ℝ} (hb : 0 < b) (z T : ℝ)
    (a : GoldbachZeros.Zeros → ℂ) :
    Integrable (fun u => GoldbachGaussian.weight b (u - z) * ‖partialSum a T u‖^2) := by
  let A := ∑ ρ ∈ zerosUpTo T, ‖(GoldbachZeros.multiplicity ρ : ℂ) * a ρ‖
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hbound (u : ℝ) : ‖partialSum a T u‖ ≤ A := by
    unfold partialSum
    apply (norm_sum_le _ _).trans_eq
    simp [A]
  refine (((GoldbachGaussian.integrable_weight hb).comp_sub_right z).mul_const (A^2)).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold GoldbachGaussian.weight partialSum GoldbachGaussian.wave
    fun_prop
  · filter_upwards with u
    have hw : 0 ≤ GoldbachGaussian.weight b (u - z) := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound u) _) hw

/-- Fatou's lemma for the Gaussian-weighted square. If a local almost
everywhere explicit formula identifies `F`, its mean square is bounded
by the summable diagonal energy. -/
theorem local_mean_square_of_ae_limit {b : ℝ} (hb : 0 < b) (z : ℝ) (J : Set ℝ)
    (a : GoldbachZeros.Zeros → ℂ) (F : ℝ → ℂ)
    (hE : Summable (diagonalEnergy b a))
    (hF : IntegrableOn (fun u => GoldbachGaussian.weight b (u - z) * ‖F u‖^2) J)
    (hlim : ∀ᵐ u ∂volume.restrict J, Tendsto
      (fun n : ℕ => partialSum a n u) atTop (𝓝 (F u))) :
    (∫ u in J, GoldbachGaussian.weight b (u - z) * ‖F u‖^2) ≤ ∑' ρ, diagonalEnergy b a ρ := by
  let μ : Measure ℝ := volume.restrict J
  let B := ∑' ρ, diagonalEnergy b a ρ
  let Q := fun (n : ℕ) u => GoldbachGaussian.weight b (u - z) * ‖partialSum a n u‖^2
  let L := fun u => GoldbachGaussian.weight b (u - z) * ‖F u‖^2
  have hB : 0 ≤ B := tsum_nonneg (energy_nonneg b a)
  have hnn (n : ℕ) (u : ℝ) : 0 ≤ Q n u := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hLn (u : ℝ) : 0 ≤ L u := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hi (n : ℕ) : Integrable (Q n) := integrable_finite_weighted_square hb z n a
  have hiJ (n : ℕ) : Integrable (Q n) μ := (hi n).integrableOn
  have hBnd (n : ℕ) : (∫ u, Q n u ∂μ) ≤ B := by
    calc
      _ ≤ ∫ u, Q n u := integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall (hnn n)) (hi n)
      _ ≤ ∑ ρ ∈ zerosUpTo n, diagonalEnergy b a ρ := finite_zero_sum_mean_square hb z n a
      _ ≤ B := hE.sum_le_tsum _ (fun ρ _ => energy_nonneg b a ρ)
  have hlim' : ∀ᵐ u ∂μ,
      Tendsto (fun n => ENNReal.ofReal (Q n u)) atTop (𝓝 (ENNReal.ofReal (L u))) := by
    filter_upwards [hlim] with u hu
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((hu.norm.pow 2).const_mul _)
  have hle : (∫⁻ u, ENNReal.ofReal (L u) ∂μ) ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ u, liminf (fun n : ℕ => ENNReal.ofReal (Q n u)) atTop ∂μ :=
        lintegral_congr_ae (hlim'.mono (fun _ h => h.liminf_eq.symm))
      _ ≤ liminf (fun n : ℕ => ∫⁻ u, ENNReal.ofReal (Q n u) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hiJ n).aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal B := by
        apply liminf_le_of_frequently_le'
        apply Frequently.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hiJ n) (Filter.Eventually.of_forall (hnn n))]
        exact ENNReal.ofReal_le_ofReal (hBnd n)
  rw [← ofReal_integral_eq_lintegral_ofReal hF (Filter.Eventually.of_forall hLn)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hle

end GoldbachSpectrum
