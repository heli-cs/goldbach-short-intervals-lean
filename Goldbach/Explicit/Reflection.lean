import Goldbach.Explicit.CosineKernel
import Goldbach.Moments

/-! Symmetric reflection for the explicit compact weight. -/

open MeasureTheory Set
noncomputable section

namespace GoldbachExplicit

open GoldbachConcrete

def upperWeight (V x y : ℝ) : ℝ :=
  cosineWeight V (Real.log (x / y))

def reflectedWeight (V x y : ℝ) : ℝ :=
  upperWeight V x (min y (x - y))

theorem reflectedWeight_reflect (V x y : ℝ) :
    reflectedWeight V x (x - y) = reflectedWeight V x y := by
  unfold reflectedWeight
  rw [show x - (x - y) = y by ring, min_comm (x - y) y]

private theorem cosineWeight_antitone_nonneg {V : ℝ} (hV : 0 < V) :
    AntitoneOn (cosineWeight V) (Ici 0) := by
  intro s hs t ht hst
  by_cases h : t ≤ V
  · exact cosineWeight_antitoneOn hV ⟨hs, hst.trans h⟩ ⟨ht, h⟩ hst
  · have ht' : V < |t| := by rw [abs_of_nonneg ht]; exact lt_of_not_ge h
    rw [cosineWeight_zero_of_lt_abs ht']
    exact cosineWeight_nonneg hV _

theorem reflectedWeight_le_upperWeight {V x A y : ℝ} (hV : 0 < V)
    (hA : 0 < A) (hy : y ∈ Icc A (x - A)) :
    reflectedWeight V x y ≤ upperWeight V x y := by
  have hy₀ : 0 < y := hA.trans_le hy.1
  have hxy : 0 < x - y := by linarith [hy.2]
  have hx : 0 < x := by linarith
  have hm : 0 < min y (x - y) := lt_min hy₀ hxy
  have hlog : 0 ≤ Real.log (x / y) :=
    Real.log_nonneg ((one_le_div hy₀).mpr (by linarith))
  have hle : Real.log (x / y) ≤ Real.log (x / min y (x - y)) :=
    Real.log_le_log (div_pos hx hy₀) (div_le_div_of_nonneg_left hx.le hm (min_le_left _ _))
  exact cosineWeight_antitone_nonneg hV (mem_Ici.mpr hlog)
    (mem_Ici.mpr (hlog.trans hle)) hle

private theorem integrable_mul_weight {f w : ℝ → ℝ} {a b : ℝ}
    (hf : IntegrableOn f (Icc a b)) (hw : Measurable w)
    (hb : ∀ x ∈ Icc a b, w x ∈ Icc (0 : ℝ) 1) :
    IntegrableOn (fun x => w x * f x) (Icc a b) := by
  refine hf.norm.mono' (hw.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with y hy
  rw [norm_mul, Real.norm_eq_abs (w y), abs_of_nonneg (hb y hy).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb y hy).2

private theorem preserve_reflection (x A : ℝ) :
    MeasurePreserving (fun y : ℝ => x - y) (volume.restrict (Icc A (x - A)))
      (volume.restrict (Icc A (x - A))) := by
  have hpre : (fun y : ℝ => x - y) ⁻¹' Icc A (x - A) = Icc A (x - A) := by
    ext y
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simpa only [hpre] using (volume.measurePreserving_sub_left x).restrict_preimage
    (s := Icc A (x - A)) measurableSet_Icc

/-- The compact-weight reflection lower bound when the target interval is Goldbach-free. -/
theorem weighted_reflection_of_no_goldbach {V x A d : ℝ}
    (hV : 0 < V) (hA : 0 < A) (hd : 0 < d) (hn : ¬ HasGoldbach x (d * x)) :
    2 * (∫ y in Icc A (x - A), reflectedWeight V x y * density d y) -
      (∫ y in Icc A (x - A), reflectedWeight V x y) ≤
      ∫ y in Icc A (x - A), upperWeight V x y * (density d y - 1)^2 := by
  let J := Icc A (x - A)
  let μ := volume.restrict J
  let r (y : ℝ) := x - y
  let w := reflectedWeight V x
  let W := upperWeight V x
  let F := density d
  have hr : MeasurePreserving r μ μ := preserve_reflection x A
  have hre : MeasurableEmbedding r := (Homeomorph.subLeft x).measurableEmbedding
  have hW : Measurable W := by
    change Measurable (fun y : ℝ => cosineWeight V (Real.log (x / y)))
    exact (continuous_cosineWeight hV).measurable.comp (measurable_const.div measurable_id).log
  have hw : Measurable w := hW.comp (measurable_id.min (measurable_const.sub measurable_id))
  have hb : ∀ y : ℝ, W y ∈ Icc (0 : ℝ) 1 :=
    fun _ => ⟨cosineWeight_nonneg hV _, cosineWeight_le_one hV _⟩
  have hw₀ : ∀ y : ℝ, w y ∈ Icc (0 : ℝ) 1 := fun y => hb (min y (x - y))
  let q (y : ℝ) := w y * F y
  let e (y : ℝ) := W y * (F y - 1)^2
  have hq : Integrable q μ :=
    integrable_mul_weight (integrableOn_density hd hA) hw (fun y _ => hw₀ y)
  have he : Integrable e μ :=
    integrable_mul_weight (integrableOn_density_error hd hA) hW (fun y _ => hb y)
  have hwI : Integrable w μ := by
    have hh := integrable_mul_weight
      (f := fun _ => 1) (integrableOn_const (by exact measure_Icc_lt_top.ne))
      hw (fun y (_ : y ∈ J) => hw₀ y)
    change IntegrableOn w J
    simpa only [mul_one] using hh
  have hqr : Integrable (fun y => q (r y)) μ := hr.integrable_comp_of_integrable hq
  have her : Integrable (fun y => e (r y)) μ := hr.integrable_comp_of_integrable he
  have hpt : ∀ᵐ y ∂μ, q y + q (r y) - w y ≤ (e y + e (r y)) / 2 := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := J) measurableSet_Icc] with y hy
    have hyr : r y ∈ J := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have h₁ := mul_le_mul_of_nonneg_left (pair_deficit (F y) (F (r y)) (no_pair x d y hn)) (hw₀ y).1
    have h₂ := mul_le_mul_of_nonneg_right (reflectedWeight_le_upperWeight hV hA hy)
      (sq_nonneg (F y - 1))
    have h₃ := mul_le_mul_of_nonneg_right (reflectedWeight_le_upperWeight hV hA hyr)
      (sq_nonneg (F (r y) - 1))
    have hsym : w (r y) = w y := reflectedWeight_reflect V x y
    change w y * F y + w (r y) * F (r y) - w y ≤
      (W y * (F y - 1)^2 + W (r y) * (F (r y) - 1)^2) / 2
    change w y * (F y - 1)^2 ≤ W y * (F y - 1)^2 at h₂
    change w (r y) * (F (r y) - 1)^2 ≤ W (r y) * (F (r y) - 1)^2 at h₃
    rw [hsym] at h₃ ⊢
    linarith only [h₁, h₂, h₃]
  have h := integral_mono_ae ((hq.add hqr).sub hwI) ((he.add her).div_const 2) hpt
  change (∫ y, q y + q (r y) - w y ∂μ) ≤ ∫ y, (e y + e (r y)) / 2 ∂μ at h
  have hqa : Integrable (fun y => q y + q (r y)) μ := hq.add hqr
  rw [integral_sub hqa hwI, integral_add hq hqr, integral_div, integral_add he her,
    hr.integral_comp hre q, hr.integral_comp hre e] at h
  change 2 * (∫ y, q y ∂μ) - (∫ y, w y ∂μ) ≤ ∫ y, e y ∂μ
  linarith only [h]

end GoldbachExplicit
