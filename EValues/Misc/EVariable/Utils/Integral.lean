/-
 - Created in 2025 by Gaëtan Serré
-/

-- import EVariable.Utils.Filter
import EValues.Misc.EIntegral.Defs
import Mathlib

open Function Set ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

noncomputable def e_average (μ : Measure α) (f : α → EReal) : EReal :=
    ∫ᵉ x, f x ∂(μ univ)⁻¹ • μ

notation3 "⨍ᵉ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => e_average μ r

/- lemma integral_pos₀ {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (hμ : μ ≠ 0) {f : α → ℝ} (hf : 0 <ᵐ[μ] f) (hfi : Integrable f μ) :
    0 < ∫ (x : α), f x ∂μ := by
  refine (integral_pos_iff_support_of_nonneg_ae hf.eventually_le hfi).mpr ?_
  suffices μ (support f) = μ univ by
      rw [this]
      simp [hμ]
  have : μ (support f) + μ (support f)ᶜ = μ univ := by
    refine measure_add_measure_compl₀ <| AEStronglyMeasurable.nullMeasurableSet_support ?_
    exact hfi.1
  rw [← this]
  have : μ (support f)ᶜ = μ {x | 0 < f x}ᶜ := by
    suffices (support f) =ᵐ[μ] {x | 0 < f x} from
      measure_congr this.compl
    filter_upwards [hf] with x hx
    simp only [support, ne_eq, eq_iff_iff]
    exact ⟨fun _ ↦ hx, fun _ ↦ ne_of_gt hx⟩
  rw [this]
  simp only [Filter.EventuallyLT, Filter.Eventually, ae, Pi.zero_apply,
    Filter.mem_ofCountableUnion] at hf
  rw [hf]
  simp

lemma integral_pos {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : 0 <ᵐ[μ] f) (hfi : Integrable f μ) :
    0 < ∫ (x : α), f x ∂μ := integral_pos₀ (NeZero.ne' μ).symm hf hfi -/

end MeasureTheory

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set ℝ≥0∞} {t : Set α}
  {f : α → ℝ≥0∞} {g : ℝ≥0∞ → ℝ≥0∞}

theorem ConvexOn.map_laverage_le [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConvexOn ℝ≥0∞ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) : g (⨍⁻ x, f x ∂μ) ≤ ⨍⁻ x, g (f x) ∂μ := by
  sorry

theorem StrictConvexOn.ae_eq_const_or_map_laverage_lt [IsFiniteMeasure μ]
    (hg : StrictConvexOn ℝ≥0∞ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) :
    f =ᵐ[μ] const α (⨍⁻ x, f x ∂μ) ∨ g (⨍⁻ x, f x ∂μ) < ⨍⁻ x, g (f x) ∂μ := by
  sorry
