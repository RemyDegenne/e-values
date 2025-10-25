/-
  - Created in 2025 by Gaëtan Serré
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α]

structure EVariable (P : Set (ProbabilityMeasure α)) where
  protected toFun : α → ℝ≥0∞
  private measurable' : Measurable toFun
  private integral_le_one' : ∀ ⦃μ⦄, μ ∈ P → ∫⁻ a, toFun a ∂μ ≤ 1

namespace EVariable

variable {P : Set (ProbabilityMeasure α)}

instance : FunLike (EVariable P) α ℝ≥0∞ where
  coe := EVariable.toFun
  coe_injective' f g _ := by cases f; cases g; congr

variable (e : EVariable P)

lemma measurable : Measurable e := e.measurable'

lemma lintegral_le_one {μ : ProbabilityMeasure α} (hμ : μ ∈ P) : ∫⁻ a, e a ∂μ ≤ 1 :=
  e.integral_le_one' hμ

lemma integrable {μ : ProbabilityMeasure α} (hμ : μ ∈ P) : Integrable e μ :=
  ⟨e.measurable.aestronglyMeasurable, lt_of_le_of_lt (e.lintegral_le_one hμ) (by simp)⟩

end EVariable

def is_evariable (P : Set (ProbabilityMeasure α)) (e : α → ℝ≥0∞) : Prop :=
  Measurable e ∧ ∀ ⦃μ⦄, μ ∈ P → ∫⁻ a, e a ∂μ ≤ 1

namespace is_evariable

variable {P : Set (ProbabilityMeasure α)} {e : α → ℝ≥0∞} (he : is_evariable P e)

def to_Evariable : EVariable P := ⟨e, he.1, he.2⟩

include he in
lemma mono {P' : Set (ProbabilityMeasure α)} (hP : P' ⊆ P) : is_evariable P' e := by
  refine ⟨he.1, ?_⟩
  intro μ hμ
  exact he.2 (hP hμ)

end is_evariable

namespace EVariable

variable {P : Set (ProbabilityMeasure α)} {e : EVariable P}

lemma is_evariable : is_evariable P e := ⟨e.measurable, fun _ h ↦ e.lintegral_le_one h⟩

def mono {P' : Set (ProbabilityMeasure α)} (hP : P' ⊆ P) : EVariable P' :=
  (e.is_evariable.mono hP).to_Evariable

end EVariable
