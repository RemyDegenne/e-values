/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Notation
import EValues.Mathlib.ENNReal
import EValues.Mathlib.unitInterval
import EValues.Utility

/-!
# E-variables



## Main definitions

* TODO

## Main statements

* TODO

-/

open scoped ENNReal NNReal ProbabilityTheory

open MeasureTheory ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ : Measure 𝓧} {S : Set (Measure 𝓧)}

namespace ProbabilityTheory

/-- A random variable `X` is an e-variable for a set of measures `S` if it is measurable and
its expectation is at most one for all measures in `S`. -/
structure IsEVar (X : 𝓧 → ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  measurable : Measurable X
  lintegral_le_one : ∀ μ ∈ S, ∫⁻ ω, X ω ∂μ ≤ 1

/-- A random variables `X` is an e-variable for a set of measures `S` if it is measurable and
its expectation is at most one for all measures in `S`. -/
structure IsRandEVar (κ : Kernel 𝓧 ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  [markov : IsMarkovKernel κ]
  lintegral_le_one : ∀ μ ∈ S, ∫⁻ ω, ω ∂(κ ∘ₘ μ) ≤ 1

variable {X Y : 𝓧 → ℝ≥0∞} {κ η : Kernel 𝓧 ℝ≥0∞} [IsMarkovKernel κ] {S T : Set (Measure 𝓧)}

/-- A kernel `κ` is a randomized e-variable iff its mean function `x ↦ ∫⁻ y, y ∂κ x` is an
e-variable. -/
lemma isRandEVar_iff_isEVar : IsRandEVar κ S ↔ IsEVar (fun x ↦ ∫⁻ y, y ∂κ x) S := by
  refine ⟨fun h ↦ ⟨by fun_prop, fun μ hμ ↦ ?_⟩, fun h ↦ ⟨fun μ hμ ↦ ?_⟩⟩
  · have h' := h.lintegral_le_one μ hμ
    rwa [Measure.lintegral_bind (by fun_prop)] at h'
    exact measurable_id.aemeasurable
  · rw [Measure.lintegral_bind (by fun_prop)]
    · exact h.lintegral_le_one μ hμ
    · exact measurable_id.aemeasurable

lemma IsEVar.isRandEVar_deterministic (hX : IsEVar X S) :
    IsRandEVar (Kernel.deterministic X hX.measurable) S where
  lintegral_le_one μ hμ := by
    rw [Measure.lintegral_bind (Kernel.measurable _).aemeasurable]
    · simpa using hX.lintegral_le_one μ hμ
    · exact measurable_id.aemeasurable

@[simp]
lemma isEVar_empty (hX : Measurable X) :
   IsEVar X (∅ : Set (Measure 𝓧)) where
  measurable := hX
  lintegral_le_one := by simp_all

lemma isEVar_zero : IsEVar 0 S where
  measurable := measurable_const
  lintegral_le_one μ hμ := by simp

lemma isEVar_one (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    IsEVar 1 S where
  measurable := measurable_const
  lintegral_le_one μ hμ := by simp [hS μ hμ]

lemma isEVar_fun_one (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    IsEVar (fun _ ↦ 1) S := isEVar_one S hS

lemma IsEVar.ae_lt_top (hX : IsEVar X S) {μ : Measure 𝓧} (hμ : μ ∈ S) : ∀ᵐ ω ∂μ, X ω < ⊤ := by
  by_contra h
  suffices ∫⁻ ω, X ω ∂μ = ⊤ by
    have lintegral_le_one := hX.lintegral_le_one μ hμ
    rw [this] at lintegral_le_one
    contradiction
  refine lintegral_eq_top_of_measure_eq_top_ne_zero hX.measurable.aemeasurable ?_
  · unfold Filter.Eventually at h
    simp [MeasureTheory.ae] at h
    suffices {ω | X ω < ⊤}ᶜ = {ω | X ω = ⊤} by
      rwa [← this]
    ext ω
    simp

lemma IsEVar.ae_ne_top (hX : IsEVar X S) {μ : Measure 𝓧} (hμ : μ ∈ S) : ∀ᵐ ω ∂μ, X ω ≠ ⊤ := by
  filter_upwards [hX.ae_lt_top hμ] with ω hω using hω.ne

lemma _root_.Measurable.measurable_fsupport (hX : Measurable X) :
    MeasurableSet X.fsupport := by
  suffices MeasurableSet {ω | X ω ≠ ⊤} ∧ MeasurableSet {ω | X ω ≠ 0} from this.1.inter this.2
  constructor <;> exact ((measurableSet_singleton _).preimage hX).compl

lemma IsEVar.measurable_fsupport (hX : IsEVar X S) :
    MeasurableSet X.fsupport := hX.measurable.measurable_fsupport

lemma IsEVar.mono (hY : IsEVar Y S) (hX : Measurable X) (hXY : X ≤ Y) : IsEVar X S where
  measurable := hX
  lintegral_le_one μ hμ := (lintegral_mono hXY).trans (hY.lintegral_le_one μ hμ)

lemma IsRandEVar.mono (hη : IsRandEVar η S) (hκη : κ ≤ η) : IsRandEVar κ S where
  lintegral_le_one μ hμ := by
    refine (lintegral_mono' ?_ le_rfl).trans (hη.lintegral_le_one μ hμ)
    rw [MeasureTheory.Measure.le_iff]
    intro A hA
    rw [μ.bind_apply hA κ.aemeasurable, μ.bind_apply hA η.aemeasurable]
    exact lintegral_mono fun x ↦ hκη x A

lemma IsEVar.anti_set (hST : S ⊆ T) (hX : IsEVar X T) : IsEVar X S where
  measurable := hX.measurable
  lintegral_le_one μ hμ := hX.lintegral_le_one μ (hST hμ)

lemma IsRandEVar.anti_set (hST : S ⊆ T) (hκ : IsRandEVar κ T) : IsRandEVar κ S where
  lintegral_le_one μ hμ := hκ.lintegral_le_one μ (hST hμ)

lemma IsEVar.union (hXS : IsEVar X S) (hXT : IsEVar X T) : IsEVar X (S ∪ T) where
  measurable := hXS.measurable
  lintegral_le_one μ hμ := by
    simp only [Set.mem_union] at hμ
    rcases hμ with hμS | hμT
    · exact hXS.lintegral_le_one μ hμS
    · exact hXT.lintegral_le_one μ hμT

lemma isEVar_union_iff : IsEVar X (S ∪ T) ↔ IsEVar X S ∧ IsEVar X T := by
  refine ⟨fun h ↦ ?_, fun ⟨hXS, hXT⟩ ↦ hXS.union hXT⟩
  exact ⟨⟨h.measurable, fun μ hμ ↦ h.lintegral_le_one _ (Set.subset_union_left hμ)⟩,
    ⟨h.measurable, fun μ hμ ↦ h.lintegral_le_one _ (Set.subset_union_right hμ)⟩⟩

lemma IsEVar.comp {Y : 𝓨 → ℝ≥0∞} {S : Set (Measure 𝓧)} {φ : 𝓧 → 𝓨}
    (hφ : Measurable φ) (h : IsEVar Y {μ.map φ | μ ∈ S}) :
    IsEVar (Y ∘ φ) S where
  measurable := h.measurable.comp hφ
  lintegral_le_one μ hμ := by
    have h' := h.lintegral_le_one (μ.map φ) ?_
    · rwa [lintegral_map h.measurable hφ] at h'
    · exact ⟨μ, hμ, rfl⟩

lemma IsRandEVar.comp {ξ : Kernel 𝓨 ℝ≥0∞} {S : Set (Measure 𝓧)}
    {κ : Kernel 𝓧 𝓨} [IsMarkovKernel κ] (h : IsRandEVar ξ {κ ∘ₘ μ | μ ∈ S}) :
    IsRandEVar (ξ ∘ₖ κ) S where
  markov := have := h.markov; inferInstance
  lintegral_le_one μ hμ := by
    have h' := h.lintegral_le_one (κ ∘ₘ μ) ⟨μ, hμ, rfl⟩
    rwa [Measure.comp_assoc] at h'

/-- An e-variable for which the eintegral of the composition with a utility function is not ⊥. -/
structure NeBotUtilityEVar (X : 𝓧 → ℝ≥0∞) (P : Measure 𝓧)
    (S : Set (Measure 𝓧)) (U : Utility) : Prop extends IsEVar X S where
  eintegral_ne_bot : ∫ᵉ x, (U ∘ X) x ∂P ≠ ⊥

lemma NeBotUtilityEVar.eintegrable (X : 𝓧 → ℝ≥0∞) (P : Measure 𝓧) (S : Set (Measure 𝓧))
    (U : Utility) (hX : NeBotUtilityEVar X P S U) : eintegrable (U ∘ X) P :=
  eintegrable_of_eintegral_ne_bot hX.eintegral_ne_bot

lemma IsEVar.NeBotUtilityEVar_iff (hX : IsEVar X S) {P : Measure 𝓧} {U : Utility} :
    NeBotUtilityEVar X P S U ↔ ∫ᵉ x, (U ∘ X) x ∂P ≠ ⊥ :=
  ⟨fun h ↦ h.eintegral_ne_bot, fun h_eintegrable ↦ ⟨hX, h_eintegrable⟩⟩

end ProbabilityTheory
