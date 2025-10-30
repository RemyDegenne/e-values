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

namespace MeasureTheory

lemma Measure.integrable_comp_iff
    {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    [NormedAddCommGroup E] {κ : Kernel α β} {μ : Measure α} {f : β → E}
    (h_meas : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    Integrable f (κ ∘ₘ μ)
      ↔ (∀ᵐ x ∂μ, Integrable f (κ x)) ∧ Integrable (fun x ↦ ∫ y, ‖f y‖ ∂κ x) μ := by
  rw [Measure.comp_eq_comp_const_apply, ProbabilityTheory.integrable_comp_iff]
  · simp
  · simpa [Kernel.comp_apply]

/-- The almost everywhere filter with respect to a set of measures, defined as the supremum of the
almost everywhere filters of the measures in the set. -/
def aeSet (S : Set (Measure 𝓧)) : Filter 𝓧 := ⨆ m ∈ S, ae m

lemma mem_aeSet_iff {t : Set 𝓧} : t ∈ aeSet S ↔ ∀ m ∈ S, m tᶜ = 0 := by simp [aeSet, mem_ae_iff]

/-- The pairing function between a signed measure and a real function. -/
noncomputable
def pairingFun (s : SignedMeasure 𝓧) (f : 𝓧 → ℝ) : ℝ :=
  ∫ ω, f ω ∂s.toJordanDecomposition.posPart
    - ∫ ω, f ω ∂s.toJordanDecomposition.negPart

/-- The set of functions that are integrable against all measures in a given set. -/
def integrableFunctions (S : Set (Measure 𝓧)) :=
  {f : 𝓧 → ℝ // Measurable f ∧ ∀ μ ∈ S, Integrable f μ}

/-- The set of measures against which all functions in a given set are integrable. -/
def integrableMeasures (L : Set (𝓧 → ℝ)) := {μ : Measure 𝓧 // ∀ f ∈ L, Integrable f μ}

/-- The set of signed measures against which all functions in a given set are integrable. -/
def integrableSignedMeasures (L : Set (𝓧 → ℝ)) :=
  {s : SignedMeasure 𝓧 // ∀ f ∈ L, Integrable f s.totalVariation}
-- being integrable against `totalVariation` is equivalent to being integrable against both
-- positive and negative parts. That is, both parts are in `integrableMeasures L`.

end MeasureTheory

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

lemma isEVar_zero : IsEVar 0 S where
  measurable := measurable_const
  lintegral_le_one μ hμ := by simp

lemma isEVar_one (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    IsEVar 1 S where
  measurable := measurable_const
  lintegral_le_one μ hμ := by simp [hS μ hμ]

lemma isEVar_fun_one (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    IsEVar (fun _ ↦ 1) S := isEVar_one S hS

lemma IsEVar.ae_ne_top (hX : IsEVar X S) : ∀ μ ∈ S, ∀ᵐ ω ∂μ, X ω < ⊤ := by
  intro μ hμ
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

lemma IsEVar.ae_finite (hX : IsEVar X S) : ∀ μ ∈ S, ∀ᵐ ω ∂μ, X ω ≠ ⊤ := by
  intro μ hμ
  filter_upwards [hX.ae_ne_top μ hμ] with ω hω using hω.ne

lemma IsEVar.measurable_fsupport (hX : IsEVar X S) :
    MeasurableSet X.fsupport := by
  suffices MeasurableSet {ω | X ω ≠ ⊤} ∧ MeasurableSet {ω | X ω ≠ 0} from this.1.inter this.2
  constructor
  · rw [← MeasurableSet.compl_iff]
    suffices {ω | X ω ≠ ⊤}ᶜ = {ω | X ω = ⊤} by
      rw [this]
      exact hX.measurable <| measurableSet_singleton ⊤
    ext ω
    simp
  · rw [← MeasurableSet.compl_iff]
    suffices {ω | X ω ≠ 0}ᶜ = {ω | X ω = 0} by
      rw [this]
      exact hX.measurable <| measurableSet_singleton 0
    ext ω
    simp

lemma IsEVar.mono (hY : IsEVar Y S) (hX : Measurable X) (hXY : X ≤ Y) : IsEVar X S where
  measurable := hX
  lintegral_le_one μ hμ := (lintegral_mono hXY).trans (hY.lintegral_le_one μ hμ)

lemma IsRandEVar.mono (hη : IsRandEVar η S) (hκη : κ ≤ η) : IsRandEVar κ S where
  lintegral_le_one μ hμ := by
    refine (lintegral_mono' ?_ le_rfl).trans (hη.lintegral_le_one μ hμ)
    sorry

lemma IsEVar.anti_set (hST : S ⊆ T) (hX : IsEVar X T) : IsEVar X S where
  measurable := hX.measurable
  lintegral_le_one μ hμ := hX.lintegral_le_one μ (hST hμ)

lemma IsRandEVar.anti_set (hST : S ⊆ T) (hκ : IsRandEVar κ T) : IsRandEVar κ S where
  lintegral_le_one μ hμ := hκ.lintegral_le_one μ (hST hμ)

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

end ProbabilityTheory
