/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Notation

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

structure IsEVar (X : 𝓧 → ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  measurable : Measurable X
  lintegral_le_one : ∀ μ ∈ S, ∫⁻ ω, X ω ∂μ ≤ 1

structure IsRandEVar (κ : Kernel 𝓧 ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  lintegral_le_one : ∀ μ ∈ S, ∫⁻ ω, ω ∂(κ ∘ₘ μ) ≤ 1

variable {X Y : 𝓧 → ℝ≥0∞} {κ η : Kernel 𝓧 ℝ≥0∞} {S T : Set (Measure 𝓧)}

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

lemma isEVar_one (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    IsEVar 1 S where
  measurable := measurable_const
  lintegral_le_one μ hμ := by simp [hS μ hμ]

lemma isEVar_fun_one (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    IsEVar (fun _ ↦ 1) S := isEVar_one S hS

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

lemma IsRandEVar.comp {ξ : Kernel 𝓨 ℝ≥0∞} {S : Set (Measure 𝓧)} {κ : Kernel 𝓧 𝓨}
    (h : IsRandEVar ξ {κ ∘ₘ μ | μ ∈ S}) :
    IsRandEVar (ξ ∘ₖ κ) S where
  lintegral_le_one μ hμ := by
    have h' := h.lintegral_le_one (κ ∘ₘ μ) ⟨μ, hμ, rfl⟩
    rwa [Measure.comp_assoc] at h'

/-- The maximum utility `P[U ∘ X]` of a measure `P` over all e-variables `X` for
a set of measures `S`. -/
noncomputable
def maxUtility (P : Measure 𝓧) (S : Set (Measure 𝓧)) (U : ℝ≥0∞ → ℝ) : ℝ :=
  ⨆ (X : 𝓧 → ℝ≥0∞) (_hX : IsEVar X S), P[U ∘ X]

/-- The maximum randomized utility `(η ∘ₘ P)[U]` of a measure `P` over all randomized e-variables
`η` for a set of measures `S`. -/
noncomputable
def maxRandUtility (P : Measure 𝓧) (S : Set (Measure 𝓧)) (U : ℝ≥0∞ → ℝ) : ℝ :=
  ⨆ (η : Kernel 𝓧 ℝ≥0∞) (_hη : IsRandEVar η S), (η ∘ₘ P)[U]

variable {P : Measure 𝓧} {S T : Set (Measure 𝓧)} {U : ℝ≥0∞ → ℝ} {φ : 𝓧 → 𝓨} {κ : Kernel 𝓧 𝓨}

lemma maxUtility_anti (hS : S ⊆ T) (hU : Measurable U) :
    maxUtility P T U ≤ maxUtility P S U := by
  refine ciSup_mono ?_ fun X ↦ ?_
  · sorry
  by_cases hX : IsEVar X T
  · simp [hX, hX.anti_set hS]
  · sorry

lemma maxRandUtility_anti (hS : S ⊆ T) (hU : Measurable U) :
    maxRandUtility P T U ≤ maxRandUtility P S U := by
  sorry

lemma maxRandUtility_eq_maxUtility (P : Measure 𝓧) (S : Set (Measure 𝓧))
    (hU : Measurable U) (hU_ccv : ConcaveOn ℝ≥0 Set.univ U) :
    maxRandUtility P S U = maxUtility P S U := by
  rw [maxRandUtility, maxUtility]
  sorry

lemma maxUtility_map_le (P : Measure 𝓧) (S : Set (Measure 𝓧))
    (hφ : Measurable φ) (hU : Measurable U) :
    maxUtility (P.map φ) {μ.map φ | μ ∈ S} U ≤ maxUtility P S U := by
  calc maxUtility (P.map φ) {μ.map φ | μ ∈ S} U
  _ = ⨆ (Y) (_hY : IsEVar Y {μ.map φ | μ ∈ S}), (P.map φ)[U ∘ Y] := rfl
  _ = ⨆ (Y) (_hY : IsEVar Y {μ.map φ | μ ∈ S}), P[U ∘ Y ∘ φ] := by
    congr with Y
    congr with hY
    rw [integral_map hφ.aemeasurable]
    · rfl
    refine Measurable.aestronglyMeasurable ?_
    exact hU.comp hY.measurable
  _ = ⨆ (X) (_hX : ∃ Y, IsEVar Y {μ.map φ | μ ∈ S} ∧ X = Y ∘ φ), P[U ∘ X] := sorry
  _ ≤ ⨆ (X) (_hX : IsEVar X S), P[U ∘ X] := by
    rw [ciSup_le_iff]
    swap; · sorry
    intro X
    sorry
  _ = maxUtility P S U := rfl

lemma maxRandUtility_comp_le (P : Measure 𝓧) (S : Set (Measure 𝓧)) (κ : Kernel 𝓧 𝓨)
    (hU : Measurable U) :
    maxRandUtility (κ ∘ₘ P) {κ ∘ₘ μ | μ ∈ S} U ≤ maxRandUtility P S U := by
  sorry

lemma maxUtility_comp_le (P : Measure 𝓧) (S : Set (Measure 𝓧)) (κ : Kernel 𝓧 𝓨)
    (hU : Measurable U) (hU_ccv : ConcaveOn ℝ≥0 Set.univ U) :
    maxUtility (κ ∘ₘ P) {κ ∘ₘ μ | μ ∈ S} U ≤ maxUtility P S U := by
  rw [← maxRandUtility_eq_maxUtility _ _ hU hU_ccv,
    ← maxRandUtility_eq_maxUtility _ _ hU hU_ccv]
  exact maxRandUtility_comp_le P S κ hU

end ProbabilityTheory
