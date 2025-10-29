/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib
import EValues.EValue
import EValues.Utility

open scoped ENNReal NNReal ProbabilityTheory

open MeasureTheory ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ : Measure 𝓧} {S : Set (Measure 𝓧)}

namespace MeasureTheory

/-- The maximum utility `P[U ∘ X]` of a measure `P` over all e-variables `X` for
a set of measures `S`. -/

noncomputable
def maxUtility (P : Measure 𝓧) (S : Set (Measure 𝓧)) (U : Utility) : EReal :=
  sSup {y | ∃ X, IsEVar X S ∧ y = ∫ᵉ x, (U ∘ X) x ∂P}

/-- The maximum randomized utility `(η ∘ₘ P)[U]` of a measure `P` over all randomized e-variables
`η` for a set of measures `S`. -/
noncomputable
def maxRandUtility (P : Measure 𝓧) (S : Set (Measure 𝓧)) (U : Utility) : EReal :=
  ⨆ (η : Kernel 𝓧 ℝ≥0∞) (_hη : IsRandEVar η S), ∫ᵉ x, U x ∂(η ∘ₘ P)

variable {P : Measure 𝓧} {S T : Set (Measure 𝓧)} {U : Utility} {φ : 𝓧 → 𝓨} {κ : Kernel 𝓧 𝓨}

lemma maxUtility_anti (hS : S ⊆ T) : maxUtility P T U ≤ maxUtility P S U := by
  refine sSup_le_sSup ?_
  rintro y ⟨X, hX, hy⟩
  exact ⟨X, hX.anti_set hS, hy⟩

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
  _ = sSup {y | ∃ Y, IsEVar Y {μ.map φ | μ ∈ S} ∧ y = ∫ᵉ x, (U ∘ Y) x ∂(P.map φ)} := rfl
  _ = sSup {y | ∃ Y, IsEVar Y {μ.map φ | μ ∈ S} ∧ y = ∫ᵉ x, (U ∘ Y ∘ φ) x ∂P} := by
    congr with y
    constructor
    all_goals
    rintro ⟨Y, hY_evar, hY⟩
    refine ⟨Y, hY_evar, ?_⟩
    rw [hY, eintegral_map (hU.comp hY_evar.measurable) hφ]
    rfl
  _ = sSup {y | ∃ X, ∃ Y, IsEVar Y {μ.map φ | μ ∈ S} ∧ X = Y ∘ φ ∧ y = ∫ᵉ x, (U ∘ Y ∘ φ) x ∂P} := by
    congr with y
    constructor
    · rintro ⟨Y, hY_evar, hY⟩
      refine ⟨Y ∘ φ, Y, hY_evar, rfl, ?_⟩
      simp_all
    · rintro ⟨X, Y, hY_evar, hX, hY⟩
      refine ⟨Y, hY_evar, ?_⟩
      simp_all
  _ ≤ sSup {y | ∃ X, IsEVar X S ∧ y = ∫ᵉ x, (U ∘ X) x ∂P} := by
    refine sSup_le_sSup <| fun y ↦ ?_
    rintro ⟨X, Y, hY_evar, hX, hY⟩
    refine ⟨Y ∘ φ, ⟨hY_evar.measurable.comp hφ, ?_⟩, hY⟩
    intro μ hμ
    have := hY_evar.lintegral_le_one (μ.map φ) ⟨μ, hμ, rfl⟩
    rwa [lintegral_map hY_evar.measurable hφ] at this
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

end MeasureTheory
