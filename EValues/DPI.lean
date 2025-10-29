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

/-- The maximum utility `∫ᵉ x, (U ∘ X) x ∂P` of a measure `P` over all e-variables `X` for
a set of measures `S`. -/
noncomputable
def maxUtility (P : Measure 𝓧) (S : Set (Measure 𝓧)) (U : Utility) : EReal :=
  ⨆ (X : 𝓧 → ℝ≥0∞) (_hX : IsEVar X S), ∫ᵉ x, (U ∘ X) x ∂P

/-- The maximum randomized utility `∫ᵉ x, U x ∂(η ∘ₘ P)` of a measure `P` over all randomized
e-variables `η` for a set of measures `S`. -/
noncomputable
def maxRandUtility (P : Measure 𝓧) (S : Set (Measure 𝓧)) (U : Utility) : EReal :=
  ⨆ (η : Kernel 𝓧 ℝ≥0∞) (_hη₁ : IsMarkovKernel η) (_hη₂ : IsRandEVar η S), ∫ᵉ x, U x ∂(η ∘ₘ P)

variable {P : Measure 𝓧} {S T : Set (Measure 𝓧)} {U : Utility} {φ : 𝓧 → 𝓨}

lemma maxUtility_eq_sSup : maxUtility P S U = sSup {y | ∃ X, IsEVar X S ∧ y = ∫ᵉ x, (U ∘ X) x ∂P} := by
  rw [sSup_eq_iSup]
  simp_rw [Set.mem_setOf_eq, iSup_exists, iSup_and]
  simp only [maxUtility]
  suffices ⨆ a, ⨆ X, ⨆ (_ : IsEVar X S), ⨆ (_ : a = ∫ᵉ x, (U ∘ X) x ∂P), a =
      ⨆ X, ⨆ (_ : IsEVar X S), ⨆ a, ⨆ (_ : a = ∫ᵉ x, (U ∘ X) x ∂P), a by
    simp_rw [this, iSup_iSup_eq_left]
  rw [iSup_comm]
  refine iSup_congr (fun i => ?_)
  rw [iSup_comm]

lemma maxRandUtility_eq_sSup : maxRandUtility P S U =
      sSup {y | ∃ η, IsMarkovKernel η ∧ IsRandEVar η S ∧ y = ∫ᵉ x, U x ∂(η ∘ₘ P)} := by
  rw [sSup_eq_iSup]
  simp_rw [Set.mem_setOf_eq, iSup_exists, iSup_and]
  simp only [maxRandUtility]
  suffices ⨆ a, ⨆ η, ⨆ (_ : IsMarkovKernel η), ⨆ (_ : IsRandEVar η S),
      ⨆ (_ : a = ∫ᵉ x, U x ∂(η ∘ₘ P)), a =
        ⨆ η, ⨆ (_ : IsMarkovKernel η), ⨆ (_ : IsRandEVar η S),
        ⨆ a, ⨆ (_ : a = ∫ᵉ x, U x ∂(η ∘ₘ P)), a by
    simp_rw [this, iSup_iSup_eq_left]
  rw [iSup_comm]
  refine iSup_congr (fun i => ?_)
  rw [iSup_comm]
  refine iSup_congr (fun η => ?_)
  rw [iSup_comm]

lemma maxUtility_anti (hS : S ⊆ T) : maxUtility P T U ≤ maxUtility P S U := by
  rw [maxUtility_sSup, maxUtility_sSup]
  refine sSup_le_sSup ?_
  rintro y ⟨X, hX, hy⟩
  exact ⟨X, hX.anti_set hS, hy⟩

lemma maxRandUtility_anti (hS : S ⊆ T) : maxRandUtility P T U ≤ maxRandUtility P S U := by
  rw [maxRandUtility_sSup, maxRandUtility_sSup]
  refine sSup_le_sSup ?_
  rintro y ⟨η, hη₁, hη₂, hy⟩
  exact ⟨η, hη₁, hη₂.anti_set hS, hy⟩

lemma maxRandUtility_eq_maxUtility (P : Measure 𝓧) (S : Set (Measure 𝓧)) (hU : Measurable U) :
    maxRandUtility P S U = maxUtility P S U := by
  rw [maxRandUtility, maxUtility]
  sorry

lemma maxRandUtility_comp_le (P : Measure 𝓧) (S : Set (Measure 𝓧)) (κ : Kernel 𝓧 𝓨)
    [IsMarkovKernel κ] : maxRandUtility (κ ∘ₘ P) {κ ∘ₘ μ | μ ∈ S} U ≤ maxRandUtility P S U := by
  calc maxRandUtility (κ ∘ₘ P) {κ ∘ₘ μ | μ ∈ S} U
  _ = sSup {y | ∃ η, IsMarkovKernel η ∧ IsRandEVar η {κ ∘ₘ μ | μ ∈ S} ∧
      y = ∫ᵉ x, U x ∂(η ∘ₘ κ ∘ₘ P)} := maxRandUtility_sSup
  _ = sSup {y | ∃ ξ, ∃ η, IsMarkovKernel η ∧ IsRandEVar η {κ ∘ₘ μ | μ ∈ S} ∧
      ξ = η ∘ₖ κ ∧ y = ∫ᵉ x, U x ∂(ξ ∘ₘ P)} := by
    congr with y
    constructor
    · rintro ⟨η, hη₁, hη₂, hη_int⟩
      refine ⟨η ∘ₖ κ, η, hη₁, hη₂, rfl, ?_⟩
      rw [hη_int, P.comp_assoc]
    · rintro ⟨ξ, η, hη₁, hη₂, hξ, hξ_int⟩
      refine ⟨η, hη₁, hη₂, ?_⟩
      rw [hξ_int, hξ, P.comp_assoc]
  _ ≤ maxRandUtility P S U := by
    rw [maxRandUtility_sSup]
    refine sSup_le_sSup <| fun y ↦ ?_
    rintro ⟨ξ, η, hη₁, hη₂, hξ, hξ_int⟩
    haveI : IsMarkovKernel ξ := by
      rw [hξ]
      infer_instance
    refine ⟨ξ, this, ⟨fun μ hμ ↦ ?_⟩, hξ_int⟩
    rw [hξ, ← μ.comp_assoc]
    exact hη₂.lintegral_le_one (κ ∘ₘ μ) ⟨μ, hμ, rfl⟩

lemma maxUtility_map_le (P : Measure 𝓧) (S : Set (Measure 𝓧))
    (hφ : Measurable φ) (hU : Measurable U) :
    maxUtility (P.map φ) {μ.map φ | μ ∈ S} U ≤ maxUtility P S U := by
  rw [← maxRandUtility_eq_maxUtility _ _ hU, ← maxRandUtility_eq_maxUtility _ _ hU]
  rw [← Measure.deterministic_comp_eq_map hφ]
  simp_rw [← Measure.deterministic_comp_eq_map hφ]
  exact maxRandUtility_comp_le P S <| Kernel.deterministic φ hφ

lemma maxUtility_comp_le (P : Measure 𝓧) (S : Set (Measure 𝓧)) (κ : Kernel 𝓧 𝓨)
    [IsMarkovKernel κ] (hU : Measurable U) :
    maxUtility (κ ∘ₘ P) {κ ∘ₘ μ | μ ∈ S} U ≤ maxUtility P S U := by
  rw [← maxRandUtility_eq_maxUtility _ _ hU, ← maxRandUtility_eq_maxUtility _ _ hU]
  exact maxRandUtility_comp_le P S κ

end MeasureTheory
