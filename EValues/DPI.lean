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

lemma maxUtility_eq_sSup : maxUtility P S U =
    sSup {y | ∃ X, IsEVar X S ∧ y = ∫ᵉ x, (U ∘ X) x ∂P} := by
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
  rw [maxUtility_eq_sSup, maxUtility_eq_sSup]
  refine sSup_le_sSup ?_
  rintro y ⟨X, hX, hy⟩
  exact ⟨X, hX.anti_set hS, hy⟩

lemma maxRandUtility_anti (hS : S ⊆ T) : maxRandUtility P T U ≤ maxRandUtility P S U := by
  rw [maxRandUtility_eq_sSup, maxRandUtility_eq_sSup]
  refine sSup_le_sSup ?_
  rintro y ⟨η, hη₁, hη₂, hy⟩
  exact ⟨η, hη₁, hη₂.anti_set hS, hy⟩

lemma maxRandUtility_eq_maxUtility (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    maxRandUtility P S U = maxUtility P S U := by
  refine le_antisymm ?_ ?_
  · rw [maxRandUtility_eq_sSup]
    rw [sSup_le_iff]
    rintro y ⟨η, hη₁, hη₂, hy⟩
    obtain ⟨X, hX, h_le⟩ : ∃ X, IsEVar X S ∧ y ≤ ∫ᵉ x, (U ∘ X) x ∂P := by
      let X := fun x ↦ ∫⁻ y, y ∂(η x)
      refine ⟨X, ⟨by fun_prop, fun μ hμ ↦ ?_⟩, ?_⟩
      · rw [isRandEVar_iff_isEVar] at hη₂
        exact hη₂.lintegral_le_one μ hμ
      · rw [hy, eintegral_bind η.aemeasurable U.aemeasurable]
        sorry
    trans ∫ᵉ x, (U ∘ X) x ∂P
    · exact h_le
    · rw [maxUtility_eq_sSup]
      refine le_sSup ?_
      exact ⟨X, hX, rfl⟩
  · rw [maxRandUtility_eq_sSup, maxUtility_eq_sSup]
    refine sSup_le_sSup ?_
    rintro y ⟨X, hX, hy⟩
    refine ⟨Kernel.deterministic X hX.measurable, inferInstance, ⟨fun μ hμ ↦ ?_⟩, ?_⟩
    · rw [Measure.deterministic_comp_eq_map hX.measurable,
        lintegral_map (by measurability) hX.measurable]
      exact hX.lintegral_le_one μ hμ
    · rw [hy, Measure.deterministic_comp_eq_map hX.measurable,
        eintegral_map U.measurable hX.measurable]
      rfl

example : Measurable ENNReal.log := by measurability

lemma maxRandUtility_comp_le (P : Measure 𝓧) (S : Set (Measure 𝓧)) (κ : Kernel 𝓧 𝓨)
    [IsMarkovKernel κ] : maxRandUtility (κ ∘ₘ P) {κ ∘ₘ μ | μ ∈ S} U ≤ maxRandUtility P S U := by
  calc maxRandUtility (κ ∘ₘ P) {κ ∘ₘ μ | μ ∈ S} U
  _ = sSup {y | ∃ η, IsMarkovKernel η ∧ IsRandEVar η {κ ∘ₘ μ | μ ∈ S} ∧
      y = ∫ᵉ x, U x ∂(η ∘ₘ κ ∘ₘ P)} := maxRandUtility_eq_sSup
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
    rw [maxRandUtility_eq_sSup]
    refine sSup_le_sSup <| fun y ↦ ?_
    rintro ⟨ξ, η, hη₁, hη₂, hξ, hξ_int⟩
    haveI : IsMarkovKernel ξ := by
      rw [hξ]
      infer_instance
    refine ⟨ξ, this, ⟨fun μ hμ ↦ ?_⟩, hξ_int⟩
    rw [hξ, ← μ.comp_assoc]
    exact hη₂.lintegral_le_one (κ ∘ₘ μ) ⟨μ, hμ, rfl⟩

lemma maxUtility_map_le (P : Measure 𝓧) {S : Set (Measure 𝓧)} (hφ : Measurable φ) :
    maxUtility (P.map φ) {μ.map φ | μ ∈ S} U ≤ maxUtility P S U := by
  rw [← maxRandUtility_eq_maxUtility _ _, ← maxRandUtility_eq_maxUtility _ _,
    ← Measure.deterministic_comp_eq_map hφ]
  simp_rw [← Measure.deterministic_comp_eq_map hφ]
  exact maxRandUtility_comp_le P S <| Kernel.deterministic φ hφ

lemma maxUtility_comp_le (P : Measure 𝓧) (S : Set (Measure 𝓧)) (κ : Kernel 𝓧 𝓨)
    [IsMarkovKernel κ] :
    maxUtility (κ ∘ₘ P) {κ ∘ₘ μ | μ ∈ S} U ≤ maxUtility P S U := by
  rw [← maxRandUtility_eq_maxUtility _ _, ← maxRandUtility_eq_maxUtility _ _]
  exact maxRandUtility_comp_le P S κ

end MeasureTheory
