/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import EValues.DPI
import EValues.Product
import EValues.Mathlib.iSup

/-!
# E-Rényi divergence

An analogue of the Rényi divergence for e-variables.

-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {P : Measure 𝓧} [IsProbabilityMeasure P] {S T : Set (Measure 𝓧)}
  {α : ℝ≥0∞}

/-- The e-Rényi divergence between two sets of measures.

Note that the two integrals are non-negative, so the application of `EReal.toENNReal` does not
truncate. -/
noncomputable
def erenyiDiv (α : ℝ≥0∞) (S T : Set (Measure 𝓧)) : ℝ≥0∞ :=
  (1 - α)⁻¹ * ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
    α * (maxUtility R S logUtility).toENNReal + (1 - α) * (maxUtility R T logUtility).toENNReal

/-- The e-Chernoff divergence between two sets of measures. -/
noncomputable
def echernoffDiv (S T : Set (Measure 𝓧)) : ℝ≥0∞ :=
  ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
    max (maxUtility R S logUtility).toENNReal (maxUtility R T logUtility).toENNReal

lemma echernoffDiv_eq_sInf : echernoffDiv S T =
    sInf {y | ∃ R, IsProbabilityMeasure R ∧
    y = max (maxUtility R S logUtility).toENNReal (maxUtility R T logUtility).toENNReal} :=
  iInf₂_eq_sInf (ι := ℝ≥0∞)

lemma erenyiDiv_anti {α : ℝ≥0∞} {S₁ S₂ T₁ T₂ : Set (Measure 𝓧)} (hS : S₁ ⊆ S₂) (hT : T₁ ⊆ T₂) :
    erenyiDiv α S₂ T₂ ≤ erenyiDiv α S₁ T₁ := by
  unfold erenyiDiv
  gcongr with P hP
  · exact EReal.toENNReal_le_toENNReal <| maxUtility_anti hS
  · exact EReal.toENNReal_le_toENNReal <| maxUtility_anti hT

lemma echernoffDiv_anti {S₁ S₂ T₁ T₂ : Set (Measure 𝓧)} (hS : S₁ ⊆ S₂) (hT : T₁ ⊆ T₂) :
    echernoffDiv S₂ T₂ ≤ echernoffDiv S₁ T₁ := by
  unfold echernoffDiv
  gcongr with P hP
  · exact EReal.toENNReal_le_toENNReal <| maxUtility_anti hS
  · exact EReal.toENNReal_le_toENNReal <| maxUtility_anti hT

/-- Data processing inequality for the e-Rényi divergence. -/
lemma erenyiDiv_map_le {f : 𝓧 → 𝓨} (hf : Measurable f) :
    erenyiDiv α {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} ≤ erenyiDiv α S T := by
  unfold erenyiDiv
  gcongr 1
  set S' := {μ.map f | μ ∈ S}
  set T' := {μ.map f | μ ∈ T}
  calc
  _ ≤ ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
      α * (maxUtility (R.map f) S' logUtility).toENNReal +
        (1 - α) * (maxUtility (R.map f) T' logUtility).toENNReal := by
    rw [iInf₂_eq_sInf (ι := ℝ≥0∞), iInf₂_eq_sInf (ι := ℝ≥0∞)]
    refine sInf_le_sInf fun y ↦ ?_
    rintro ⟨R, hR, rfl⟩
    exact ⟨R.map f, R.isProbabilityMeasure_map hf.aemeasurable, rfl⟩
  _ ≤ ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
      α * (maxUtility R S logUtility).toENNReal +
        (1 - α) * (maxUtility R T logUtility).toENNReal := by
    refine iInf₂_mono fun R _ ↦ add_le_add ?_ ?_
    · gcongr 1
      exact EReal.toENNReal_le_toENNReal <| maxUtility_map_le R hf
    · gcongr 1
      exact EReal.toENNReal_le_toENNReal <| maxUtility_map_le R hf

/-- Data processing inequality for the e-Chernoff divergence. -/
lemma echernoffDiv_map_le {f : 𝓧 → 𝓨} (hf : Measurable f) :
    echernoffDiv {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} ≤ echernoffDiv S T := by
  set S' := {μ.map f | μ ∈ S}
  set T' := {μ.map f | μ ∈ T}
  calc echernoffDiv S' T'
  _ ≤ ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R), max
      (maxUtility (R.map f) S' logUtility).toENNReal
      (maxUtility (R.map f) T' logUtility).toENNReal := by
    rw [iInf₂_eq_sInf (ι := ℝ≥0∞), echernoffDiv_eq_sInf]
    refine sInf_le_sInf fun y ↦ ?_
    rintro ⟨R, hR, rfl⟩
    exact ⟨R.map f, R.isProbabilityMeasure_map hf.aemeasurable, rfl⟩
  _ ≤ echernoffDiv S T := by
    refine iInf₂_mono fun R _ ↦ max_le_max ?_ ?_
    all_goals exact (EReal.toENNReal_le_toENNReal <| maxUtility_map_le R hf)

lemma erenyiDiv_prod {S₁ S₂ : Set (Measure 𝓧)} {T₁ T₂ : Set (Measure 𝓨)}
    (hS₁ : ∀ μ ∈ S₁, IsProbabilityMeasure μ) (hS₂ : ∀ μ ∈ S₂, IsProbabilityMeasure μ)
    (hT₁ : ∀ μ ∈ T₁, IsProbabilityMeasure μ) (hT₂ : ∀ μ ∈ T₂, IsProbabilityMeasure μ) :
    erenyiDiv α (Measure.prod.uncurry '' (S₁ ×ˢ T₁)) (Measure.prod.uncurry '' (S₂ ×ˢ T₂))
      = erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := by
  sorry

lemma echernoffDiv_prod_le {S₁ S₂ : Set (Measure 𝓧)} {T₁ T₂ : Set (Measure 𝓨)}
    (hS₁ : ∀ μ ∈ S₁, IsProbabilityMeasure μ) (hS₂ : ∀ μ ∈ S₂, IsProbabilityMeasure μ)
    (hT₁ : ∀ μ ∈ T₁, IsProbabilityMeasure μ) (hT₂ : ∀ μ ∈ T₂, IsProbabilityMeasure μ) :
    echernoffDiv (Measure.prod.uncurry '' (S₁ ×ˢ T₁)) (Measure.prod.uncurry '' (S₂ ×ˢ T₂))
      ≤ echernoffDiv S₁ S₂ + echernoffDiv T₁ T₂ := by
  sorry

-- todo: rename
theorem main_result_one_sample {f : 𝓧 → ℝ≥0∞} (hf : Measurable f) (hf_le : ∀ x, f x ≤ 1)
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, IsProbabilityMeasure μ)
    {δ : ℝ≥0∞}
    (hSf : ∀ μ ∈ S, ∫⁻ ω, f ω ∂μ ≤ δ) (hTf : ∀ ν ∈ T, 1 - δ ≤ ∫⁻ ω, f ω ∂ν) :
    ENNReal.ofReal (Real.log (1 / (4 * δ.toReal * (1 - δ).toReal))) ≤ erenyiDiv 2⁻¹ S T := by
  sorry

end ProbabilityTheory
