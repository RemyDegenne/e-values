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

lemma erenyiDiv_eq_sInf : erenyiDiv α S T =
    (1 - α)⁻¹ * sInf {y | ∃ R, IsProbabilityMeasure R ∧
    y = α * (maxUtility R S logUtility).toENNReal
      + (1 - α) * (maxUtility R T logUtility).toENNReal} := by
  simp [erenyiDiv, iInf₂_eq_sInf (ι := ℝ≥0∞)]

/-- The e-Chernoff divergence between two sets of measures. -/
noncomputable
def echernoffDiv (S T : Set (Measure 𝓧)) : ℝ≥0∞ :=
  ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
    max (maxUtility R S logUtility).toENNReal (maxUtility R T logUtility).toENNReal

lemma echernoffDiv_eq_sInf : echernoffDiv S T =
    sInf {y | ∃ R, IsProbabilityMeasure R ∧
    y = max (maxUtility R S logUtility).toENNReal (maxUtility R T logUtility).toENNReal} :=
  iInf₂_eq_sInf (ι := ℝ≥0∞)

lemma erenyiDiv_comp_le (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    erenyiDiv α {κ ∘ₘ μ | μ ∈ S} {κ ∘ₘ μ | μ ∈ T} ≤ erenyiDiv α S T := by
  unfold erenyiDiv
  gcongr 1
  calc
  _ ≤ ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
      α * (maxUtility (κ ∘ₘ R) {κ ∘ₘ μ | μ ∈ S} logUtility).toENNReal +
        (1 - α) * (maxUtility (κ ∘ₘ R) {κ ∘ₘ μ | μ ∈ T} logUtility).toENNReal := by
    rw [iInf₂_eq_sInf (ι := ℝ≥0∞), iInf₂_eq_sInf (ι := ℝ≥0∞)]
    refine sInf_le_sInf fun y ↦ ?_
    rintro ⟨R, hR, rfl⟩
    exact ⟨κ ∘ₘ R, inferInstance, rfl⟩
  _ ≤ ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
      α * (maxUtility R S logUtility).toENNReal +
        (1 - α) * (maxUtility R T logUtility).toENNReal := by
    refine iInf₂_mono fun R _ ↦ add_le_add ?_ ?_
    all_goals
      gcongr 1
      exact EReal.toENNReal_le_toENNReal <| maxUtility_comp_le R κ

/-- Data processing inequality for the e-Rényi divergence. -/
lemma erenyiDiv_map_le {f : 𝓧 → 𝓨} (hf : Measurable f) :
    erenyiDiv α {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} ≤ erenyiDiv α S T := by
  simp_rw [← Measure.deterministic_comp_eq_map hf]
  exact erenyiDiv_comp_le <| Kernel.deterministic f hf

lemma echernoffDiv_comp_le (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    echernoffDiv {κ ∘ₘ μ | μ ∈ S} {κ ∘ₘ μ | μ ∈ T} ≤ echernoffDiv S T := by
  calc echernoffDiv {κ ∘ₘ μ | μ ∈ S} {κ ∘ₘ μ | μ ∈ T}
  _ ≤ ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R), max
      (maxUtility (κ ∘ₘ R) {κ ∘ₘ μ | μ ∈ S} logUtility).toENNReal
      (maxUtility (κ ∘ₘ R) {κ ∘ₘ μ | μ ∈ T} logUtility).toENNReal := by
    rw [iInf₂_eq_sInf (ι := ℝ≥0∞), echernoffDiv_eq_sInf]
    refine sInf_le_sInf fun y ↦ ?_
    rintro ⟨R, hR, rfl⟩
    exact ⟨κ ∘ₘ R, inferInstance, rfl⟩
  _ ≤ echernoffDiv S T := by
    refine iInf₂_mono fun R _ ↦ max_le_max ?_ ?_
    all_goals exact EReal.toENNReal_le_toENNReal <| maxUtility_comp_le R κ

/-- Data processing inequality for the e-Chernoff divergence. -/
lemma echernoffDiv_map_le {f : 𝓧 → 𝓨} (hf : Measurable f) :
    echernoffDiv {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} ≤ echernoffDiv S T := by
  simp_rw [← Measure.deterministic_comp_eq_map hf]
  exact echernoffDiv_comp_le <| Kernel.deterministic f hf

lemma erenyiDiv_prod {S₁ S₂ : Set (Measure 𝓧)} {T₁ T₂ : Set (Measure 𝓨)}
    (hS₁ : ∀ μ ∈ S₁, IsProbabilityMeasure μ) (hS₂ : ∀ μ ∈ S₂, IsProbabilityMeasure μ)
    (hT₁ : ∀ μ ∈ T₁, IsProbabilityMeasure μ) (hT₂ : ∀ μ ∈ T₂, IsProbabilityMeasure μ) :
    erenyiDiv α (Measure.prod.uncurry '' (S₁ ×ˢ T₁)) (Measure.prod.uncurry '' (S₂ ×ˢ T₂))
      = erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := by
  set ST₁ := Measure.prod.uncurry '' (S₁ ×ˢ T₁)
  set ST₂ := Measure.prod.uncurry '' (S₂ ×ˢ T₂)
  refine le_antisymm ?_ ?_
  · calc
    _ ≤ (1 - α)⁻¹ * sInf {y | ∃ R₁ R₂,
        IsProbabilityMeasure R₁ ∧ IsProbabilityMeasure R₂ ∧
        y = α * (maxUtility (R₁.prod R₂) ST₁ logUtility).toENNReal +
            (1 - α) * (maxUtility (R₁.prod R₂) ST₂ logUtility).toENNReal} := by
      rw [erenyiDiv_eq_sInf]
      gcongr 1
      refine sInf_le_sInf fun y ↦ ?_
      rintro ⟨R₁, R₂, hR₁, hR₂, rfl⟩
      exact ⟨R₁.prod R₂, inferInstance, rfl⟩
    _ = (1 - α)⁻¹ * sInf {y | ∃ R₁ R₂,
        IsProbabilityMeasure R₁ ∧ IsProbabilityMeasure R₂ ∧
        y = α * (maxUtility R₁ S₁ logUtility + maxUtility R₂ T₁ logUtility).toENNReal +
            (1 - α) * (maxUtility R₁ S₂ logUtility + maxUtility R₂ T₂ logUtility).toENNReal} := by
      congr with y
      constructor
      · rintro ⟨R₁, R₂, hR₁, hR₂, rfl⟩
        rw [maxUtility_prod _ _ hS₁ hT₁, maxUtility_prod _ _ hS₂ hT₂]
        exact ⟨R₁, R₂, hR₁, hR₂, rfl⟩
      · rintro ⟨R₁, R₂, hR₁, hR₂, rfl⟩
        rw [← maxUtility_prod _ _ hS₁ hT₁, ← maxUtility_prod _ _ hS₂ hT₂]
        exact ⟨R₁, R₂, hR₁, hR₂, rfl⟩
    _ = (1 - α)⁻¹ * (sInf {y | ∃ R₁,
                      IsProbabilityMeasure R₁ ∧
                      y = α * (maxUtility R₁ S₁ logUtility).toENNReal +
                          (1 - α) * (maxUtility R₁ S₂ logUtility).toENNReal}
                    +
                     sInf {y | ∃ R₂,
                      IsProbabilityMeasure R₂ ∧
                      y = α * (maxUtility R₂ T₁ logUtility).toENNReal +
                          (1 - α) * (maxUtility R₂ T₂ logUtility).toENNReal}) := by
      congr 1
      rw [← sInf_add']
      congr 1 with y
      constructor
      · rintro ⟨R₁, R₂, hR₁, hR₂, rfl⟩
        rw [Set.mem_add]
        let x := α * (maxUtility R₁ S₁ logUtility).toENNReal +
          (1 - α) * (maxUtility R₁ S₂ logUtility).toENNReal
        let z := α * (maxUtility R₂ T₁ logUtility).toENNReal +
          (1 - α) * (maxUtility R₂ T₂ logUtility).toENNReal
        refine ⟨x, ⟨R₁, hR₁, rfl⟩, z, ⟨R₂, hR₂, rfl⟩, ?_⟩
        rw [EReal.mul_add_ENNReal, EReal.mul_add_ENNReal]
        · ring
        · exact maxUtility_nonneg _ hS₂
        · exact maxUtility_nonneg _ hT₂
        · exact maxUtility_nonneg _ hS₁
        · exact maxUtility_nonneg _ hT₁
      · rw [Set.mem_add]
        rintro ⟨_, ⟨R₁, hR₁, rfl⟩, _, ⟨R₂, hR₂, rfl⟩, rfl⟩
        refine ⟨R₁, R₂, hR₁, hR₂, ?_⟩
        rw [EReal.mul_add_ENNReal, EReal.mul_add_ENNReal]
        · ring
        · exact maxUtility_nonneg _ hS₂
        · exact maxUtility_nonneg _ hT₂
        · exact maxUtility_nonneg _ hS₁
        · exact maxUtility_nonneg _ hT₁
    _ = erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := by
      rw [erenyiDiv_eq_sInf, erenyiDiv_eq_sInf]
      ring
  · sorry

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
