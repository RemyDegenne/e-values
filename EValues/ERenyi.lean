/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import EValues.Product

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
    α * (∫ᵉ x, ENNReal.log (numeraire R S x) ∂R).toENNReal +
    (1 - α) * (∫ᵉ x, ENNReal.log (numeraire R T x) ∂R).toENNReal

/-- Data processing inequality for the e-Rényi divergence. -/
lemma erenyiDiv_map_le {f : 𝓧 → 𝓨} (hf : Measurable f) :
    erenyiDiv α (Measure.map f '' S) (Measure.map f '' T) ≤ erenyiDiv α S T := by
  unfold erenyiDiv
  gcongr 1
  sorry

lemma erenyiDiv_prod (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    (hT : ∀ μ ∈ T, IsProbabilityMeasure μ) :
    erenyiDiv α (Measure.prod.uncurry '' (S ×ˢ T)) (Measure.prod.uncurry '' (S ×ˢ T))
      = erenyiDiv α S T + erenyiDiv α T S := by
  sorry

-- todo: rename
theorem main_result_one_sample {f : 𝓧 → ℝ≥0∞} (hf : Measurable f) (hf_le : ∀ x, f x ≤ 1)
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, IsProbabilityMeasure μ)
    {δ : ℝ≥0∞}
    (hSf : ∀ μ ∈ S, ∫⁻ ω, f ω ∂μ ≤ δ) (hTf : ∀ ν ∈ T, 1 - δ ≤ ∫⁻ ω, f ω ∂ν) :
    ENNReal.ofReal (Real.log (1 / (4 * δ.toReal * (1 - δ).toReal))) ≤ erenyiDiv 2⁻¹ S T := by
  sorry

end ProbabilityTheory
