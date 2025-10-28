/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import EValues.NumeraireExistence

/-!
# Numeraire of a product

-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {P : Measure 𝓧} [IsProbabilityMeasure P] {Q : Measure 𝓨} [IsProbabilityMeasure Q]
  {S : Set (Measure 𝓧)} {T : Set (Measure 𝓨)}

/-- The numeraire on a product space is the product of the numeraires. -/
lemma numeraire_prod (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, IsProbabilityMeasure μ) :
    IsNumeraire (fun (x : 𝓧 × 𝓨) ↦ numeraire P S x.1 * numeraire Q T x.2)
      {ρ | ∃ μ ∈ S, ∃ ν ∈ T, ρ = μ.prod ν} (P.prod Q) where
  toIsEVar := by
    constructor
    · fun_prop
    rintro _ ⟨μ, hμS, ν, hνT, rfl⟩
    specialize hS μ hμS
    specialize hT ν hνT
    rw [lintegral_prod_mul (by fun_prop) (by fun_prop)]
    sorry
  isProbabilityMeasure := by
    rintro ρ ⟨μ, hμS, ν, hνT, rfl⟩
    specialize hS μ hμS
    specialize hT ν hνT
    infer_instance
  lintegral_div_le_one Y hY_evar := by
    sorry

end ProbabilityTheory
