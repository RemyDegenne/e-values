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

/-!
# E-variables



## Main definitions

* TODO

## Main statements

* TODO

-/

open scoped ENNReal

open MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {S : Set (Measure Ω)}

noncomputable
def pairingFun (s : SignedMeasure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ ω, f ω ∂s.toJordanDecomposition.posPart
    - ∫ ω, f ω ∂s.toJordanDecomposition.negPart

def integrableFunctions (S : Set (Measure Ω)) :=
  {f : Ω → ℝ | Measurable f ∧ ∀ μ ∈ S, Integrable f μ}

def integrableMeasures (L : Set (Ω → ℝ)) := {μ : Measure Ω | ∀ f ∈ L, Integrable f μ}

def integrableSignedMeasures (L : Set (Ω → ℝ)) :=
  {s : SignedMeasure Ω | ∀ f ∈ L, Integrable f s.totalVariation}
-- being integrable against `totalVariation` is equivalent to being integrable against both
-- positive and negative parts. That is, both parts are in `integrableMeasures L`.

end MeasureTheory

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧} {S : Set (Measure 𝓧)}

structure IsEVar (X : 𝓧 → ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  measurable : Measurable X
  lintegral_le_one : ∀ μ ∈ S, ∫⁻ ω, X ω ∂μ ≤ 1

structure IsRandEVar (κ : Kernel 𝓧 ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  lintegral_le_one : ∀ μ ∈ S, ∫⁻ ω, ω ∂(κ ∘ₘ μ) ≤ 1

end ProbabilityTheory
