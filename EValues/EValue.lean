/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib

/-!
# E-variables



## Main definitions

* TODO

## Main statements

* TODO

-/

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {S : Set (Measure Ω)}

structure IsEVar (X : Ω → ℝ≥0∞) (S : Set (Measure Ω)) : Prop where
  measurable : Measurable X
  integrable : ∀ μ ∈ S, ∫⁻ ω, X ω ∂μ ≤ 1

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
