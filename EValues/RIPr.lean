/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import EValues.DPI
import EValues.NumeraireExistence
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Reverse Information Projection

## Main definitions

* TODO

## Main statements

* TODO

-/

open scoped ENNReal NNReal ProbabilityTheory

open MeasureTheory ProbabilityTheory InformationTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {P : Measure 𝓧} {S : Set (Measure 𝓧)}

namespace ProbabilityTheory

/-- Reverse Information Projection. -/
noncomputable
def ripr (P : Measure 𝓧) (S : Set (Measure 𝓧)) : Measure 𝓧 :=
  P.withDensity fun ω ↦ (numeraire P S ω)⁻¹

lemma ripr_univ_le_one (P : Measure 𝓧) [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    ripr P S .univ ≤ 1 := by
  rw [ripr, withDensity_apply _ .univ, setLIntegral_univ]
  simpa using (isNumeraire_numeraire P hS).lintegral_div_le_one (isEVar_fun_one S hS)

lemma isFiniteMeasure_ripr (P : Measure 𝓧) [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    IsFiniteMeasure (ripr P S) where
  measure_univ_lt_top := by
    rw [lt_top_iff_ne_top]
    exact ne_top_of_le_ne_top (by simp) (ripr_univ_le_one P hS)

-- not true because our definition of klDiv compensates for non-probability measures
lemma maxUtility_eq_klDiv (P : Measure 𝓧) [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    maxUtility P S logUtility = klDiv P (ripr P S) := by
  have := isFiniteMeasure_ripr P hS
  rw [maxUtility_eq_integral_numeraire _ hS, klDiv_eq_lintegral_klFun]
  sorry

end ProbabilityTheory
