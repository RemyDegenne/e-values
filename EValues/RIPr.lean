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

lemma ripr_univ_le_measure_univ (P : Measure 𝓧) [IsFiniteMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ripr P S .univ ≤ P .univ := by
  rw [ripr, withDensity_apply _ .univ, setLIntegral_univ]
  simpa using (isNumeraire_numeraire P hS).lintegral_div_le_measure_univ (isEVar_fun_one S)

lemma ripr_univ_le_one (P : Measure 𝓧) [IsProbabilityMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ripr P S .univ ≤ 1 := by simpa using ripr_univ_le_measure_univ P hS

lemma isFiniteMeasure_ripr (P : Measure 𝓧) [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    IsFiniteMeasure (ripr P S) where
  measure_univ_lt_top := by
    rw [lt_top_iff_ne_top]
    exact ne_top_of_le_ne_top (by simp) (ripr_univ_le_measure_univ P hS)

lemma absolutelyContinuous_ripr_of_ae_ne_top (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    P ≪ ripr P S := by
  refine withDensity_absolutelyContinuous' (by fun_prop) ?_
  simp only [ne_eq, ENNReal.inv_eq_zero, h_top]

lemma rnDeriv_div_ripr [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    P.rnDeriv (ripr P S) =ᵐ[P] numeraire P S := by
  refine (Measure.rnDeriv_withDensity_right _ _ (by fun_prop) ?_ ?_).trans ?_
  · simpa
  · simp only [ne_eq, ENNReal.inv_eq_top]
    exact IsNumeraire.ae_ne_zero (isNumeraire_numeraire P hS)
  simp only [inv_inv]
  filter_upwards [Measure.rnDeriv_self P] with x hx using by simp [hx]

lemma llr_div_ripr [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    llr P (ripr P S) =ᵐ[P] fun x ↦ Real.log (numeraire P S x).toReal := by
  unfold llr
  filter_upwards [rnDeriv_div_ripr hS h_top] with x hx using by simp [hx]

-- not true because our definition of klDiv compensates for non-probability measures
lemma maxUtility_eq_klDiv (P : Measure 𝓧) [IsFiniteMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    maxUtility P S logUtility = klDiv P (ripr P S) := by
  have := isFiniteMeasure_ripr P hS
  rw [maxUtility_eq_integral_numeraire _ hS]
  rw [klDiv]
  -- rw [klDiv_eq_lintegral_klFun]
  have h_int : Integrable (llr P (ripr P S)) P := by sorry
  have h_ac : P ≪ ripr P S := sorry -- may not be true. for simplicity
  have h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤ := by sorry -- same
  simp only [h_ac, h_int, and_self, ↓reduceIte, measureReal_def, EReal.coe_ennreal_ofReal]
  rw [integral_congr_ae (llr_div_ripr hS h_top)]
  sorry

structure IsNullMeasure (μ : Measure 𝓧) (E : Set (𝓧 → ℝ≥0∞)) : Prop where
  isFiniteMeasure : IsFiniteMeasure μ
  eintegral_nonpos : ∀ f ∈ E, ∫ᵉ x, f x - 1 ∂μ ≤ 0

end ProbabilityTheory
