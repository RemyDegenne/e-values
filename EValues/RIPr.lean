/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import EValues.DPI
import EValues.NumeraireExistence
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Reverse Information Projection and duality

## Main definitions

* `ripr P S`: Reverse Information Projection of the measure `P` on the set `S`.
  It is defined as `P.withDensity fun ω ↦ (numeraire P S ω)⁻¹`.
* `KL`: a version of the Kullback-Leibler divergence between two measures, which differ from the
  one in Mathlib (`klDiv`) in that it has only the integral term. It does not compensate for the
  case where the measures are not probability measures.

## Main statements

* `maxUtility_eq_KL_ripr`: if the numeraire is almost everywhere finite, then
  `maxUtility P S logUtility = KL P (ripr P S)`.

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

lemma ripr_univ (P : Measure 𝓧) : ripr P S .univ = ∫⁻ x, (numeraire P S x)⁻¹ ∂P := by
  rw [ripr, withDensity_apply _ .univ, setLIntegral_univ]

lemma ripr_univ_le_measure_fsupport (P : Measure 𝓧) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ripr P S .univ ≤ P (numeraire P S).fsupport := by
  rw [ripr_univ]
  simpa using (isNumeraire_numeraire P hS).lintegral_div_le_measure_fsupport (isEVar_fun_one S)

lemma ripr_univ_le_measure_univ (P : Measure 𝓧) :
    ripr P S .univ ≤ P .univ := by
  by_cases hS : ∀ μ ∈ S, IsFiniteMeasure μ
  · exact (ripr_univ_le_measure_fsupport P hS).trans (measure_mono (Set.subset_univ _))
  · unfold ripr numeraire
    simp [hS]

lemma ripr_univ_le_one (P : Measure 𝓧) [IsProbabilityMeasure P] :
    ripr P S .univ ≤ 1 := by simpa using ripr_univ_le_measure_univ P

instance isFiniteMeasure_ripr (P : Measure 𝓧) [IsFiniteMeasure P] : IsFiniteMeasure (ripr P S) where
  measure_univ_lt_top := by
    rw [lt_top_iff_ne_top]
    exact ne_top_of_le_ne_top (by simp) (ripr_univ_le_measure_univ P)

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

lemma llr_div_ripr' [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    llr P (ripr P S) =ᵐ[P] fun x ↦ (ENNReal.log (numeraire P S x)).toReal := by
  have h_ne_zero := (isNumeraire_numeraire P hS).ae_ne_zero
  filter_upwards [h_ne_zero, h_top, llr_div_ripr hS h_top] with x hx1 hx2
  unfold ENNReal.log
  simp [hx1, hx2]

open Classical in
/-- A version of the Kullback-Leibler divergence between two measures. -/
noncomputable irreducible_def KL (μ ν : Measure 𝓧) : ℝ≥0∞ :=
  if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, llr μ ν x ∂μ) else ∞

lemma eintegral_log_numeraire_eq_integral [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤)
    (h_int : ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P ≠ ⊤) :
    ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P = ∫ x, Real.log (numeraire P S x).toReal ∂P := by
  rw [eintegral_eq_integral_toReal (by fun_prop) _ h_int]
  · congr 1
    refine integral_congr_ae ?_
    have h_ne_zero := (isNumeraire_numeraire P hS).ae_ne_zero
    filter_upwards [h_ne_zero, h_top] with x hx1 hx2
    unfold ENNReal.log
    simp [hx1, hx2]
  · exact (neBotUtilityEVar_numeraire hS).utility_ne_bot

lemma integrable_llr_div_ripr_iff [IsFiniteMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    Integrable (llr P (ripr P S)) P ↔ ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P ≠ ⊤ := by
  rw [integrable_congr (llr_div_ripr' hS h_top)]
  rw [integrable_ereal_toReal_iff (by fun_prop)]
  · have h_bot := (neBotUtilityEVar_numeraire (P := P) hS).utility_ne_bot
    simp only [Function.comp_apply, ne_eq, logUtility] at h_bot
    simp [h_bot]
  · simp only [ne_eq, ENNReal.log_eq_bot_iff]
    exact (isNumeraire_numeraire P hS).ae_ne_zero
  · simpa

lemma maxUtility_eq_KL_ripr [IsFiniteMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    maxUtility P S logUtility = KL P (ripr P S) := by
  have h_ac : P ≪ ripr P S := absolutelyContinuous_ripr_of_ae_ne_top h_top
  rw [maxUtility_eq_integral_numeraire _ hS, KL]
  by_cases h_int : Integrable (llr P (ripr P S)) P
  · simp only [h_ac, h_int, and_self, ↓reduceIte]
    rw [integral_congr_ae (llr_div_ripr hS h_top)]
    rw [integrable_congr (llr_div_ripr' hS h_top)] at h_int
    have h_int' := (integrable_ereal_toReal_iff (by fun_prop) ?_ ?_).mp h_int
    rotate_left
    · simp only [ne_eq, ENNReal.log_eq_bot_iff]
      exact (isNumeraire_numeraire P hS).ae_ne_zero
    · simpa
    rw [eintegral_log_numeraire_eq_integral hS h_top h_int'.2]
    congr
    simp only [NNReal.val_eq_coe, Real.coe_toNNReal', left_eq_sup]
    suffices 0 ≤ ((∫ x, Real.log (numeraire P S x).toReal ∂P : ℝ) : EReal) by simpa
    rw [← eintegral_log_numeraire_eq_integral hS h_top h_int'.2]
    exact (isNumeraire_numeraire P hS).eintegral_log_nonneg
  · simp only [h_int, and_false, ↓reduceIte, EReal.coe_ennreal_top]
    rw [integrable_llr_div_ripr_iff hS h_top] at h_int
    simpa using h_int

end ProbabilityTheory
