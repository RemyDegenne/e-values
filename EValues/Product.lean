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

/-- The numeraire of a product measure with respect to a product of sets is the product
of the numeraires. -/
lemma numeraire_prod (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, IsProbabilityMeasure μ) :
    IsNumeraire (fun (x : 𝓧 × 𝓨) ↦ numeraire P S x.1 * numeraire Q T x.2)
      {ρ | ∃ μ ∈ S, ∃ ν ∈ T, ρ = μ.prod ν} (P.prod Q) where
  measurable := by fun_prop
  lintegral_le_one := by
    rintro _ ⟨μ, hμS, ν, hνT, rfl⟩
    specialize hS μ hμS
    specialize hT ν hνT
    rw [lintegral_prod_mul (by fun_prop) (by fun_prop)]
    have h1 := (isEVar_numeraire P S).lintegral_le_one
    have h2 := (isEVar_numeraire Q T).lintegral_le_one
    exact mul_le_one' (h1 μ hμS) (h2 ν hνT)
  isProbabilityMeasure := by
    rintro _ ⟨μ, hμS, ν, hνT, rfl⟩
    specialize hS μ hμS
    specialize hT ν hνT
    infer_instance
  lintegral_div_le_one Y hY_evar := by
    have hY_meas := hY_evar.measurable
    rw [lintegral_prod _ (by fun_prop)]
    simp only [ge_iff_le]
    simp_rw [mul_comm (numeraire P S _)]
    have h_eq : ∫⁻ x, ∫⁻ y, Y (x, y) / (numeraire Q T y * numeraire P S x) ∂Q ∂P
        = ∫⁻ x, (∫⁻ y, Y (x, y) / numeraire Q T y ∂Q) / numeraire P S x ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [(isNumeraire_numeraire P hS).ae_ne_zero] with x hx
      simp_rw [div_eq_mul_inv]
      rw [← lintegral_mul_const _ (by fun_prop)]
      refine lintegral_congr_ae ?_
      filter_upwards [(isNumeraire_numeraire Q hT).ae_ne_zero] with y hy
      rw [ENNReal.mul_inv (.inl hy) (.inr hx), mul_assoc]
    suffices IsEVar (fun x ↦ ∫⁻ y, Y (x, y) / numeraire Q T y ∂Q) S by
      rw [h_eq]
      exact (isNumeraire_numeraire P hS).lintegral_div_le_one this
    constructor
    · fun_prop
    intro μ hμS
    have := (isNumeraire_numeraire P hS).isProbabilityMeasure μ hμS
    rw [lintegral_lintegral_swap (by fun_prop)]
    have h_eq' : ∫⁻ y, ∫⁻ x, Y (x, y) / numeraire Q T y ∂μ ∂Q
        = ∫⁻ y, (∫⁻ x, Y (x, y) ∂μ) / numeraire Q T y ∂Q := by
      congr with y
      simp_rw [div_eq_mul_inv]
      rw [lintegral_mul_const _ (by fun_prop)]
    suffices IsEVar (fun y ↦ ∫⁻ x, Y (x, y) ∂μ) T by
      rw [h_eq']
      exact (isNumeraire_numeraire Q hT).lintegral_div_le_one this
    constructor
    · fun_prop
    intro ν hνT
    have := (isNumeraire_numeraire Q hT).isProbabilityMeasure ν hνT
    rw [lintegral_lintegral_symm (by fun_prop)]
    exact hY_evar.lintegral_le_one (μ.prod ν) ⟨μ, hμS, ν, hνT, rfl⟩

end ProbabilityTheory
