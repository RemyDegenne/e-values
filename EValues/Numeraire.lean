/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib
import EValues.EValue
import EValues.Mathlib.EDiv
import EValues.Mathlib.Convex
import EValues.Mathlib.Jensen
import EValues.Mathlib.ENNReal

/-!
# Numeraire E-variables



## Main definitions

* TODO

## Main statements

* TODO

-/

open ENNReal

open MeasureTheory ProbabilityTheory Set Function

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}

namespace MeasureTheory

/-- A random variable `X` is the numeraire for a set of measures `S` and a measure `μ`
if it is an E-variable for `S` and the expectation of the ratio of any E-variable `Y` over `X`
is at most one under `μ`. -/
structure IsNumeraire (X : 𝓧 → ℝ≥0∞) {S : Set (Measure 𝓧)} (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    (μ : Measure 𝓧) [IsProbabilityMeasure μ] : Prop extends IsEVar X S where
  lintegral_ratio_le_one : ∀ ⦃Y⦄, IsEVar Y S → ∫⁻ ω, Y ω / X ω ∂μ ≤ 1

namespace IsNumeraire

variable {X Y : 𝓧 → ℝ≥0∞} {μ : Measure 𝓧} [IsProbabilityMeasure μ] {S : Set (Measure 𝓧)}
  {hS : ∀ μ ∈ S, IsProbabilityMeasure μ}

lemma ae_pos (hX : IsNumeraire X hS μ) : ∀ᵐ ω ∂μ, X ω ≠ 0 := by
  by_contra h
  suffices ∫⁻ ω, (X ω)⁻¹ ∂μ = ⊤ by
    have lintegral_ratio_le_one := hX.lintegral_ratio_le_one (isEVar_one S hS)
    simp only [Pi.one_apply, one_div, this] at lintegral_ratio_le_one
    contradiction
  refine lintegral_eq_top_of_measure_eq_top_ne_zero hX.measurable.inv.aemeasurable ?_
  unfold Filter.Eventually at h
  simp [MeasureTheory.ae] at h
  suffices {ω | X ω ≠ 0}ᶜ = {ω | (X ω)⁻¹ = ⊤} by
    rwa [← this]
  ext ω
  simp

lemma lintegral_eq_lintegral_on_support (hX : IsNumeraire X hS μ)
    (hY : IsEVar Y S) : ∫⁻ ω, Y ω / X ω ∂μ = ∫⁻ ω in {ω | X ω ≠ ⊤ ∧ X ω ≠ 0}, Y ω / X ω ∂μ := by
  rw [← lintegral_add_compl _ hX.measurable_support]
  suffices ∫⁻ ω in {ω | X ω ≠ ⊤ ∧ X ω ≠ 0}ᶜ, Y ω / X ω ∂μ = 0 by
    simp [this]
  rw [setLIntegral_eq_zero_iff (hX.measurable_support).compl <| hY.measurable.div hX.measurable]
  filter_upwards [hX.ae_pos] with ω hω hω₂
  simp only [ne_eq, mem_compl_iff, mem_setOf_eq, not_and_or, not_not] at hω₂
  rcases hω₂ with hω₂ | hω₂
  · simp [hω₂]
  · contradiction

lemma lintegral_eq_lintegral_on_reverse_support (hX : IsNumeraire X hS μ)
    (hY : IsEVar Y S) : ∫⁻ ω, Y ω / X ω ∂μ = ∫⁻ ω in {ω | Y ω ≠ ⊤ ∧ Y ω ≠ 0}, Y ω / X ω ∂μ := by
  rw [← lintegral_add_compl _ hY.measurable_support]
  suffices ∫⁻ ω in {ω | Y ω ≠ ⊤ ∧ Y ω ≠ 0}ᶜ, Y ω / X ω ∂μ = 0 by
    simp [this]
  rw [setLIntegral_eq_zero_iff (hY.measurable_support).compl <| hY.measurable.div hX.measurable]
  have : ∀ᵐ ω ∂μ, Y ω = ⊤ → X ω = ⊤ := by
    by_contra h
    have lintegral_ratio_le_one := hX.lintegral_ratio_le_one hY
    unfold Filter.Eventually at h
    replace h : μ {ω | Y ω = ⊤ → X ω = ⊤}ᶜ ≠ 0 := h
    have : {ω | Y ω = ⊤ → X ω = ⊤}ᶜ = {ω | Y ω = ⊤ ∧ X ω ≠ ⊤} := by
      ext ω
      simp
    rw [this] at h
    clear this
    have m : MeasurableSet {ω | Y ω = ⊤ ∧ X ω ≠ ⊤} := by
      suffices MeasurableSet {ω | Y ω = ⊤} ∧ MeasurableSet {ω | X ω ≠ ⊤} from this.1.inter this.2
      constructor
      · exact hY.measurable <| measurableSet_singleton ⊤
      · rw [← MeasurableSet.compl_iff]
        suffices {ω | X ω ≠ ⊤}ᶜ = {ω | X ω = ⊤} by
          rw [this]
          exact hX.measurable <| measurableSet_singleton ⊤
        ext ω
        simp
    rw [← lintegral_add_compl _ m] at lintegral_ratio_le_one
    suffices ∀ ω ∈ {ω | Y ω = ⊤ ∧ X ω ≠ ⊤}, Y ω / X ω = ⊤ by
      rw [setLIntegral_congr_fun m this] at lintegral_ratio_le_one
      simp only [ne_eq, lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
        univ_inter] at lintegral_ratio_le_one
      rw [top_mul h] at lintegral_ratio_le_one
      contradiction
    intro ω hω
    simp [hω.1, ENNReal.top_div, hω.2]
  filter_upwards [this] with ω hω hω₂
  simp only [ne_eq, mem_compl_iff, mem_setOf_eq, not_and_or, not_not] at hω₂
  rcases hω₂ with hω₂ | hω₂
  · rw [hω₂, hω hω₂]
    simp
  · rw [hω₂]
    simp

lemma measure_support_ne_zero_or_ae_top (hX : IsNumeraire X hS μ) :
    μ {ω | X ω ≠ ⊤ ∧ X ω ≠ 0} ≠ 0 ∨ X =ᵐ[μ] ⊤ := by
  by_contra h
  push_neg at h
  have ratio_eq_zero : ∫⁻ ω, X ω / X ω ∂μ = 0 := by
    rw [hX.lintegral_eq_lintegral_on_support hX.toIsEVar]
    exact setLIntegral_measure_zero _ _ h.1
  rw [lintegral_eq_zero_iff <| hX.measurable.div hX.measurable] at ratio_eq_zero
  have mₜ : MeasurableSet {ω | X ω = ⊤} := hX.measurable <| measurableSet_singleton ⊤
  have m₀ : MeasurableSet {ω | X ω = 0} := hX.measurable <| measurableSet_singleton 0
  replace ratio_eq_zero : μ ({ω | X ω = 0} ∪ {ω | X ω = ⊤}) = μ univ := by
    rw [measure_univ, ← prob_compl_eq_zero_iff <| m₀.union mₜ]
    suffices ({ω | X ω = 0} ∪ {ω | X ω = ⊤}) ∈ ae μ by
      simp_all [MeasureTheory.ae]
    filter_upwards [ratio_eq_zero] with ω hω
    simp_all
  rw [measure_union ?_ mₜ] at ratio_eq_zero
  · have : {ω | X ω = 0} = {ω | X ω ≠ 0}ᶜ := by
      ext ω
      simp
    rw [this, hX.ae_pos, zero_add, measure_univ, ← prob_compl_eq_zero_iff mₜ] at ratio_eq_zero
    exact h.2 ratio_eq_zero
  · rw [disjoint_iff_inter_eq_empty]
    ext ω
    simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro hω
    rw [hω]
    simp

/-- This is most-likely false as `X` can be infinite a.e. and therefore the measure of
`{ω | X ω ≠ ⊤ ∧ X ω ≠ 0}` can be `0`. If it happens, `Y` must also be equal to `⊤` a.e. as
the integral of `X / Y` must be finite. In the original paper, the authors
set `⊤ / ⊤ = 1` which makes this lemma true, but this is not compatible with Lean's
definition of division on `ℝ≥0∞`. -/
lemma inv_lintegral_eq_one (hX : IsNumeraire X hS μ) (hY : IsNumeraire Y hS μ) :
    (∫⁻ ω, Y ω / X ω ∂μ)⁻¹ = 1 := by
  set W := Y / X
  set E := {ω | X ω ≠ ⊤ ∧ X ω ≠ 0}
  have mE : MeasurableSet E := hX.measurable_support
  rw [hX.lintegral_eq_lintegral_on_support hY.toIsEVar]
  suffices 1 ≤ (∫⁻ ω in E, W ω ∂μ)⁻¹ by
    refine ENNReal.le_antisymm_iff_toReal this ?_
    suffices (∫⁻ ω in E, W ω ∂μ)⁻¹ ≤ ∫⁻ ω in E, (W ω)⁻¹ ∂μ by
      trans ∫⁻ ω in E, (W ω)⁻¹ ∂μ
      · assumption
      · have : ∀ ω ∈ E, ((Y / X) ω)⁻¹ = Y ω / X ω := by sorry
        rw [setLIntegral_congr_fun mE this]
        rw [← hX.lintegral_eq_lintegral_on_support hY.toIsEVar]
        exact hX.lintegral_ratio_le_one hY.toIsEVar
    rcases hX.measure_support_ne_zero_or_ae_top with hX₀ | hXₜ
    · refine strictConvexOn_inv.convexOn.map_set_lintegral_le continuousOn_inv ?_ hX₀ ?_ ?_
      · exact isClosed_univ
      · simp
      · simp
    · have : ∀ᵐ ω ∂μ, ω ∈ E → W ω = 0 := by sorry
      rw [setLIntegral_congr_fun_ae mE this]
      have : ∀ᵐ ω ∂μ, ω ∈ E → (W ω)⁻¹ = ⊤ := by sorry
      rw [setLIntegral_congr_fun_ae mE this]
      simp
      sorry
  simp only [ne_eq, Pi.div_apply, ← hX.lintegral_eq_lintegral_on_support hY.toIsEVar,
    le_inv_iff_mul_le, one_mul, E, W]
  exact hX.lintegral_ratio_le_one hY.toIsEVar

lemma ae_unique (hX : IsNumeraire X hS μ) (hY : IsNumeraire Y hS μ) : X =ᵐ[μ] Y := by
  have strc_convex := strictConvexOn_inv
  let W := X / Y
  let E := {ω | Y ω ≠ ⊤ ∧ Y ω ≠ 0}
  have mE : MeasurableSet E := hY.measurable_support
  have inv_avg_eq_one : (∫⁻ ω in E, W ω ∂μ)⁻¹ = 1 := by
    simp only [ne_eq, Pi.div_apply, ← hY.lintegral_eq_lintegral_on_support hX.toIsEVar, E, W]
    exact hY.inv_lintegral_eq_one hX
  have avg_eq_one : ∫⁻ ω, W ω ∂μ = 1 := by
    simp only [ne_eq, Pi.div_apply, ENNReal.inv_eq_one, E, W] at inv_avg_eq_one
    rwa [← hY.lintegral_eq_lintegral_on_support hX.toIsEVar] at inv_avg_eq_one
  rcases hY.measure_support_ne_zero_or_ae_top with hY₀ | hYₜ
  · have strict_Jensen : W =ᵐ[μ] const 𝓧 (∫⁻ ω, W ω ∂μ) ∨
        (∫⁻ ω in E, W ω ∂μ)⁻¹ < ∫⁻ ω in E, (W ω)⁻¹ ∂μ := by
      refine strc_convex.ae_eq_const_or_map_set_lintegral_lt continuousOn_inv ?_ hY₀ ?_ ?_
      · exact isClosed_univ
      · simp
      · simp
    rcases strict_Jensen with h | h
    · rw [avg_eq_one] at h
      filter_upwards [h] with ω hx
      simp only [Pi.div_apply, const_apply, W] at hx
      exact ENNReal.div_eq_one_imp_eq hx
    · exfalso
      rw [inv_avg_eq_one] at h
      have inv_div : ∀ ω ∈ E, ((X / Y) ω)⁻¹ = Y ω / X ω := by
        intro ω hω
        simp only [Pi.div_apply]
        rw [ENNReal.inv_div]
        · exact Or.inl hω.1
        · exact Or.inl hω.2
      rw [setLIntegral_congr_fun mE inv_div] at h
      refine ENNReal.lt_and_le_false h ?_
      rw [← hX.lintegral_eq_lintegral_on_reverse_support hY.toIsEVar]
      exact hX.lintegral_ratio_le_one hY.toIsEVar
  · suffices ∀ᵐ ω ∂μ, W ω = 0 by
      simp [lintegral_congr_ae this] at avg_eq_one
    filter_upwards [hYₜ] with ω hω
    simp_all [W]

end IsNumeraire

end MeasureTheory
