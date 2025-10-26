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

lemma lintegral_eq_lintegral_on_fsupport (hX : IsNumeraire X hS μ)
    (hY : IsEVar Y S) : ∫⁻ ω, Y ω / X ω ∂μ = ∫⁻ ω in X.fsupport, Y ω / X ω ∂μ := by
  rw [← lintegral_add_compl _ hX.measurable_fsupport]
  suffices ∫⁻ ω in X.fsupportᶜ, Y ω / X ω ∂μ = 0 by
    simp [this]
  rw [setLIntegral_eq_zero_iff (hX.measurable_fsupport).compl
    <| hY.measurable.div hX.measurable]
  filter_upwards [hX.ae_pos] with ω hω hω₂
  rw [X.fsupport_compl] at hω₂
  rcases hω₂ with hω₂ | hω₂
  · simp_all
  · contradiction

lemma ae_top_implies_numeraire_top (hX : IsNumeraire X hS μ) (hY : IsEVar Y S) :
    ∀ᵐ ω ∂μ, Y ω = ⊤ → X ω = ⊤ := by
  by_contra h
  unfold Filter.Eventually at h
  replace h : μ {ω | Y ω = ⊤ ∧ X ω ≠ ⊤} ≠ 0 := by
    suffices {ω | Y ω = ⊤ ∧ X ω ≠ ⊤} = {ω | Y ω = ⊤ → X ω = ⊤}ᶜ by
      rw [this]
      exact h
    ext ω
    simp
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
  have lintegral_ratio_le_one := hX.lintegral_ratio_le_one hY
  rw [← lintegral_add_compl _ m] at lintegral_ratio_le_one
  suffices ∀ ω ∈ {ω | Y ω = ⊤ ∧ X ω ≠ ⊤}, Y ω / X ω = ⊤ by
    rw [setLIntegral_congr_fun m this] at lintegral_ratio_le_one
    simp only [ne_eq, lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
      univ_inter] at lintegral_ratio_le_one
    rw [top_mul h] at lintegral_ratio_le_one
    contradiction
  intro ω hω
  simp [hω.1, ENNReal.top_div, hω.2]

lemma lintegral_eq_lintegral_on_rev_fsupport (hX : IsNumeraire X hS μ)
    (hY : IsEVar Y S) : ∫⁻ ω, Y ω / X ω ∂μ = ∫⁻ ω in Y.fsupport, Y ω / X ω ∂μ := by
  rw [← lintegral_add_compl _ hY.measurable_fsupport]
  suffices ∫⁻ ω in Y.fsupportᶜ, Y ω / X ω ∂μ = 0 by
    simp [this]
  rw [setLIntegral_eq_zero_iff (hY.measurable_fsupport).compl
    <| hY.measurable.div hX.measurable]
  filter_upwards [hX.ae_top_implies_numeraire_top hY] with ω hω hω₂
  rw [Y.fsupport_compl] at hω₂
  rcases hω₂ with hω₂ | hω₂
  · rw [hω₂, hω hω₂]
    simp
  · rw [hω₂]
    simp

lemma measure_fsupport_ne_zero_or_ae_top (hX : IsNumeraire X hS μ) :
    μ X.fsupport ≠ 0 ∨ X =ᵐ[μ] ⊤ := by
  by_contra h
  push_neg at h
  have ratio_eq_zero : ∫⁻ ω, X ω / X ω ∂μ = 0 := by
    rw [hX.lintegral_eq_lintegral_on_fsupport hX.toIsEVar]
    exact setLIntegral_measure_zero _ _ h.1
  rw [lintegral_eq_zero_iff <| hX.measurable.div hX.measurable] at ratio_eq_zero
  have mₜ : MeasurableSet {ω | X ω = ⊤} := hX.measurable <| measurableSet_singleton ⊤
  have m₀ : MeasurableSet {ω | X ω = 0} := hX.measurable <| measurableSet_singleton 0
  replace ratio_eq_zero : μ X.fsupportᶜ = μ univ := by
    rw [measure_univ, ← prob_compl_eq_zero_iff hX.measurable_fsupport.compl]
    suffices X.fsupportᶜ ∈ ae μ by
      simp_all [X.fsupport_compl, MeasureTheory.ae]
    filter_upwards [ratio_eq_zero] with ω hω
    simp_all only [measurableSet_setOf, X.fsupport_compl, Pi.zero_apply,
      ENNReal.div_eq_zero_iff, mem_union, mem_setOf_eq]
    exact hω.symm
  rw [X.fsupport_compl, measure_union ?_ m₀] at ratio_eq_zero
  · have : {ω | X ω = 0} = {ω | X ω ≠ 0}ᶜ := by
      ext ω
      simp
    rw [this, hX.ae_pos, add_zero, measure_univ, ← prob_compl_eq_zero_iff mₜ] at ratio_eq_zero
    exact h.2 ratio_eq_zero
  · rw [disjoint_iff_inter_eq_empty]
    ext ω
    simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro hω
    rw [hω]
    simp

lemma inv_lintegral_eq_one (hX : IsNumeraire X hS μ) (hY : IsNumeraire Y hS μ)
    (h : μ X.fsupport ≠ 0) : (∫⁻ ω, Y ω / X ω ∂μ)⁻¹ = 1 := by
  set W := Y / X
  rw [hX.lintegral_eq_lintegral_on_fsupport hY.toIsEVar]
  suffices 1 ≤ (∫⁻ ω in X.fsupport, W ω ∂μ)⁻¹ by
    refine ENNReal.le_antisymm_iff_toReal this ?_
    suffices (∫⁻ ω in X.fsupport, W ω ∂μ)⁻¹ ≤ ∫⁻ ω in X.fsupport, (W ω)⁻¹ ∂μ by
      trans ∫⁻ ω in X.fsupport, (W ω)⁻¹ ∂μ
      · assumption
      · rw [setLIntegral_congr_fun hX.measurable_fsupport <| ENNReal.inv_div_fsupport Y X]
        rw [← hY.lintegral_eq_lintegral_on_rev_fsupport hX.toIsEVar]
        exact hY.lintegral_ratio_le_one hX.toIsEVar
    refine strictConvexOn_inv.convexOn.map_set_lintegral_le continuousOn_inv ?_ h ?_ ?_
    · exact isClosed_univ
    · simp
    · simp
  simp only [Pi.div_apply, ← hX.lintegral_eq_lintegral_on_fsupport hY.toIsEVar, le_inv_iff_mul_le,
    one_mul, W]
  exact hX.lintegral_ratio_le_one hY.toIsEVar

/-- The Numeraire is almost-everywhere unique. -/
lemma ae_unique (hX : IsNumeraire X hS μ) (hY : IsNumeraire Y hS μ) : X =ᵐ[μ] Y := by
  have strc_convex := strictConvexOn_inv
  rcases hY.measure_fsupport_ne_zero_or_ae_top with μ_fsupport | hYₜ
  · let W := X / Y
    have inv_avg_eq_one : (∫⁻ ω in Y.fsupport, W ω ∂μ)⁻¹ = 1 := by
      simp only [Pi.div_apply, ← hY.lintegral_eq_lintegral_on_fsupport hX.toIsEVar, W]
      exact hY.inv_lintegral_eq_one hX μ_fsupport
    have avg_eq_one : ∫⁻ ω, W ω ∂μ = 1 := by
      simp only [Pi.div_apply, ENNReal.inv_eq_one, W] at inv_avg_eq_one
      rwa [← hY.lintegral_eq_lintegral_on_fsupport hX.toIsEVar] at inv_avg_eq_one
    rcases hY.measure_fsupport_ne_zero_or_ae_top with hY₀ | hYₜ
    · have strict_Jensen : W =ᵐ[μ] const 𝓧 (∫⁻ ω, W ω ∂μ) ∨
          (∫⁻ ω in Y.fsupport, W ω ∂μ)⁻¹ < ∫⁻ ω in Y.fsupport, (W ω)⁻¹ ∂μ := by
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
        rw [setLIntegral_congr_fun hY.measurable_fsupport <| ENNReal.inv_div_fsupport X Y] at h
        refine ENNReal.lt_and_le_false h ?_
        rw [← hX.lintegral_eq_lintegral_on_rev_fsupport hY.toIsEVar]
        exact hX.lintegral_ratio_le_one hY.toIsEVar
    · suffices ∀ᵐ ω ∂μ, W ω = 0 by
        simp [lintegral_congr_ae this] at avg_eq_one
      filter_upwards [hYₜ] with ω hω
      simp_all [W]
  · filter_upwards [hYₜ, hX.ae_top_implies_numeraire_top hY.toIsEVar] with ω hω hω₂
    simp_all


end IsNumeraire

end MeasureTheory
