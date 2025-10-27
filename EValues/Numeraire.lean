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

lemma lintegral_inv_le_one (hX : IsNumeraire X hS μ) : ∫⁻ ω, (X ω)⁻¹ ∂μ ≤ 1 := by
  simpa using hX.lintegral_ratio_le_one (isEVar_one S hS)

lemma ae_pos (hX : IsNumeraire X hS μ) : ∀ᵐ ω ∂μ, 0 < X ω := by
  suffices ∀ᵐ ω ∂μ, (X ω)⁻¹ < ∞ by
    simp only [pos_iff_ne_zero]
    filter_upwards [this] with ω hω using by simpa using hω.ne
  refine ae_lt_top ?_ ?_
  · have := hX.measurable
    fun_prop
  · exact ne_top_of_le_ne_top (by simp) (hX.lintegral_inv_le_one)

lemma ae_ne_zero (hX : IsNumeraire X hS μ) : ∀ᵐ ω ∂μ, X ω ≠ 0 := by
  filter_upwards [hX.ae_pos] with ω hω using hω.ne'

lemma lintegral_eq_setLIntegral_fsupport (hX : IsNumeraire X hS μ) (hY : IsEVar Y S) :
    ∫⁻ ω, Y ω / X ω ∂μ = ∫⁻ ω in X.fsupport, Y ω / X ω ∂μ := by
  rw [← lintegral_add_compl _ hX.measurable_fsupport]
  suffices ∫⁻ ω in X.fsupportᶜ, Y ω / X ω ∂μ = 0 by simp [this]
  rw [setLIntegral_eq_zero_iff (hX.measurable_fsupport).compl <| hY.measurable.div hX.measurable]
  filter_upwards [hX.ae_ne_zero] with ω hω hω₂
  simp only [fsupport, ne_eq, mem_compl_iff, mem_inter_iff, mem_setOf_eq, hω, not_false_eq_true,
    and_true, Decidable.not_not] at hω₂
  simp [hω₂]

lemma ae_top_implies_numeraire_top (hX : IsNumeraire X hS μ) (hY : IsEVar Y S) :
    ∀ᵐ ω ∂μ, Y ω = ∞ → X ω = ∞ := by
  by_contra h
  simp only [ae_iff, Classical.not_imp] at h
  have m : MeasurableSet {ω | Y ω = ∞ ∧ X ω ≠ ∞} :=
    MeasurableSet.inter ((measurableSet_singleton ∞).preimage hY.measurable)
      ((measurableSet_singleton ∞).compl.preimage hX.measurable)
  have lintegral_ratio_le_one := hX.lintegral_ratio_le_one hY
  rw [← lintegral_add_compl _ m] at lintegral_ratio_le_one
  suffices ∀ ω ∈ {ω | Y ω = ∞ ∧ X ω ≠ ∞}, Y ω / X ω = ∞ by
    rw [setLIntegral_congr_fun m this] at lintegral_ratio_le_one
    simp [top_mul h] at lintegral_ratio_le_one
  intro ω hω
  simp [hω.1, ENNReal.top_div, hω.2]

-- `rev`?
lemma lintegral_eq_setLIntegral_rev_fsupport (hX : IsNumeraire X hS μ) (hY : IsEVar Y S) :
    ∫⁻ ω, Y ω / X ω ∂μ = ∫⁻ ω in Y.fsupport, Y ω / X ω ∂μ := by
  rw [← lintegral_add_compl _ hY.measurable_fsupport]
  suffices ∫⁻ ω in Y.fsupportᶜ, Y ω / X ω ∂μ = 0 by simp [this]
  rw [setLIntegral_eq_zero_iff (hY.measurable_fsupport).compl
    <| hY.measurable.div hX.measurable]
  filter_upwards [hX.ae_top_implies_numeraire_top hY] with ω hω hω₂
  simp only [ENNReal.div_eq_zero_iff]
  by_cases hω_top : Y ω = ∞
  · simp [hω_top, hω hω_top]
  · simp only [fsupport, ne_eq, mem_compl_iff, mem_inter_iff, mem_setOf_eq, not_and,
      Decidable.not_not] at hω₂
    simp [hω_top, hω₂]

lemma measure_fsupport_ne_zero_or_ae_top (hX : IsNumeraire X hS μ) :
    μ X.fsupport ≠ 0 ∨ X =ᵐ[μ] fun _ ↦ ∞ := by
  by_contra! h
  have ratio_eq_zero : ∫⁻ ω, X ω / X ω ∂μ = 0 := by
    rw [hX.lintegral_eq_setLIntegral_fsupport hX.toIsEVar]
    exact setLIntegral_measure_zero _ _ h.1
  rw [lintegral_eq_zero_iff <| hX.measurable.div hX.measurable] at ratio_eq_zero
  have mₜ : MeasurableSet {ω | X ω = ∞} := hX.measurable <| measurableSet_singleton ∞
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
  · have : {ω | X ω = 0} = {ω | X ω ≠ 0}ᶜ := by ext; simp
    rw [this, hX.ae_ne_zero, add_zero, measure_univ, ← prob_compl_eq_zero_iff mₜ] at ratio_eq_zero
    exact h.2 ratio_eq_zero
  · exact Disjoint.preimage X (s := {∞}) (t := {0}) (by simp)

lemma inv_lintegral_eq_one (hX : IsNumeraire X hS μ) (hY : IsNumeraire Y hS μ)
    (h : μ X.fsupport ≠ 0) : (∫⁻ ω, Y ω / X ω ∂μ)⁻¹ = 1 := by
  set W := Y / X
  rw [hX.lintegral_eq_setLIntegral_fsupport hY.toIsEVar]
  suffices 1 ≤ (∫⁻ ω in X.fsupport, W ω ∂μ)⁻¹ by
    refine le_antisymm ?_ this
    suffices (∫⁻ ω in X.fsupport, W ω ∂μ)⁻¹ ≤ ∫⁻ ω in X.fsupport, (W ω)⁻¹ ∂μ by
      trans ∫⁻ ω in X.fsupport, (W ω)⁻¹ ∂μ
      · assumption
      · rw [setLIntegral_congr_fun hX.measurable_fsupport <| ENNReal.inv_div_fsupport Y X]
        rw [← hY.lintegral_eq_setLIntegral_rev_fsupport hX.toIsEVar]
        exact hY.lintegral_ratio_le_one hX.toIsEVar
    refine strictConvexOn_inv.convexOn.map_set_lintegral_le continuousOn_inv ?_ h ?_ ?_
    · exact isClosed_univ
    · simp
    · simp
  simp only [Pi.div_apply, ← hX.lintegral_eq_setLIntegral_fsupport hY.toIsEVar, le_inv_iff_mul_le,
    one_mul, W]
  exact hX.lintegral_ratio_le_one hY.toIsEVar

/-- The Numeraire is almost-everywhere unique. -/
lemma ae_unique (hX : IsNumeraire X hS μ) (hY : IsNumeraire Y hS μ) : X =ᵐ[μ] Y := by
  have strc_convex := strictConvexOn_inv
  rcases hY.measure_fsupport_ne_zero_or_ae_top with μ_fsupport | hYₜ
  · let W := X / Y
    have inv_avg_eq_one : (∫⁻ ω in Y.fsupport, W ω ∂μ)⁻¹ = 1 := by
      simp only [Pi.div_apply, ← hY.lintegral_eq_setLIntegral_fsupport hX.toIsEVar, W]
      exact hY.inv_lintegral_eq_one hX μ_fsupport
    have avg_eq_one : ∫⁻ ω, W ω ∂μ = 1 := by
      simp only [Pi.div_apply, ENNReal.inv_eq_one, W] at inv_avg_eq_one
      rwa [← hY.lintegral_eq_setLIntegral_fsupport hX.toIsEVar] at inv_avg_eq_one
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
        exact ENNReal.eq_of_div_eq_one hx
      · exfalso
        rw [inv_avg_eq_one,
          setLIntegral_congr_fun hY.measurable_fsupport <| ENNReal.inv_div_fsupport X Y] at h
        refine h.not_ge ?_
        rw [← hX.lintegral_eq_setLIntegral_rev_fsupport hY.toIsEVar]
        exact hX.lintegral_ratio_le_one hY.toIsEVar
    · suffices ∀ᵐ ω ∂μ, W ω = 0 by
        simp [lintegral_congr_ae this] at avg_eq_one
      filter_upwards [hYₜ] with ω hω
      simp_all [W]
  · filter_upwards [hYₜ, hX.ae_top_implies_numeraire_top hY.toIsEVar] with ω hω hω₂
    simp_all


end IsNumeraire

end MeasureTheory
