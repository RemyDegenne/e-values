/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/

import EValues.EValue
import EValues.Mathlib.Convex
import EValues.Mathlib.Jensen
import EValues.Utility
import Mathlib.MeasureTheory.Constructions.Polish.Basic

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
  lintegral_div_le_one : ∀ ⦃Y⦄, IsEVar Y S → ∫⁻ ω, Y ω / X ω ∂μ ≤ 1

namespace IsNumeraire

variable {X Y : 𝓧 → ℝ≥0∞} {μ : Measure 𝓧} [IsProbabilityMeasure μ] {S : Set (Measure 𝓧)}
  {hS : ∀ μ ∈ S, IsProbabilityMeasure μ}

lemma lintegral_inv_le_one (hX : IsNumeraire X hS μ) : ∫⁻ ω, (X ω)⁻¹ ∂μ ≤ 1 := by
  simpa using hX.lintegral_div_le_one (isEVar_one S hS)

lemma ae_pos (hX : IsNumeraire X hS μ) : ∀ᵐ ω ∂μ, 0 < X ω := by
  suffices ∀ᵐ ω ∂μ, (X ω)⁻¹ < ∞ by
    simp only [pos_iff_ne_zero]
    filter_upwards [this] with ω hω using by simpa using hω.ne
  refine ae_lt_top ?_ ?_
  · have := hX.measurable
    fun_prop
  · exact ne_top_of_le_ne_top (by simp) hX.lintegral_inv_le_one

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
  have lintegral_div_le_one := hX.lintegral_div_le_one hY
  rw [← lintegral_add_compl _ m] at lintegral_div_le_one
  suffices ∀ ω ∈ {ω | Y ω = ∞ ∧ X ω ≠ ∞}, Y ω / X ω = ∞ by
    rw [setLIntegral_congr_fun m this] at lintegral_div_le_one
    simp [top_mul h] at lintegral_div_le_one
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
  rcases h with ⟨h, h_top⟩
  rw [← compl_compl (fsupport X)] at h
  have h' : ∀ᵐ x ∂μ, x ∈ (fsupport X)ᶜ := by rwa [ae_iff]
  refine h_top ?_
  filter_upwards [h', ae_ne_zero hX] with ω hω_mem hω_ne_zero
  simpa [hω_ne_zero] using hω_mem

lemma setLIntegral_fsupport_inv_le_one (hX : IsEVar X S) (hY : IsNumeraire Y hS μ) :
    ∫⁻ ω in X.fsupport, (Y ω / X ω)⁻¹ ∂μ ≤ 1 := by
  suffices ∫⁻ ω in X.fsupport, ((Y / X) ω)⁻¹ ∂μ ≤ 1 by exact this
  rw [setLIntegral_congr_fun hX.measurable_fsupport <| ENNReal.inv_div_fsupport Y X,
    ← hY.lintegral_eq_setLIntegral_rev_fsupport hX]
  exact hY.lintegral_div_le_one hX

lemma inv_lintegral_div_eq_one (hX : IsNumeraire X hS μ) (hY : IsNumeraire Y hS μ)
    (h : μ X.fsupport ≠ 0) :
    (∫⁻ ω, Y ω / X ω ∂μ)⁻¹ = 1 := by
  set W := Y / X
  rw [hX.lintegral_eq_setLIntegral_fsupport hY.toIsEVar]
  refine le_antisymm ?_ ?_
  · calc (∫⁻ ω in X.fsupport, W ω ∂μ)⁻¹
    _ ≤ ∫⁻ ω in X.fsupport, (W ω)⁻¹ ∂μ :=
      strictConvexOn_inv.convexOn.map_set_lintegral_le continuousOn_inv isClosed_univ h (by simp)
        (by simp)
    _ ≤ 1 := setLIntegral_fsupport_inv_le_one hX.toIsEVar hY
  · simp only [← hX.lintegral_eq_setLIntegral_fsupport hY.toIsEVar, le_inv_iff_mul_le, one_mul]
    exact hX.lintegral_div_le_one hY.toIsEVar

lemma lintegral_div_eq_one (hX : IsNumeraire X hS μ) (hY : IsNumeraire Y hS μ)
    (h : μ X.fsupport ≠ 0) :
    ∫⁻ ω, Y ω / X ω ∂μ = 1 := by
  rw [← ENNReal.inv_eq_one]
  exact hX.inv_lintegral_div_eq_one hY h

/-- The Numeraire is almost-everywhere unique. -/
lemma ae_unique (hX : IsNumeraire X hS μ) (hY : IsNumeraire Y hS μ) : X =ᵐ[μ] Y := by
  rcases hY.measure_fsupport_ne_zero_or_ae_top with μ_fsupport | hYₜ
  swap
  · filter_upwards [hYₜ, hX.ae_top_implies_numeraire_top hY.toIsEVar] with ω hω hω₂
    simp_all
  let W := X / Y
  have inv_avg_eq_one : (∫⁻ ω in Y.fsupport, W ω ∂μ)⁻¹ = 1 := by
    simp only [Pi.div_apply, ← hY.lintegral_eq_setLIntegral_fsupport hX.toIsEVar, W]
    exact hY.inv_lintegral_div_eq_one hX μ_fsupport
  have avg_eq_one : ∫⁻ ω, W ω ∂μ = 1 := lintegral_div_eq_one hY hX μ_fsupport
  rcases hY.measure_fsupport_ne_zero_or_ae_top with hY₀ | hYₜ
  · have strict_Jensen : W =ᵐ[μ] const 𝓧 (∫⁻ ω, W ω ∂μ) ∨
        (∫⁻ ω in Y.fsupport, W ω ∂μ)⁻¹ < ∫⁻ ω in Y.fsupport, (W ω)⁻¹ ∂μ :=
      strictConvexOn_inv.ae_eq_const_or_map_set_lintegral_lt continuousOn_inv isClosed_univ hY₀
        (by simp) (by simp)
    have h_le : ∫⁻ ω in fsupport Y, (W ω)⁻¹ ∂μ ≤ 1 :=
      setLIntegral_fsupport_inv_le_one hY.toIsEVar hX
    simp only [inv_avg_eq_one, not_lt.mpr h_le, or_false, avg_eq_one] at strict_Jensen
    filter_upwards [strict_Jensen] with ω hx
    simp only [Pi.div_apply, const_apply, W] at hx
    exact ENNReal.eq_of_div_eq_one hx
  · suffices ∀ᵐ ω ∂μ, W ω = 0 by simp [lintegral_congr_ae this] at avg_eq_one
    filter_upwards [hYₜ] with ω hω
    simp [W, hω]

section LogOptimal

lemma ENNReal.log_div (a b : ℝ≥0∞) : ENNReal.log (a / b) = ENNReal.log a - ENNReal.log b := by
  simp_rw [div_eq_mul_inv, ENNReal.log_mul_add, ENNReal.log_inv, sub_eq_add_neg]

-- todo: prove that log-optimal implies numeraire
/-- A Numeraire is log-optimal. -/
theorem eintegral_log_div_nonpos (hX : IsNumeraire X hS μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, ENNReal.log (Y ω / X ω) ∂μ ≤ 0:= by
  calc ∫ᵉ ω, ENNReal.log (Y ω / X ω) ∂μ
  _ ≤ ENNReal.log (∫⁻ ω, Y ω / X ω ∂μ) := by
    refine Utility.eintegral_le_map logUtility ?_
    exact hY.measurable.aemeasurable.div hX.measurable.aemeasurable
  _ ≤ 0 := by
    simp only [ENNReal.log_le_zero_iff]
    exact lintegral_div_le_one hX hY

/-- A Numeraire maximizes the integral of the logarithm. -/
theorem eintegral_log_le (hX : IsNumeraire X hS μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, ENNReal.log (Y ω) ∂μ ≤ ∫ᵉ ω, ENNReal.log (X ω) ∂μ := by
  have h_nonpos := eintegral_log_div_nonpos hX hY
  simp_rw [ENNReal.log_div] at h_nonpos
  rwa [eintegral_sub, EReal.sub_nonpos] at h_nonpos

end LogOptimal

end IsNumeraire

end MeasureTheory
