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
structure IsNumeraire (X : 𝓧 → ℝ≥0∞) (S : Set (Measure 𝓧)) (μ : Measure 𝓧)
    [IsProbabilityMeasure μ] : Prop extends IsEVar X S where
  lintegral_ratio_le_one : ∀ ⦃Y⦄, IsEVar Y S → ∫⁻ ω, Y ω /ₑ X ω ∂μ ≤ 1

variable {X Y : 𝓧 → ℝ≥0∞} {μ : Measure 𝓧} [IsProbabilityMeasure μ] {S : Set (Measure 𝓧)}

lemma IsNumeraire.average_ratio_le_one (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ⨍⁻ ω, Y ω /ₑ X ω ∂μ ≤ 1 := by
  simp only [laverage, measure_univ, inv_one, one_smul]
  exact hX.lintegral_ratio_le_one hY

lemma ENNReal.le_antisymm_iff_toReal {a b : ℝ≥0∞} (h1 : b ≤ a) (h2 : a ≤ b) : a = b := by
  by_cases a₁ : a = ⊤
  · rw [a₁] at h1 h2 ⊢
    simp_all
  · push_neg at a₁
    have b₁ : b ≠ ⊤ := ne_top_of_le_ne_top a₁ h1
    refine (toReal_eq_toReal_iff' a₁ b₁).mp ?_
    rw [← toReal_le_toReal b₁ a₁] at h1
    rw [← toReal_le_toReal a₁ b₁] at h2
    linarith

lemma ENNReal.lt_and_le_false {a b : ℝ≥0∞} (h1 : b < a) (h2 : a ≤ b) : False := by
  by_cases a₁ : a = ⊤
  · rw [a₁] at h1 h2
    rw [top_le_iff] at h2
    have : b ≠ ⊤ := LT.lt.ne_top h1
    contradiction
  · push_neg at a₁
    have b₁ : b ≠ ⊤ := LT.lt.ne_top h1
    rw [← toReal_lt_toReal b₁ a₁] at h1
    rw [← toReal_le_toReal a₁ b₁] at h2
    linarith

lemma IsNumeraire.ae_unique (hX : IsNumeraire X S μ) (hY : IsNumeraire Y S μ) : X =ᵐ[μ] Y := by
  let f := Inv.inv (α := ℝ≥0∞)
  have strc_convex : StrictConvexOn ℝ≥0∞ univ f := strictConvexOn_inv
  let W := X /ₑ Y
  have inv_avg_eq_one : f (⨍⁻ ω, W ω ∂μ) = 1 :=
    suffices 1 ≤ f (⨍⁻ ω, W ω ∂μ) by
      refine ENNReal.le_antisymm_iff_toReal this ?_
      suffices f (⨍⁻ ω, W ω ∂μ) ≤ ⨍⁻ ω, f (W ω) ∂μ by
          trans ⨍⁻ ω, f (W ω) ∂μ
          · assumption
          · simp only [inv_ediv_enn, f, W]
            exact hX.average_ratio_le_one hY.toIsEVar
      exact strc_convex.convexOn.map_laverage_le continuousOn_inv isClosed_univ (by simp)
    ENNReal.one_le_inv.mpr <| hY.average_ratio_le_one hX.toIsEVar
  have strict_Jensen : W =ᵐ[μ] const 𝓧 (⨍⁻ ω, W ω ∂μ) ∨
      f (⨍⁻ ω, W ω ∂μ) < ⨍⁻ ω, f (W ω) ∂μ :=
    strc_convex.ae_eq_const_or_map_laverage_lt continuousOn_inv isClosed_univ (by simp)
  cases strict_Jensen with
  | inl h =>
    have avg_eq_one : ⨍⁻ ω, W ω ∂μ = 1 := by
      simp only [ENNReal.inv_eq_one, f] at inv_avg_eq_one
      assumption
    rw [avg_eq_one] at h
    filter_upwards [h] with ω hx
    simp only [const_apply, W] at hx
    exact (ediv_eq_one_iff_eq_enn ..).mp hx
  | inr h =>
    exfalso
    rw [inv_avg_eq_one] at h
    simp only [inv_ediv_enn, f, W] at h
    refine ENNReal.lt_and_le_false h <| hX.average_ratio_le_one hY.toIsEVar

end MeasureTheory
