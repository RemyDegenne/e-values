/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import EValues.EIntegral
import EValues.Mathlib.Convex
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Utility functions

-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {U : ℝ≥0∞ → EReal}

/-- A utility function is a concave, monotone and differentiable function from `ℝ≥0∞` to `EReal`,
which is finite on `(0, ∞)`. -/
structure Utility where
  /-- The function itself. -/
  toFun : ℝ≥0∞ → EReal
  eq_coe' : ∀ x, x ≠ 0 → x ≠ ∞ → toFun x ≠ ⊥ ∧ toFun x ≠ ⊤
  monotone' : Monotone toFun
  continuous' : Continuous toFun
  concave' : ConcaveOn ℝ≥0 Set.univ toFun
  differentiable' : ContDiffOn ℝ 1 (fun x ↦ (toFun (ENNReal.ofReal x)).toReal) (Set.Ioi 0)

-- instance : Coe (Utility) (ℝ≥0∞ → EReal) := ⟨Utility.toFun⟩
instance : CoeFun (Utility) (fun _ ↦ ℝ≥0∞ → EReal) := ⟨Utility.toFun⟩

lemma Utility.eq_coe (U : Utility) {x : ℝ≥0∞} (hx0 : x ≠ 0) (hx_top : x ≠ ∞) :
    U x ≠ ⊥ ∧ U x ≠ ⊤ := U.eq_coe' x hx0 hx_top

lemma Utility.monotone (U : Utility) : Monotone U := U.monotone'

lemma Utility.continuous (U : Utility) : Continuous U := U.continuous'

@[fun_prop]
lemma Utility.measurable (U : Utility) : Measurable U := U.continuous.measurable

lemma Utility.aemeasurable {μ : Measure ℝ≥0∞} (U : Utility) :
    AEMeasurable U μ := U.measurable.aemeasurable

lemma Utility.concave (U : Utility) : ConcaveOn ℝ≥0 Set.univ U := U.concave'

lemma Utility.ne_top (U : Utility) {x : ℝ≥0∞} (hx_top : x ≠ ∞) : U x ≠ ⊤ := by
  by_cases hx0 : x = 0
  · simp only [hx0, ne_eq]
    refine ne_top_of_le_ne_top (b := U 1) ?_ ?_
    · exact (U.eq_coe (by simp) (by simp)).2
    · exact U.monotone (by simp)
  · exact (U.eq_coe hx0 hx_top).2

lemma Utility.ne_bot (U : Utility) {x : ℝ≥0∞} (hx0 : x ≠ 0) : U x ≠ ⊥ := by
  by_cases hx_top : x = ∞
  · simp only [hx_top, ne_eq]
    refine ne_bot_of_le_ne_bot (b := U 1) ?_ ?_
    · exact (U.eq_coe (by simp) (by simp)).1
    · exact U.monotone (by simp)
  · exact (U.eq_coe hx0 hx_top).1

/-- The real-valued representation of a utility function. -/
def Utility.real (U : Utility) : ℝ → ℝ := fun x ↦ (U (ENNReal.ofReal x)).toReal

lemma Utility.contDiffOn (U : Utility) : ContDiffOn ℝ 1 U.real (Set.Ioi 0) := U.differentiable'

/-- The derivative of a utility function.
At `x ∈ (0, ∞)`, this is the derivative of the real-valued representation.
At `0` or `∞`, this is defined as a limit. -/
protected noncomputable
def Utility.deriv (U : Utility) (x : ℝ≥0∞) : EReal :=
  if x = 0 then
    limsup (fun y : ℝ≥0∞ ↦ ((deriv U.real y.toReal : ℝ) : EReal)) (𝓝[>] 0)
  else if x = ∞ then
    limsup (fun y : ℝ≥0∞ ↦ ((deriv U.real y.toReal : ℝ) : EReal)) (𝓝[<] ∞)
  else
    ((deriv U.real x.toReal : ℝ) : EReal)

/-- Jensen's inequality. -/
theorem Utility.eintegral_le_map {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} [IsProbabilityMeasure μ]
    (U : Utility) {X : α → ℝ≥0∞} (hX_meas : AEMeasurable X μ) :
    ∫ᵉ x, U (X x) ∂μ ≤ U (∫⁻ x, X x ∂μ) := by
  by_cases h : ∫ᵉ x, U (X x) ∂μ = ⊥
  · simp [h]
  have h_ne_bot : ∀ᵐ ω ∂μ, U (X ω) ≠ ⊥ := ae_ne_bot_of_eintegral_ne_bot (by fun_prop) h
  by_cases hX_int_top : ∫⁻ x, X x ∂μ = ∞
  · rw [hX_int_top]
    calc ∫ᵉ x, U (X x) ∂μ
    _ ≤ ∫ᵉ x, U ∞ ∂μ := eintegral_mono (fun _ ↦ U.monotone (by simp))
    _ = U ∞ := by simp
  have hX_top : ∀ᵐ ω ∂μ, X ω ≠ ∞ := by
    filter_upwards [ae_lt_top' (by fun_prop) hX_int_top] with x hx using hx.ne
  have h_ne_top : ∀ᵐ ω ∂μ, U (X ω) ≠ ⊤ := by
    filter_upwards [hX_top] with x hx using U.ne_top hx
  sorry

section Log

/-- The logarithmic utility function. -/
noncomputable def logUtility : Utility where
  toFun := ENNReal.log
  eq_coe' := by
    intros x hx0 hx_top
    simp [ENNReal.log_eq_bot_iff, ENNReal.log_eq_top_iff, hx0, hx_top]
  monotone' := ENNReal.log_monotone
  continuous' := ENNReal.continuous_log
  concave' := ConcaveOn_log
  differentiable' := by
    have h_eq x (hx : 0 < x) : (ENNReal.log (ENNReal.ofReal x)).toReal = Real.log x := by
      simp [ENNReal.log_ofReal, not_le.mpr hx]
    have h_diff : ContDiffOn ℝ 1 Real.log (Set.Ioi 0) :=
      analyticOn_log.contDiffOn (uniqueDiffOn_Ioi 0)
    exact ContDiffOn.congr h_diff h_eq

@[simp]
lemma real_logUtility {x : ℝ} (hx : 0 < x) :
    logUtility.real x = Real.log x := by
  simp [logUtility, Utility.real, ENNReal.log_ofReal, not_le.mpr hx]

lemma deriv_logUtility (x : ℝ≥0∞) :
    logUtility.deriv x = if x = 0 then ⊤ else 1 / x := by
  by_cases hx0 : x = 0
  · simp only [hx0, ↓reduceIte, EReal.coe_ennreal_top]
    sorry
  by_cases hx_top : x = ∞
  · simp only [hx_top, ENNReal.top_ne_zero, ↓reduceIte, one_div, ENNReal.inv_top,
      EReal.coe_ennreal_zero]
    sorry
  simp only [Utility.deriv, hx0, ↓reduceIte, hx_top, one_div]
  have hx_pos : 0 < x.toReal := by
    sorry
  suffices deriv logUtility.real x.toReal = 1 / x.toReal by
    simp only [this, one_div]
    sorry
  have h_deriv_log : deriv Real.log x.toReal = 1 / x.toReal := by
    sorry
  rw [← h_deriv_log]
  refine EventuallyEq.deriv_eq ?_
  have h_ev_pos : ∀ᶠ y in 𝓝 x.toReal, 0 < y := by
    sorry
  filter_upwards [h_ev_pos] with y hy using real_logUtility hy

lemma deriv_logUtility_eq_ennreal (x : ℝ≥0∞) :
    logUtility.deriv x = (1 / x : ℝ≥0∞) := by
  by_cases hx0 : x = 0 <;> simp [deriv_logUtility, hx0]

end Log

end ProbabilityTheory
