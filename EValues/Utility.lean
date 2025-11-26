/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import EValues.EIntegral
import EValues.Mathlib.Convex
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Deriv
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

lemma Utility.real_toReal (U : Utility) {x : ℝ≥0∞} (hx_top : x ≠ ∞) :
    U.real x.toReal = (U x).toReal := by
  simp only [real]
  rw [ENNReal.ofReal_toReal hx_top]

lemma Utility.coe_real_toReal' (U : Utility) {x : ℝ≥0∞} (hx0 : U x ≠ ⊥) (hx_top : x ≠ ∞) :
    (U.real x.toReal : EReal) = U x := by
  rw [U.real_toReal hx_top, EReal.coe_toReal]
  · exact U.ne_top hx_top
  · exact hx0

lemma Utility.coe_real_toReal (U : Utility) {x : ℝ≥0∞} (hx0 : x ≠ 0) (hx_top : x ≠ ∞) :
    (U.real x.toReal : EReal) = U x :=
  coe_real_toReal' U (U.ne_bot hx0) hx_top

lemma Utility.contDiffOn (U : Utility) : ContDiffOn ℝ 1 U.real (Set.Ioi 0) := U.differentiable'

lemma Utility.differentiableOn (U : Utility) : DifferentiableOn ℝ U.real (Set.Ioi 0) :=
  U.contDiffOn.differentiableOn le_rfl

lemma Utility.monotoneOn_Ioi_real (U : Utility) : MonotoneOn U.real (Set.Ioi 0) := by
  intro x hx y hy hxy
  refine EReal.toReal_le_toReal ?_ ?_ ?_
  · exact U.monotone (ENNReal.ofReal_le_ofReal hxy)
  · exact U.ne_bot (by simpa)
  · exact U.ne_top (by simp)

lemma Utility.monotoneOn_Ici_real (U : Utility) (hU0 : U 0 ≠ ⊥) :
    MonotoneOn U.real (Set.Ici 0) := by
  intro x hx y hy hxy
  refine EReal.toReal_le_toReal ?_ ?_ ?_
  · exact U.monotone (ENNReal.ofReal_le_ofReal hxy)
  · by_cases hx0 : x = 0
    · simpa [hx0]
    · exact U.ne_bot (by simp [lt_of_le_of_ne (Set.mem_Ici.mp hx) (Ne.symm hx0)])
  · exact U.ne_top (by simp)

lemma Utility.concaveOn_Ioi_real (U : Utility) : ConcaveOn ℝ (Set.Ioi 0) U.real := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have h_ccv := U.concave.2 (Set.mem_univ (ENNReal.ofReal x)) (Set.mem_univ (ENNReal.ofReal y))
    (by simp : 0 ≤ (⟨a, ha⟩ : ℝ≥0)) (by simp : 0 ≤ (⟨b, hb⟩ : ℝ≥0)) (by ext; simp [hab])
  simp only [EReal.smul_nnreal_eq_mul, NNReal.coe_mk, ENNReal.smul_def, smul_eq_mul] at h_ccv
  sorry

lemma Utility.concaveOn_Ici_real (U : Utility) (h0 : U 0 ≠ ⊥) : ConcaveOn ℝ (Set.Ici 0) U.real := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have h_ccv := U.concave.2 (Set.mem_univ (ENNReal.ofReal x)) (Set.mem_univ (ENNReal.ofReal y))
    (by simp : 0 ≤ (⟨a, ha⟩ : ℝ≥0)) (by simp : 0 ≤ (⟨b, hb⟩ : ℝ≥0)) (by ext; simp [hab])
  simp only [EReal.smul_nnreal_eq_mul, NNReal.coe_mk, ENNReal.smul_def, smul_eq_mul] at h_ccv
  sorry

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

-- should also be true at 0 and ∞, but we don't need it now
lemma Utility.deriv_nonneg (U : Utility) {x : ℝ≥0∞} (hx0 : x ≠ 0) (hx_top : x ≠ ∞) :
    0 ≤ U.deriv x := by
  simp only [Utility.deriv, hx0, ↓reduceIte, hx_top, EReal.coe_nonneg]
  have h_nonneg := U.monotoneOn_Ioi_real.derivWithin_nonneg (x := x.toReal)
  refine h_nonneg.trans_eq ?_
  refine derivWithin_of_mem_nhds ?_
  refine isOpen_Ioi.mem_nhds ?_
  simp only [Set.mem_Ioi, ENNReal.toReal_pos_iff]
  exact ⟨hx0.bot_lt, hx_top.lt_top⟩

lemma Utility.todo (U : Utility) (x y : ℝ≥0∞) (hx_top : x ≠ ∞) (hy_zero : y ≠ 0) (hy_top : y ≠ ∞) :
    U x ≤ U y + U.deriv y * (x - y) := by
  by_cases h_bot : U x = ⊥
  · simp [h_bot]
  have hUx_top : U x ≠ ⊤ := U.ne_top hx_top
  by_cases hU0 : U 0 = ⊥
  · by_cases hx0 : x = 0
    · simp [hx0, hU0]
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · have h_ccv := ConcaveOn.deriv_le_slope U.concaveOn_Ioi_real (x := x.toReal) (y := y.toReal)
        ?_ ?_ ?_ ?_
      rotate_left
      · simpa [ENNReal.toReal_pos_iff] using ⟨Ne.bot_lt hx0, Ne.lt_top hx_top⟩
      · simpa [ENNReal.toReal_pos_iff] using ⟨hy_zero.bot_lt, hy_top.lt_top⟩
      · exact (ENNReal.toReal_lt_toReal hx_top hy_top).mpr hxy
      · refine U.differentiableOn.differentiableAt (isOpen_Ioi.mem_nhds ?_)
        simpa [ENNReal.toReal_pos_iff] using ⟨hy_zero.bot_lt, hy_top.lt_top⟩
      simp only [slope, vsub_eq_sub, smul_eq_mul] at h_ccv
      rw [← U.coe_real_toReal hx0 hx_top, ← U.coe_real_toReal hy_zero hy_top, Utility.deriv]
      simp only [hy_zero, ↓reduceIte, hy_top, ge_iff_le]
      nth_rw 2 [← ENNReal.ofReal_toReal hx_top]
      nth_rw 3 [← ENNReal.ofReal_toReal hy_top]
      simp only [EReal.coe_ennreal_ofReal, ENNReal.toReal_nonneg, sup_of_le_left]
      norm_cast
      have : 0 < (y.toReal - x.toReal) :=
        sub_pos.mpr ((ENNReal.toReal_lt_toReal hx_top hy_top).mpr hxy)
      field_simp at h_ccv
      linarith
    · rw [EReal.sub_self (by simpa) (by simp)]
      simp
    · have h_ccv := ConcaveOn.slope_le_deriv U.concaveOn_Ioi_real (x := y.toReal) (y := x.toReal)
        ?_ ?_ ?_ ?_
      rotate_left
      · simpa [ENNReal.toReal_pos_iff] using ⟨hy_zero.bot_lt, hy_top.lt_top⟩
      · simpa [ENNReal.toReal_pos_iff] using ⟨Ne.bot_lt hx0, Ne.lt_top hx_top⟩
      · exact (ENNReal.toReal_lt_toReal hy_top hx_top).mpr hyx
      · refine U.differentiableOn.differentiableAt (isOpen_Ioi.mem_nhds ?_)
        simpa [ENNReal.toReal_pos_iff] using ⟨hy_zero.bot_lt, hy_top.lt_top⟩
      simp only [slope, vsub_eq_sub, smul_eq_mul] at h_ccv
      rw [← U.coe_real_toReal hx0 hx_top, ← U.coe_real_toReal hy_zero hy_top, Utility.deriv]
      simp only [hy_zero, ↓reduceIte, hy_top, ge_iff_le]
      nth_rw 2 [← ENNReal.ofReal_toReal hx_top]
      nth_rw 3 [← ENNReal.ofReal_toReal hy_top]
      simp only [EReal.coe_ennreal_ofReal, ENNReal.toReal_nonneg, sup_of_le_left]
      norm_cast
      have : 0 < (x.toReal - y.toReal) :=
        sub_pos.mpr ((ENNReal.toReal_lt_toReal hy_top hx_top).mpr hyx)
      field_simp at h_ccv
      linarith
  · rcases lt_trichotomy x y with hxy | rfl | hyx
    · have h_ccv := ConcaveOn.deriv_le_slope (U.concaveOn_Ici_real hU0)
        (x := x.toReal) (y := y.toReal) (by simp) (by simp) ?_ ?_
      rotate_left
      · exact (ENNReal.toReal_lt_toReal hx_top hy_top).mpr hxy
      · refine U.differentiableOn.differentiableAt (isOpen_Ioi.mem_nhds ?_)
        simpa [ENNReal.toReal_pos_iff] using ⟨hy_zero.bot_lt, hy_top.lt_top⟩
      simp only [slope, vsub_eq_sub, smul_eq_mul] at h_ccv
      rw [← U.coe_real_toReal' h_bot hx_top, ← U.coe_real_toReal hy_zero hy_top, Utility.deriv]
      simp only [hy_zero, ↓reduceIte, hy_top, ge_iff_le]
      nth_rw 2 [← ENNReal.ofReal_toReal hx_top]
      nth_rw 3 [← ENNReal.ofReal_toReal hy_top]
      simp only [EReal.coe_ennreal_ofReal, ENNReal.toReal_nonneg, sup_of_le_left]
      norm_cast
      have : 0 < (y.toReal - x.toReal) :=
        sub_pos.mpr ((ENNReal.toReal_lt_toReal hx_top hy_top).mpr hxy)
      field_simp at h_ccv
      linarith
    · rw [EReal.sub_self (by simpa) (by simp)]
      simp
    · have h_ccv := ConcaveOn.slope_le_deriv (U.concaveOn_Ici_real hU0)
        (x := y.toReal) (y := x.toReal) (by simp) (by simp) ?_ ?_
      rotate_left
      · exact (ENNReal.toReal_lt_toReal hy_top hx_top).mpr hyx
      · refine U.differentiableOn.differentiableAt (isOpen_Ioi.mem_nhds ?_)
        simpa [ENNReal.toReal_pos_iff] using ⟨hy_zero.bot_lt, hy_top.lt_top⟩
      simp only [slope, vsub_eq_sub, smul_eq_mul] at h_ccv
      rw [← U.coe_real_toReal' h_bot hx_top, ← U.coe_real_toReal hy_zero hy_top, Utility.deriv]
      simp only [hy_zero, ↓reduceIte, hy_top, ge_iff_le]
      nth_rw 2 [← ENNReal.ofReal_toReal hx_top]
      nth_rw 3 [← ENNReal.ofReal_toReal hy_top]
      simp only [EReal.coe_ennreal_ofReal, ENNReal.toReal_nonneg, sup_of_le_left]
      norm_cast
      have : 0 < (x.toReal - y.toReal) :=
        sub_pos.mpr ((ENNReal.toReal_lt_toReal hy_top hx_top).mpr hyx)
      field_simp at h_ccv
      linarith

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
  by_cases hX_int_zero : ∫⁻ x, X x ∂μ = 0
  · rw [hX_int_zero]
    rw [lintegral_eq_zero_iff' hX_meas] at hX_int_zero
    have : ∀ᵐ x ∂μ, U (X x) = U 0 := by
      filter_upwards [hX_int_zero] with x hx
      simp [hx]
    rw [eintegral_congr_ae this]
    simp
  have hX_top : ∀ᵐ ω ∂μ, X ω ≠ ∞ := by
    filter_upwards [ae_lt_top' (by fun_prop) hX_int_top] with x hx using hx.ne
  have h_ne_top : ∀ᵐ ω ∂μ, U (X ω) ≠ ⊤ := by
    filter_upwards [hX_top] with x hx using U.ne_top hx
  have h_ccv : ∀ᵐ x ∂μ, U (X x)
      ≤ U (∫⁻ y, X y ∂μ) + (U.deriv (∫⁻ y, X y ∂μ)) * (X x - ∫⁻ y, X y ∂μ) := by
    filter_upwards [h_ne_bot, h_ne_top, hX_top] with x hx_bot hx_top hx_top'
    exact U.todo _ _ hx_top' hX_int_zero hX_int_top
  calc ∫ᵉ x, U (X x) ∂μ
  _ ≤ ∫ᵉ x, U (∫⁻ y, X y ∂μ) + (U.deriv (∫⁻ y, X y ∂μ)) * (X x - ∫⁻ y, X y ∂μ) ∂μ :=
    eintegral_mono_ae h_ccv
  _ = U (∫⁻ y, X y ∂μ) := by
    have h_int_eq : ∫ᵉ x, U.deriv (∫⁻ y, X y ∂μ) * (X x - ∫⁻ y, X y ∂μ) ∂μ = 0 := by
      rw [eintegral_mul_const, eintegral_sub']
      rotate_left
      · fun_prop
      · fun_prop
      · simpa
      · exact EReal.ne_bot_of_nonneg (eintegral_nonneg (fun _ ↦ by positivity))
      · simp [Utility.deriv, hX_int_zero, hX_int_top]
      · simp [Utility.deriv, hX_int_zero, hX_int_top]
      · sorry
      simp only [eintegral_const, measure_univ, EReal.coe_ennreal_one, mul_one, mul_eq_zero]
      rw [eintegral_eq_lintegral, EReal.sub_self (by simpa) (by simp)]
      simp
    rw [eintegral_add', h_int_eq]
    rotate_left
    · fun_prop
    · fun_prop
    · simp [h_int_eq]
    · simp [h_int_eq]
    simp

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
