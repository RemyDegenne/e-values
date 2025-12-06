/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import EValues.EIntegral
import EValues.Mathlib.Convex
import Mathlib.Analysis.Calculus.Deriv.Inv

open Function Set ENNReal

open MeasureTheory ProbabilityTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set ℝ≥0∞} {t : Set α}
  {f : α → ℝ≥0∞} {g : ℝ≥0∞ → ℝ≥0∞}

/- theorem ConvexOn.map_laverage_le' [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConvexOn ℝ≥0∞ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hgₜ : g 0 = ⊤) (hgₜ₂ : ∀ x ≠ 0, g x ≠ ⊤) (hfm : Measurable f)
    (hμ : μ univ ≠ 0)
    : g (⨍⁻ x, f x ∂μ) ≤ ⨍⁻ x, g (f x) ∂μ := by
  by_cases h : ⨍⁻ x, f x ∂μ = 0
  · rw [h]
    simp_all only [ne_eq, Measure.measure_univ_eq_zero, laverage, lintegral_smul_measure,
      smul_eq_mul, mul_eq_zero, ENNReal.inv_eq_zero, measure_ne_top, lintegral_eq_zero_iff,
      false_or, top_le_iff]
    suffices ∀ᵐ x ∂μ, g (f x) = ⊤ by
      rw [lintegral_congr_ae this]
      simp [hμ]
    filter_upwards [h] with x hx
    rw [hx]
    exact hgₜ
  · push_neg at h
    by_cases h2 : ⨍⁻ (x : α), g (f x) ∂μ = ⊤
    · simp_all
    · suffices (g (⨍⁻ x, f x ∂μ)).toReal ≤ (⨍⁻ x, g (f x) ∂μ).toReal from
        (toReal_le_toReal (hgₜ₂ _ h) h2).mp this

      sorry

theorem ConvexOn.map_laverage_le [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConvexOn ℝ≥0∞ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) : g (⨍⁻ x, f x ∂μ) ≤ ⨍⁻ x, g (f x) ∂μ := by
  sorry -/

/-- The derivative of the function `Inv.inv` on `EReal`. -/
protected noncomputable
def Inv.deriv (x : ℝ≥0∞) : EReal :=
  if x = 0 then ⊤
  else if x = ∞ then 0
  else ((deriv Inv.inv x.toReal : ℝ) : EReal)

@[simp]
lemma deriv_inv_ne_bot (x : ℝ≥0∞) : Inv.deriv x ≠ ⊥ := by
  unfold Inv.deriv
  split_ifs <;> simp

lemma deriv_inv_ne_top {x : ℝ≥0∞} (hx : x ≠ 0) : Inv.deriv x ≠ ⊤ := by
  unfold Inv.deriv
  simp only [hx, ↓reduceIte, deriv_inv', EReal.coe_neg, ne_eq]
  split_ifs <;> simp

lemma Inv.le_add_deriv_mul {x y : ℝ≥0∞} (hx_top : x ≠ ⊤) (hy_zero : y ≠ 0) :
    y⁻¹ + Inv.deriv y * (x - y) ≤ x⁻¹ := by
  by_cases hy_top : y = ⊤
  · simp only [hy_top, inv_top, EReal.coe_ennreal_zero, Inv.deriv, top_ne_zero, ↓reduceIte,
    EReal.coe_ennreal_top, EReal.sub_top, zero_mul, add_zero]
    positivity
  · push_neg at hy_top
    by_cases hx_zero: x = 0
    · simp [hx_zero]
    have h_cvx := convexOn_inv_Ioi.add_deriv_mul_le (x := x.toReal) (y := y.toReal) ?_ ?_ ?_
    rotate_left
    · simpa [ENNReal.toReal_pos_iff] using ⟨Ne.bot_lt hx_zero, Ne.lt_top hx_top⟩
    · simpa [ENNReal.toReal_pos_iff] using ⟨hy_zero.bot_lt, hy_top.lt_top⟩
    · exact differentiableAt_inv <| toReal_ne_zero.mpr ⟨hy_zero, hy_top⟩
    simp only [← toReal_inv] at h_cvx
    simp only [Inv.deriv, hy_zero, ↓reduceIte, hy_top]
    rw [← EReal.coe_ennreal_toReal hx_top, ← EReal.coe_ennreal_toReal hy_top,
      ← EReal.coe_ennreal_toReal <| inv_ne_top.mpr hx_zero,
      ← EReal.coe_ennreal_toReal <| inv_ne_top.mpr hy_zero]
    norm_cast

lemma eintegrable_const {μ : Measure α} [IsFiniteMeasure μ] {c : EReal} :
    eintegrable (fun _ ↦ c) μ := by
  rcases le_total c 0 with hc | hc
  · left
    simp [hc]
  · right
    simp [hc]

theorem Inv.map_lintegral_le [IsProbabilityMeasure μ] (hf : AEMeasurable f μ)
    (hf_top : ∀ᵐ x ∂μ, f x ≠ ⊤) : (∫⁻ x, f x ∂μ)⁻¹ ≤ ∫⁻ x, (f x)⁻¹ ∂μ := by
  by_cases h0 : ∫⁻ x, f x ∂μ = 0
  · simp only [h0, ENNReal.inv_zero]
    rw [lintegral_eq_zero_iff' hf] at h0
    have : ∀ᵐ x ∂μ, (f x)⁻¹ = ⊤ := by
      filter_upwards [h0] with x hx
      rw [hx]
      simp
    rw [lintegral_congr_ae this]
    simp
  by_cases htop_inv : ∫⁻ x, (f x)⁻¹ ∂μ = ⊤
  · simp [htop_inv]
  let y := ∫⁻ x, f x ∂μ
  calc
  _ = (∫ᵉ x, f x ∂μ).toENNReal⁻¹ := by
    rw [lintegral_eq_eintegral _]
  _ = (∫ᵉ x, y⁻¹ + Inv.deriv y * (f x - y) ∂μ).toENNReal := by
    rw [eintegral_add]
    · have : ∫ᵉ x, Inv.deriv y * ((f x) - y) ∂μ = 0 := by sorry
      rw [this]
      simp [eintegral_const, ← lintegral_eq_eintegral, y]
    · fun_prop
    · fun_prop
    · exact eintegrable_const
    · sorry
    · simp
    · simp [y, h0]
  _ ≤ (∫ᵉ x, (Inv.inv (α := ℝ≥0∞) (f x)) ∂μ).toENNReal := by
    refine EReal.toENNReal_le_toENNReal ?_
    refine eintegral_mono_ae ?_
    filter_upwards [hf_top] with x hx
    exact Inv.le_add_deriv_mul hx h0
  _ ≤ ∫⁻ x, (f x)⁻¹ ∂μ := by
    rw [← lintegral_eq_eintegral _]
  /- have := Inv.map_set_lintegral_le (f := f) (μ := μ) MeasurableSet.univ hf.restrict (by simp) ?_
  · simp_all
  · simp_all only [ne_eq, mem_univ, forall_const] -/

lemma AEMeasurable.cond {μ : Measure α}
    (hf : AEMeasurable f (μ.restrict t)) : AEMeasurable f μ[|t] := by
  simp [ProbabilityTheory.cond, hf.smul_measure (μ t)⁻¹]

theorem Inv.map_set_lintegral_le (ht : MeasurableSet t) (hf : AEMeasurable f (μ.restrict t))
    (hμ_t₀ : μ t ≠ 0) (hμ_t₁ : μ t ≠ ⊤) (ht_top : ∀ᵐ x ∂μ, x ∈ t → f x ≠ ⊤) :
    μ t * (∫⁻ x in t, f x ∂μ)⁻¹ ≤ (μ t)⁻¹ * ∫⁻ x in t, (f x)⁻¹ ∂μ := by
  have : IsProbabilityMeasure μ[|t] := cond_isProbabilityMeasure_of_finite hμ_t₀ hμ_t₁
  replace hf : AEMeasurable f μ[|t] := hf.cond
  replace ht_top : ∀ᵐ x ∂μ[|t], f x ≠ ⊤ := by
    unfold ProbabilityTheory.cond
    rw [← μ.restrict_smul, ae_restrict_iff' ht]
    change ((μ t)⁻¹ • μ) {x | x ∈ t → f x ≠ ⊤}ᶜ = 0
    rw [Measure.smul_apply]
    exact smul_eq_zero_of_right (μ t)⁻¹ ht_top
  calc
  _ = (∫⁻ x, f x ∂μ[|t])⁻¹ := by
    simp only [lintegral_smul_measure, smul_eq_mul, ProbabilityTheory.cond]
    rw [ENNReal.mul_inv, inv_inv]
    · left
      simp [hμ_t₁]
    · left
      simp [hμ_t₀]
  _ ≤ ∫⁻ x, (f x)⁻¹ ∂μ[|t] := Inv.map_lintegral_le hf ht_top
  _ = (μ t)⁻¹ * ∫⁻ x in t, (f x)⁻¹ ∂μ := by
    simp [ProbabilityTheory.cond]

/- example (ht : MeasurableSet t) (hf : AEMeasurable f (μ.restrict t))
    (hμ_t₀ : μ t ≠ 0) (hμ_t₁ : μ t ≠ ⊤) (ht_top : ∀ᵐ x ∂μ, x ∈ t → f x ≠ ⊤) :
    (∫⁻ x, f x ∂(renorm_measure μ t))⁻¹ ≤ ∫⁻ x, (f x)⁻¹ ∂(renorm_measure μ t) := by
  /- let ν : Measure α := μ.restrict t
  have : IsProbabilityMeasure ν := by sorry
  replace hf : AEMeasurable f ν := by sorry
  replace ht_top : ∀ᵐ x ∂ν, f x ≠ ⊤ := by sorry -/
  have : MeasurableSet (Set.univ : Set α) := by exact MeasurableSet.univ
  let f' : α → ℝ≥0∞ := fun x ↦ f x * (μ t)⁻¹
  have := Inv.map_set_lintegral_le ht (f := f') (μ := μ) ?_ hμ_t₀ hμ_t₁ ?_
  · simp at this
    sorry
  · fun_prop
  · filter_upwards [ht_top] with x hx hxt
    simp only [f']
    refine mul_ne_top (hx hxt) ?_
    simp [hμ_t₀]

example (ht : MeasurableSet t) (hf : AEMeasurable f (μ.restrict t))
    (hμ_t : μ t ≠ 0) (ht_top : ∀ᵐ x ∂μ, x ∈ t → f x ≠ ⊤) :
    μ t * ((μ t)⁻¹ * ∫⁻ x in t, f x ∂μ)⁻¹ ≤ ∫⁻ x in t, (f x)⁻¹ ∂μ := by
  let ν : Measure α := (μ t)⁻¹ • (μ.restrict t)
  have : IsProbabilityMeasure ν := by sorry
  replace hf : AEMeasurable f ν := by sorry
  replace ht_top : ∀ᵐ x ∂ν, f x ≠ ⊤ := by sorry
  have := Inv.map_lintegral_le hf ht_top
  replace := mul_le_mul_left' this (μ t)
  simp only [lintegral_smul_measure, smul_eq_mul, ν] at this
  refine le_trans this ?_
  rw [← mul_assoc]
  rw [ENNReal.mul_inv_cancel hμ_t]
  · simp
  · by_contra! h
    simp_all

example (hμ_t : μ t ≠ 0) [IsProbabilityMeasure μ] :
    (μ t * ∫⁻ x in t, f x ∂μ)⁻¹ ≤ μ t * ∫⁻ x in t, (f x)⁻¹ ∂μ := by
  have := strictConvexOn_inv.convexOn.2
  let x := (μ t)⁻¹ * ∫⁻ x in t, f x ∂μ
  specialize @this x (by trivial) 0 (by trivial) (μ t) (1 - μ t) (by positivity) (by positivity)
    ?_
  · refine (toReal_eq_one_iff (μ t + (1 - μ t))).mp ?_
    rw [toReal_add (by simp) (by simp)]
    sorry
  · simp_all
    --exact this
    sorry -/

lemma Inv.lt_add_deriv_mul {x y : ℝ≥0∞} (hx_top : x ≠ ⊤) (hy_zero : y ≠ 0) (hxy : x ≠ y) :
    y⁻¹ + Inv.deriv y * (x - y) < x⁻¹ := by
  by_cases hy_top : y = ⊤
  · simp [hy_top, Inv.deriv, hx_top]
  · push_neg at hy_top
    by_cases hx_zero: x = 0
    · simp_all only [ne_eq, zero_ne_top, not_false_eq_true, Inv.deriv, ↓reduceIte, deriv_inv',
      EReal.coe_neg, EReal.coe_ennreal_zero, zero_sub, mul_neg, neg_mul, neg_neg, ENNReal.inv_zero,
      EReal.coe_ennreal_top]
      refine EReal.add_lt_top ?_ ?_
      · simp [hy_zero]
      · refine (EReal.mul_ne_top ↑(y.toReal ^ 2)⁻¹ ↑y).mpr ⟨?_, ?_, ?_, ?_⟩ <;> simp [hy_top]
    have h_cvx := strictConvexOn_inv_Ioi.add_deriv_mul_lt (x := x.toReal) (y := y.toReal)
      ?_ ?_ ?_ ?_
    rotate_left
    · simpa [ENNReal.toReal_pos_iff] using ⟨Ne.bot_lt hx_zero, Ne.lt_top hx_top⟩
    · simpa [ENNReal.toReal_pos_iff] using ⟨hy_zero.bot_lt, hy_top.lt_top⟩
    · by_contra! h
      exact hxy <| (toReal_eq_toReal_iff' hx_top hy_top).mp h
    · exact differentiableAt_inv <| toReal_ne_zero.mpr ⟨hy_zero, hy_top⟩
    simp only [← toReal_inv] at h_cvx
    simp only [Inv.deriv, hy_zero, ↓reduceIte, hy_top]
    rw [← EReal.coe_ennreal_toReal hx_top, ← EReal.coe_ennreal_toReal hy_top,
      ← EReal.coe_ennreal_toReal <| inv_ne_top.mpr hx_zero,
      ← EReal.coe_ennreal_toReal <| inv_ne_top.mpr hy_zero]
    norm_cast

theorem Inv.ae_eq_const_or_map_lintegral_lt' [IsProbabilityMeasure μ] (hf : Measurable f)
    (hf_top : ∀ᵐ x ∂μ, f x ≠ ⊤) :
    f =ᵐ[μ] const α (∫⁻ x, f x ∂μ) ∨ (∫⁻ x, f x ∂μ)⁻¹ < ∫⁻ x, (f x)⁻¹ ∂μ := by
  by_cases hf_const : f =ᵐ[μ] fun _ ↦ (∫⁻ x, f x ∂μ)
  · exact .inl hf_const
  right
  have h_int_ne_zero : ∫⁻ x, f x ∂μ ≠ 0 := by
    by_contra! h
    rw [h] at hf_const
    rw [lintegral_eq_zero_iff hf] at h
    exact hf_const h
  by_cases h_int_top : ∫⁻ x, f x ∂μ = ∞
  · simp only [h_int_top, inv_top, gt_iff_lt]
    by_contra! h
    simp only [nonpos_iff_eq_zero, lintegral_eq_zero_iff hf.inv] at h
    refine absurd h ?_
    rw [Filter.EventuallyEq]
    simp only [Pi.zero_apply, ENNReal.inv_eq_zero, Filter.not_eventually]
    exact hf_top.frequently
  by_cases h_int_inv_top : ∫⁻ x, (f x)⁻¹ ∂μ = ∞
  · simp [h_int_inv_top, pos_iff_ne_zero, h_int_ne_zero]
  have h_left_eq_add : (∫⁻ x, f x ∂μ)⁻¹
      = ∫⁻ x in {y | f y = ∫⁻ z, f z ∂μ}, (∫⁻ y, f y ∂μ)⁻¹ ∂μ
        + ∫⁻ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, (∫⁻ y, f y ∂μ)⁻¹ ∂μ := by
    simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, ne_eq]
    change _ = _ * μ {x | f x = ∫⁻ y, f y ∂μ} + _ * μ {x | f x = ∫⁻ y, f y ∂μ}ᶜ
    rw [← mul_add, measure_add_measure_compl, measure_univ, mul_one]
    exact measurableSet_eq_fun' hf measurable_const
  have h_right_eq_add : ∫⁻ x, (f x)⁻¹ ∂μ
      = ∫⁻ x in {y | f y = ∫⁻ z, f z ∂μ}, (f x)⁻¹ ∂μ
        + ∫⁻ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, (f x)⁻¹ ∂μ := by
    change _ = _ + ∫⁻ x in {y | f y = ∫⁻ z, f z ∂μ}ᶜ, (f x)⁻¹ ∂μ
    rw [lintegral_add_compl]
    exact measurableSet_eq_fun' hf measurable_const
  rw [h_left_eq_add, h_right_eq_add]
  refine ENNReal.add_lt_add_of_le_of_lt ?_ ?_ ?_
  · simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, ne_eq]
    exact ENNReal.mul_ne_top (by simpa) (by simp)
  · refine le_of_eq ?_
    refine setLIntegral_congr_fun ?_ fun x hx ↦ ?_
    · exact measurableSet_eq_fun' hf measurable_const
    simp only [mem_setOf_eq] at hx
    rw [hx]
  · have h_cvx_lt x (hx : f x ≠ ∞) := Inv.lt_add_deriv_mul (y := ∫⁻ x, f x ∂μ) hx h_int_ne_zero
    rw [lintegral_eq_eintegral, lintegral_eq_eintegral (μ := μ.restrict {y | f y ≠ ∫⁻ z, f z ∂μ})]
    refine EReal.toENNReal_lt_toENNReal ?_ ?_
    · rw [eintegral_eq_lintegral]
      exact EReal.coe_ennreal_nonneg _
    calc ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, ((∫⁻ y, f y ∂μ)⁻¹ : ℝ≥0∞) ∂μ
    _ < ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ},
        (f x)⁻¹ - Inv.deriv (∫⁻ z, f z ∂μ) * (f x - ∫⁻ z, f z ∂μ) ∂μ := by
      refine eintegral_strict_mono_ae ?_ ?_
      · rw [ae_restrict_iff']
        swap; · exact (measurableSet_eq_fun' hf measurable_const).compl
        filter_upwards [hf_top] with x hx hx_ne
        specialize h_cvx_lt x hx hx_ne
        rwa [EReal.lt_sub_iff_add_lt (by simp [h_int_ne_zero]) (by simp)]
      · simp [h_int_ne_zero, lt_top_iff_ne_top, EReal.mul_ne_top]
    _ = ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, ((f x)⁻¹ : ℝ≥0∞) ∂μ
        - Inv.deriv (∫⁻ z, f z ∂μ) * ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, (f x - ∫⁻ z, f z ∂μ) ∂μ := by
      rw [eintegral_sub]
      rotate_left
      · exact eintegrable_of_nonneg fun x ↦ by positivity
      · fun_prop
      · sorry
      · fun_prop
      · left
        rw [eintegral_eq_lintegral, ne_eq, EReal.coe_ennreal_eq_top_iff]
        refine ne_top_of_le_ne_top h_int_inv_top ?_
        exact setLIntegral_le_lintegral _ _
      · simp [eintegral_eq_lintegral]
      congr
      rw [eintegral_mul_const]
      · simp
      · exact deriv_inv_ne_top h_int_ne_zero
      · sorry
    _ = ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, ((f x)⁻¹ : ℝ≥0∞) ∂μ
        - Inv.deriv (∫⁻ z, f z ∂μ) * ∫ᵉ x, (f x - ∫⁻ z, f z ∂μ) ∂μ := by
      congr 2
      nth_rw 2 [eintegral_add_compl (A := {y | f y = ∫⁻ z, f z ∂μ})]
      swap; · exact measurableSet_eq_fun' hf measurable_const
      suffices h_zero : ∫ᵉ x in {y | f y = ∫⁻ z, f z ∂μ}, (f x - ∫⁻ z, f z ∂μ) ∂μ = 0 by
        rw [h_zero, zero_add]
        congr
      suffices ∀ x ∈ {y | f y = ∫⁻ z, f z ∂μ}, (f x : EReal) - ∫⁻ z, f z ∂μ = 0 by
        rw [eintegral_congr_ae (ae_restrict_of_forall_mem ?_ this)]
        · simp
        · exact measurableSet_eq_fun' hf measurable_const
      intro x hx
      rw [hx, EReal.sub_self (by simp [h_int_top]) (by simp)]
    _ = ∫ᵉ x in {y | f y ≠ ∫⁻ z, f z ∂μ}, ((f x)⁻¹ : ℝ≥0∞) ∂μ := by
      suffices ∫ᵉ x, (f x - ∫⁻ z, f z ∂μ) ∂μ = 0 by simp [this]
      rw [eintegral_sub]
      · rw [eintegral_eq_lintegral]
        simp only [eintegral_const, measure_univ, EReal.coe_ennreal_one, mul_one]
        rw [EReal.sub_self (by simp [h_int_top]) (by simp)]
      · exact eintegrable_of_nonneg fun x ↦ by positivity
      · fun_prop
      · exact eintegrable_const
      · fun_prop
      · simp [h_int_top]
      · simp

theorem Inv.ae_eq_const_or_map_lintegral_lt [IsProbabilityMeasure μ] (hf : AEMeasurable f μ)
    (hf_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    f =ᵐ[μ] const α (∫⁻ x, f x ∂μ) ∨ (∫⁻ x, f x ∂μ)⁻¹ < ∫⁻ x, (f x)⁻¹ ∂μ := by
  have hf_top' : ∀ᵐ x ∂μ, hf.mk f x ≠ ∞ := by
    filter_upwards [hf_top, hf.ae_eq_mk] with x hx_ne hx_eq using by rwa [← hx_eq]
  have h := Inv.ae_eq_const_or_map_lintegral_lt' hf.measurable_mk (μ := μ) hf_top'
  cases h with
  | inl h =>
    left
    filter_upwards [hf.ae_eq_mk, h] with x hx_eq hx_const
    rw [hx_eq, hx_const]
    congr 1
    exact lintegral_congr_ae hf.ae_eq_mk.symm
  | inr h =>
    right
    rw [lintegral_congr_ae hf.ae_eq_mk]
    refine h.trans_eq ?_
    refine lintegral_congr_ae ?_
    filter_upwards [hf.ae_eq_mk] with x hx_eq
    rw [hx_eq]

theorem Inv.ae_eq_const_or_map_set_lintegral_lt (ht : MeasurableSet t)
    (hf : AEMeasurable f (μ.restrict t)) (hμ_t₀ : μ t ≠ 0) (hμ_t₁ : μ t ≠ ⊤)
    (ht_top : ∀ᵐ x ∂μ, x ∈ t → f x ≠ ⊤) :
    f =ᵐ[μ.restrict t] const α ((μ t)⁻¹ * ∫⁻ x in t, f x ∂μ) ∨
      μ t * (∫⁻ x in t, f x ∂μ)⁻¹ < (μ t)⁻¹ * ∫⁻ x in t, (f x)⁻¹ ∂μ := by
  have : IsProbabilityMeasure μ[|t] := cond_isProbabilityMeasure_of_finite hμ_t₀ hμ_t₁
  replace hf : AEMeasurable f μ[|t] := hf.cond
  replace ht_top : ∀ᵐ x ∂μ[|t], f x ≠ ⊤ := by
    unfold ProbabilityTheory.cond
    rw [← μ.restrict_smul, ae_restrict_iff' ht]
    change ((μ t)⁻¹ • μ) {x | x ∈ t → f x ≠ ⊤}ᶜ = 0
    rw [Measure.smul_apply]
    exact smul_eq_zero_of_right (μ t)⁻¹ ht_top
  rcases Inv.ae_eq_const_or_map_lintegral_lt hf ht_top with h | h
  · left
    unfold Filter.EventuallyEq at h ⊢
    rw [ae_restrict_iff' ht]
    simp only [const_apply] at h ⊢
    change μ {x | x ∈ t → f x = ((μ t)⁻¹ * ∫⁻ x in t, f x ∂μ)}ᶜ = 0
    replace h : μ[|t] {x | f x = ∫⁻ x, f x ∂μ[|t]}ᶜ = 0 := h
    simp_all only [ne_eq, ProbabilityTheory.cond, ENNReal.inv_eq_zero, not_false_eq_true,
      aemeasurable_smul_measure_iff, Measure.ae_smul_measure_eq, ae_restrict_eq,
      lintegral_smul_measure, smul_eq_mul, Measure.smul_apply, Measure.restrict_apply', mul_eq_zero,
      false_or]
    rw [← h]
    congr
    simp only [compl_def, mem_setOf_eq, Classical.not_imp]
    ext x
    constructor
    · rintro ⟨hxt, hx⟩
      refine ⟨hx, hxt⟩
    · rintro ⟨hx, hxt⟩
      refine ⟨hxt, hx⟩
  · right
    calc
    _ = (∫⁻ x, f x ∂μ[|t])⁻¹ := by
      simp only [lintegral_smul_measure, smul_eq_mul, ProbabilityTheory.cond]
      rw [ENNReal.mul_inv, inv_inv]
      · left
        simp [hμ_t₁]
      · left
        simp [hμ_t₀]
    _ < ∫⁻ x, (f x)⁻¹ ∂μ[|t] := h
    _ = (μ t)⁻¹ * ∫⁻ x in t, (f x)⁻¹ ∂μ := by
      simp [ProbabilityTheory.cond]

/- theorem Inv.ae_eq_const_or_map_set_lintegral_lt (ht : MeasurableSet t)
    (hf : AEMeasurable f (μ.restrict t)) (hμ_t₀ : μ t ≠ 0) (hμ_t₁ : μ t ≠ ⊤)
    (ht_top : ∀ᵐ x ∂μ, x ∈ t → f x ≠ ⊤) :
    f =ᵐ[μ.restrict t] const α (∫⁻ x in t, f x ∂μ) ∨
      μ t * (∫⁻ x in t, f x ∂μ)⁻¹ < ∫⁻ x in t, (f x)⁻¹ ∂μ := by
  by_cases h0 : ∫⁻ x in t, f x ∂μ = 0
  · simp only [h0, const_zero, ENNReal.inv_zero]
    left
    rw [setLIntegral_eq_zero_iff' ht hf] at h0
    rw [← ae_restrict_iff' ht] at h0
    filter_upwards [h0] with x hx using hx
  · by_cases htop_inv : ∫⁻ x in t, (f x)⁻¹ ∂μ = ⊤
    · simp only [htop_inv]
      right
      refine mul_lt_top ?_ ?_
      · exact Ne.lt_top' hμ_t₁.symm
      · simp [pos_of_ne_zero h0]
    · let y := ∫⁻ x in t, f x ∂μ
      by_cases h_eq : f =ᵐ[μ.restrict t] const α y
      · exact .inl h_eq
        /- unfold Filter.EventuallyEq
        rw [ae_restrict_iff' ht]
        filter_upwards with x hxt
        exact h_eq x hxt -/
      · right
        let S := {x | f x ≠ y} ∩ t
        have hS_meas : MeasurableSet S := by sorry
        have : μ t * (∫⁻ (x : α) in t, f x ∂μ)⁻¹ =
            (∫ᵉ x in S, y⁻¹ + Inv.deriv y * (f x - y) ∂μ).toENNReal := by
          calc
          _ = μ t * ((∫ᵉ x in t, f x ∂μ).toENNReal)⁻¹ := by
            rw [lintegral_eq_eintegral _]
          _ = (∫ᵉ x in t, y⁻¹ + Inv.deriv y * (f x - y) ∂μ).toENNReal := by
            rw [eintegral_add]
            · have : ∫ᵉ x in t, Inv.deriv y * ((f x) - y) ∂μ = 0 := by sorry
              rw [this]
              simp only [eintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
                add_zero]
              rw [← lintegral_eq_eintegral _, EReal.toENNReal_mul <| EReal.coe_ennreal_nonneg _]
              simp
              ring
            · fun_prop
            · fun_prop
            · sorry
            · sorry
            · sorry
            · sorry
          _ = (∫ᵉ x in S, y⁻¹ + Inv.deriv y * (f x - y) ∂μ).toENNReal := by
            congr 1

            rw [eintegral_add_compl hS_meas]
            suffices ∫ᵉ x in Sᶜ, y⁻¹ + Inv.deriv y * ((f x) - y) ∂μ.restrict t = 0 by
              simp [this]
              have : μ.restrict S = (μ.restrict t).restrict S := by
                rw [Measure.restrict_restrict hS_meas]
                simp only [S]
                congr 1
                simp
              simp [this]
            rw [← eintegral_zero ((μ.restrict t).restrict Sᶜ)]
            refine eintegral_congr_ae ?_
            rw [ae_restrict_iff' hS_meas.compl, ae_restrict_iff' ht]
            filter_upwards with x hxt hxS
            simp [S] at hxS
            by_cases hxy : f x ≠ y
            · exfalso
              exact hxS hxy hxt
            · push_neg at hxy
              rw [hxy]
              have : (y : EReal) - (y : EReal) = 0 := by
                refine EReal.sub_self ?_ (EReal.coe_ennreal_ne_bot y)
                sorry
              simp [this]
        calc
        _ = (∫ᵉ x in t, y⁻¹ + Inv.deriv y * (f x - y) ∂μ).toENNReal := by rw [this]
        _ < (∫ᵉ x in t, (Inv.inv (α := ℝ≥0∞) (f x)) ∂μ).toENNReal := by
          replace h_eq : μ {x | x ∈ t → f x = y}ᶜ ≠ 0 := by
            unfold Filter.EventuallyEq at h_eq
            rw [ae_restrict_iff' ht] at h_eq
            exact h_eq

          have : {x | x ∈ t → f x = y}ᶜ = {x | x ∈ t ∧ f x ≠ y} := by simp
          rw [this] at h_eq
          clear this
          set S := {x | x ∈ t ∧ f x ≠ y}
          rw []

          refine EReal.toENNReal_lt_toENNReal ?_ ?_
          · sorry
          · refine eintegral_strict_mono_ae ?_ ?_
            · rw [ae_restrict_iff' ht]

              filter_upwards [ht_top, h_eq] with x hx hxy hxt
              exact Inv.lt_add_deriv_mul (hx hxt) h0 (hxy hxt)
            · sorry
        _ ≤ ∫⁻ x in t, (f x)⁻¹ ∂μ := by
          rw [← lintegral_eq_eintegral _] -/

/- theorem ConvexOn.map_set_lintegral_le (hg : ConvexOn ℝ≥0∞ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) :
    g (∫⁻ x in t, f x ∂μ) ≤ ∫⁻ x in t, g (f x) ∂μ :=
  sorry -/

/- theorem StrictConvexOn.ae_eq_const_or_map_laverage_lt [IsFiniteMeasure μ]
    (hg : StrictConvexOn ℝ≥0∞ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) :
    f =ᵐ[μ] const α (⨍⁻ x, f x ∂μ) ∨ g (⨍⁻ x, f x ∂μ) < ⨍⁻ x, g (f x) ∂μ := by
  sorry -/

/- theorem StrictConvexOn.ae_eq_const_or_map_set_lintegral_lt [IsFiniteMeasure μ]
    (hg : StrictConvexOn ℝ≥0∞ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) :
    f =ᵐ[μ] const α (∫⁻ x, f x ∂μ) ∨ g (∫⁻ x in t, f x ∂μ) < ∫⁻ x in t, g (f x) ∂μ := by
  sorry
 -/
#min_imports
