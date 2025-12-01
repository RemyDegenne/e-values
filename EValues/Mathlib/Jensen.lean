/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import EValues.EIntegral
import EValues.Mathlib.Convex
import Mathlib

open Function Set ENNReal

open MeasureTheory

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

theorem Inv.map_set_lintegral_le (ht : MeasurableSet t) (hf : AEMeasurable f (μ.restrict t))
    (hμ_t : μ t ≠ 0) (ht_top : ∀ᵐ x ∂μ, x ∈ t → f x ≠ ⊤) :
    μ t * (∫⁻ x in t, f x ∂μ)⁻¹ ≤ ∫⁻ x in t, (f x)⁻¹ ∂μ := by
  by_cases h0 : ∫⁻ x in t, f x ∂μ = 0
  · simp only [h0, ENNReal.inv_zero, ENNReal.mul_top hμ_t]
    rw [setLIntegral_eq_zero_iff' ht hf] at h0
    have : ∀ᵐ x ∂μ, x ∈ t → (f x)⁻¹ = ⊤ := by
      filter_upwards [h0] with x hx hxt
      rw [hx hxt]
      simp
    rw [setLIntegral_congr_fun_ae ht this]
    simp [hμ_t]
  · by_cases htop_inv : ∫⁻ x in t, (f x)⁻¹ ∂μ = ⊤
    · simp [htop_inv]
    · let y := ∫⁻ x in t, f x ∂μ
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
      _ ≤ (∫ᵉ x in t, (Inv.inv (α := ℝ≥0∞) (f x)) ∂μ).toENNReal := by
        refine EReal.toENNReal_le_toENNReal ?_
        refine eintegral_mono_ae ?_
        unfold Filter.EventuallyLE
        rw [ae_restrict_iff' ht]
        filter_upwards [ht_top] with x hx hxt
        exact Inv.le_add_deriv_mul (hx hxt) h0
      _ ≤ ∫⁻ x in t, (f x)⁻¹ ∂μ := by
        rw [← lintegral_eq_eintegral _]

theorem Inv.map_lintegral_le [IsProbabilityMeasure μ] (hf : AEMeasurable f μ)
    (hf_top : ∀ᵐ x ∂μ, f x ≠ ⊤) : (∫⁻ x, f x ∂μ)⁻¹ ≤ ∫⁻ x, (f x)⁻¹ ∂μ := by
  have := Inv.map_set_lintegral_le (f := f) (μ := μ) MeasurableSet.univ hf.restrict (by simp) ?_
  · simp_all
  · simp_all only [ne_eq, mem_univ, forall_const]

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
      · simp_all
      · refine (EReal.mul_ne_top ↑(y.toReal ^ 2)⁻¹ ↑y).mpr ⟨?_, ?_, ?_, ?_⟩
        · right
          positivity
        · right
          simp_all
        · left
          simp
        · right
          simp_all
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

theorem ConvexOn.map_set_lintegral_le (hg : ConvexOn ℝ≥0∞ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) :
    g (∫⁻ x in t, f x ∂μ) ≤ ∫⁻ x in t, g (f x) ∂μ :=
  sorry

/- theorem StrictConvexOn.ae_eq_const_or_map_laverage_lt [IsFiniteMeasure μ]
    (hg : StrictConvexOn ℝ≥0∞ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) :
    f =ᵐ[μ] const α (⨍⁻ x, f x ∂μ) ∨ g (⨍⁻ x, f x ∂μ) < ⨍⁻ x, g (f x) ∂μ := by
  sorry -/

theorem StrictConvexOn.ae_eq_const_or_map_set_lintegral_lt [IsFiniteMeasure μ]
    (hg : StrictConvexOn ℝ≥0∞ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) :
    f =ᵐ[μ] const α (∫⁻ x, f x ∂μ) ∨ g (∫⁻ x in t, f x ∂μ) < ∫⁻ x in t, g (f x) ∂μ := by
  sorry
