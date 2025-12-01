/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import EValues.EIntegral
import EValues.Mathlib.Convex

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

lemma Inv.le_add_deriv_mul {x y : ℝ≥0∞} (hx_top : x ≠ ⊤) (hy_zero : y ≠ 0) (hy_top : y ≠ ⊤) :
    y⁻¹ + Inv.deriv y * (x - y) ≤ x⁻¹ := by
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

theorem Inv.map_lintegral_le [IsProbabilityMeasure μ] (hf : AEMeasurable f μ)
    (hf_top : ∀ᵐ x ∂μ, f x ≠ ⊤) : (∫⁻ x, f x ∂μ)⁻¹ ≤ ∫⁻ x, (f x)⁻¹ ∂μ := by
  by_cases htop : ∫⁻ x, f x ∂μ = ⊤
  · simp [htop]
  · by_cases h0 : ∫⁻ x, f x ∂μ = 0
    · simp only [h0, ENNReal.inv_zero]
      rw [lintegral_eq_zero_iff' hf] at h0
      have : ∀ᵐ x ∂μ, (f x)⁻¹ = ⊤ := by
        filter_upwards [h0] with x hx
        rw [hx]
        simp
      rw [lintegral_congr_ae this]
      simp
    · by_cases htop_inv : ∫⁻ x, (f x)⁻¹ ∂μ = ⊤
      · simp [htop_inv]
      · let y := ∫⁻ x, f x ∂μ
        calc
        _ = ((∫ᵉ x, f x ∂μ).toENNReal)⁻¹ := by
          rw [lintegral_eq_eintegral _]
        _ = (∫ᵉ x, y⁻¹ + Inv.deriv y * (f x - y) ∂μ).toENNReal := by
          rw [eintegral_add]
          · have : ∫ᵉ x, Inv.deriv y * ((f x) - y) ∂μ = 0 := by sorry
            rw [this]
            simp [← lintegral_eq_eintegral _, y]
          · fun_prop
          · fun_prop
          · sorry
          · sorry
          · sorry
          · sorry
        _ ≤ (∫ᵉ x, (Inv.inv (α := ℝ≥0∞) (f x)) ∂μ).toENNReal := by
          refine EReal.toENNReal_le_toENNReal ?_
          refine eintegral_mono_ae ?_
          unfold Filter.EventuallyLE
          filter_upwards [hf_top] with x hfx
          exact Inv.le_add_deriv_mul hfx h0 htop
        _ ≤ ∫⁻ x, (f x)⁻¹ ∂μ := by
          rw [← lintegral_eq_eintegral _]

theorem Inv.map_set_lintegral_le (ht : MeasurableSet t) (hf : AEMeasurable f (μ.restrict t))
    (hμ_t : μ t ≠ 0) (ht_top : ∀ x ∈ t, f x ≠ ⊤) (ht_zero : ∀ x ∈ t, f x ≠ 0) :
    μ t * (∫⁻ x in t, f x ∂μ)⁻¹ ≤ ∫⁻ x in t, (f x)⁻¹ ∂μ := by
  by_cases htop : ∫⁻ x in t, f x ∂μ = ⊤
  · simp [htop]
  · by_cases h0 : ∫⁻ x in t, f x ∂μ = 0
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
          filter_upwards with x hx
          exact Inv.le_add_deriv_mul (ht_top x hx) h0 htop
        _ ≤ ∫⁻ x in t, (f x)⁻¹ ∂μ := by
          rw [← lintegral_eq_eintegral _]

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
