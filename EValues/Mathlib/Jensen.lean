/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.MeasureTheory.Integral.Average

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
