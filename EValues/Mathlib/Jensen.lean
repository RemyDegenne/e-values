/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

-- import EVariable.Utils.Filter
import Mathlib

open Function Set ENNReal

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set ℝ≥0∞} {t : Set α}
  {f : α → ℝ≥0∞} {g : ℝ≥0∞ → ℝ≥0∞}

theorem ConvexOn.map_laverage_le [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConvexOn ℝ≥0∞ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) : g (⨍⁻ x, f x ∂μ) ≤ ⨍⁻ x, g (f x) ∂μ := by
  sorry

theorem ConvexOn.map_set_lintegral_le (hg : ConvexOn ℝ≥0∞ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) :
    g (∫⁻ x in t, f x ∂μ) ≤ ∫⁻ x in t, g (f x) ∂μ :=
  sorry

theorem StrictConvexOn.ae_eq_const_or_map_laverage_lt [IsFiniteMeasure μ]
    (hg : StrictConvexOn ℝ≥0∞ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) :
    f =ᵐ[μ] const α (⨍⁻ x, f x ∂μ) ∨ g (⨍⁻ x, f x ∂μ) < ⨍⁻ x, g (f x) ∂μ := by
  sorry

theorem StrictConvexOn.ae_eq_const_or_map_set_lintegral_lt [IsFiniteMeasure μ]
    (hg : StrictConvexOn ℝ≥0∞ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) :
    f =ᵐ[μ] const α (∫⁻ x, f x ∂μ) ∨ g (∫⁻ x in t, f x ∂μ) < ∫⁻ x in t, g (f x) ∂μ := by
  sorry
