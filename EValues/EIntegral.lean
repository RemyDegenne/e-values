/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The integral of an `EReal`-valued function with respect to a measure `μ`, defined as the
difference of two lower Lebesgue integrals. -/
noncomputable def eintegral (μ : Measure α) (f : α → EReal) : EReal :=
    ∫⁻ x, (f x).toENNReal ∂μ - ∫⁻ x, (-f x).toENNReal ∂μ

@[inherit_doc MeasureTheory.eintegral]
notation3 "∫ᵉ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => eintegral μ r

@[inherit_doc MeasureTheory.eintegral]
notation3 "∫ᵉ "(...)", "r:60:(scoped f => eintegral volume f) => r

@[inherit_doc MeasureTheory.eintegral]
notation3 "∫ᵉ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 =>
    eintegral (Measure.restrict μ s) r

@[inherit_doc MeasureTheory.eintegral]
notation3 "∫ᵉ "(...)" in "s", "r:60:(scoped f => eintegral (Measure.restrict volume s) f) => r

lemma eintegral_sub (μ : Measure α) (f g : α → EReal) :
    ∫ᵉ x, (f x - g x) ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  sorry

end MeasureTheory
