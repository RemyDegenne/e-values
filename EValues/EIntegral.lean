/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : α → EReal}

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

@[simp]
lemma eintegral_zero (μ : Measure α) : ∫ᵉ _, (0 : EReal) ∂μ = 0 := by simp [eintegral]

lemma eintegral_of_nonneg (hf : ∀ x, 0 ≤ f x) : ∫ᵉ x, f x ∂μ = ∫⁻ x, (f x).toENNReal ∂μ := by
  simp [eintegral, hf]

lemma eintegral_of_ae_nonneg (hf : AEMeasurable f μ) (hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x) :
    ∫ᵉ x, f x ∂μ = ∫⁻ x, (f x).toENNReal ∂μ := by
  rw [eintegral]
  suffices ∫⁻ x, (-f x).toENNReal ∂μ = 0 by simp [this]
  rw [lintegral_eq_zero_iff']
  · filter_upwards [hf_nonneg] with x hx using by simp [hx]
  · fun_prop

lemma eintegral_of_nonpos (hf : ∀ x, f x ≤ 0) : ∫ᵉ x, f x ∂μ = - ∫⁻ x, (-f x).toENNReal ∂μ := by
  simp [eintegral, hf]

lemma eintegral_of_ae_nonpos (hf : AEMeasurable f μ) (hf_nonpos : ∀ᵐ x ∂μ, f x ≤ 0) :
    ∫ᵉ x, f x ∂μ = - ∫⁻ x, (-f x).toENNReal ∂μ := by
  rw [eintegral]
  suffices ∫⁻ x, (f x).toENNReal ∂μ = 0 by simp [this]
  rw [lintegral_eq_zero_iff']
  · filter_upwards [hf_nonpos] with x hx using by simp [hx]
  · fun_prop

lemma eintegral_add (μ : Measure α) (f g : α → EReal) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ := by
  -- cut the space into four parts depending on the signs of `f` and `g`
  sorry

lemma eintegral_sub (μ : Measure α) (f g : α → EReal) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  sorry

end MeasureTheory
