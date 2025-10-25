import Mathlib

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The integral of an `EReal`-valued function with respect to a measure `μ`, defined as the
difference of two lower Lebesgue integrals. -/
noncomputable def integral_ereal (μ : Measure α) (f : α → EReal) : EReal :=
    ∫⁻ x, (f x).toENNReal ∂μ - ∫⁻ x, (-f x).toENNReal ∂μ

@[inherit_doc MeasureTheory.integral_ereal]
notation3 "∫ᵉ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => integral_ereal μ r

@[inherit_doc MeasureTheory.integral_ereal]
notation3 "∫ᵉ "(...)", "r:60:(scoped f => integral_ereal volume f) => r

@[inherit_doc MeasureTheory.integral_ereal]
notation3 "∫ᵉ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 =>
    integral_ereal (Measure.restrict μ s) r

@[inherit_doc MeasureTheory.integral_ereal]
notation3 "∫ᵉ "(...)" in "s", "r:60:(scoped f => integral_ereal (Measure.restrict volume s) f) => r

end MeasureTheory
