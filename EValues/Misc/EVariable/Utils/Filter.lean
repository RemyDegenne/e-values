/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.MeasureTheory.OuterMeasure.AE

namespace Filter

variable {α : Type*} {β : Type*} (l : Filter α) (f g : α → β)

def EventuallyLT [LT β] := ∀ᶠ x in l, f x < g x

notation3 f " <ᶠ[" l:50 "] " g:50 => EventuallyLT l f g
notation3 f " <ᵐ[" μ:50 "] " g:50 => Filter.EventuallyLT (MeasureTheory.ae μ) f g

namespace EventuallyLT

lemma eventually_le [Preorder β] : f <ᶠ[l] g → f ≤ᶠ[l] g := by
  intro h
  filter_upwards [h] with x hx
  exact hx.le

end EventuallyLT

end Filter
