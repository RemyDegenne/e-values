/-
 - Created in 2025 by Gaëtan Serré
-/

import EValues.Misc.EVariable.Numeraire.Defs
import EValues.Misc.EVariable.Utils.Convex
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Convex.Integral

open MeasureTheory Function Set ENNReal

variable {α : Type*} [MeasurableSpace α]

variable {P : Set (ProbabilityMeasure α)} {Q : Measure α} [IsProbabilityMeasure Q]

namespace Numeraire

variable (e_n e : Numeraire P Q)

lemma almost_surely_unique : e =ᵐ[Q] e_n := by
  let f := Inv.inv (α := ℝ≥0∞)
  have strc_convex : StrictConvexOn ℝ≥0∞ univ f := StrictConvexOn.inv'
  let Y := fun x ↦ e x /ₑ e_n x
  have inv_avg_eq_one : f (⨍⁻ x, Y x ∂Q) = 1 := by
    suffices 1 ≤ f (⨍⁻ x, Y x ∂Q) by
      have : f (⨍⁻ (x : α), Y x ∂Q) ≤ 1 := by
        suffices f (⨍⁻ x, Y x ∂Q) ≤ ⨍⁻ x, f (Y x) ∂Q by
            trans ⨍⁻ x, f (Y x) ∂Q
            · assumption
            · simp only [enn_inv_div, f, Y]
              exact e.average_ratio_le_one e_n.toEVariable
        refine strc_convex.convexOn.map_laverage_le continuousOn_inv isClosed_univ ?_
        simp
      -- linarith
      sorry
    simp only [f]
    exact ENNReal.one_le_inv.mpr <| e_n.average_ratio_le_one e.toEVariable

  have strict_Jensen : Y =ᵐ[Q] const α (⨍⁻ x, Y x ∂Q) ∨
      f (⨍⁻ x, Y x ∂Q) < ⨍⁻ x, f (Y x) ∂Q := by
    refine strc_convex.ae_eq_const_or_map_laverage_lt continuousOn_inv isClosed_univ ?_
    simp

  cases strict_Jensen with
  | inl h =>
    have avg_eq_one : ⨍⁻ x, Y x ∂Q = 1 := by
      simp only [ENNReal.inv_eq_one, f] at inv_avg_eq_one
      assumption
    rw [avg_eq_one] at h
    filter_upwards [h] with x hx
    simp only [const_apply, Y] at hx
    rw [enn_div_eq_one] at hx
    simp_all
  | inr h =>
    rw [inv_avg_eq_one] at h
    simp only [enn_inv_div, f, Y] at h
    have : ⨍⁻ (x : α), (e_n x /ₑ e x) ∂Q ≤ 1 := e.average_ratio_le_one e_n.toEVariable
    sorry
    --linarith

end Numeraire

namespace is_numeraire

variable {e_n : α → ℝ≥0∞}

lemma mono (he_n : is_numeraire P Q e_n) {P' : Set (ProbabilityMeasure α)} (hP : P ⊆ P')
    (he : is_evariable P' e_n) : is_numeraire P' Q e_n :=
  ⟨he, fun f ↦ he_n.2 <| f.mono hP⟩

end is_numeraire

namespace Numeraire

variable {e_n : Numeraire P Q}

def mono {P' : Set (ProbabilityMeasure α)} (hP : P ⊆ P') (he : is_evariable P' e_n) :
    Numeraire P' Q := (e_n.is_numeraire.mono hP he).to_Numeraire

end Numeraire
