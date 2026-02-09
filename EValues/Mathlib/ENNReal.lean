/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Order.CompletePartialOrder

open ENNReal

namespace Function

/-- The finite support of a function `X : α → β` with top and zero elements is the set of points
where `X` is neither `⊤` or `0`. -/
abbrev fsupport {α β : Type*} [Top β] [Zero β] (f : α → β) := {x | f x ≠ ⊤} ∩ {x | f x ≠ 0}

lemma fsupport_compl {α β : Type*} [Top β] [Zero β] (X : α → β) :
    X.fsupportᶜ = {ω | X ω = ⊤} ∪ {ω | X ω = 0} := by
  ext ω
  simp [-not_and, not_and_or]

lemma fsupport_compl_disjoint {α β : Type*} [Top β] [Zero β] (X : α → β) (h : (0 : β) ≠ ⊤) :
    Disjoint {ω | X ω = ⊤} {ω | X ω = 0} := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and_or]
  by_contra! h'
  rw [h'.1] at h'
  exact h.symm h'.2

lemma not_mem_fsupport_iff {α β : Type*} [Top β] [Zero β] (X : α → β) (ω : α) :
    ω ∉ X.fsupport ↔ X ω = ⊤ ∨ X ω = 0 := by
  rw [← Set.mem_compl_iff, fsupport_compl]
  simp

end Function

namespace ENNReal

lemma eq_of_div_eq_one {a b : ℝ≥0∞} (h : a / b = 1) : a = b := by
  by_cases hb_zero : b = 0
  · simp only [hb_zero] at h ⊢
    by_cases ha_zero : a = 0
    · exact ha_zero
    · simp [ENNReal.div_zero ha_zero] at h
  by_cases hb_top : b = ⊤
  · simp [hb_top] at h
  rwa [ENNReal.div_eq_one_iff hb_zero hb_top] at h

lemma inv_div_fsupport {α : Type*} (f g : α → ℝ≥0∞) :
    ∀ x ∈ g.fsupport, ((f / g) x)⁻¹ = g x / f x := by
  intro x hx
  simp only [Pi.div_apply]
  rw [ENNReal.inv_div]
  · exact Or.inl hx.1
  · exact Or.inl hx.2

lemma log_div (a b : ℝ≥0∞) : ENNReal.log (a / b) = ENNReal.log a - ENNReal.log b := by
  simp_rw [div_eq_mul_inv, ENNReal.log_mul_add, ENNReal.log_inv, sub_eq_add_neg]

end ENNReal
