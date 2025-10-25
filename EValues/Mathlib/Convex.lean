/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Action.Prod
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.InnerProductSpace.Basic

open Set ENNReal

lemma strictConvexOn_inv_Ioi : StrictConvexOn ℝ (Ioi (0 : ℝ)) Inv.inv := by
  apply strictConvexOn_of_slope_strict_mono_adjacent (convex_Ioi (0 : ℝ))
  intro x y z (hx : 0 < x) (hz : 0 < z) hxy hyz
  have hy : 0 < y := hx.trans hxy
  have A : (y⁻¹ - x⁻¹) / (y - x) = -1 / (x * y) := by
    field_simp [ne_of_gt hx, ne_of_gt hy]
    have : (x - y) / (y - x) = -((y - x) / (y - x)) := by ring
    rw [this]
    suffices (y - x) / (y - x) = 1 by
      rw [this]
    rw [div_eq_iff (ne_of_lt <| sub_pos.2 hxy).symm]
    simp
  have B : (z⁻¹ - y⁻¹) / (z - y) = -1 / (y * z) := by
    field_simp [ne_of_gt hy, ne_of_gt hz]
    have : (y - z) / (z - y) = -((z - y) / (z - y)) := by ring
    rw [this]
    suffices (z - y) / (z - y) = 1 by
      rw [this]
    rw [div_eq_iff (ne_of_lt <| sub_pos.2 hyz).symm]
    simp
  rw [A, B]
  field_simp
  linarith

lemma strictConvexOn_inv : StrictConvexOn ℝ≥0∞ univ <| Inv.inv (α := ℝ≥0∞) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b a₀ b₀ hab
  simp only [smul_eq_mul]
  have a₁ : a ≠ ⊤ := by
    by_contra h
    simp [h] at hab
  have b₁ : b ≠ ⊤ := by
    by_contra h
    simp [h] at hab
  by_cases h : x ≠ 0 ∧ x ≠ ⊤ ∧ y ≠ 0 ∧ y ≠ ⊤
  · obtain ⟨x₀, x₁, y₀, y₁⟩ := h
    suffices (a * x + b * y)⁻¹.toReal < (a * x⁻¹ + b * y⁻¹).toReal by
      refine (toNNReal_lt_toNNReal ?_ ?_).mp this
      · refine inv_ne_top.mpr ?_
        suffices 0 < a * x + b * y from this.ne'
        exact Right.add_pos' (mul_pos a₀.ne' x₀) (mul_pos b₀.ne' y₀)
      · refine add_ne_top.mpr ⟨?_, ?_⟩
        · exact mul_ne_top a₁ <| inv_ne_top.mpr x₀
        · exact mul_ne_top b₁ <| inv_ne_top.mpr y₀
    rw [toReal_inv, toReal_add, toReal_add, toReal_mul, toReal_mul,
      toReal_mul, toReal_mul, toReal_inv, toReal_inv]
    · obtain ⟨_, strc_conv⟩ := strictConvexOn_inv_Ioi
      refine strc_conv (toReal_pos x₀ x₁) (toReal_pos y₀ y₁) ?_
        (toReal_pos a₀.ne' a₁) (toReal_pos b₀.ne.symm b₁) ?_
      · by_contra h
        have : x = y := (toReal_eq_toReal_iff' x₁ y₁).mp h
        contradiction
      · rw [← toReal_add a₁ b₁]
        exact (toReal_eq_one_iff (a + b)).mpr hab
    · exact mul_ne_top a₁ <| inv_ne_top.mpr x₀
    · exact mul_ne_top b₁ <| inv_ne_top.mpr y₀
    · exact mul_ne_top a₁ <| x₁
    · exact mul_ne_top b₁ <| y₁
  · simp only [not_and_or] at h
    rcases h with x₀ | x₁ | y₀ | y₁
    · push_neg at x₀
      simp only [x₀, mul_zero, zero_add, ENNReal.inv_zero, ENNReal.mul_top a₀.ne', top_add,
        inv_lt_top, CanonicallyOrderedAdd.mul_pos]
      refine ⟨b₀, pos_of_ne_zero ?_⟩
      rw [x₀] at hxy
      exact hxy.symm
    · push_neg at x₁
      simp only [x₁, ENNReal.mul_top a₀.ne', top_add, inv_top, mul_zero, zero_add,
        CanonicallyOrderedAdd.mul_pos, ENNReal.inv_pos, ne_eq]
      refine ⟨b₀, ?_⟩
      rw [x₁] at hxy
      exact hxy.symm
    · push_neg at y₀
      simp only [y₀, mul_zero, add_zero, ENNReal.inv_zero, ENNReal.mul_top b₀.ne', add_top,
        inv_lt_top, CanonicallyOrderedAdd.mul_pos]
      refine ⟨a₀, pos_of_ne_zero ?_⟩
      rw [y₀] at hxy
      exact hxy
    · push_neg at y₁
      simp only [y₁, ENNReal.mul_top b₀.ne', add_top, inv_top, mul_zero, add_zero,
        CanonicallyOrderedAdd.mul_pos, ENNReal.inv_pos, ne_eq]
      refine ⟨a₀, ?_⟩
      rw [y₁] at hxy
      exact hxy

lemma convexOn_inv_Ioi : ConvexOn ℝ (Ioi (0 : ℝ)) Inv.inv := strictConvexOn_inv_Ioi.convexOn

lemma convexOn_inv : ConvexOn ℝ≥0∞ univ <| Inv.inv (α := ℝ≥0∞) := strictConvexOn_inv.convexOn
