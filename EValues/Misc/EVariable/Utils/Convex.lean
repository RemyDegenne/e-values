/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib

open Set ENNReal

namespace StrictConvexOn

lemma inv : StrictConvexOn ℝ (Ioi (0 : ℝ)) Inv.inv := by
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

lemma inv' : StrictConvexOn ℝ≥0∞ univ <| Inv.inv (α := ℝ≥0∞) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b a₀ b₀ hab
  simp only [smul_eq_mul]
  by_cases x₀ : x = 0
  · simp only [x₀, mul_zero, zero_add, ENNReal.inv_zero, ENNReal.mul_top a₀.ne', top_add,
    inv_lt_top, CanonicallyOrderedAdd.mul_pos]
    refine ⟨b₀, pos_of_ne_zero ?_⟩
    rw [x₀] at hxy
    exact hxy.symm
  · push_neg at x₀
    by_cases y₀ : y = 0
    · simp only [y₀, mul_zero, add_zero, ENNReal.inv_zero, ENNReal.mul_top b₀.ne', add_top,
      inv_lt_top, CanonicallyOrderedAdd.mul_pos]
      exact ⟨a₀, pos_of_ne_zero x₀⟩
    · push_neg at y₀
      by_cases x₁ : x = ⊤
      · simp only [x₁, ENNReal.mul_top a₀.ne', top_add, inv_top, mul_zero, zero_add,
        CanonicallyOrderedAdd.mul_pos, ENNReal.inv_pos, ne_eq]
        refine ⟨b₀, ?_⟩
        rw [x₁] at hxy
        exact hxy.symm
      · push_neg at x₁
        by_cases y₁ : y = ⊤
        · simp only [y₁, ENNReal.mul_top b₀.ne', add_top, inv_top, mul_zero, add_zero,
          CanonicallyOrderedAdd.mul_pos, ENNReal.inv_pos, ne_eq]
          exact ⟨a₀, x₁⟩
        · push_neg at y₁
          have a₁ : a ≠ ⊤ := by
              by_contra h
              simp [h] at hab
          have b₁ : b ≠ ⊤ := by
            by_contra h
            simp [h] at hab
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
          · obtain ⟨_, strc_conv⟩ := StrictConvexOn.inv
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

end StrictConvexOn

namespace ConvexOn

lemma inv : ConvexOn ℝ (Ioi (0 : ℝ)) Inv.inv := StrictConvexOn.inv.convexOn

lemma inv' : ConvexOn ℝ≥0∞ univ <| Inv.inv (α := ℝ≥0∞) := StrictConvexOn.inv'.convexOn

end ConvexOn
