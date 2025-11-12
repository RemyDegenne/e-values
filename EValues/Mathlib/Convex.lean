/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import EValues.Mathlib.EReal
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Set ENNReal NNReal

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
  have aₜ : a ≠ ⊤ := by
    by_contra h
    simp [h] at hab
  have bₜ : b ≠ ⊤ := by
    by_contra h
    simp [h] at hab
  by_cases h : x ≠ 0 ∧ x ≠ ⊤ ∧ y ≠ 0 ∧ y ≠ ⊤
  · obtain ⟨x₀, xₜ, y₀, yₜ⟩ := h
    suffices (a * x + b * y)⁻¹.toReal < (a * x⁻¹ + b * y⁻¹).toReal by
      refine (toNNReal_lt_toNNReal ?_ ?_).mp this
      · refine inv_ne_top.mpr ?_
        suffices 0 < a * x + b * y from this.ne'
        exact Right.add_pos' (mul_pos a₀.ne' x₀) (mul_pos b₀.ne' y₀)
      · refine add_ne_top.mpr ⟨?_, ?_⟩
        · exact mul_ne_top aₜ <| inv_ne_top.mpr x₀
        · exact mul_ne_top bₜ <| inv_ne_top.mpr y₀
    rw [toReal_inv, toReal_add, toReal_add, toReal_mul, toReal_mul,
      toReal_mul, toReal_mul, toReal_inv, toReal_inv]
    · obtain ⟨_, strc_conv⟩ := strictConvexOn_inv_Ioi
      refine strc_conv (toReal_pos x₀ xₜ) (toReal_pos y₀ yₜ) ?_
        (toReal_pos a₀.ne' aₜ) (toReal_pos b₀.ne.symm bₜ) ?_
      · by_contra h
        have : x = y := (toReal_eq_toReal_iff' xₜ yₜ).mp h
        contradiction
      · rw [← toReal_add aₜ bₜ]
        exact (toReal_eq_one_iff (a + b)).mpr hab
    · exact mul_ne_top aₜ <| inv_ne_top.mpr x₀
    · exact mul_ne_top bₜ <| inv_ne_top.mpr y₀
    · exact mul_ne_top aₜ <| xₜ
    · exact mul_ne_top bₜ <| yₜ
  · simp only [not_and_or] at h
    rcases h with x₀ | xₜ | y₀ | yₜ
    · push_neg at x₀
      simp only [x₀, mul_zero, zero_add, ENNReal.inv_zero, ENNReal.mul_top a₀.ne', top_add,
        inv_lt_top, CanonicallyOrderedAdd.mul_pos]
      refine ⟨b₀, pos_of_ne_zero ?_⟩
      rw [← x₀]
      exact hxy.symm
    · push_neg at xₜ
      simp only [xₜ, ENNReal.mul_top a₀.ne', top_add, inv_top, mul_zero, zero_add,
        CanonicallyOrderedAdd.mul_pos, ENNReal.inv_pos, ne_eq]
      refine ⟨b₀, ?_⟩
      rw [xₜ] at hxy
      exact hxy.symm
    · push_neg at y₀
      simp only [y₀, mul_zero, add_zero, ENNReal.inv_zero, ENNReal.mul_top b₀.ne', add_top,
        inv_lt_top, CanonicallyOrderedAdd.mul_pos]
      refine ⟨a₀, pos_of_ne_zero ?_⟩
      rw [y₀] at hxy
      exact hxy
    · push_neg at yₜ
      simp only [yₜ, ENNReal.mul_top b₀.ne', add_top, inv_top, mul_zero, add_zero,
        CanonicallyOrderedAdd.mul_pos, ENNReal.inv_pos, ne_eq]
      refine ⟨a₀, ?_⟩
      rw [yₜ] at hxy
      exact hxy

lemma convexOn_inv_Ioi : ConvexOn ℝ (Ioi (0 : ℝ)) Inv.inv := strictConvexOn_inv_Ioi.convexOn

lemma convexOn_inv : ConvexOn ℝ≥0∞ univ <| Inv.inv (α := ℝ≥0∞) := strictConvexOn_inv.convexOn

noncomputable instance : SMul ℝ≥0 EReal where smul c x := c * x
noncomputable instance : SMul ℝ≥0∞ EReal where smul c x := c * x

lemma ConcaveOn_log' : ConcaveOn ℝ≥0∞ univ log := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b a₀ b₀ hab
  simp only [smul_eq_mul]
  have aₜ : a ≠ ⊤ := by
    by_contra h
    simp [h] at hab
  have bₜ : b ≠ ⊤ := by
    by_contra h
    simp [h] at hab
  have smul_log : ∀ (x y : ℝ≥0∞), x • y.log = x * y.log := fun _ _ ↦ rfl
  simp only [smul_log]
  by_cases h : x ≠ 0 ∧ x ≠ ⊤ ∧ y ≠ 0 ∧ y ≠ ⊤
  · obtain ⟨x₀, xₜ, y₀, yₜ⟩ := h
    suffices (a * x.log + b * y.log).toReal ≤ ((a * x + b * y).log).toReal by
      refine EReal.le_real_imp_le ?_ ?_ ?_ ?_ this
      · simp only [ne_eq, log_eq_top_iff, add_eq_top, not_or]
        exact ⟨mul_ne_top aₜ xₜ, mul_ne_top bₜ yₜ⟩
      · refine EReal.add_ne_top ?_ ?_
        all_goals
          rw [EReal.mul_ne_top]
          simp_all
      · aesop
      · rw [EReal.add_ne_bot_iff, EReal.mul_ne_bot]
        refine ⟨?_, ?_⟩
        · simp_all
        · simp_all [EReal.mul_ne_bot]
    rw [EReal.toReal_add, EReal.toReal_mul, EReal.toReal_mul, EReal.toReal_log, EReal.toReal_log,
      EReal.toReal_log, toReal_add, toReal_mul, toReal_mul]
    · simp only [EReal.toReal_coe_ennreal]
      obtain ⟨_, conv⟩ := strictConcaveOn_log_Ioi.concaveOn
      simp only [smul_eq_mul] at conv
      refine conv (toReal_pos x₀ xₜ) (toReal_pos y₀ yₜ) toReal_nonneg toReal_nonneg ?_
      rw [← toReal_add aₜ bₜ]
      exact (toReal_eq_one_iff (a + b)).mpr hab
    · exact mul_ne_top aₜ xₜ
    · exact mul_ne_top bₜ yₜ
    · aesop
    · refine add_ne_top.mpr ⟨?_, ?_⟩
      · exact mul_ne_top aₜ xₜ
      · exact mul_ne_top bₜ yₜ
    · exact y₀
    · exact yₜ
    · exact x₀
    · exact xₜ
    · refine (EReal.mul_ne_top _ _).mpr ?_
      aesop
    · refine (EReal.mul_ne_bot _ _).mpr ?_
      aesop
    · refine (EReal.mul_ne_top _ _).mpr ?_
      aesop
    · refine (EReal.mul_ne_bot _ _).mpr ?_
      aesop
  · simp only [not_and_or] at h
    rcases h with x₀ | xₜ | y₀ | yₜ
    · push_neg at x₀
      by_cases a_eq₀ : a = 0
      · simp_all
      · push_neg at a_eq₀
        replace a₀ : 0 < a := pos_of_ne_zero a_eq₀
        rw [x₀, log_zero, EReal.mul_bot_of_pos <| EReal.coe_ennreal_pos.mpr a₀]
        simp
    · push_neg at xₜ
      by_cases a_eq₀ : a = 0
      · simp_all
      · push_neg at a_eq₀
        replace a₀ : 0 < a := pos_of_ne_zero a_eq₀
        rw [xₜ, log_top, EReal.mul_top_of_pos <| EReal.coe_ennreal_pos.mpr a₀]
        rw [ENNReal.mul_top a₀.ne']
        simp
    · push_neg at y₀
      by_cases b_eq₀ : b = 0
      · simp_all
      · push_neg at b_eq₀
        replace b₀ : 0 < b := pos_of_ne_zero b_eq₀
        rw [y₀, log_zero, EReal.mul_bot_of_pos <| EReal.coe_ennreal_pos.mpr b₀]
        simp
    · push_neg at yₜ
      by_cases b_eq₀ : b = 0
      · simp_all
      · push_neg at b_eq₀
        replace b₀ : 0 < b := pos_of_ne_zero b_eq₀
        rw [yₜ, log_top, EReal.mul_top_of_pos <| EReal.coe_ennreal_pos.mpr b₀]
        rw [ENNReal.mul_top b₀.ne']
        simp

lemma ConcaveOn_log : ConcaveOn ℝ≥0 univ log := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b a₀ b₀ hab
  obtain ⟨_, conv⟩ := ConcaveOn_log'
  exact conv hx hy (zero_le _) (zero_le _) <| (toNNReal_eq_one_iff _).mp hab
