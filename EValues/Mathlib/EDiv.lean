/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.Data.ENNReal.Inv

open ENNReal

/-- Equality-normalized division that associates `1` when the numerator and denominator are equal.
Otherwise, it behaves like regular division.
TODO Not sure about the `DecidableEq α` instance instead of `open Classical`. -/
noncomputable
def ediv {α : Type*} [One α] [HDiv α α α] [DecidableEq α] (a b : α) : α :=
    if a = b then 1 else a / b

/-- Equality-normalized division that associates `1` when the numerator and denominator are equal.
Otherwise, it behaves like regular division. -/
infixl:70 " /ₑ " => ediv

/-- Point-wise equality-normalized division of functions. -/
noncomputable
abbrev fun_ediv {α β : Type*} [One α] [HDiv α α α] [DecidableEq α] (f g : β → α) : β → α :=
    fun x ↦ f x /ₑ g x

/-- Point-wise equality-normalized division of functions. -/
infixl:70 " /ₑ " => fun_ediv

variable {α : Type*} [DecidableEq α]

@[simp]
lemma ediv_eq_div [HDiv α α α] [One α] {a b : α} (h : a ≠ b) : a /ₑ b = a / b := by
  simp [ediv, h]

@[simp]
lemma ediv_eq_div' [HDiv α α α] [One α] {a b : α} (h : b ≠ a) : a /ₑ b = a / b :=
    ediv_eq_div h.symm

@[simp]
lemma inv_ediv [DivisionMonoid α] (a b : α) : (a /ₑ b)⁻¹ = b /ₑ a := by
  by_cases ha : a = b
  · simp [ediv, ha]
  rw [ediv_eq_div ha, ediv_eq_div' ha]
  exact inv_div a b

lemma one_ediv [DivisionMonoid α] (a : α) : 1 /ₑ a = a⁻¹ := by
  by_cases ha : a = 1
  · simp [ediv, ha]
  · push_neg at ha
    rw [ediv_eq_div' ha]
    exact one_div a

lemma ediv_eq_one_iff_eq [GroupWithZero α] {a b : α} : a /ₑ b = 1 ↔ a = b := by
  by_cases hab : a = b
  · simp [hab, ediv]
  · push_neg at hab
    rw [ediv_eq_div hab]
    by_cases b₀ : b ≠ 0
    · exact div_eq_one_iff_eq b₀
    · push_neg at b₀
      rw [b₀] at hab ⊢
      exact ⟨fun h ↦ by simp_all, fun _ ↦ by contradiction⟩

lemma inv_ediv_enn (a b : ℝ≥0∞) : (a /ₑ b)⁻¹ = b /ₑ a := by
  by_cases ha : a = b
  · simp [ha, ediv]
  rw[ediv_eq_div ha, ediv_eq_div' ha]
  refine ENNReal.inv_div ?_ ?_
  all_goals
  by_contra h
  push_neg at h ha
  rw [h.1, h.2] at ha
  contradiction

lemma ediv_eq_one_iff_eq_enn (a b : ℝ≥0∞) : a /ₑ b = 1 ↔ a = b := by
  by_cases hab : a = b
  · simp [hab, ediv]
  · push_neg at hab
    rw [ediv_eq_div hab]
    by_cases b₀ : b = 0
    · have a₀ : a ≠ 0 := by
        rwa [← b₀]
      rw [b₀, ENNReal.div_zero a₀]
      constructor
      all_goals intro _; contradiction
    · push_neg at b₀
      by_cases bₜ : b = ⊤
      · rw [bₜ, div_top]
        simp_all
      · push_neg at bₜ
        rw [ENNReal.div_eq_one_iff b₀ bₜ]
