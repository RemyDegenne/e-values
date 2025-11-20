/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

open ENNReal

lemma EReal.le_of_toReal_le {a b : EReal} (h1 : a ≠ ⊤) (h2 : b ≠ ⊤) (h3 : a ≠ ⊥) (h4 : b ≠ ⊥)
    (h5 : b.toReal ≤ a.toReal) : b ≤ a := by
  lift a to ℝ using ⟨h1, h3⟩
  lift b to ℝ using ⟨h2, h4⟩
  exact EReal.coe_le_coe_iff.mpr h5

lemma EReal.toReal_log {x : ℝ≥0∞} (hx₀ : x ≠ 0) (hxₜ : x ≠ ⊤) :
    (log x).toReal = Real.log x.toReal := by
  simp_all [log]

lemma EReal.toReal_inv (r : EReal) : (r⁻¹).toReal = (r.toReal)⁻¹ := by
    cases r with
    | bot => simp
    | coe a => rw [← EReal.coe_inv, EReal.toReal_coe, EReal.toReal_coe]
    | top => simp

lemma EReal.inv_ne_top {r : EReal} : r⁻¹ ≠ ⊤ := by
    cases r with
    | bot => simp
    | coe a => rw [← EReal.coe_inv]; simp
    | top => simp

lemma EReal.toENNReal_inv {r : EReal} (hr : 0 < r) :
    (r⁻¹).toENNReal = (r.toENNReal)⁻¹ := by
    cases r with
    | bot => simp at hr
    | coe a =>
      simp only [EReal.toENNReal, EReal.coe_ne_top, ↓reduceIte, EReal.toReal_coe]
      rw [if_neg EReal.inv_ne_top, EReal.toReal_inv, ENNReal.ofReal_inv_of_pos, EReal.toReal_coe]
      simpa using hr
    | top => simp

lemma EReal.iSup_coe_mul_of_nonneg {α : Type*} [Nonempty α] {f : α → EReal} {a : ℝ} (ha : 0 ≤ a) :
    a * (⨆ x, f x) = ⨆ x, a * f x := by
  by_cases ha' : a = 0
  · simp [ha']
  refine le_antisymm ?_ ?_
  · calc a * ⨆ x, f x
    _ ≤ a * (a⁻¹ * ⨆ x, a * f x) := by
      gcongr
      simp only [iSup_le_iff]
      intro x
      suffices a * f x ≤ ⨆ x, a * f x by
        calc f x
        _ = a⁻¹ * (a * f x) := by rw [← mul_assoc]; norm_cast; rw [inv_mul_cancel₀ ha']; simp
        _ ≤ a⁻¹ * ⨆ x, a * f x := by gcongr
      exact le_iSup (fun x ↦ a * f x) x
    _ = ⨆ x, a * f x := by rw [← mul_assoc]; norm_cast; rw [mul_inv_cancel₀ ha']; simp
  · simp only [iSup_le_iff]
    intro x
    gcongr
    exact le_iSup f x

lemma EReal.iSup_ennreal_mul {α : Type*} [Nonempty α] {f : α → EReal} {a : ℝ≥0∞} (ha : a ≠ ∞) :
    a * (⨆ x, f x) = ⨆ x, a * f x := by
  by_cases ha' : a = 0
  · simp [ha']
  refine le_antisymm ?_ ?_
  · calc a * ⨆ x, f x
    _ ≤ a * (a⁻¹ * ⨆ x, a * f x) := by
      gcongr
      simp only [iSup_le_iff]
      intro x
      suffices a * f x ≤ ⨆ x, a * f x by
        calc f x
        _ = a⁻¹ * (a * f x) := by
          rw [← mul_assoc]; norm_cast; rw [ENNReal.inv_mul_cancel ha' ha]; simp
        _ ≤ a⁻¹ * ⨆ x, a * f x := by gcongr
      exact le_iSup (fun x ↦ a * f x) x
    _ = ⨆ x, a * f x := by rw [← mul_assoc]; norm_cast; rw [ENNReal.mul_inv_cancel ha' ha]; simp
  · simp only [iSup_le_iff]
    intro x
    gcongr
    exact le_iSup f x

lemma EReal.inv_coe_ennreal {x : ℝ≥0∞} (hx : x ≠ 0) :
    (x : EReal)⁻¹ = (x⁻¹ : ℝ≥0∞) := by
  by_cases hx_top : x = ⊤
  · simp [hx_top]
  have hx_eq : x = ENNReal.ofReal x.toReal := by rw [ENNReal.ofReal_toReal hx_top]
  rw [hx_eq]
  simp only [EReal.coe_ennreal_ofReal, ENNReal.toReal_nonneg, sup_of_le_left]
  rw [← ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hx hx_top)]
  simp only [EReal.coe_ennreal_ofReal, inv_nonneg, ENNReal.toReal_nonneg, sup_of_le_left]
  rw [EReal.coe_inv]
