/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # Lemmas about EReal
-/

open ENNReal

lemma EReal.le_of_toReal_le {a b : EReal} (h1 : a ≠ ⊤) (h2 : b ≠ ⊤) (h3 : a ≠ ⊥) (h4 : b ≠ ⊥)
    (h5 : b.toReal ≤ a.toReal) : b ≤ a := by
  lift a to ℝ using ⟨h1, h3⟩
  lift b to ℝ using ⟨h2, h4⟩
  exact EReal.coe_le_coe_iff.mpr h5

lemma EReal.toReal_log {x : ℝ≥0∞} (hx₀ : x ≠ 0) (hxₜ : x ≠ ⊤) :
    (log x).toReal = Real.log x.toReal := by
  simp_all [log]

lemma EReal.mul_add_ENNReal {a : ℝ≥0∞} {b c : EReal} (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c) :
    a * (b + c).toENNReal = a * b.toENNReal + a * c.toENNReal := by
  by_cases hₜ : b + c = ⊤
  · rw [hₜ]
    by_cases ha₀ : a = 0
    · simp [ha₀]
    · simp_all only [toENNReal_top, ne_eq, not_false_eq_true, mul_top]
      have : b = ⊤ ∨ c = ⊤ := by
        by_contra! h
        exact add_ne_top h.1 h.2 hₜ
      cases this with
      | inl hbₜ =>
        rw [hbₜ]
        simp_all
      | inr hcₜ =>
        rw [hcₜ]
        simp_all
  · push Not at hₜ
    rw [toENNReal_of_ne_top hₜ]
    suffices ENNReal.ofReal (b + c).toReal = b.toENNReal + c.toENNReal by
      rw [this]
      ring
    have hb_bot : b ≠ ⊥ := by
      rintro rfl
      simp_all
    have hc_bot : c ≠ ⊥ := by
      rintro rfl
      simp_all
    obtain ⟨hbₜ, hcₜ⟩ := (add_ne_top_iff_ne_top₂ hb_bot hc_bot).mp hₜ
    rw [EReal.toReal_add, toENNReal_of_ne_top hbₜ, toENNReal_of_ne_top hcₜ, ← ENNReal.ofReal_add]
    · exact toReal_nonneg hb₀
    · exact toReal_nonneg hc₀
    · exact hbₜ
    · exact hb_bot
    · exact hcₜ
    · exact hc_bot

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

lemma EReal.mul_sub_of_nonneg_of_ne_top {a b c : EReal} (ha : 0 ≤ a) (ha' : a ≠ ⊤) :
    a * (b - c) = a * b - a * c := by
  by_cases ha_zero : a = 0
  · simp [ha_zero]
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
  have ha_ne_bot : a ≠ ⊥ := fun h_eq ↦ by simp [h_eq] at ha
  lift a to ℝ using ⟨ha', ha_ne_bot⟩
  cases b <;> cases c
  · simp [EReal.mul_bot_of_pos ha_pos]
  · simp [EReal.mul_bot_of_pos ha_pos]
  · simp [EReal.mul_bot_of_pos ha_pos]
  · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true, EReal.sub_bot,
      EReal.mul_top_of_pos ha_pos, EReal.mul_bot_of_pos ha_pos]
    rw [EReal.sub_bot]
    rw [← EReal.coe_mul]
    exact EReal.coe_ne_bot _
  · norm_cast
    ring
  · simp [EReal.mul_bot_of_pos ha_pos, EReal.mul_top_of_pos ha_pos]
  · simp [EReal.mul_top_of_pos ha_pos, EReal.mul_bot_of_pos ha_pos]
  · simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true, EReal.top_sub,
      EReal.mul_top_of_pos ha_pos]
    rw [EReal.top_sub]
    rw [← EReal.coe_mul]
    exact EReal.coe_ne_top _
  · simp [EReal.mul_bot_of_pos ha_pos, EReal.mul_top_of_pos ha_pos]

lemma EReal.add_sub_add (a b : EReal) {c d : EReal} (hc : c ≠ ⊥) (hd : d ≠ ⊥) :
    a + b - (c + d) = (a - c) + (b - d) := by
  cases a <;> cases b <;> cases c <;> cases d
  -- 81 goals :)
  any_goals simp [hc, hd]
  any_goals simp at hc
  any_goals simp at hd
  · norm_cast
    ring
  · norm_cast
  · norm_cast
  · norm_cast

lemma EReal.mul_sub_of_eq_zero {a b c : EReal} (h : b = 0 ∨ c = 0) :
    a * (b - c) = a * b - a * c := by
  cases h with
  | inl hb => simp [hb]
  | inr hc => simp [hc]

lemma EReal.ne_bot_of_nonneg {a : EReal} (ha : 0 ≤ a) : a ≠ ⊥ := by
  intro h_false
  simp [h_false] at ha

lemma EReal.neg_div (a b : EReal) : - a / b = - (a / b) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, EReal.neg_mul]

@[simp]
lemma EReal.toENNReal_one : (1 : EReal).toENNReal = 1 := by
  have : (1 : EReal) = (1 : ℝ≥0∞) := rfl
  rw [this, EReal.toENNReal_coe]

lemma EReal.coe_ennreal_div {a b : ℝ≥0∞} (hb_zero : b ≠ 0) :
    ((a / b : ℝ≥0∞) : EReal) = (a : EReal) / (b : EReal) := by
  by_cases hb_top : b = ∞
  · simp [hb_top]
  by_cases ha_top : a = ∞
  · simp only [ha_top, EReal.coe_ennreal_top]
    rw [EReal.top_div_of_pos_ne_top, ENNReal.top_div_of_ne_top]
    · simp
    · exact hb_top
    · simpa [pos_iff_ne_zero] using hb_zero
    · simpa
  have ha : a = ENNReal.ofReal a.toReal := by rw [ENNReal.ofReal_toReal ha_top]
  have hb : b = ENNReal.ofReal b.toReal := by rw [ENNReal.ofReal_toReal hb_top]
  rw [ha, hb]
  rw [← ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hb_zero hb_top)]
  simp only [EReal.coe_ennreal_ofReal]
  rw [max_eq_left (by positivity), max_eq_left (by positivity), max_eq_left (by positivity),
    EReal.coe_div]

lemma EReal.coe_ennreal_inv {a : ℝ≥0∞} (ha : a ≠ 0) : ((a⁻¹ : ℝ≥0∞) : EReal) = (a : EReal)⁻¹ := by
  by_cases ha_top : a = ⊤
  · simp [ha_top]
  have ha_eq : a = ENNReal.ofReal a.toReal := by rw [ENNReal.ofReal_toReal ha_top]
  have ha_pos : 0 < a.toReal := ENNReal.toReal_pos ha ha_top
  rw [ha_eq, EReal.coe_ennreal_ofReal, ← ENNReal.ofReal_inv_of_pos ha_pos, EReal.coe_ennreal_ofReal]
  simp only [inv_nonneg, ENNReal.toReal_nonneg, sup_of_le_left]
  rw [EReal.coe_inv]

instance : MeasurableInv EReal where
  measurable_inv := by
    refine EReal.measurable_of_measurable_real ?_
    simp_rw [← EReal.coe_inv]
    change Measurable (Real.toEReal ∘ _)
    exact Measurable.comp measurable_coe_real_ereal (by fun_prop)

lemma EReal.sub_lt_sub_of_le_of_lt {x y z t : EReal} (h : x ≤ y) (h' : z < t)
  (hy_top : y ≠ ⊤) (hy_bot : y ≠ ⊥) : x - t < y - z := by
  refine sub_lt_of_lt_add' ?_
  rw [add_sub_assoc', add_comm, add_sub_assoc]
  by_cases hxy : x = y
  · rw [hxy]
    lift y to ℝ using ⟨hy_top, hy_bot⟩
    by_cases htz_top : t - z = ⊤
    · simp_all
    rw [← coe_toReal htz_top <| ne_bot_of_nonneg (sub_pos.mpr h').le]
    norm_cast
    refine lt_add_of_pos_right y ?_
    exact EReal.toReal_pos (sub_pos.mpr h') htz_top
  · rw [← add_zero x]
    refine add_lt_add ?_ ?_
    · grind
    · exact sub_pos.mpr h'

lemma EReal.top_sub_eq_top_or_bot {a : EReal} : ⊤ - a = ⊤ ∨ ⊤ - a = ⊥ := by
  cases a with
  | bot => simp
  | coe a => simp
  | top => simp

-- In newer versions of Mathlib
lemma EReal.sub_eq_bot {a b : EReal} : a - b = ⊥ ↔ a = ⊥ ∨ b = ⊤ := by
  cases a <;> cases b <;> simp_all
  norm_cast
  simp [-coe_sub]

lemma EReal.add_sub_add_comm {a b c d : EReal} (h1 : c ≠ ⊥ ∨ d ≠ ⊤) (h2 : c ≠ ⊤ ∨ d ≠ ⊥) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, EReal.neg_add h1 h2, sub_eq_add_neg]
  grind

lemma EReal.coe_ennreal_sub_toENNReal (a b : ℝ≥0∞) :
    ((a : EReal) - (b : EReal)).toENNReal = a - b := by
  cases a <;> cases b <;> aesop

lemma EReal.neg_coe_ennreal_sub_toENNReal {a b : ℝ≥0∞} (h : a ≠ ∞ ∨ b ≠ ∞) :
    (-((a : EReal) - (b : EReal))).toENNReal = b - a := by
  by_contra h_contra;
  rcases a with ( _ | a ) <;> rcases b with ( _ | b ) <;> norm_cast at *;
  · aesop;
  · refine h_contra ?_;
    convert EReal.coe_ennreal_sub_toENNReal _ _ using 1;
    congr! 1;
    exact EReal.coe_eq_coe_iff.mpr (by norm_num)
