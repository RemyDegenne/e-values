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

lemma EReal.mul_add_ENNReal {a : ℝ≥0∞} {b c : EReal} (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c) :
    a * (b + c).toENNReal = a * b.toENNReal + a * c.toENNReal := by
  by_cases hₜ : b + c = ⊤
  · rw [hₜ]
    by_cases ha₀ : a = 0
    · simp [ha₀]
    · simp_all only [toENNReal_top, ne_eq, not_false_eq_true, mul_top]
      have : b = ⊤ ∨ c = ⊤ := by
        by_contra h
        push_neg at h
        exact add_ne_top h.1 h.2 hₜ
      cases this with
      | inl hbₜ =>
        rw [hbₜ]
        simp_all
      | inr hcₜ =>
        rw [hcₜ]
        simp_all
  · push_neg at hₜ
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
