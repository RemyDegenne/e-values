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
