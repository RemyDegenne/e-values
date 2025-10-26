/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.Data.ENNReal.Inv

open ENNReal

lemma ENNReal.le_antisymm_iff_toReal {a b : ℝ≥0∞} (h1 : b ≤ a) (h2 : a ≤ b) : a = b := by
  by_cases aₜ : a = ⊤
  · rw [aₜ] at h1 h2 ⊢
    simp_all
  · push_neg at aₜ
    have bₜ : b ≠ ⊤ := ne_top_of_le_ne_top aₜ h1
    refine (toReal_eq_toReal_iff' aₜ bₜ).mp ?_
    rw [← toReal_le_toReal bₜ aₜ] at h1
    rw [← toReal_le_toReal aₜ bₜ] at h2
    linarith

lemma ENNReal.lt_and_le_false {a b : ℝ≥0∞} (h1 : b < a) (h2 : a ≤ b) : False := by
  by_cases aₜ : a = ⊤
  · rw [aₜ] at h1 h2
    rw [top_le_iff] at h2
    have : b ≠ ⊤ := LT.lt.ne_top h1
    contradiction
  · push_neg at aₜ
    have bₜ : b ≠ ⊤ := LT.lt.ne_top h1
    rw [← toReal_lt_toReal bₜ aₜ] at h1
    rw [← toReal_le_toReal aₜ bₜ] at h2
    linarith

lemma ENNReal.div_eq_one_imp_eq {a b : ℝ≥0∞} (h : a / b = 1) : a = b := by
  by_cases hb : b ≠ 0 ∧ b ≠ ⊤
  · rcases hb with ⟨b₀, bₜ⟩
    rwa [← ENNReal.div_eq_one_iff b₀ bₜ]
  · simp only [not_and_or] at hb
    rcases hb with b₀ | bₜ
    · push_neg at b₀
      by_cases a₀ : a = 0
      · rw [a₀, b₀]
      · push_neg at a₀
        rw [b₀, ENNReal.div_zero a₀] at h
        contradiction
    · push_neg at bₜ
      rw [bₜ] at h
      simp_all
