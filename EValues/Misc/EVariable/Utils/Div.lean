import Mathlib

open ENNReal

noncomputable def enn_div (a b : ℝ≥0∞) : ℝ≥0∞ :=
  if a = b then 1 else a / b

infixl:70 " /ₑ " => enn_div

@[simp]
lemma enn_div_eq_div {a b : ℝ≥0∞} (h : a ≠ b) : a /ₑ b = a / b := by
  simp [enn_div, h]

@[simp]
lemma enn_div_eq_div' {a b : ℝ≥0∞} (h : b ≠ a) : a /ₑ b = a / b := by
  simp [enn_div, h.symm]

@[simp]
lemma enn_inv_div (a b : ℝ≥0∞) : (a /ₑ b)⁻¹ = b /ₑ a := by
  by_cases ha : a = b
  · simp [ha, enn_div]
  simp only [enn_div_eq_div ha, enn_div_eq_div' ha]
  refine ENNReal.inv_div ?_ ?_
  all_goals
  by_contra h
  push_neg at h ha
  rw [h.1, h.2] at ha
  contradiction

@[simp]
lemma enn_div_eq_one {a b : ℝ≥0∞} : a /ₑ b = 1 ↔ a = b := by
  constructor
  · intro h
    by_contra hab
    push_neg at hab
    simp only [enn_div_eq_div hab] at h
    by_cases hb_zero : b = 0
    · rw [hb_zero] at h
      have : a ≠ 0 := by
        rwa [← hb_zero]
      have : a / 0 = ⊤ := ENNReal.div_zero this
      rw [this] at h
      contradiction
    · push_neg at hb_zero
      by_cases hb_top : b = ⊤
      · rw [hb_top, div_top] at h
        simp_all
      · push_neg at hb_top
        rw [ENNReal.div_eq_one_iff hb_zero hb_top] at h
        contradiction
  · intro h
    simp [h, enn_div]
