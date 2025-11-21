/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Prod

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- The integral of an `EReal`-valued function with respect to a measure `μ`, defined as the
difference of two lower Lebesgue integrals. -/
noncomputable def eintegral (μ : Measure α) (f : α → EReal) : EReal :=
    ∫⁻ x, (f x).toENNReal ∂μ - ∫⁻ x, (-f x).toENNReal ∂μ

@[inherit_doc MeasureTheory.eintegral]
notation3 "∫ᵉ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => eintegral μ r

@[inherit_doc MeasureTheory.eintegral]
notation3 "∫ᵉ "(...)", "r:60:(scoped f => eintegral volume f) => r

@[inherit_doc MeasureTheory.eintegral]
notation3 "∫ᵉ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 =>
    eintegral (Measure.restrict μ s) r

@[inherit_doc MeasureTheory.eintegral]
notation3 "∫ᵉ "(...)" in "s", "r:60:(scoped f => eintegral (Measure.restrict volume s) f) => r

@[simp]
lemma eintegral_zero (μ : Measure α) : ∫ᵉ _, (0 : EReal) ∂μ = 0 := by simp [eintegral]

lemma eintegral_congr {f g : α → EReal} (h : ∀ x, f x = g x) :
    ∫ᵉ x, f x ∂μ = ∫ᵉ x, g x ∂μ := by
  simp_rw [h]

lemma eintegral_congr_ae {f g : α → EReal} (h : ∀ᵐ x ∂μ, f x = g x) :
    ∫ᵉ x, f x ∂μ = ∫ᵉ x, g x ∂μ := by
  simp_rw [eintegral]
  congr 2 <;> exact lintegral_congr_ae <| by filter_upwards [h] with x hx using by rw [hx]

lemma eintegral_of_nonneg {f : α → EReal} (hf : ∀ x, 0 ≤ f x) :
    ∫ᵉ x, f x ∂μ = ∫⁻ x, (f x).toENNReal ∂μ := by
  simp [eintegral, hf]

lemma eintegral_of_ae_nonneg {f : α → EReal} (hf : AEMeasurable f μ)
    (hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x) : ∫ᵉ x, f x ∂μ = ∫⁻ x, (f x).toENNReal ∂μ := by
  rw [eintegral]
  suffices ∫⁻ x, (-f x).toENNReal ∂μ = 0 by simp [this]
  rw [lintegral_eq_zero_iff']
  · filter_upwards [hf_nonneg] with x hx using by simp [hx]
  · fun_prop

lemma eintegral_of_nonpos {f : α → EReal} (hf : ∀ x, f x ≤ 0) :
    ∫ᵉ x, f x ∂μ = - ∫⁻ x, (-f x).toENNReal ∂μ := by
  simp [eintegral, hf]

lemma eintegral_of_ae_nonpos {f : α → EReal} (hf : AEMeasurable f μ)
    (hf_nonpos : ∀ᵐ x ∂μ, f x ≤ 0) : ∫ᵉ x, f x ∂μ = - ∫⁻ x, (-f x).toENNReal ∂μ := by
  rw [eintegral]
  suffices ∫⁻ x, (f x).toENNReal ∂μ = 0 by simp [this]
  rw [lintegral_eq_zero_iff']
  · filter_upwards [hf_nonpos] with x hx using by simp [hx]
  · fun_prop

@[simp]
lemma eintegral_const (c : EReal) (μ : Measure α) :
    ∫ᵉ _, c ∂μ = c * (μ Set.univ : EReal) := by
  rcases le_total 0 c with hc | hc
  · rw [eintegral_of_nonneg (fun _ ↦ hc)]
    simp only [lintegral_const, EReal.coe_ennreal_mul]
    rw [EReal.coe_toENNReal hc]
  · rw [eintegral_of_nonpos (fun _ ↦ hc)]
    simp only [lintegral_const, EReal.coe_ennreal_mul]
    rw [EReal.coe_toENNReal]
    · simp
    · exact EReal.neg_nonneg.mpr hc

lemma eintegral_mono_ae {f g : α → EReal} (hfg : f ≤ᵐ[μ] g) : ∫ᵉ x, f x ∂μ ≤ ∫ᵉ x, g x ∂μ := by
  refine EReal.sub_le_sub ?_ ?_
  · rw [EReal.coe_ennreal_le_coe_ennreal_iff]
    refine lintegral_mono_ae ?_
    filter_upwards [hfg] with x hfgx
    exact EReal.toENNReal_le_toENNReal hfgx
  · rw [EReal.coe_ennreal_le_coe_ennreal_iff]
    refine lintegral_mono_ae ?_
    filter_upwards [hfg] with x hfgx
    rw [← EReal.neg_le_neg_iff] at hfgx
    exact EReal.toENNReal_le_toENNReal hfgx

lemma eintegral_mono {f g : α → EReal} (hfg : f ≤ g) : ∫ᵉ x, f x ∂μ ≤ ∫ᵉ x, g x ∂μ :=
  eintegral_mono_ae <| ae_of_all _ hfg

lemma eintegral_mul_const {c : EReal} {f : α → EReal} :
    ∫ᵉ x, c * f x ∂μ = c * ∫ᵉ x, f x ∂μ := by
  sorry

lemma eintegral_add (μ : Measure α) (f g : α → EReal) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ := by
  sorry
  -- cut the space into four parts depending on the signs of `f` and `g`

lemma eintegral_sub (μ : Measure α) (f g : α → EReal) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  have h₁ : ∀ x, f x - g x = f x + (-g x) := fun _ ↦ rfl
  have h₂ : ∀ x, -g x = (-1 : EReal) * g x := fun _ ↦ (neg_one_mul _).symm
  simp_rw [h₁, h₂]
  rw [eintegral_add]
  congr 1
  rw [eintegral_mul_const]
  simp

lemma eintegral_prod {β : Type*} {mβ : MeasurableSpace β} {ν : Measure β} [SFinite ν]
    (f : α × β → EReal) (hf : AEMeasurable f (μ.prod ν)) :
    ∫ᵉ z, f z ∂(μ.prod ν) = ∫ᵉ x, ∫ᵉ y, f (x, y) ∂ν ∂μ := by
  sorry

lemma eintegral_prod_symm {β : Type*} {mβ : MeasurableSpace β} [SFinite μ]
    {ν : Measure β} [SFinite ν]
    (f : α × β → EReal) (hf : AEMeasurable f (μ.prod ν)) :
    ∫ᵉ z, f z ∂(μ.prod ν) = ∫ᵉ y, ∫ᵉ x, f (x, y) ∂μ ∂ν := by
  sorry

theorem eintegral_map {β : Type*} {mβ : MeasurableSpace β} {f : β → EReal} {g : α → β}
    (hf : Measurable f) (hg : Measurable g) : ∫ᵉ a, f a ∂μ.map g = ∫ᵉ a, f (g a) ∂μ := by
  simp only [eintegral]
  repeat rw [lintegral_map (by fun_prop) hg]

lemma eintegral_lintegral_toEReal {β : Type*} {mβ : MeasurableSpace β} {m : α → Measure β}
    {f : β → EReal} : ∫ᵉ a, (∫⁻ x, (f x).toENNReal ∂m a).toEReal ∂μ =
    ∫⁻ a, ∫⁻ x, (f x).toENNReal ∂m a ∂μ := by
  simp only [eintegral]
  simp only [EReal.toENNReal_coe]
  have : ∀ x, (-(∫⁻ (x : β), (f x).toENNReal ∂m x).toEReal).toENNReal = 0 := by
    intro x
    simp
  simp_rw [this]
  simp

theorem eintegral_bind {β : Type*} {mβ : MeasurableSpace β} {m : α → Measure β} {f : β → EReal}
    (hμ : AEMeasurable m μ) (hf : AEMeasurable f (μ.bind m)) :
    ∫ᵉ x, f x ∂μ.bind m = ∫ᵉ a, ∫ᵉ x, f x ∂m a ∂μ := by
  simp only [eintegral]
  rw [μ.lintegral_bind hμ (by fun_prop)]
  rw [μ.lintegral_bind hμ (by fun_prop)]
  sorry

lemma todo' (a b : EReal) {c d : EReal} (hc : c ≠ ⊥) (hd : d ≠ ⊥) :
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

lemma todo (a b c d : ℝ≥0∞) : (a : EReal) + b - (c + d) = (a - c) + (b - d) := by
  rw [todo' _ _ (by simp) (by simp)]

lemma eintegral_add_measure {ν : Measure α} (f : α → EReal) :
    ∫ᵉ x, f x ∂(μ + ν) = ∫ᵉ x, f x ∂μ + ∫ᵉ x, f x ∂ν := by
  simp only [eintegral, lintegral_add_measure, EReal.coe_ennreal_add]
  rw [todo]

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

lemma eintegral_smul_measure {c : ℝ≥0∞} (hc : c ≠ ∞) (f : α → EReal) :
    ∫ᵉ x, f x ∂(c • μ) = c * ∫ᵉ x, f x ∂μ := by
  simp only [eintegral, lintegral_smul_measure, smul_eq_mul, EReal.coe_ennreal_mul]
  rw [EReal.mul_sub_of_nonneg_of_ne_top _ (by simp [hc])]
  norm_cast
  exact zero_le'

@[simp]
lemma eintegral_dirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {x₀ : α} {f : α → EReal} :
    ∫ᵉ x, f x ∂(Measure.dirac x₀) = f x₀ := by
  simp only [eintegral, lintegral_dirac]
  rcases le_total (f x₀) 0 with (h | h) <;> simp [h]

end MeasureTheory
