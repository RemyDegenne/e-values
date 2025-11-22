/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Prod
import EValues.Mathlib.EReal

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

/-- Condition for a function to have a well-defined extended integral,
avoiding the `⊤ - ⊤` bad case in the definition. -/
def eintegrable (f : α → EReal) (μ : Measure α := by volume_tac) : Prop :=
  ∫⁻ x, (f x).toENNReal ∂μ ≠ ⊤ ∨ ∫⁻ x, (-f x).toENNReal ∂μ ≠ ⊤

-- if the integral of `f` gives `⊤ - ⊤ = ⊥`, then `-f` also gives `⊤ - ⊤ = ⊥`, so the integral
-- of `-f` is not the negation of the integral of `f`

@[simp]
lemma eintegral_of_not_eintegrable {f : α → EReal} (hf : ¬ eintegrable f μ) :
    ∫ᵉ x, f x ∂μ = ⊥ := by
  simp only [eintegrable, ne_eq, not_or, Decidable.not_not] at hf
  simp [eintegral, hf]

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

lemma eintegral_nonneg {f : α → EReal} (hf : ∀ x, 0 ≤ f x) : 0 ≤ ∫ᵉ x, f x ∂μ := by
  rw [eintegral_of_nonneg hf]
  positivity

lemma eintegral_nonpos {f : α → EReal} (hf : ∀ x, f x ≤ 0) : ∫ᵉ x, f x ∂μ ≤ 0 := by
  rw [eintegral_of_nonpos hf]
  simp only [EReal.neg_le_zero]
  positivity

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

lemma todo_add (f : α → EReal) :
    ∃ f₁ f₂ : α → EReal, (∀ x, 0 ≤ f₁ x) ∧ (∀ x, 0 ≤ f₂ x) ∧ (∀ x, f x = f₁ x - f₂ x) ∧
      (∀ x, f₁ x = 0 ∨ f₂ x = 0) := by
  refine ⟨fun x ↦ max (f x) 0, fun x ↦ - min (f x) 0, fun _ ↦ by positivity, fun _ ↦ by simp,
    fun x ↦ ?_, fun x ↦ ?_⟩
  · rcases le_total 0 (f x) with h | h <;> simp [h]
  · rcases le_total 0 (f x) with h | h <;> simp [h]

lemma eintegral_sub_of_nonneg_of_eq_zero {f g : α → EReal} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (h_or : ∀ x, f x = 0 ∨ g x = 0) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  simp_rw [eintegral_of_nonneg hf, eintegral_of_nonneg hg, eintegral]
  congr with x
  · cases h_or x with
  | inl h =>
    simp only [h, zero_sub, ne_eq, EReal.zero_ne_top, not_false_eq_true,
      EReal.toENNReal_of_ne_top, EReal.toReal_zero, ENNReal.ofReal_zero]
    rw [EReal.toENNReal_of_nonpos]
    simp [hg x]
  | inr h => simp [h]
  · by_cases hg_top : g x = ⊤
    · simp [hg_top]
    rw [EReal.neg_sub]
    · cases h_or x with
      | inl h =>  simp [h]
      | inr h =>
        simp only [h, add_zero, ne_eq, EReal.zero_ne_top, not_false_eq_true,
          EReal.toENNReal_of_ne_top, EReal.toReal_zero, ENNReal.ofReal_zero]
        rw [EReal.toENNReal_of_nonpos]
        simp [hf x]
    · left
      specialize hf x
      intro h_false
      simp [h_false] at hf
    · exact .inr hg_top

lemma eintegral_mul_const_of_nonneg {c : EReal} (hc_bot : c ≠ ⊥) (hc_top : c ≠ ⊤)
    {f : α → EReal} (hf : ∀ x, 0 ≤ f x) :
    ∫ᵉ x, c * f x ∂μ = c * ∫ᵉ x, f x ∂μ := by
  lift c to ℝ using ⟨hc_top, hc_bot⟩ with c
  rcases le_total 0 c with hc | hc
  · have hc' : 0 ≤ (c : EReal) := mod_cast hc
    rw [eintegral_of_nonneg (fun x ↦ mul_nonneg hc' (hf x)), eintegral_of_nonneg hf]
    simp_rw [EReal.toENNReal_mul hc']
    simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true, EReal.toENNReal_of_ne_top,
      EReal.toReal_coe]
    rw [lintegral_const_mul' _ _ (by simp)]
    simp [hc]
  · have hc' : (c : EReal) ≤ 0 := mod_cast hc
    rw [eintegral_of_nonpos, eintegral_of_nonneg hf]
    swap; · exact fun x ↦ EReal.mul_nonpos_iff.mpr <| by simp [hc, hf]
    have : 0 ≤ - (c : EReal) := by simp [hc']
    simp_rw [← EReal.neg_mul, EReal.toENNReal_mul this]
    simp only [ne_eq, EReal.neg_eq_top_iff, EReal.coe_ne_bot, not_false_eq_true,
      EReal.toENNReal_of_ne_top, EReal.toReal_neg, EReal.toReal_coe]
    rw [lintegral_const_mul' _ _ (by simp)]
    simp [hc]

lemma eintegral_mul_const {c : EReal} (hc_bot : c ≠ ⊥) (hc_top : c ≠ ⊤) {f : α → EReal}
    (hf : eintegrable f μ) :
    ∫ᵉ x, c * f x ∂μ = c * ∫ᵉ x, f x ∂μ := by
  lift c to ℝ using ⟨hc_top, hc_bot⟩ with c
  let f₁ := fun x ↦ max (f x) 0
  let f₂ := fun x ↦ - min (f x) 0
  have hf₁ x : 0 ≤ f₁ x := by simp [f₁]
  have hf₂ x : 0 ≤ f₂ x := by simp [f₂]
  have h_or x : f₁ x = 0 ∨ f₂ x = 0 := by
    rcases le_total 0 (f x) with h | h <;> simp [f₁, f₂, h]
  have h_eq x : f x = f₁ x - f₂ x := by
    rcases le_total 0 (f x) with h | h <;> simp [f₁, f₂, h]
  have h_int_or : ∫ᵉ x, f₁ x ∂μ ≠ ⊤ ∨ ∫ᵉ x, f₂ x ∂μ ≠ ⊤ := by
    unfold eintegrable at hf
    rcases hf with h | h
    · left
      rw [eintegral_of_nonneg hf₁]
      simp only [ne_eq, EReal.coe_ennreal_eq_top_iff, f₁]
      convert h using 4 with x
      rcases le_total 0 (f x) with h | h <;> simp [h]
    · right
      rw [eintegral_of_nonneg hf₂]
      simp only [ne_eq, EReal.coe_ennreal_eq_top_iff, f₂]
      convert h using 4 with x
      rcases le_total 0 (f x) with h | h <;> simp [h]
  simp_rw [h_eq]
  rw [eintegral_sub_of_nonneg_of_eq_zero hf₁ hf₂ h_or]
  simp_rw [EReal.mul_sub_of_eq_zero (h_or _)]
  rcases le_total 0 c with hc | hc
  · have hc' : 0 ≤ (c : EReal) := mod_cast hc
    rw [eintegral_sub_of_nonneg_of_eq_zero, eintegral_mul_const_of_nonneg (by simp) (by simp) hf₁,
      eintegral_mul_const_of_nonneg (by simp) (by simp) hf₂]
    · rw [EReal.mul_sub_of_nonneg_of_ne_top hc' hc_top]
    · intro x
      positivity
    · intro x
      specialize hf₂ x
      positivity
    · intro x
      rcases h_or x with h | h <;> simp [h]
  · have hc' : (c : EReal) ≤ 0 := mod_cast hc
    have h_sub x : c * f₁ x - c * f₂ x = (-c) * f₂ x - (-c) * f₁ x := by
      rw [EReal.neg_mul, EReal.neg_mul, sub_eq_add_neg, sub_eq_add_neg, add_comm, neg_neg]
    simp_rw [h_sub]
    rw [eintegral_sub_of_nonneg_of_eq_zero, eintegral_mul_const_of_nonneg (by simp) (by simp) hf₂,
      eintegral_mul_const_of_nonneg (by simp) (by simp) hf₁]
    · conv_rhs => rw [← neg_neg (c : EReal), neg_mul]
      rw [EReal.mul_sub_of_nonneg_of_ne_top (by simp [hc]) (by simp)]
      suffices ∀ (a b : EReal), 0 ≤ a → 0 ≤ b → (a ≠ ⊤ ∨ b ≠ ⊤) →
          -c * b - -c * a = -(-c * a - -c * b) from
        this _ _ (eintegral_nonneg hf₁) (eintegral_nonneg hf₂) h_int_or
      rcases eq_or_lt_of_le hc with rfl | hc
      · simp
      intro a b ha hb h_or
      cases a <;> cases b
      · simp at ha
      · simp at ha
      · simp at ha
      · simp at hb
      · rw [EReal.neg_sub, sub_eq_add_neg, neg_mul, neg_mul, neg_neg, add_comm]
        · left
          rw [neg_mul, ← EReal.coe_mul]
          simp only [ne_eq, EReal.neg_eq_bot_iff]
          exact EReal.coe_ne_top _
        · left
          rw [neg_mul, ← EReal.coe_mul]
          exact EReal.coe_ne_top _
      · rw [EReal.mul_top_of_pos (by simp [hc]), EReal.top_sub, EReal.sub_top, EReal.neg_bot]
        rw [neg_mul, ← EReal.coe_mul]
        simp only [EReal.coe_mul, ne_eq, EReal.neg_eq_top_iff]
        exact EReal.coe_ne_bot _
      · simp at hb
      · rw [EReal.mul_top_of_pos (by simp [hc]), EReal.sub_top, EReal.top_sub, EReal.neg_top]
        rw [neg_mul, ← EReal.coe_mul]
        exact EReal.coe_ne_top _
      · simp at h_or
    · intro x
      rw [EReal.mul_nonneg_iff]
      simp [hc, hf₂ x]
    · intro x
      rw [EReal.mul_nonneg_iff]
      simp [hc, hf₁ x]
    · intro x
      rcases h_or x with h | h <;> simp [h]

lemma eintegral_neg (μ : Measure α) (f : α → EReal) (hf : eintegrable f μ) :
    ∫ᵉ x, -f x ∂μ = - ∫ᵉ x, f x ∂μ := by
  have h₁ : ∀ x, -f x = (-1 : EReal) * f x := fun _ ↦ (neg_one_mul _).symm
  simp_rw [h₁]
  rw [eintegral_mul_const (by norm_cast) (by norm_cast) hf]
  simp

lemma eintegral_add (μ : Measure α) (f g : α → EReal) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ := by
  sorry
  -- cut the space into four parts depending on the signs of `f` and `g`

lemma eintegral_sub (μ : Measure α) (f g : α → EReal) (hg : eintegrable g μ) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  simp_rw [sub_eq_add_neg]
  rw [eintegral_add, eintegral_neg μ g hg]

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

lemma eintegral_add_measure {ν : Measure α} (f : α → EReal) :
    ∫ᵉ x, f x ∂(μ + ν) = ∫ᵉ x, f x ∂μ + ∫ᵉ x, f x ∂ν := by
  simp only [eintegral, lintegral_add_measure, EReal.coe_ennreal_add]
  rw [EReal.add_sub_add _ _ (by simp) (by simp)]

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
