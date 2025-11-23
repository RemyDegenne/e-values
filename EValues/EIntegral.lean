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

lemma eintegrable_of_nonneg {f : α → EReal} (hf : ∀ x, 0 ≤ f x) : eintegrable f μ :=
  Or.inr <| by simp [hf]

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

lemma eintegral_nonneg' {f : α → EReal} (hf_meas : AEMeasurable f μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    0 ≤ ∫ᵉ x, f x ∂μ := by
  rw [eintegral_of_ae_nonneg hf_meas hf]
  positivity

lemma eintegral_nonpos {f : α → EReal} (hf : ∀ x, f x ≤ 0) : ∫ᵉ x, f x ∂μ ≤ 0 := by
  rw [eintegral_of_nonpos hf]
  simp only [EReal.neg_le_zero]
  positivity

lemma eintegral_nonpos' {f : α → EReal} (hf_meas : AEMeasurable f μ) (hf : ∀ᵐ x ∂μ, f x ≤ 0) :
    ∫ᵉ x, f x ∂μ ≤ 0 := by
  rw [eintegral_of_ae_nonpos hf_meas hf]
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

lemma ae_ne_bot_of_eintegral_ne_bot {f : α → EReal}
    (hf_meas : AEMeasurable f μ) (hf : ∫ᵉ x, f x ∂μ ≠ ⊥) :
    ∀ᵐ x ∂μ, f x ≠ ⊥ := by
  rw [eintegral, sub_eq_add_neg, ne_eq, EReal.add_eq_bot_iff] at hf
  simp only [EReal.coe_ennreal_ne_bot, EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff,
    false_or] at hf
  have h := ae_lt_top' (by fun_prop) hf
  filter_upwards [h] with x hx
  rw [lt_top_iff_ne_top, ne_eq, EReal.toENNReal_eq_top_iff] at hx
  simpa using hx

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
      | inl h => simp [h]
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

lemma eintegral_sub_of_nonneg_of_eq_zero' {f g : α → EReal}
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hg : ∀ᵐ x ∂μ, 0 ≤ g x)
    (h_or : ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  let f' := fun x ↦ if (0 ≤ f x ∧ 0 ≤ g x ∧ (f x = 0 ∨ g x = 0)) then f x else 0
  let g' := fun x ↦ if (0 ≤ f x ∧ 0 ≤ g x ∧ (f x = 0 ∨ g x = 0)) then g x else 0
  have hf' x : 0 ≤ f' x := by simp only [f']; split_ifs with h <;> simp [h]
  have hg' x : 0 ≤ g' x := by simp only [g']; split_ifs with h <;> simp [h]
  have h_or' x : f' x = 0 ∨ g' x = 0 := by
    simp only [f', g']; split_ifs with h <;> simp [h]
  have hf_eq : ∀ᵐ x ∂μ, f x = f' x := by
    filter_upwards [hf, hg, h_or] with x hf_x hg_x h_or_x
    simp [f', hf_x, hg_x, h_or_x]
  have hg_eq : ∀ᵐ x ∂μ, g x = g' x := by
    filter_upwards [hf, hg, h_or] with x hf_x hg_x h_or_x
    simp [g', hf_x, hg_x, h_or_x]
  have hf_sub_g : ∀ᵐ x ∂μ, f x - g x = f' x - g' x := by
    filter_upwards [hf_eq, hg_eq] with x hfx hgx
    rw [hfx, hgx]
  rw [eintegral_congr_ae hf_eq, eintegral_congr_ae hg_eq, eintegral_congr_ae hf_sub_g,
    eintegral_sub_of_nonneg_of_eq_zero hf' hg' h_or']

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

lemma eintegral_add_of_nonneg (μ : Measure α) {f g : α → EReal} (hf_meas : AEMeasurable f μ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ := by
  rw [eintegral_of_nonneg (fun x ↦ add_nonneg (hf x) (hg x)),
    eintegral_of_nonneg hf, eintegral_of_nonneg hg, ← EReal.coe_ennreal_add,
    ← lintegral_add_left' (by fun_prop)]
  simp_rw [EReal.toENNReal_add (hf _) (hg _)]

lemma eintegral_add_of_nonneg_of_measurable' (μ : Measure α) {f g : α → EReal}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hg : ∀ᵐ x ∂μ, 0 ≤ g x) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ := by
  let f' := fun x ↦ if (0 ≤ f x ∧ 0 ≤ g x) then f x else 0
  let g' := fun x ↦ if (0 ≤ f x ∧ 0 ≤ g x) then g x else 0
  have hf' x : 0 ≤ f' x := by simp only [f']; split_ifs with h <;> simp [h]
  have hg' x : 0 ≤ g' x := by simp only [g']; split_ifs with h <;> simp [h]
  have hf_eq : ∀ᵐ x ∂μ, f x = f' x := by
    filter_upwards [hf, hg] with x hf_x hg_x using by simp [f', hf_x, hg_x]
  have hg_eq : ∀ᵐ x ∂μ, g x = g' x := by
    filter_upwards [hf, hg] with x hf_x hg_x using by simp [g', hf_x, hg_x]
  have hf_add_g : ∀ᵐ x ∂μ, f x + g x = f' x + g' x := by
    filter_upwards [hf_eq, hg_eq] with x hfx hgx
    rw [hfx, hgx]
  rw [eintegral_congr_ae hf_eq, eintegral_congr_ae hg_eq, eintegral_congr_ae hf_add_g,
    eintegral_add_of_nonneg _ _ hf' hg']
  refine (Measurable.ite ?_ hf_meas measurable_const).aemeasurable
  exact MeasurableSet.inter (measurableSet_le measurable_const hf_meas)
    (measurableSet_le measurable_const hg_meas)

lemma eintegral_add_of_nonneg' {f g : α → EReal}
    (hf_meas : AEMeasurable f μ) (hg_meas : AEMeasurable g μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hg : ∀ᵐ x ∂μ, 0 ≤ g x) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ := by
  rw [eintegral_congr_ae hf_meas.ae_eq_mk, eintegral_congr_ae hg_meas.ae_eq_mk,
    ← eintegral_add_of_nonneg_of_measurable']
  · refine eintegral_congr_ae ?_
    filter_upwards [hf_meas.ae_eq_mk, hg_meas.ae_eq_mk] with x hfx hgx
    rw [hfx, hgx]
  · exact hf_meas.measurable_mk
  · exact hg_meas.measurable_mk
  · filter_upwards [hf_meas.ae_eq_mk, hf] with x hfx hfx_nonneg
    rwa [← hfx]
  · filter_upwards [hg_meas.ae_eq_mk, hg] with x hgx hgx_nonneg
    rwa [← hgx]

lemma EReal.ne_bot_of_nonneg {a : EReal} (ha : 0 ≤ a) : a ≠ ⊥ := by
  intro h_false
  simp [h_false] at ha

lemma eintegral_sub_of_nonneg {f g : α → EReal} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hf_meas : AEMeasurable f μ) (hg_meas : AEMeasurable g μ)
    (hfg : ∫ᵉ x, min (f x) (g x) ∂μ ≠ ⊤) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  have hf_ne_bot x : f x ≠ ⊥ := by
    intro h_false
    specialize hf x
    simp [h_false] at hf
  have hg_ne_bot x : g x ≠ ⊥ := by
    intro h_false
    specialize hg x
    simp [h_false] at hg
  by_cases hg_top : ∀ᵐ x ∂μ, g x ≠ ⊤
  swap
  · -- right side is bot
    have h_imp : ∫ᵉ x, -g x ∂μ ≠ ⊥ → ∀ᵐ x ∂μ, -g x ≠ ⊥ := ae_ne_bot_of_eintegral_ne_bot hg_meas.neg
    rw [← not_imp_not] at h_imp
    simp only [ne_eq, EReal.neg_eq_bot_iff, Decidable.not_not] at h_imp
    specialize h_imp hg_top
    rw [eintegral_neg] at h_imp
    swap; · exact eintegrable_of_nonneg hg
    rw [sub_eq_add_neg, h_imp, EReal.add_bot]
    -- left side is also bot
    have h_imp' : ∫ᵉ x, f x - g x ∂μ ≠ ⊥ → ∀ᵐ x ∂μ, f x - g x ≠ ⊥ :=
      ae_ne_bot_of_eintegral_ne_bot (hf_meas.sub hg_meas)
    rw [← not_imp_not] at h_imp'
    simp only [ne_eq, Filter.not_eventually, Decidable.not_not] at h_imp'
    refine h_imp' ?_
    simp only [ne_eq, Filter.not_eventually, Decidable.not_not] at hg_top
    exact hg_top.mono fun x hx ↦ by simp [hx]
  let f' := fun x ↦ f x - min (f x) (g x)
  let g' := fun x ↦ g x - min (f x) (g x)
  have hf' : ∀ᵐ x ∂μ, 0 ≤ f' x := by
    filter_upwards [hg_top] with x hgx
    unfold f'
    rw [EReal.sub_nonneg (by simp [hgx]) (by simp [hf_ne_bot])]
    simp
  have hg' : ∀ᵐ x ∂μ, 0 ≤ g' x := by
    filter_upwards [hg_top] with x hgx
    unfold g'
    rw [EReal.sub_nonneg (by simp [hgx]) (by simp [hg_ne_bot])]
    simp
  have hf_eq : ∀ᵐ x ∂μ, f x = f' x + min (f x) (g x) := by
    unfold f'
    filter_upwards [hg_top] with x hgx
    rcases le_total (f x) (g x) with h | h
    · simp only [h, inf_of_le_left]
      rw [EReal.sub_self (ne_top_of_le_ne_top hgx h) (hf_ne_bot x), zero_add]
    · simp only [h, inf_of_le_right]
      lift g x to ℝ using ⟨hgx, hg_ne_bot x⟩ with gx
      rw [EReal.sub_add_cancel]
  have hg_eq : ∀ᵐ x ∂μ, g x = g' x + min (f x) (g x) := by
    unfold g'
    filter_upwards [hg_top] with x hgx
    rcases le_total (f x) (g x) with h | h
    · simp only [h, inf_of_le_left]
      lift f x to ℝ using ⟨ne_top_of_le_ne_top hgx h, hf_ne_bot x⟩ with gx
      rw [EReal.sub_add_cancel]
    · simp only [h, inf_of_le_right]
      rw [EReal.sub_self hgx (hg_ne_bot x), zero_add]
  have h_or : ∀ᵐ x ∂μ, f' x = 0 ∨ g' x = 0 := by
    filter_upwards [hg_top] with x hgx
    unfold f' g'
    rcases le_total (f x) (g x) with h | h
    · left
      simp only [h, inf_of_le_left]
      rw [EReal.sub_self]
      · exact ne_top_of_le_ne_top hgx h
      · exact hf_ne_bot x
    · right
      simp only [h, inf_of_le_right]
      rw [EReal.sub_self hgx (hg_ne_bot x)]
  have hf_sub_g : ∀ᵐ x ∂μ, f x - g x = f' x - g' x := by
    filter_upwards [hg_top] with x hgx
    unfold f' g'
    rcases le_total (f x) (g x) with h | h
    · simp only [h, inf_of_le_left]
      rw [EReal.sub_self]
      · rw [zero_sub]
        rw [EReal.neg_sub]
        · rw [add_comm, ← sub_eq_add_neg]
        · simp [hf_ne_bot x]
        · simp [hgx]
      · exact ne_top_of_le_ne_top hgx h
      · exact hf_ne_bot x
    · simp [h, inf_of_le_right, EReal.sub_self hgx (hg_ne_bot x)]
  rw [eintegral_congr_ae hf_sub_g, eintegral_congr_ae hf_eq, eintegral_congr_ae hg_eq,
    eintegral_sub_of_nonneg_of_eq_zero' hf' hg' h_or,
    eintegral_add_of_nonneg' (by fun_prop) (by fun_prop) hg',
    eintegral_add_of_nonneg' (by fun_prop) (by fun_prop) hf']
  rotate_left
  · filter_upwards [] with x using by simp [hf, hg]
  · filter_upwards [] with x using by simp [hf, hg]
  rw [EReal.add_sub_add]
  rotate_left
  · refine EReal.ne_bot_of_nonneg <| eintegral_nonneg' ?_ hg'
    simp only [g']; fun_prop
  · exact EReal.ne_bot_of_nonneg <| eintegral_nonneg (by simp [hf, hg])
  rw [EReal.sub_self hfg]
  · simp
  · exact EReal.ne_bot_of_nonneg <| eintegral_nonneg (by simp [hf, hg])

lemma eintegral_add (μ : Measure α) (f g : α → EReal)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ := by
  let f₁ := fun x ↦ max (f x) 0
  let f₂ := fun x ↦ - min (f x) 0
  have hf₁ x : 0 ≤ f₁ x := by simp [f₁]
  have hf₂ x : 0 ≤ f₂ x := by simp [f₂]
  have hf_or x : f₁ x = 0 ∨ f₂ x = 0 := by
    rcases le_total 0 (f x) with h | h <;> simp [f₁, f₂, h]
  have hf_eq x : f x = f₁ x - f₂ x := by
    rcases le_total 0 (f x) with h | h <;> simp [f₁, f₂, h]
  let g₁ := fun x ↦ max (g x) 0
  let g₂ := fun x ↦ - min (g x) 0
  have hg₁ x : 0 ≤ g₁ x := by simp [g₁]
  have hg₂ x : 0 ≤ g₂ x := by simp [g₂]
  have hg_or x : g₁ x = 0 ∨ g₂ x = 0 := by
    rcases le_total 0 (g x) with h | h <;> simp [g₁, g₂, h]
  have hg_eq x : g x = g₁ x - g₂ x := by
    rcases le_total 0 (g x) with h | h <;> simp [g₁, g₂, h]
  simp_rw [hf_eq, hg_eq]
  rw [eintegral_sub_of_nonneg_of_eq_zero hf₁ hf₂ hf_or,
    eintegral_sub_of_nonneg_of_eq_zero hg₁ hg₂ hg_or]
  have : ∫ᵉ x, f₁ x ∂μ - ∫ᵉ x, f₂ x ∂μ + (∫ᵉ x, g₁ x ∂μ - ∫ᵉ x, g₂ x ∂μ)
      = ∫ᵉ x, f₁ x ∂μ + ∫ᵉ x, g₁ x ∂μ - (∫ᵉ x, f₂ x ∂μ + ∫ᵉ x, g₂ x ∂μ) := by
    rw [EReal.add_sub_add]
    · exact EReal.ne_bot_of_nonneg <| eintegral_nonneg hf₂
    · exact EReal.ne_bot_of_nonneg <| eintegral_nonneg hg₂
  rw [this, ← eintegral_add_of_nonneg _ (by fun_prop) hf₁ hg₁,
    ← eintegral_add_of_nonneg _ (by fun_prop) hf₂ hg₂,
    ← eintegral_sub_of_nonneg _ _ (by fun_prop) (by fun_prop)]
  rotate_left
  · sorry -- false as it is now?
  · intro x; positivity
  · intro x; specialize hf₂ x; specialize hg₂ x; positivity
  congr with x
  specialize hf_or x
  specialize hg_or x
  rcases hf_or with hfo | hfo <;> rcases hg_or with hgo | hgo
  · simp [hfo, hgo]
    -- rw [EReal.neg_add]
    sorry
  · simp [hfo, hgo]
    sorry
  · simp [hfo, hgo]
    sorry
  · simp [hfo, hgo]

lemma eintegral_sub (μ : Measure α) (f g : α → EReal)
    (hf : AEMeasurable f μ) (hg : eintegrable g μ) (hg_meas : AEMeasurable g μ) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  simp_rw [sub_eq_add_neg]
  rw [eintegral_add _ _ _ hf hg_meas.neg, eintegral_neg μ g hg]

lemma eintegral_prod_of_nonneg {β : Type*} {mβ : MeasurableSpace β} {ν : Measure β} [SFinite ν]
    (f : α × β → EReal) (hf : AEMeasurable f (μ.prod ν)) (hf_nonneg : ∀ (x : α × β), 0 ≤ f x) :
    ∫ᵉ z, f z ∂(μ.prod ν) = ∫ᵉ x, ∫ᵉ y, f (x, y) ∂ν ∂μ := by
  have hf_nonneg' x : ∀ y, 0 ≤ f (x, y) := fun y ↦ hf_nonneg (x, y)
  rw [eintegral_of_nonneg hf_nonneg, eintegral_of_nonneg]
  swap; · exact fun x ↦ eintegral_nonneg (hf_nonneg' x)
  simp_rw [eintegral_of_nonneg (hf_nonneg' _)]
  congr
  rw [lintegral_prod _ (by fun_prop)]
  congr with x
  rw [EReal.toENNReal_coe]

lemma eintegral_prod {β : Type*} {mβ : MeasurableSpace β} {ν : Measure β} [SFinite ν]
    (f : α × β → EReal) (hf : AEMeasurable f (μ.prod ν)) :
    ∫ᵉ z, f z ∂(μ.prod ν) = ∫ᵉ x, ∫ᵉ y, f (x, y) ∂ν ∂μ := by
  let f₁ := fun x ↦ max (f x) 0
  let f₂ := fun x ↦ - min (f x) 0
  have hf₁ x : 0 ≤ f₁ x := by simp [f₁]
  have hf₂ x : 0 ≤ f₂ x := by simp [f₂]
  have h_or x : f₁ x = 0 ∨ f₂ x = 0 := by
    rcases le_total 0 (f x) with h | h <;> simp [f₁, f₂, h]
  have h_eq x : f x = f₁ x - f₂ x := by
    rcases le_total 0 (f x) with h | h <;> simp [f₁, f₂, h]
  simp_rw [h_eq]
  rw [eintegral_sub_of_nonneg_of_eq_zero hf₁ hf₂ h_or]
  rw [eintegral_prod_of_nonneg, eintegral_prod_of_nonneg]
  rotate_left
  · unfold f₂; fun_prop
  · exact hf₂
  · unfold f₁; fun_prop
  · exact hf₁
  rw [← eintegral_sub _ _ _ _ (eintegrable_of_nonneg (fun _ ↦ eintegral_nonneg (fun _ ↦ hf₂ _)))]
  · congr with x
    rw [eintegral_sub]
    · sorry
    · exact eintegrable_of_nonneg (fun _ ↦ hf₂ _)
    · sorry
  · sorry
  · sorry

theorem eintegral_map {β : Type*} {mβ : MeasurableSpace β} {f : β → EReal} {g : α → β}
    (hf : Measurable f) (hg : Measurable g) : ∫ᵉ a, f a ∂μ.map g = ∫ᵉ a, f (g a) ∂μ := by
  simp only [eintegral]
  repeat rw [lintegral_map (by fun_prop) hg]

theorem eintegral_map' {β : Type*} {mβ : MeasurableSpace β} {f : β → EReal} {g : α → β}
    (hf : AEMeasurable f (μ.map g)) (hg : AEMeasurable g μ) :
    ∫ᵉ a, f a ∂μ.map g = ∫ᵉ a, f (g a) ∂μ := by
  simp only [eintegral]
  repeat rw [lintegral_map' (by fun_prop) hg]

lemma eintegral_prod_symm {β : Type*} {mβ : MeasurableSpace β} [SFinite μ]
    {ν : Measure β} [SFinite ν]
    (f : α × β → EReal) (hf : AEMeasurable f (μ.prod ν)) :
    ∫ᵉ z, f z ∂(μ.prod ν) = ∫ᵉ y, ∫ᵉ x, f (x, y) ∂μ ∂ν := by
  calc ∫ᵉ z, f z ∂(μ.prod ν)
  _ = ∫ᵉ z, (f ∘ Prod.swap) z ∂(ν.prod μ) := by
    simp only [Function.comp_apply]
    rw [← eintegral_map' _ measurable_swap.aemeasurable, Measure.prod_swap]
    rwa [Measure.prod_swap]
  _ = ∫ᵉ y, ∫ᵉ x, (f ∘ Prod.swap) (y, x) ∂μ ∂ν := by
    rw [eintegral_prod]
    refine AEMeasurable.comp_aemeasurable ?_ (by fun_prop)
    rwa [Measure.prod_swap]
  _ = ∫ᵉ y, ∫ᵉ x, f (x, y) ∂μ ∂ν := by simp

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
