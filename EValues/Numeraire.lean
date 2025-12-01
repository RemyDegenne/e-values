/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/

import EValues.EValue
import EValues.Mathlib.Convex
import EValues.Mathlib.Jensen
import EValues.Mathlib.ENNReal
import EValues.Utility
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Numeraire E-variables



## Main definitions

* TODO

## Main statements

* TODO

-/

open ENNReal

open MeasureTheory ProbabilityTheory Set Function

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}

namespace ProbabilityTheory

/-- A random variable `X` is the numeraire for a set of measures `S` and a measure `μ`
if it is an E-variable for `S` and the expectation of the ratio of any E-variable `Y` over `X`
is at most one under `μ`. -/
structure IsNumeraire (X : 𝓧 → ℝ≥0∞) (S : Set (Measure 𝓧)) (μ : Measure 𝓧) : Prop
    extends IsEVar X S where
  isProbabilityMeasure_set : ∀ μ ∈ S, IsProbabilityMeasure μ
  lintegral_div_le_one : ∀ ⦃Y⦄, IsEVar Y S → ∫⁻ ω, Y ω / X ω ∂μ ≤ 1

namespace IsNumeraire

variable {X Y : 𝓧 → ℝ≥0∞} {μ : Measure 𝓧} {S : Set (Measure 𝓧)}
  {hS : ∀ μ ∈ S, IsProbabilityMeasure μ}

lemma lintegral_inv_le_one (hX : IsNumeraire X S μ) : ∫⁻ ω, (X ω)⁻¹ ∂μ ≤ 1 := by
  simpa using hX.lintegral_div_le_one (isEVar_one S hX.isProbabilityMeasure_set)

lemma ae_pos (hX : IsNumeraire X S μ) : ∀ᵐ ω ∂μ, 0 < X ω := by
  suffices ∀ᵐ ω ∂μ, (X ω)⁻¹ < ∞ by
    simp only [pos_iff_ne_zero]
    filter_upwards [this] with ω hω using by simpa using hω.ne
  refine ae_lt_top ?_ ?_
  · have := hX.measurable
    fun_prop
  · exact ne_top_of_le_ne_top (by simp) hX.lintegral_inv_le_one

lemma ae_ne_zero (hX : IsNumeraire X S μ) : ∀ᵐ ω ∂μ, X ω ≠ 0 := by
  filter_upwards [hX.ae_pos] with ω hω using hω.ne'

lemma div_ae_finite (hX : IsNumeraire X S μ) (hY : IsEVar Y S) : ∀ᵐ x ∂μ, Y x / X x ≠ ⊤ := by
  rw [ae_iff]
  by_contra! h
  have le_one := hX.lintegral_div_le_one hY
  rw [lintegral_eq_top_of_measure_eq_top_ne_zero
      (hY.measurable.div hX.measurable).aemeasurable h] at le_one
  contradiction

lemma lintegral_eq_setLIntegral_fsupport (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫⁻ ω, Y ω / X ω ∂μ = ∫⁻ ω in X.fsupport, Y ω / X ω ∂μ := by
  rw [← lintegral_add_compl _ hX.measurable_fsupport]
  suffices ∫⁻ ω in X.fsupportᶜ, Y ω / X ω ∂μ = 0 by simp [this]
  rw [setLIntegral_eq_zero_iff (hX.measurable_fsupport).compl <| hY.measurable.div hX.measurable]
  filter_upwards [hX.ae_ne_zero] with ω hω hω₂
  simp only [fsupport, ne_eq, mem_compl_iff, mem_inter_iff, mem_setOf_eq, hω, not_false_eq_true,
    and_true, Decidable.not_not] at hω₂
  simp [hω₂]

lemma ae_top_implies_numeraire_top (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∀ᵐ ω ∂μ, Y ω = ∞ → X ω = ∞ := by
  by_contra h
  simp only [ae_iff, Classical.not_imp] at h
  have m : MeasurableSet {ω | Y ω = ∞ ∧ X ω ≠ ∞} :=
    MeasurableSet.inter ((measurableSet_singleton ∞).preimage hY.measurable)
      ((measurableSet_singleton ∞).compl.preimage hX.measurable)
  have lintegral_div_le_one := hX.lintegral_div_le_one hY
  rw [← lintegral_add_compl _ m] at lintegral_div_le_one
  suffices ∀ ω ∈ {ω | Y ω = ∞ ∧ X ω ≠ ∞}, Y ω / X ω = ∞ by
    rw [setLIntegral_congr_fun m this] at lintegral_div_le_one
    simp [top_mul h] at lintegral_div_le_one
  intro ω hω
  simp [hω.1, ENNReal.top_div, hω.2]

-- `rev`?
lemma lintegral_eq_setLIntegral_rev_fsupport (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫⁻ ω, Y ω / X ω ∂μ = ∫⁻ ω in Y.fsupport, Y ω / X ω ∂μ := by
  rw [← lintegral_add_compl _ hY.measurable_fsupport]
  suffices ∫⁻ ω in Y.fsupportᶜ, Y ω / X ω ∂μ = 0 by simp [this]
  rw [setLIntegral_eq_zero_iff (hY.measurable_fsupport).compl
    <| hY.measurable.div hX.measurable]
  filter_upwards [hX.ae_top_implies_numeraire_top hY] with ω hω hω₂
  simp only [ENNReal.div_eq_zero_iff]
  by_cases hω_top : Y ω = ∞
  · simp [hω_top, hω hω_top]
  · simp only [fsupport, ne_eq, mem_compl_iff, mem_inter_iff, mem_setOf_eq, not_and,
      Decidable.not_not] at hω₂
    simp [hω_top, hω₂]

lemma measure_fsupport_ne_zero_or_ae_top (hX : IsNumeraire X S μ) :
    μ X.fsupport ≠ 0 ∨ X =ᵐ[μ] fun _ ↦ ∞ := by
  by_contra! h
  rcases h with ⟨h, h_top⟩
  rw [← compl_compl (fsupport X)] at h
  have h' : ∀ᵐ x ∂μ, x ∈ (fsupport X)ᶜ := by rwa [ae_iff]
  refine h_top ?_
  filter_upwards [h', ae_ne_zero hX] with ω hω_mem hω_ne_zero
  simpa [hω_ne_zero] using hω_mem

lemma setLIntegral_fsupport_inv_le_one (hX : IsEVar X S) (hY : IsNumeraire Y S μ) :
    ∫⁻ ω in X.fsupport, (Y ω / X ω)⁻¹ ∂μ ≤ 1 := by
  suffices ∫⁻ ω in X.fsupport, ((Y / X) ω)⁻¹ ∂μ ≤ 1 by exact this
  rw [setLIntegral_congr_fun hX.measurable_fsupport <| ENNReal.inv_div_fsupport Y X,
    ← hY.lintegral_eq_setLIntegral_rev_fsupport hX]
  exact hY.lintegral_div_le_one hX

lemma inv_lintegral_div_eq_one [IsProbabilityMeasure μ]
    (hX : IsNumeraire X S μ) (hY : IsNumeraire Y S μ) (h : μ X.fsupport ≠ 0) :
    (∫⁻ ω, Y ω / X ω ∂μ)⁻¹ = 1 := by
  set W := Y / X
  --rw [hX.lintegral_eq_setLIntegral_fsupport hY.toIsEVar]
  refine le_antisymm ?_ ?_
  · calc (∫⁻ ω, W ω ∂μ)⁻¹
    _ ≤ ∫⁻ ω, (W ω)⁻¹ ∂μ := by
      refine Inv.map_lintegral_le ?_ ?_
      · exact (hY.measurable.div hX.measurable).aemeasurable
      · exact div_ae_finite hX hY.toIsEVar
    _ = ∫⁻ ω in X.fsupport, (W ω)⁻¹ ∂μ := by
        sorry
      /- rw [← lintegral_add_compl _ hX.measurable_fsupport]
      suffices ∫⁻ ω in X.fsupportᶜ, (W ω)⁻¹ ∂μ = 0 by simp [this]
      rw [setLIntegral_eq_zero_iff (hX.measurable_fsupport).compl]
      swap
      · have : Measurable W := hY.measurable.div hX.measurable
        fun_prop
      · filter_upwards [hY.ae_ne_zero, hX.ae_ne_zero, ae_top_implies_numeraire_top hX hY.toIsEVar]
          with ω hω hXω hYXω hYω
        simp [W]
        rw [div_eq_top]
        rw [fsupport_compl] at hYω
        rcases hYω with hYω_top | hYω_zero
        · simp_all [W]
          apply?
          sorry
        · contradiction -/
    /- _ = ∫⁻ ω, (X ω / Y ω) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [div_ae_finite hX hY.toIsEVar, ae_ne_zero hX] with ω hω hXω
      refine ENNReal.inv_div ?_ (.inl hXω)
      by_contra! h
      sorry -/
    _ ≤ 1 := setLIntegral_fsupport_inv_le_one hX.toIsEVar hY

  · rw [hX.lintegral_eq_setLIntegral_fsupport hY.toIsEVar]
    simp only [← hX.lintegral_eq_setLIntegral_fsupport hY.toIsEVar, le_inv_iff_mul_le, one_mul]
    exact hX.lintegral_div_le_one hY.toIsEVar

lemma lintegral_div_eq_one [IsProbabilityMeasure μ]
    (hX : IsNumeraire X S μ) (hY : IsNumeraire Y S μ) (h : μ X.fsupport ≠ 0) :
    ∫⁻ ω, Y ω / X ω ∂μ = 1 := by
  rw [← ENNReal.inv_eq_one]
  exact hX.inv_lintegral_div_eq_one hY h

/-- The Numeraire is almost-everywhere unique. -/
theorem ae_unique [IsProbabilityMeasure μ] (hX : IsNumeraire X S μ) (hY : IsNumeraire Y S μ) :
    X =ᵐ[μ] Y := by
  rcases hY.measure_fsupport_ne_zero_or_ae_top with μ_fsupport | hYₜ
  swap
  · filter_upwards [hYₜ, hX.ae_top_implies_numeraire_top hY.toIsEVar] with ω hω hω₂
    simp_all
  let W := X / Y
  have inv_avg_eq_one : (∫⁻ ω in Y.fsupport, W ω ∂μ)⁻¹ = 1 := by
    simp only [Pi.div_apply, ← hY.lintegral_eq_setLIntegral_fsupport hX.toIsEVar, W]
    exact hY.inv_lintegral_div_eq_one hX μ_fsupport
  have avg_eq_one : ∫⁻ ω, W ω ∂μ = 1 := lintegral_div_eq_one hY hX μ_fsupport
  have strict_Jensen : W =ᵐ[μ] const 𝓧 (∫⁻ ω, W ω ∂μ) ∨
      (∫⁻ ω in Y.fsupport, W ω ∂μ)⁻¹ < ∫⁻ ω in Y.fsupport, (W ω)⁻¹ ∂μ :=
    strictConvexOn_inv.ae_eq_const_or_map_set_lintegral_lt continuousOn_inv
        isClosed_univ μ_fsupport (by simp) (by simp)
  have h_le : ∫⁻ ω in fsupport Y, (W ω)⁻¹ ∂μ ≤ 1 :=
    setLIntegral_fsupport_inv_le_one hY.toIsEVar hX
  simp only [inv_avg_eq_one, not_lt.mpr h_le, or_false, avg_eq_one] at strict_Jensen
  filter_upwards [strict_Jensen] with ω hx
  simp only [Pi.div_apply, const_apply, W] at hx
  exact ENNReal.eq_of_div_eq_one hx

lemma congr (hX : IsNumeraire X S μ) (hY_evar : IsEVar Y S) (hY : Y =ᵐ[μ] X) :
    IsNumeraire Y S μ := by
  refine ⟨hY_evar, hX.isProbabilityMeasure_set, fun Z hZ_evar ↦ ?_⟩
  calc ∫⁻ ω, Z ω / Y ω ∂μ
    _ = ∫⁻ ω, Z ω / X ω ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hY] with ω hω
      rw [hω]
    _ ≤ 1 := hX.lintegral_div_le_one hZ_evar

section LogOptimal

-- todo: prove that log-optimal implies numeraire
/-- A Numeraire is log-optimal. -/
theorem eintegral_log_div_nonpos [IsProbabilityMeasure μ]
    (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, ENNReal.log (Y ω / X ω) ∂μ ≤ 0:= by
  calc ∫ᵉ ω, ENNReal.log (Y ω / X ω) ∂μ
  _ ≤ ENNReal.log (∫⁻ ω, Y ω / X ω ∂μ) := by
    refine Utility.eintegral_le_map logUtility ?_
    exact hY.measurable.aemeasurable.div hX.measurable.aemeasurable
  _ ≤ 0 := by
    simp only [ENNReal.log_le_zero_iff]
    exact lintegral_div_le_one hX hY

lemma eintegral_eq_setEIntegral_of_eq_zero {f : 𝓧 → EReal}
    {s : Set 𝓧} (hs : MeasurableSet s) (h_zero : ∀ᵐ ω ∂μ, ω ∈ sᶜ → f ω = 0) :
    ∫ᵉ ω, f ω ∂μ = ∫ᵉ ω in s, f ω ∂μ:= by
  unfold eintegral
  simp_rw [← lintegral_indicator hs]
  congr 2 <;>
  · refine lintegral_congr_ae ?_
    filter_upwards [h_zero] with ω hω
    by_cases hωs : ω ∈ s
    · simp [hωs]
    · simp [hω hωs, hωs]

lemma eintegral_div_le_one (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, Y ω / X ω ∂μ ≤ 1 := by
  rw [eintegral_of_nonneg (fun _ ↦ by positivity)]
  norm_cast
  refine le_trans (le_of_eq ?_) (hX.lintegral_div_le_one hY)
  refine lintegral_congr_ae ?_
  filter_upwards [hX.ae_ne_zero] with ω hω
  rw [← EReal.coe_ennreal_div hω, EReal.toENNReal_coe]

lemma setEIntegral_le_eintegral_of_nonneg {f : 𝓧 → EReal} (hf_nonneg : ∀ ω, 0 ≤ f ω) (s : Set 𝓧) :
    ∫ᵉ ω in s, f ω ∂μ ≤ ∫ᵉ ω, f ω ∂μ := by
  rw [eintegral_of_nonneg hf_nonneg, eintegral_of_nonneg]
  · norm_cast
    exact setLIntegral_le_lintegral s fun x ↦ (f x).toENNReal
  · exact hf_nonneg

lemma setEIntegral_le_eintegral_of_ae_nonneg {f : 𝓧 → EReal} (hf_meas : AEMeasurable f μ)
    (hf_nonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω) (s : Set 𝓧) :
    ∫ᵉ ω in s, f ω ∂μ ≤ ∫ᵉ ω, f ω ∂μ := by
  rw [eintegral_of_ae_nonneg hf_meas hf_nonneg, eintegral_of_ae_nonneg]
  · norm_cast
    exact setLIntegral_le_lintegral s fun x ↦ (f x).toENNReal
  · exact hf_meas.restrict
  · exact ae_restrict_of_ae hf_nonneg

-- todo: it should really be ≤ 0 instead, but this weaker result will be useful to prove that a
-- numeraire is `eintegrable`
lemma eintegral_sub_div_le_one (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, (Y ω - X ω) / X ω ∂μ ≤ 1 := by
  have h_eq : ∀ᵐ ω ∂μ, X ω ≠ ⊤ → ((Y ω : EReal) - X ω) / X ω = Y ω / X ω - 1 := by
    filter_upwards [hX.ae_ne_zero, ae_top_implies_numeraire_top hX hY] with ω hX0 h_imp_top hX_top
    have hY_top : Y ω ≠ ∞ := fun h_false ↦ hX_top <| h_imp_top h_false
    have hX_eq : (X ω : EReal) = (X ω).toReal := by rw [EReal.coe_ennreal_toReal hX_top]
    have hY_eq : (Y ω : EReal) = (Y ω).toReal := by rw [EReal.coe_ennreal_toReal hY_top]
    rw [hX_eq, hY_eq]
    norm_cast
    rw [← EReal.coe_div, ← EReal.coe_div]
    have hX_ne_zero : (X ω).toReal ≠ 0 := by simp [ENNReal.toReal_eq_zero_iff, hX0, hX_top]
    simp [sub_div, div_self hX_ne_zero]
  have h_int_restrict : ∫ᵉ ω, (Y ω - X ω) / X ω ∂μ
      = ∫ᵉ ω in {ω | X ω ≠ ⊤}, (Y ω - X ω) / X ω ∂μ := by
    refine eintegral_eq_setEIntegral_of_eq_zero ?_ ?_
    · exact ((measurableSet_singleton _).preimage hX.measurable).compl
    · filter_upwards [] with ω hω_top
      simp only [ne_eq, mem_compl_iff, mem_setOf_eq, Decidable.not_not] at hω_top
      simp [hω_top]
  have h_int_restrict' : ∫ᵉ ω, Y ω / X ω ∂μ = ∫ᵉ ω in {ω | X ω ≠ ⊤}, Y ω / X ω ∂μ := by
    refine eintegral_eq_setEIntegral_of_eq_zero ?_ ?_
    · exact ((measurableSet_singleton _).preimage hX.measurable).compl
    · filter_upwards [] with ω hω_top
      simp only [ne_eq, mem_compl_iff, mem_setOf_eq, Decidable.not_not] at hω_top
      simp [hω_top]
  rw [h_int_restrict]
  calc ∫ᵉ ω in {ω | X ω ≠ ⊤}, (Y ω - X ω) / X ω ∂μ
  _ = ∫ᵉ ω in {ω | X ω ≠ ⊤}, Y ω / X ω - 1 ∂μ := by
    refine eintegral_congr_ae ?_
    rwa [ae_restrict_iff']
    exact ((measurableSet_singleton _).preimage hX.measurable).compl
  _ ≤ ∫ᵉ ω in {ω | X ω ≠ ⊤}, Y ω / X ω ∂μ := by
    gcongr
    intro ω
    simp only
    rw [sub_eq_add_neg]
    conv_rhs => rw [← add_zero ((Y ω : EReal) / X ω)]
    gcongr
    simp
  _ ≤ ∫ᵉ ω, Y ω / X ω ∂μ := by
    refine setEIntegral_le_eintegral_of_nonneg (fun _ ↦ ?_) _
    positivity
  _ ≤ 1 := hX.eintegral_div_le_one hY

theorem eintegral_log_ge_neg_one [IsProbabilityMeasure μ] (hX : IsNumeraire X S μ) :
    -1 ≤ ∫ᵉ ω, ENNReal.log (X ω) ∂μ := by
  have hX_meas := hX.measurable
  have hY : IsEVar (fun _ ↦ 1) S := isEVar_one S hX.isProbabilityMeasure_set
  suffices 0 ≤ ∫ᵉ ω, ENNReal.log (X ω) ∂μ + 1 by
    conv_lhs => rw [← zero_add (-1), ← sub_eq_add_neg]
    rwa [EReal.sub_le_iff_le_add]
    · left; norm_cast
    · left; norm_cast
  calc 0
  _ = ∫ᵉ ω, ENNReal.log 1 ∂μ := by simp
  _ ≤ ∫ᵉ ω, ENNReal.log (X ω) + (1 - X ω) * (if X ω = 0 then ⊤ else 1 / X ω) ∂μ := by
    refine eintegral_mono_ae ?_
    filter_upwards [hX.ae_ne_zero] with ω hω
    by_cases hX_top : X ω = ∞
    · simp [hX_top]
    simp only [log_one, hω, ↓reduceIte, one_div]
    have : X ω = ENNReal.ofReal (X ω).toReal := by rw [ENNReal.ofReal_toReal hX_top]
    have h_pos : 0 < (X ω).toReal := ENNReal.toReal_pos hω hX_top
    rw [this, ENNReal.log_ofReal, EReal.coe_ennreal_ofReal, EReal.coe_ennreal_inv,
      EReal.coe_ennreal_ofReal, ← EReal.coe_inv]
    swap; · rwa [ENNReal.ofReal_toReal hX_top]
    simp only [not_le.mpr h_pos, ↓reduceIte, toReal_nonneg, sup_of_le_left, ge_iff_le]
    norm_cast
    have h := Real.one_sub_inv_le_log_of_pos h_pos
    field_simp at h ⊢
    linarith
  _ = ∫ᵉ ω, ENNReal.log (X ω) + (1 - X ω) / X ω ∂μ := by
    refine eintegral_congr_ae ?_
    filter_upwards [hX.ae_ne_zero] with ω hω
    congr
    simp only [hω, ↓reduceIte, one_div]
    rw [← EReal.inv_coe_ennreal hω]
    rfl
  _ = ∫ᵉ ω, ENNReal.log (X ω) ∂μ + ∫ᵉ ω, (1 - X ω) / X ω ∂μ := by
    rw [eintegral_add']
    · fun_prop
    · fun_prop
    · refine ne_top_of_le_ne_top (by norm_cast : (1 : EReal) ≠ ⊤) ?_
      calc ∫ᵉ ω, (1 - X ω) / X ω ∂μ
      _ ≤ ∫ᵉ ω, 1 / X ω ∂μ := by
        refine eintegral_mono ?_
        intro ω
        simp only
        gcongr
        rw [sub_eq_add_neg]
        conv_rhs => rw [← add_zero 1]
        gcongr
        simp only [EReal.neg_le_zero]
        positivity
      _ = ∫⁻ ω, 1 / X ω ∂μ := by
        rw [eintegral_of_nonneg]
        · congr 1
          refine lintegral_congr_ae ?_
          filter_upwards [hX.ae_ne_zero] with ω hω
          rw [div_eq_mul_inv, EReal.toENNReal_mul, EReal.toENNReal_one, EReal.toENNReal_inv,
            EReal.toENNReal_coe, div_eq_mul_inv]
          · positivity
          · positivity
        · intro x
          positivity
      _ ≤ 1 := mod_cast hX.lintegral_div_le_one hY
    · refine ne_bot_of_le_ne_bot (by norm_cast : (-1 : EReal) ≠ ⊥) ?_
      calc -1
      _ = ∫ᵉ ω, -1 ∂μ := by simp
      _ ≤ ∫ᵉ ω, - X ω / X ω ∂μ := by
        gcongr
        intro ω
        simp only
        by_cases hX0 : X ω = 0
        · simp [hX0]
        by_cases hX_top : X ω = ∞
        · simp [hX_top]
        rw [EReal.neg_div, EReal.div_self (by simp) (by simp [hX_top]) (by simp [hX0])]
      _ ≤ ∫ᵉ ω, (1 - X ω) / X ω ∂μ := by
        gcongr
        intro ω
        simp only
        gcongr
        rw [sub_eq_add_neg]
        conv_lhs => rw [← zero_add (- (X ω : EReal))]
        gcongr
        simp
  _ ≤ ∫ᵉ ω, ENNReal.log (X ω) ∂μ + 1 := by
    gcongr
    convert hX.eintegral_sub_div_le_one hY -- `convert` instead of `exact` for speed

/-- The logarithm of the numeraire is integrable. -/
protected lemma eintegrable_log [IsProbabilityMeasure μ] (hX : IsNumeraire X S μ) :
    eintegrable (fun ω ↦ ENNReal.log (X ω)) μ := by
  have h_le := eintegral_log_ge_neg_one hX
  by_contra h_false
  simp [eintegral_of_not_eintegrable h_false] at h_le
  norm_cast at h_le

/-- A Numeraire maximizes the integral of the logarithm. -/
theorem eintegral_log_le [IsProbabilityMeasure μ] (hX : IsNumeraire X S μ) (hY : IsEVar Y S) :
    ∫ᵉ ω, ENNReal.log (Y ω) ∂μ ≤ ∫ᵉ ω, ENNReal.log (X ω) ∂μ := by
  by_cases hY_bot : ∫ᵉ ω, ENNReal.log (Y ω) ∂μ = ⊥
  · simp [hY_bot]
  by_cases hX_top : ∫ᵉ ω, ENNReal.log (X ω) ∂μ = ⊤
  · simp [hX_top]
  have hY_int : eintegrable (fun ω ↦ ENNReal.log (Y ω)) μ := by
    by_contra h_false
    simp [eintegral_of_not_eintegrable h_false] at hY_bot
  have h_nonpos := eintegral_log_div_nonpos hX hY
  simp_rw [ENNReal.log_div] at h_nonpos
  rwa [eintegral_sub hY_int, EReal.sub_nonpos] at h_nonpos
  · have := hY.measurable
    fun_prop
  · exact hX.eintegrable_log
  · have := hX.measurable
    fun_prop
  · simp [hX_top]
  · simp [hY_bot]

lemma eintegral_log_nonneg [IsProbabilityMeasure μ] (hX : IsNumeraire X S μ) :
    0 ≤ ∫ᵉ ω, ENNReal.log (X ω) ∂μ := by
  simpa using eintegral_log_le hX (isEVar_one S hX.isProbabilityMeasure_set)

end LogOptimal

end IsNumeraire

end ProbabilityTheory
