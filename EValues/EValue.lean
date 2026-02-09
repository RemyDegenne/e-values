/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Notation
import EValues.EIntegral
import EValues.Mathlib.Convex
import EValues.Mathlib.ENNReal
import EValues.Mathlib.unitInterval

/-!
# E-variables



## Main definitions

* TODO

## Main statements

* TODO

-/

open scoped ENNReal NNReal ProbabilityTheory

open MeasureTheory ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ : Measure 𝓧} {S : Set (Measure 𝓧)}

namespace ProbabilityTheory

-- section NegFun

-- variable {X Y : 𝓧 → EReal} {S : Set (Measure 𝓧)}

-- structure IsNegFun (X : 𝓧 → EReal) (S : Set (Measure 𝓧)) : Prop where
--   measurable : Measurable X := by fun_prop
--   eintegral_ne_bot : ∀ μ ∈ S, ∫ᵉ ω, X ω ∂μ ≠ ⊥
--   eintegral_nonpos : ∀ μ ∈ S, ∫ᵉ ω, X ω ∂μ ≤ 0

-- lemma isNegFun_of_isEmpty (hS : IsEmpty S) (hX : Measurable X) :
--     IsNegFun X S where
--   eintegral_ne_bot := by simp_all
--   eintegral_nonpos := by simp_all

-- lemma isNegFun_zero : IsNegFun 0 S where
--   eintegral_ne_bot μ hμ := by simp
--   eintegral_nonpos μ hμ := by simp

-- lemma IsNegFun.congr (hX : IsNegFun X S) (hY : Measurable Y) (hXY : ∀ μ ∈ S, X =ᵐ[μ] Y) :
--     IsNegFun Y S where
--   measurable := hY
--   eintegral_ne_bot μ hμ := by
--     rw [eintegral_congr_ae (hXY μ hμ).symm]
--     exact hX.eintegral_ne_bot μ hμ
--   eintegral_nonpos μ hμ := by
--     rw [eintegral_congr_ae (hXY μ hμ).symm]
--     exact hX.eintegral_nonpos μ hμ

-- lemma IsNegFun.ae_lt_top (hX : IsNegFun X S) {μ : Measure 𝓧} (hμ : μ ∈ S) :
--     ∀ᵐ ω ∂μ, X ω < ⊤ := by
--   simp_rw [lt_top_iff_ne_top]
--   refine ae_ne_top_of_eintegral_ne_top hX.measurable.aemeasurable (hX.eintegral_ne_bot μ hμ) ?_
--   intro h_contra
--   have h_le := hX.eintegral_nonpos μ hμ
--   simp [h_contra] at h_le

-- lemma IsNegFun.ae_ne_top (hX : IsNegFun X S) {μ : Measure 𝓧} (hμ : μ ∈ S) :
--     ∀ᵐ ω ∂μ, X ω ≠ ⊤ := by
--   filter_upwards [hX.ae_lt_top hμ] with ω hω using hω.ne

-- end NegFun

/-- A random variable `X` is an e-variable for a set of measures `S` if it is measurable and
its expectation is at most one for all measures in `S`. -/
structure IsEVar (X : 𝓧 → ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  measurable : Measurable X := by fun_prop
  eintegral_ne_bot : ∀ μ ∈ S, ∫ᵉ ω, X ω - 1 ∂μ ≠ ⊥
  eintegral_nonpos : ∀ μ ∈ S, ∫ᵉ ω, X ω - 1 ∂μ ≤ 0

-- lemma isEVar_iff_isNegFun {X : 𝓧 → ℝ≥0∞} {S : Set (Measure 𝓧)} :
--     IsEVar X S ↔ IsNegFun (fun ω ↦ (X ω : EReal) - 1) S := by
--   refine ⟨fun h ↦ ⟨by have := h.measurable; fun_prop, h.eintegral_ne_bot, h.eintegral_nonpos⟩,
--     fun h ↦ ⟨?_, h.eintegral_ne_bot, h.eintegral_nonpos⟩⟩
--   have : X = fun ω ↦ ((X ω : EReal) - 1 + 1 : EReal).toENNReal := by
--     ext ω
--     have : (1 : EReal) = (1 : ℝ) := by norm_cast
--     simp_rw [this]
--     rw [EReal.sub_add_cancel]
--     simp
--   rw [this]
--   have h_meas := h.measurable
--   fun_prop

-- lemma IsEVar.isNegFun_sub_one {X : 𝓧 → ℝ≥0∞} (hX : IsEVar X S) :
--     IsNegFun (fun ω ↦ (X ω : EReal) - 1) S :=
--   isEVar_iff_isNegFun.1 hX

lemma eintegral_sub_one_ne_bot_of_isFiniteMeasure {X : 𝓧 → ℝ≥0∞} {S : Set (Measure 𝓧)}
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) {μ : Measure 𝓧} (hμ : μ ∈ S) :
    ∫ᵉ ω, X ω - 1 ∂μ ≠ ⊥ := by
  refine ne_bot_of_le_ne_bot (b := ∫ᵉ ω, - 1 ∂μ) ?_ ?_
  · specialize hS μ hμ
    simp
  · gcongr
    intro x
    simp only
    conv_lhs => rw [← zero_sub (1 : EReal)]
    refine EReal.sub_le_sub ?_ le_rfl -- add gcongr tag?
    positivity

lemma IsEVar.eintegrable_sub_one {X : 𝓧 → ℝ≥0∞} (hX : IsEVar X S) (μ : Measure 𝓧) (hμ : μ ∈ S) :
    eintegrable (fun ω ↦ (X ω : EReal) - 1) μ :=
  eintegrable_of_eintegral_ne_bot (hX.eintegral_ne_bot μ hμ)

lemma IsEVar.lintegral_le_measure_univ {X : 𝓧 → ℝ≥0∞} (hX : IsEVar X S)
    (μ : Measure 𝓧) (hμ : μ ∈ S) :
    ∫⁻ ω, X ω ∂μ ≤ μ .univ := by
  have h_nonpos := hX.eintegral_nonpos μ hμ
  by_cases hμ : IsFiniteMeasure μ
  swap
  · simp only [not_isFiniteMeasure_iff] at hμ
    simp [hμ]
  rw [eintegral_sub_of_nonneg] at h_nonpos
  rotate_left
  · exact fun _ ↦ by positivity
  · simp
  · have := hX.measurable; fun_prop
  · fun_prop
  · refine ne_top_of_le_ne_top (b := ∫⁻ ω, 1 ∂μ) ?_ ?_
    · simp
    rw [← eintegral_eq_lintegral]
    gcongr
    intro x
    simp
  rw [eintegral_eq_lintegral] at h_nonpos
  simpa only [eintegral_const, one_mul, EReal.sub_nonpos, EReal.coe_ennreal_le_coe_ennreal_iff]
    using h_nonpos

lemma isEvar_of_lintegral_le_measure_univ (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_meas : Measurable X) (hX : ∀ μ ∈ S, ∫⁻ ω, X ω ∂μ ≤ μ .univ) :
    IsEVar X S where
  eintegral_ne_bot μ hμ := eintegral_sub_one_ne_bot_of_isFiniteMeasure hS hμ
  eintegral_nonpos μ hμ := by
    have h_le := hX μ hμ
    rw [eintegral_sub_of_nonneg]
    rotate_left
    · exact fun _ ↦ by positivity
    · simp
    · fun_prop
    · fun_prop
    · specialize hS μ hμ
      refine ne_top_of_le_ne_top (b := ∫⁻ ω, 1 ∂μ) ?_ ?_
      · simp
      rw [← eintegral_eq_lintegral]
      gcongr
      intro x
      simp
    rw [eintegral_eq_lintegral]
    simpa only [eintegral_const, one_mul, EReal.sub_nonpos, EReal.coe_ennreal_le_coe_ennreal_iff]
      using h_le

/-- A random variables `X` is an e-variable for a set of measures `S` if it is measurable and
its expectation is at most one for all measures in `S`. -/
structure IsRandEVar (κ : Kernel 𝓧 ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  [markov : IsMarkovKernel κ]
  eintegral_ne_bot : ∀ μ ∈ S, ∫ᵉ ω, ∫⁻ x, x ∂(κ ω) - 1 ∂μ ≠ ⊥
  eintegral_nonpos : ∀ μ ∈ S, ∫ᵉ ω, ∫⁻ x, x ∂(κ ω) - 1 ∂μ ≤ 0

lemma IsRandEVar.lintegral_le_one {κ : Kernel 𝓧 ℝ≥0∞} (hκ : IsRandEVar κ S)
    (μ : Measure 𝓧) (hμ : μ ∈ S) :
    ∫⁻ ω, ∫⁻ x, x ∂(κ ω) ∂μ ≤ μ .univ := by
  have h_nonpos := hκ.eintegral_nonpos μ hμ
  by_cases hμ : IsFiniteMeasure μ
  swap
  · simp only [not_isFiniteMeasure_iff] at hμ
    simp [hμ]
  rw [eintegral_sub_of_nonneg] at h_nonpos
  rotate_left
  · exact fun _ ↦ by positivity
  · simp
  · fun_prop
  · fun_prop
  · refine ne_top_of_le_ne_top (b := ∫⁻ ω, 1 ∂μ) ?_ ?_
    · simp
    rw [← eintegral_eq_lintegral]
    gcongr
    intro x
    simp
  rw [eintegral_eq_lintegral] at h_nonpos
  simpa only [eintegral_const, one_mul, EReal.sub_nonpos, EReal.coe_ennreal_le_coe_ennreal_iff]
    using h_nonpos

variable {X Y : 𝓧 → ℝ≥0∞} {κ η : Kernel 𝓧 ℝ≥0∞} [IsMarkovKernel κ] {S T : Set (Measure 𝓧)}

/-- A kernel `κ` is a randomized e-variable iff its mean function `x ↦ ∫⁻ y, y ∂κ x` is an
e-variable. -/
lemma isRandEVar_iff_isEVar : IsRandEVar κ S ↔ IsEVar (fun x ↦ ∫⁻ y, y ∂κ x) S :=
  ⟨fun h ↦ ⟨by fun_prop, h.eintegral_ne_bot, h.eintegral_nonpos⟩,
    fun h ↦ ⟨h.eintegral_ne_bot, h.eintegral_nonpos⟩⟩

lemma IsEVar.isRandEVar_deterministic (hX : IsEVar X S) :
    IsRandEVar (Kernel.deterministic X hX.measurable) S where
  eintegral_ne_bot μ hμ := by
    simp only [Kernel.lintegral_deterministic]
    exact hX.eintegral_ne_bot μ hμ
  eintegral_nonpos μ hμ := by
    simp only [Kernel.lintegral_deterministic]
    exact hX.eintegral_nonpos μ hμ

lemma isEVar_of_isEmpty (hS : IsEmpty S) (hX : Measurable X) :
    IsEVar X S where
  eintegral_ne_bot := by simp_all
  eintegral_nonpos := by simp_all

lemma isEVar_zero (hS : ∀ μ ∈ S, IsFiniteMeasure μ) : IsEVar 0 S where
  eintegral_ne_bot μ hμ := by specialize hS μ hμ; simp
  eintegral_nonpos μ hμ := by
    simp only [Pi.zero_apply, EReal.coe_ennreal_zero, zero_sub, eintegral_const, neg_mul, one_mul,
      EReal.neg_le_zero]
    positivity

lemma isEVar_one (S : Set (Measure 𝓧)) : IsEVar 1 S where
  eintegral_ne_bot μ hμ := by
    simp only [Pi.one_apply, EReal.coe_ennreal_one, eintegral_const]
    rw [EReal.sub_self (by norm_cast) (by norm_cast)]
    simp
  eintegral_nonpos μ hμ := by
    simp only [Pi.one_apply, EReal.coe_ennreal_one, eintegral_const]
    rw [EReal.sub_self (by norm_cast) (by norm_cast)]
    simp

lemma isEVar_fun_one (S : Set (Measure 𝓧)) : IsEVar (fun _ ↦ 1) S := isEVar_one S

lemma IsEVar.congr (hX : IsEVar X S) (hY : Measurable Y) (hXY : ∀ μ ∈ S, X =ᵐ[μ] Y) :
    IsEVar Y S where
  measurable := hY
  eintegral_ne_bot μ hμ := by
    have : ∀ᵐ ω ∂μ, (Y ω : EReal) - 1 = X ω - 1 := by
      filter_upwards [hXY μ hμ] with ω hω
      rw [hω]
    rw [eintegral_congr_ae this]
    exact hX.eintegral_ne_bot μ hμ
  eintegral_nonpos μ hμ := by
    have : ∀ᵐ ω ∂μ, (Y ω : EReal) - 1 = X ω - 1 := by
      filter_upwards [hXY μ hμ] with ω hω
      rw [hω]
    rw [eintegral_congr_ae this]
    exact hX.eintegral_nonpos μ hμ

lemma IsEVar.ae_lt_top (hX : IsEVar X S) {μ : Measure 𝓧} (hμ : μ ∈ S) :
    ∀ᵐ ω ∂μ, X ω < ⊤ := by
  by_contra h
  have hX_le := hX.eintegral_nonpos μ hμ
  suffices ∫ᵉ ω, X ω - 1 ∂μ = ⊤ by simp [this] at hX_le
  unfold eintegral
  have h_top : ∫⁻ x, ((X x : EReal) - 1).toENNReal ∂μ = ∞ := by
    rw [lintegral_eq_top_of_measure_eq_top_ne_zero]
    · have := hX.measurable; fun_prop
    simp only [EReal.toENNReal_eq_top_iff, ne_eq]
    rw [measure_eq_zero_iff_ae_notMem]
    refine fun h_contra ↦ h ?_
    filter_upwards [h_contra] with ω hω
    rw [lt_top_iff_ne_top]
    intro h_eq_top
    simp [h_eq_top] at hω
    norm_cast
  rw [h_top, EReal.coe_ennreal_top, EReal.top_sub]
  simp only [ne_eq, EReal.coe_ennreal_eq_top_iff]
  have h_ne := hX.eintegral_ne_bot μ hμ
  simp only [eintegral, h_top, EReal.coe_ennreal_top, ne_eq] at h_ne
  intro h_contra
  simp [h_contra] at h_ne

lemma IsEVar.ae_ne_top (hX : IsEVar X S) {μ : Measure 𝓧} (hμ : μ ∈ S) :
    ∀ᵐ ω ∂μ, X ω ≠ ⊤ := by
  filter_upwards [hX.ae_lt_top hμ] with ω hω using hω.ne

lemma _root_.Measurable.measurable_fsupport (hX : Measurable X) :
    MeasurableSet X.fsupport := by
  suffices MeasurableSet {ω | X ω ≠ ⊤} ∧ MeasurableSet {ω | X ω ≠ 0} from this.1.inter this.2
  constructor <;> exact ((measurableSet_singleton _).preimage hX).compl

lemma IsEVar.measurable_fsupport (hX : IsEVar X S) :
    MeasurableSet X.fsupport := hX.measurable.measurable_fsupport

lemma IsEVar.mono (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (hY : IsEVar Y S) (hX : Measurable X) (hXY : X ≤ Y) : IsEVar X S where
  eintegral_ne_bot μ hμ := eintegral_sub_one_ne_bot_of_isFiniteMeasure hS hμ
  eintegral_nonpos μ hμ := by
    refine (eintegral_mono ?_).trans (hY.eintegral_nonpos μ hμ)
    intro x
    simp only
    refine EReal.sub_le_sub ?_ le_rfl
    exact mod_cast hXY x

lemma IsRandEVar.mono (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (hη : IsRandEVar η S) (hκη : κ ≤ η) : IsRandEVar κ S where
  eintegral_ne_bot μ hμ := eintegral_sub_one_ne_bot_of_isFiniteMeasure hS hμ
  eintegral_nonpos μ hμ := by
    refine le_trans ?_ (hη.eintegral_nonpos μ hμ)
    gcongr
    intro x
    refine EReal.sub_le_sub ?_ le_rfl
    norm_cast
    refine lintegral_mono' ?_ le_rfl
    exact hκη x

lemma IsEVar.anti_set (hST : S ⊆ T) (hX : IsEVar X T) : IsEVar X S where
  measurable := hX.measurable
  eintegral_ne_bot μ hμ := hX.eintegral_ne_bot μ (hST hμ)
  eintegral_nonpos μ hμ := hX.eintegral_nonpos μ (hST hμ)

lemma IsRandEVar.anti_set (hST : S ⊆ T) (hκ : IsRandEVar κ T) : IsRandEVar κ S where
  eintegral_ne_bot μ hμ := hκ.eintegral_ne_bot μ (hST hμ)
  eintegral_nonpos μ hμ := hκ.eintegral_nonpos μ (hST hμ)

lemma IsEVar.comp {Y : 𝓨 → ℝ≥0∞} {S : Set (Measure 𝓧)} {φ : 𝓧 → 𝓨}
    (hφ : Measurable φ) (h : IsEVar Y {μ.map φ | μ ∈ S}) :
    IsEVar (Y ∘ φ) S where
  measurable := h.measurable.comp hφ
  eintegral_ne_bot μ hμ := by
    have h' := h.eintegral_ne_bot (μ.map φ) ⟨μ, hμ, rfl⟩
    have h_meas := h.measurable
    rwa [eintegral_map (by fun_prop) hφ] at h'
  eintegral_nonpos μ hμ := by
    have h' := h.eintegral_nonpos (μ.map φ) ⟨μ, hμ, rfl⟩
    have h_meas := h.measurable
    rwa [eintegral_map (by fun_prop) hφ] at h'

lemma IsRandEVar.comp {ξ : Kernel 𝓨 ℝ≥0∞} {S : Set (Measure 𝓧)}
    {κ : Kernel 𝓧 𝓨} [IsMarkovKernel κ] (h : IsRandEVar ξ {κ ∘ₘ μ | μ ∈ S}) :
    IsRandEVar (ξ ∘ₖ κ) S where
  markov := have := h.markov; inferInstance
  eintegral_ne_bot μ hμ := by
    have h' := h.eintegral_ne_bot (κ ∘ₘ μ) ⟨μ, hμ, rfl⟩
    rw [eintegral_comp_measure] at h'
    rotate_left
    · fun_prop
    · exact eintegrable_of_eintegral_ne_bot h'
    convert h' with ω
    rw [eintegral_sub_of_nonneg]
    rotate_left
    · exact fun _ ↦ by positivity
    · simp
    · fun_prop
    · fun_prop
    · refine ne_top_of_le_ne_top (b := ∫ᵉ x, 1 ∂(κ ω)) ?_ ?_
      · simp
        norm_cast
      · gcongr
        intro x
        exact min_le_right _ _
    simp only [eintegral_const, measure_univ, EReal.coe_ennreal_one, mul_one]
    rw [eintegral_eq_lintegral, Kernel.comp_apply,
      Measure.lintegral_bind (by fun_prop) (by fun_prop)]
  eintegral_nonpos μ hμ := by
    have h' := h.eintegral_nonpos (κ ∘ₘ μ) ⟨μ, hμ, rfl⟩
    rw [eintegral_comp_measure] at h'
    rotate_left
    · fun_prop
    · exact eintegrable_of_eintegral_ne_bot (h.eintegral_ne_bot _ ⟨μ, hμ, rfl⟩)
    refine le_trans ?_ h'
    gcongr
    intro ω
    simp only
    rw [eintegral_sub_of_nonneg]
    rotate_left
    · exact fun _ ↦ by positivity
    · simp
    · fun_prop
    · fun_prop
    · refine ne_top_of_le_ne_top (b := ∫ᵉ x, 1 ∂(κ ω)) ?_ ?_
      · simp
        norm_cast
      · gcongr
        intro x
        exact min_le_right _ _
    simp only [eintegral_const, measure_univ, EReal.coe_ennreal_one, mul_one]
    refine EReal.sub_le_sub ?_ le_rfl
    rw [eintegral_eq_lintegral, Kernel.comp_apply,
      Measure.lintegral_bind (by fun_prop) (by fun_prop)]

/-- The set of e-variables is convex. -/
lemma convex_isEVar (S : Set (Measure 𝓧)) : Convex ℝ≥0∞ {Z | IsEVar Z S} := by
  intro X hX Y hY a b ha hb hab
  simp only [Set.mem_setOf_eq]
  have := hX.measurable
  have := hY.measurable
  have ha_top' : a ≠ ⊤ := by
    by_contra ha_top
    simp [ha_top] at hab
  have ha_top : (a : EReal) ≠ ⊤ := by simp [ha_top']
  have hb_top : (b : EReal) ≠ ⊤ := by
    simp only [ne_eq, EReal.coe_ennreal_eq_top_iff]
    by_contra hb_top
    simp [hb_top] at hab
  have h_eq {μ : Measure 𝓧} (hμ : μ ∈ S) :
      ∫ᵉ ω, (a • X + b • Y) ω - 1 ∂μ = a * ∫ᵉ ω, X ω - 1 ∂μ + b * ∫ᵉ ω, Y ω - 1 ∂μ := by
    calc ∫ᵉ ω, (a • X + b • Y) ω - 1 ∂μ
    _ = ∫ᵉ ω, a • (X ω - 1) + b • (Y ω - 1) ∂μ := by
      congr with ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, EReal.coe_ennreal_add,
        EReal.coe_ennreal_mul, EReal.smul_ennreal_eq_mul]
      rw [EReal.mul_sub_of_nonneg_of_ne_top (by positivity) ha_top,
        EReal.mul_sub_of_nonneg_of_ne_top (by positivity) hb_top]
      simp only [mul_one]
      rw [← EReal.add_sub_add_comm (by simp) (by simp)]
      congr
      norm_cast
      rw [hab]
    _ = a * ∫ᵉ ω, X ω - 1 ∂μ + b * ∫ᵉ ω, Y ω - 1 ∂μ := by
      have := hX.measurable
      have := hY.measurable
      simp only [EReal.smul_ennreal_eq_mul]
      rw [eintegral_add (by fun_prop) (by fun_prop)]
      rotate_left
      · exact (hX.eintegrable_sub_one μ hμ).const_mul (by simp) ha_top
      · exact (hY.eintegrable_sub_one μ hμ).const_mul (by simp) hb_top
      · left
        rw [eintegral_mul_const (by simp) ha_top]
        · rw [ne_eq, EReal.mul_eq_bot]
          have : ¬ (a : EReal) < 0 := by norm_cast; simp
          simp [hX.eintegral_ne_bot μ hμ, ha_top, this]
        · exact hX.eintegrable_sub_one μ hμ
      · right
        rw [eintegral_mul_const (by simp) hb_top]
        · rw [ne_eq, EReal.mul_eq_bot]
          have : ¬ (b : EReal) < 0 := by norm_cast; simp
          simp [hY.eintegral_ne_bot μ hμ, hb_top, this]
        · exact hY.eintegrable_sub_one μ hμ
      rw [eintegral_mul_const (by simp) ha_top, eintegral_mul_const (by simp) hb_top]
      · exact hY.eintegrable_sub_one μ hμ
      · exact hX.eintegrable_sub_one μ hμ
  refine ⟨by fun_prop, fun μ hμ ↦ ?_, fun μ hμ ↦ ?_⟩
  · rw [h_eq hμ]
    have ha_not_lt : ¬ (a : EReal) < 0 := by norm_cast; simp
    have hb_not_lt : ¬ (b : EReal) < 0 := by norm_cast; simp
    simp [EReal.mul_eq_bot, ha_not_lt, hb_not_lt, hX.eintegral_ne_bot μ hμ,
      hY.eintegral_ne_bot μ hμ, ha_top, hb_top]
  · rw [h_eq hμ]
    conv_rhs => rw [← add_zero 0]
    gcongr
    · refine EReal.mul_nonpos_iff.mpr ?_
      norm_cast
      exact .inl ⟨ha, hX.eintegral_nonpos μ hμ⟩
    · refine EReal.mul_nonpos_iff.mpr ?_
      norm_cast
      exact .inl ⟨hb, hY.eintegral_nonpos μ hμ⟩

end ProbabilityTheory
