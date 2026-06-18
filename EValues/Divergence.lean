/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
module

public import EValues.DPI
public import EValues.Product
public import EValues.Mathlib.iSup
public import EValues.Mathlib.unitInterval
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# E-variable divergences

We define analogues of the Rényi and Chernoff divergences for e-variables that share the same
properties as the classical divergences. In particular, they satisfy a data processing inequality.

## Main definitions

* `erenyiDiv α S T`: the e-Rényi divergence of order `α` between two sets of
  measures `S` and `T`.
* `echernoffDiv S T`: the e-Chernoff divergence between two sets of measures `S`
  and `T`.

## Main statements

* `erenyiDiv_comp_le`: data processing inequality for the e-Rényi divergence.
* `echernoffDiv_comp_le`: data processing inequality for the e-Chernoff
  divergence.
* `erenyiDiv_prod`: e-Rényi divergence of product sets of measures is the sum of
  the e-Rényi divergences.
* `echernoffDiv_prod_le`: e-Chernoff divergence of product sets of measures is
  less than the sum of the e-Chernoff divergences.

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {P : Measure 𝓧} [IsProbabilityMeasure P] {S T : Set (Measure 𝓧)}
  {α : ℝ≥0∞}

/-- The e-Rényi divergence between two sets of measures.

Note that the two integrals are non-negative, so the application of `EReal.toENNReal` does not
truncate. -/
noncomputable
def erenyiDiv (α : ℝ≥0∞) (S T : Set (Measure 𝓧)) : ℝ≥0∞ :=
  (1 - α)⁻¹ * ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
    α * (maxUtility R S logUtility).toENNReal + (1 - α) * (maxUtility R T logUtility).toENNReal

lemma erenyiDiv_eq_sInf : erenyiDiv α S T =
    (1 - α)⁻¹ * sInf {y | ∃ R, IsProbabilityMeasure R ∧
    y = α * (maxUtility R S logUtility).toENNReal
      + (1 - α) * (maxUtility R T logUtility).toENNReal} := by
  simp [erenyiDiv, iInf₂_eq_sInf]

lemma erenyiDiv_empty_left {T : Set (Measure 𝓧)} (hα : α ≠ 0) : erenyiDiv α ∅ T = ⊤ := by
  simp only [erenyiDiv_eq_sInf, maxUtility_empty, logUtility_top,
    EReal.toENNReal_mul (by simp : (0 : EReal) ≤ ⊤), EReal.toENNReal_top, EReal.toENNReal_coe]
  have : (1 - α)⁻¹ * ⊤ = ⊤ := ENNReal.mul_top (by simp)
  conv_rhs => rw [← this]
  congr
  have h_eq R [IsProbabilityMeasure R] : α * (⊤ * R Set.univ)
      + (1 - α) * (maxUtility R T logUtility).toENNReal = ⊤ := by
    rw [ENNReal.top_mul (by simp), ENNReal.mul_top hα, top_add]
  by_cases hR_prob : ¬ (∃ (R : Measure 𝓧), IsProbabilityMeasure R)
  · suffices {y | ∃ R, IsProbabilityMeasure R ∧
        y = α * (⊤ * R Set.univ) + (1 - α) * (maxUtility R T logUtility).toENNReal} = ∅ by
      rw [this, sInf_empty]
    simp_all
  · push Not at hR_prob
    suffices {y | ∃ R, IsProbabilityMeasure R ∧
        y = α * (⊤ * R Set.univ) + (1 - α) * (maxUtility R T logUtility).toENNReal} = {⊤} by
      rw [this]
      simp
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨R, hR, rfl⟩ := h
      exact h_eq R
    · obtain ⟨R, hR⟩ := hR_prob
      refine ⟨R, hR, ?_⟩
      rw [h, h_eq R]

lemma erenyiDiv_empty_right {S : Set (Measure 𝓧)} (hα : α < 1) : erenyiDiv α S ∅ = ⊤ := by
  simp only [erenyiDiv_eq_sInf, maxUtility_empty, logUtility_top,
    EReal.toENNReal_mul (by simp : (0 : EReal) ≤ ⊤), EReal.toENNReal_top, EReal.toENNReal_coe]
  have : (1 - α)⁻¹ * ⊤ = ⊤ := ENNReal.mul_top (by simp)
  conv_rhs => rw [← this]
  congr
  have h_eq R [IsProbabilityMeasure R] : α * (maxUtility R S logUtility).toENNReal
      + (1 - α) * (⊤ * R Set.univ) = ⊤ := by
    rw [ENNReal.top_mul (by simp), ENNReal.mul_top, add_top]
    rw [ne_eq, tsub_eq_zero_iff_le]
    exact not_le.mpr hα
  by_cases hR_prob : ¬ (∃ (R : Measure 𝓧), IsProbabilityMeasure R)
  · suffices {y | ∃ R, IsProbabilityMeasure R ∧
        y = α * (maxUtility R S logUtility).toENNReal + (1 - α) * (⊤ * R Set.univ)} = ∅ by
      rw [this, sInf_empty]
    simp_all
  · push Not at hR_prob
    suffices {y | ∃ R, IsProbabilityMeasure R ∧
        y = α * (maxUtility R S logUtility).toENNReal + (1 - α) * (⊤ * R Set.univ)} = {⊤} by
      rw [this]
      simp
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨R, hR, rfl⟩ := h
      exact h_eq R
    · obtain ⟨R, hR⟩ := hR_prob
      refine ⟨R, hR, ?_⟩
      rw [h, h_eq R]

@[simp]
lemma erenyiDiv_empty : erenyiDiv α ∅ ∅ (m𝓧 := m𝓧) = ⊤ := by
  by_cases hα : α = 0
  · rw [hα, erenyiDiv_empty_right (by simp)]
  · rw [erenyiDiv_empty_left hα]

/-- The e-Chernoff divergence between two sets of measures. -/
noncomputable
def echernoffDiv (S T : Set (Measure 𝓧)) : ℝ≥0∞ :=
  ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
    max (maxUtility R S logUtility).toENNReal (maxUtility R T logUtility).toENNReal

lemma echernoffDiv_eq_sInf : echernoffDiv S T =
    sInf {y | ∃ R, IsProbabilityMeasure R ∧
    y = max (maxUtility R S logUtility).toENNReal (maxUtility R T logUtility).toENNReal} :=
  iInf₂_eq_sInf

lemma erenyiDiv_anti {S₁ S₂ T₁ T₂ : Set (Measure 𝓧)} (hS : S₁ ⊆ S₂) (hT : T₁ ⊆ T₂) :
    erenyiDiv α S₂ T₂ ≤ erenyiDiv α S₁ T₁ := by
  unfold erenyiDiv
  gcongr with P hP
  · exact EReal.toENNReal_le_toENNReal <| maxUtility_anti hS
  · exact EReal.toENNReal_le_toENNReal <| maxUtility_anti hT

lemma echernoffDiv_anti {S₁ S₂ T₁ T₂ : Set (Measure 𝓧)} (hS : S₁ ⊆ S₂) (hT : T₁ ⊆ T₂) :
    echernoffDiv S₂ T₂ ≤ echernoffDiv S₁ T₁ := by
  unfold echernoffDiv
  gcongr with P hP
  · exact EReal.toENNReal_le_toENNReal <| maxUtility_anti hS
  · exact EReal.toENNReal_le_toENNReal <| maxUtility_anti hT

/-- Data processing inequality for the e-Rényi divergence with a Markov kernel. -/
lemma erenyiDiv_comp_le (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    erenyiDiv α {κ ∘ₘ μ | μ ∈ S} {κ ∘ₘ μ | μ ∈ T} ≤ erenyiDiv α S T := by
  unfold erenyiDiv
  gcongr 1
  calc
  _ ≤ ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
      α * (maxUtility (κ ∘ₘ R) {κ ∘ₘ μ | μ ∈ S} logUtility).toENNReal +
        (1 - α) * (maxUtility (κ ∘ₘ R) {κ ∘ₘ μ | μ ∈ T} logUtility).toENNReal := by
    rw [iInf₂_eq_sInf, iInf₂_eq_sInf]
    refine sInf_le_sInf fun y ↦ ?_
    rintro ⟨R, hR, rfl⟩
    exact ⟨κ ∘ₘ R, inferInstance, rfl⟩
  _ ≤ ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
      α * (maxUtility R S logUtility).toENNReal +
        (1 - α) * (maxUtility R T logUtility).toENNReal := by
    refine iInf₂_mono fun R _ ↦ add_le_add ?_ ?_
    all_goals
      gcongr 1
      exact EReal.toENNReal_le_toENNReal <| maxUtility_comp_le R κ

/-- Data processing inequality for the e-Rényi divergence with a measurable function. -/
lemma erenyiDiv_map_le {f : 𝓧 → 𝓨} (hf : Measurable f) :
    erenyiDiv α {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} ≤ erenyiDiv α S T := by
  simp_rw [← Measure.deterministic_comp_eq_map hf]
  exact erenyiDiv_comp_le <| Kernel.deterministic f hf

/-- Data processing inequality for the e-Chernoff divergence with a Markov kernel. -/
lemma echernoffDiv_comp_le (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    echernoffDiv {κ ∘ₘ μ | μ ∈ S} {κ ∘ₘ μ | μ ∈ T} ≤ echernoffDiv S T := by
  calc echernoffDiv {κ ∘ₘ μ | μ ∈ S} {κ ∘ₘ μ | μ ∈ T}
  _ ≤ ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R), max
      (maxUtility (κ ∘ₘ R) {κ ∘ₘ μ | μ ∈ S} logUtility).toENNReal
      (maxUtility (κ ∘ₘ R) {κ ∘ₘ μ | μ ∈ T} logUtility).toENNReal := by
    rw [iInf₂_eq_sInf, echernoffDiv_eq_sInf]
    refine sInf_le_sInf fun y ↦ ?_
    rintro ⟨R, hR, rfl⟩
    exact ⟨κ ∘ₘ R, inferInstance, rfl⟩
  _ ≤ echernoffDiv S T := by
    refine iInf₂_mono fun R _ ↦ max_le_max ?_ ?_
    all_goals exact EReal.toENNReal_le_toENNReal <| maxUtility_comp_le R κ

/-- Data processing inequality for the e-Chernoff divergence with a measurable function. -/
lemma echernoffDiv_map_le {f : 𝓧 → 𝓨} (hf : Measurable f) :
    echernoffDiv {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} ≤ echernoffDiv S T := by
  simp_rw [← Measure.deterministic_comp_eq_map hf]
  exact echernoffDiv_comp_le <| Kernel.deterministic f hf

lemma erenyiDiv_add_eq_sInf (S₁ S₂ : Set (Measure 𝓧)) (T₁ T₂ : Set (Measure 𝓨)) :
      (1 - α)⁻¹ * sInf {y | ∃ R₁ R₂,
        IsProbabilityMeasure R₁ ∧ IsProbabilityMeasure R₂ ∧
        y = α * (maxUtility R₁ S₁ logUtility + maxUtility R₂ T₁ logUtility).toENNReal +
            (1 - α) * (maxUtility R₁ S₂ logUtility + maxUtility R₂ T₂ logUtility).toENNReal} =
         erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := by
  calc
  _ = (1 - α)⁻¹ * (sInf {y | ∃ R₁,
                    IsProbabilityMeasure R₁ ∧
                    y = α * (maxUtility R₁ S₁ logUtility).toENNReal +
                        (1 - α) * (maxUtility R₁ S₂ logUtility).toENNReal}
                  +
                    sInf {y | ∃ R₂,
                    IsProbabilityMeasure R₂ ∧
                    y = α * (maxUtility R₂ T₁ logUtility).toENNReal +
                        (1 - α) * (maxUtility R₂ T₂ logUtility).toENNReal}) := by
    congr 1
    rw [← sInf_add']
    congr 1 with y
    constructor
    · rintro ⟨R₁, R₂, hR₁, hR₂, rfl⟩
      rw [Set.mem_add]
      let x := α * (maxUtility R₁ S₁ logUtility).toENNReal +
        (1 - α) * (maxUtility R₁ S₂ logUtility).toENNReal
      let z := α * (maxUtility R₂ T₁ logUtility).toENNReal +
        (1 - α) * (maxUtility R₂ T₂ logUtility).toENNReal
      refine ⟨x, ⟨R₁, hR₁, rfl⟩, z, ⟨R₂, hR₂, rfl⟩, ?_⟩
      rw [EReal.mul_add_ENNReal, EReal.mul_add_ENNReal]
      · ring
      all_goals exact maxUtility_nonneg _
    · rw [Set.mem_add]
      rintro ⟨_, ⟨R₁, hR₁, rfl⟩, _, ⟨R₂, hR₂, rfl⟩, rfl⟩
      refine ⟨R₁, R₂, hR₁, hR₂, ?_⟩
      rw [EReal.mul_add_ENNReal, EReal.mul_add_ENNReal]
      · ring
      all_goals exact maxUtility_nonneg _
  _ = erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := by
    rw [erenyiDiv_eq_sInf, erenyiDiv_eq_sInf]
    ring

lemma erenyiDiv_prod_le {S₁ S₂ : Set (Measure 𝓧)} {T₁ T₂ : Set (Measure 𝓨)}
    (hS₁ : ∀ μ ∈ S₁, IsFiniteMeasure μ) (hS₂ : ∀ μ ∈ S₂, IsFiniteMeasure μ)
    (hT₁ : ∀ μ ∈ T₁, IsFiniteMeasure μ) (hT₂ : ∀ μ ∈ T₂, IsFiniteMeasure μ) :
    erenyiDiv α (Measure.prod.uncurry '' (S₁ ×ˢ T₁)) (Measure.prod.uncurry '' (S₂ ×ˢ T₂))
      ≤ erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := by
  set ST₁ := Measure.prod.uncurry '' (S₁ ×ˢ T₁)
  set ST₂ := Measure.prod.uncurry '' (S₂ ×ˢ T₂)
  calc
  _ ≤ (1 - α)⁻¹ * sInf {y | ∃ R₁ R₂,
      IsProbabilityMeasure R₁ ∧ IsProbabilityMeasure R₂ ∧
      y = α * (maxUtility (R₁.prod R₂) ST₁ logUtility).toENNReal +
          (1 - α) * (maxUtility (R₁.prod R₂) ST₂ logUtility).toENNReal} := by
    rw [erenyiDiv_eq_sInf]
    gcongr 1
    refine sInf_le_sInf fun y ↦ ?_
    rintro ⟨R₁, R₂, hR₁, hR₂, rfl⟩
    exact ⟨R₁.prod R₂, inferInstance, rfl⟩
  _ = (1 - α)⁻¹ * sInf {y | ∃ R₁ R₂,
      IsProbabilityMeasure R₁ ∧ IsProbabilityMeasure R₂ ∧
      y = α * (maxUtility R₁ S₁ logUtility + maxUtility R₂ T₁ logUtility).toENNReal +
          (1 - α) * (maxUtility R₁ S₂ logUtility + maxUtility R₂ T₂ logUtility).toENNReal} := by
    congr with y
    constructor
    · rintro ⟨R₁, R₂, hR₁, hR₂, rfl⟩
      rw [maxUtility_prod _ _ hS₁ (fun μ hμ ↦  by have := hT₁ μ hμ; infer_instance),
        maxUtility_prod _ _ hS₂ (fun μ hμ ↦  by have := hT₂ μ hμ; infer_instance)]
      exact ⟨R₁, R₂, hR₁, hR₂, rfl⟩
    · rintro ⟨R₁, R₂, hR₁, hR₂, rfl⟩
      rw [← maxUtility_prod _ _ hS₁ (fun μ hμ ↦  by have := hT₁ μ hμ; infer_instance),
        ← maxUtility_prod _ _ hS₂ (fun μ hμ ↦  by have := hT₂ μ hμ; infer_instance)]
      exact ⟨R₁, R₂, hR₁, hR₂, rfl⟩
  _ = erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := erenyiDiv_add_eq_sInf _ _ _ _

lemma erenyiDiv_prod {S₁ S₂ : Set (Measure 𝓧)} {T₁ T₂ : Set (Measure 𝓨)}
    (hS₁ : ∀ μ ∈ S₁, IsFiniteMeasure μ) (hS₂ : ∀ μ ∈ S₂, IsFiniteMeasure μ)
    (hT₁ : ∀ μ ∈ T₁, IsFiniteMeasure μ) (hT₂ : ∀ μ ∈ T₂, IsFiniteMeasure μ) :
    erenyiDiv α (Measure.prod.uncurry '' (S₁ ×ˢ T₁)) (Measure.prod.uncurry '' (S₂ ×ˢ T₂))
      = erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := by
  set ST₁ := Measure.prod.uncurry '' (S₁ ×ˢ T₁)
  set ST₂ := Measure.prod.uncurry '' (S₂ ×ˢ T₂)
  refine le_antisymm (erenyiDiv_prod_le hS₁ hS₂ hT₁ hT₂) ?_
  calc
    _ ≥ (1 - α)⁻¹ * ⨅ (R : Measure (𝓧 × 𝓨)) (_ : IsProbabilityMeasure R),
        α * (⨆ (X : 𝓧 → ℝ≥0∞) (Y : 𝓨 → ℝ≥0∞)
            (_ : NeBotUtilityEVar X (R.map Prod.fst) S₁ logUtility)
            (_ : NeBotUtilityEVar Y (R.map Prod.snd) T₁ logUtility),
              ∫ᵉ x, (logUtility ∘ (fun x ↦ X x.1 * Y x.2)) x ∂R).toENNReal +
          (1 - α) * (⨆ (X : 𝓧 → ℝ≥0∞) (Y : 𝓨 → ℝ≥0∞)
          (_ : NeBotUtilityEVar X (R.map Prod.fst) S₂ logUtility)
          (_ : NeBotUtilityEVar Y (R.map Prod.snd) T₂ logUtility),
              ∫ᵉ x, (logUtility ∘ (fun x ↦ X x.1 * Y x.2)) x ∂R).toENNReal := by
      unfold erenyiDiv
      gcongr 1
      refine iInf₂_mono fun R _ ↦ add_le_add ?_ ?_
      · gcongr 1
        exact EReal.toENNReal_le_toENNReal <| iSup_prod_le_maxUtility _ hS₁ hT₁
      · gcongr 1
        exact EReal.toENNReal_le_toENNReal <| iSup_prod_le_maxUtility _ hS₂ hT₂
    _ = (1 - α)⁻¹ * ⨅ (R) (_ : IsProbabilityMeasure R),
        α * (maxUtility (R.map Prod.fst) S₁ logUtility
            + maxUtility (R.map Prod.snd) T₁ logUtility).toENNReal +
          (1 - α) * (maxUtility (R.map Prod.fst) S₂ logUtility
            + maxUtility (R.map Prod.snd) T₂ logUtility).toENNReal := by
      congr with R
      congr with hR
      set R₁ := R.map Prod.fst
      set R₂ := R.map Prod.snd
      have : IsProbabilityMeasure R₁ := R.isProbabilityMeasure_map measurable_fst.aemeasurable
      have : IsProbabilityMeasure R₂ := R.isProbabilityMeasure_map measurable_snd.aemeasurable
      have sup_prod_sum (S : Set (Measure 𝓧)) (T : Set (Measure 𝓨)) :
          ⨆ X, ⨆ Y, ⨆ (_ : NeBotUtilityEVar X R₁ S logUtility),
            ⨆ (_ : NeBotUtilityEVar Y R₂ T logUtility),
            ∫ᵉ x, (logUtility ∘ fun x ↦ X x.1 * Y x.2) x ∂R =
          ⨆ X, ⨆ Y, ⨆ (_ : NeBotUtilityEVar X R₁ S logUtility),
            ⨆ (_ : NeBotUtilityEVar Y R₂ T logUtility),
            ∫ᵉ x, (logUtility ∘ X) x ∂R₁ + ∫ᵉ x, (logUtility ∘ Y) x ∂R₂ := by
        congr with X
        congr with Y
        congr with hX
        congr with hY
        have := hX.measurable
        have := hY.measurable
        have hXY1 : ∫ᵉ (x : 𝓧 × 𝓨), (X x.1).log ∂R ≠ ⊥ := by
          have hXe := hX.utility_ne_bot
          simp only [logUtility, Function.comp_apply] at hXe
          rwa [eintegral_map (by fun_prop) measurable_fst] at hXe
        have hXY2 : ∫ᵉ (x : 𝓧 × 𝓨), (Y x.2).log ∂R ≠ ⊥ := by
          have hXe := hY.utility_ne_bot
          simp only [logUtility, Function.comp_apply] at hXe
          rwa [eintegral_map (by fun_prop) measurable_snd] at hXe
        calc
        _ = ∫ᵉ x, logUtility (X x.1) ∂R + ∫ᵉ x, logUtility (Y x.2) ∂R := by
          simp_rw [logUtility, Function.comp, ENNReal.log_mul_add]
          rw [eintegral_add (by fun_prop) (by fun_prop)]
          · have hXe := hX.utility_ne_bot
            refine eintegrable_of_eintegral_ne_bot ?_
            rwa [eintegral_map (by fun_prop) measurable_fst] at hXe
          · have hYe := hY.utility_ne_bot
            refine eintegrable_of_eintegral_ne_bot ?_
            rwa [eintegral_map (by fun_prop) measurable_snd] at hYe
          · exact Or.inl hXY1
          · exact Or.inr hXY2
        _ = ∫ᵉ x, logUtility (X x) ∂R₁ + ∫ᵉ x, logUtility (Y x) ∂R₂ := by
            congr <;> rw [eintegral_map (by fun_prop) (by fun_prop)]
      congr
      · rw [sup_prod_sum S₁ T₁, ← exists_iSup₂_EReal_add,
            ← maxUtility_eq_iSup_neBotUtilityEVar, ← maxUtility_eq_iSup_neBotUtilityEVar]
        · exact neBotUtilityEVar_numeraire hS₁
        · exact numeraire R₂ T₁
        · exact neBotUtilityEVar_numeraire hT₁
        · rw [← maxUtility_eq_iSup_neBotUtilityEVar, maxUtility_eq_integral_numeraire R₁ hS₁]
          rfl
        · rw [← maxUtility_eq_iSup_neBotUtilityEVar, maxUtility_eq_integral_numeraire R₂ hT₁]
          rfl
      · rw [sup_prod_sum S₂ T₂, ← exists_iSup₂_EReal_add,
            ← maxUtility_eq_iSup_neBotUtilityEVar, ← maxUtility_eq_iSup_neBotUtilityEVar]
        · exact neBotUtilityEVar_numeraire hS₂
        · exact numeraire R₂ T₂
        · exact neBotUtilityEVar_numeraire hT₂
        · rw [← maxUtility_eq_iSup_neBotUtilityEVar, maxUtility_eq_integral_numeraire R₁ hS₂]
          rfl
        · rw [← maxUtility_eq_iSup_neBotUtilityEVar, maxUtility_eq_integral_numeraire R₂ hT₂]
          rfl
    _ = (1 - α)⁻¹ * sInf {y | ∃ R₁ R₂,
        IsProbabilityMeasure R₁ ∧ IsProbabilityMeasure R₂ ∧
        y = α * (maxUtility R₁ S₁ logUtility + maxUtility R₂ T₁ logUtility).toENNReal +
            (1 - α) * (maxUtility R₁ S₂ logUtility + maxUtility R₂ T₂ logUtility).toENNReal} := by
      congr
      rw [iInf₂_eq_sInf]
      congr with y
      constructor
      · rintro ⟨R, hR, rfl⟩
        refine ⟨R.map Prod.fst, R.map Prod.snd, ?_, ?_, rfl⟩
        · exact R.isProbabilityMeasure_map measurable_fst.aemeasurable
        · exact R.isProbabilityMeasure_map measurable_snd.aemeasurable
      · rintro ⟨R₁, R₂, hR₁, hR₂, rfl⟩
        refine ⟨R₁.prod R₂, inferInstance, ?_⟩
        simp
    _ = erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := erenyiDiv_add_eq_sInf _ _ _ _

lemma echernoffDiv_prod_le {S₁ S₂ : Set (Measure 𝓧)} {T₁ T₂ : Set (Measure 𝓨)}
    (hS₁ : ∀ μ ∈ S₁, IsFiniteMeasure μ) (hS₂ : ∀ μ ∈ S₂, IsFiniteMeasure μ)
    (hT₁ : ∀ μ ∈ T₁, IsFiniteMeasure μ) (hT₂ : ∀ μ ∈ T₂, IsFiniteMeasure μ) :
    echernoffDiv (Measure.prod.uncurry '' (S₁ ×ˢ T₁)) (Measure.prod.uncurry '' (S₂ ×ˢ T₂))
      ≤ echernoffDiv S₁ S₂ + echernoffDiv T₁ T₂ := by
  calc
  _ ≤ sInf {y | ∃ R₁ R₂, IsProbabilityMeasure R₁ ∧ IsProbabilityMeasure R₂ ∧
      y = max (maxUtility (R₁.prod R₂) (Measure.prod.uncurry '' (S₁ ×ˢ T₁)) logUtility).toENNReal
        (maxUtility (R₁.prod R₂) (Measure.prod.uncurry '' (S₂ ×ˢ T₂)) logUtility).toENNReal} := by
      rw [echernoffDiv_eq_sInf]
      refine sInf_le_sInf fun y ↦ ?_
      rintro ⟨R₁, R₂, hR₁, hR₂, rfl⟩
      exact ⟨R₁.prod R₂, inferInstance, rfl⟩
  _ ≤ sInf {y | ∃ R₁ R₂, IsProbabilityMeasure R₁ ∧ IsProbabilityMeasure R₂ ∧
      y = max (maxUtility R₁ S₁ logUtility + maxUtility R₂ T₁ logUtility).toENNReal
        (maxUtility R₁ S₂ logUtility + maxUtility R₂ T₂ logUtility).toENNReal} := by
      refine sInf_le_sInf fun y ↦ ?_
      rintro ⟨R₁, R₂, hR₁, hR₂, rfl⟩
      refine ⟨R₁, R₂, hR₁, hR₂, ?_⟩
      rw [maxUtility_prod _ _ hS₁ (fun μ hμ ↦  by have := hT₁ μ hμ; infer_instance),
        maxUtility_prod _ _ hS₂ (fun μ hμ ↦  by have := hT₂ μ hμ; infer_instance)]
  _ ≤ echernoffDiv S₁ S₂ + echernoffDiv T₁ T₂ := by
    rw [← iInf₄_eq_sInf, echernoffDiv, echernoffDiv, iInf₂_add]
    refine iInf₂_mono fun R₁ R₂ ↦ iInf₂_mono fun hR₁ hR₂ ↦ ?_
    rw [EReal.toENNReal_add, EReal.toENNReal_add]
    · exact max_add_add_le_max_add_max
    all_goals exact maxUtility_nonneg _

lemma erenyiDiv_of_involutive_aux {S T : Set (Measure 𝓧)}
    {φ : 𝓧 → 𝓧} (hφ : Measurable φ) (hφ_inv : φ ∘ φ = id)
    (hφST : {μ.map φ | μ ∈ S} = T) :
    erenyiDiv 2⁻¹ S T = 2 *
      ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R) (_ : R.map φ = R),
        (2 : ℝ≥0∞)⁻¹ * (maxUtility R S logUtility).toENNReal
        + (2 : ℝ≥0∞)⁻¹ * (maxUtility R T logUtility).toENNReal := by
  rw [erenyiDiv, iInf₃_eq_sInf, iInf₂_eq_sInf]
  congr 1
  · simp
  apply le_antisymm
  · refine sInf_le_sInf fun y hy ↦ ?_
    simp only [Set.mem_setOf_eq] at hy ⊢
    obtain ⟨R, hR, hRφ, rfl⟩ := hy
    refine ⟨R, hR, ?_⟩
    simp only [ENNReal.one_sub_inv_two]
  · refine sInf_le_sInf_of_isCoinitialFor fun y hy ↦ ?_
    simp only [Set.mem_setOf_eq] at hy ⊢
    obtain ⟨R, hR, rfl⟩ := hy
    let R' := (2 : ℝ≥0∞)⁻¹ • (R + R.map φ)
    have hR' : IsProbabilityMeasure R' := by
      constructor
      have : IsProbabilityMeasure (R.map φ) := R.isProbabilityMeasure_map hφ.aemeasurable
      simpa [R'] using ENNReal.add_halves 1
    have hR'φ : R'.map φ = R' := by
      unfold R'
      rw [Measure.map_smul, Measure.map_add _ _ (by fun_prop), Measure.map_map hφ hφ,
        hφ_inv, Measure.map_id, add_comm]
    refine ⟨(2 : ℝ≥0∞)⁻¹ * (maxUtility R' S logUtility).toENNReal
      + (2 : ℝ≥0∞)⁻¹ * (maxUtility R' T logUtility).toENNReal, ⟨R', hR', hR'φ, rfl⟩, ?_⟩
    simp only [ENNReal.one_sub_inv_two]
    calc (2 : ℝ≥0∞)⁻¹ * (maxUtility R' S logUtility).toENNReal
        + (2 : ℝ≥0∞)⁻¹ * (maxUtility R' T logUtility).toENNReal
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹ * maxUtility R S logUtility
          + (2 : ℝ≥0∞)⁻¹ * maxUtility (R.map φ) S logUtility).toENNReal
        + (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹ * maxUtility R T logUtility
          + (2 : ℝ≥0∞)⁻¹ * maxUtility (R.map φ) T logUtility).toENNReal := by
      gcongr
      · refine EReal.toENNReal_le_toENNReal ?_
        have h_conv := (convexOn_maxUtility S (U := logUtility)).2 (by simp : R ∈ Set.univ)
          (by simp : R.map φ ∈ Set.univ) (zero_le : 0 ≤ (2 : ℝ≥0∞)⁻¹)
          (zero_le : 0 ≤ (2 : ℝ≥0∞)⁻¹) (by simpa using ENNReal.add_halves 1)
        unfold R'
        rwa [smul_add]
      · refine EReal.toENNReal_le_toENNReal ?_
        have h_conv := (convexOn_maxUtility T (U := logUtility)).2 (by simp : R ∈ Set.univ)
          (by simp : R.map φ ∈ Set.univ) (zero_le : 0 ≤ (2 : ℝ≥0∞)⁻¹)
          (zero_le : 0 ≤ (2 : ℝ≥0∞)⁻¹) (by simpa using ENNReal.add_halves 1)
        unfold R'
        rwa [smul_add]
    _ = (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹ * maxUtility R S logUtility
          + (2 : ℝ≥0∞)⁻¹ * maxUtility R T logUtility).toENNReal
        + (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹ * maxUtility R T logUtility
          + (2 : ℝ≥0∞)⁻¹ * maxUtility R S logUtility).toENNReal := by
      congr 5
      · rw [← maxUtility_involutive _ _ hφ hφ_inv, hφST]
      · rw [← hφST, maxUtility_involutive _ _ hφ hφ_inv, Measure.map_map hφ hφ, hφ_inv,
          Measure.map_id]
    _ = ((2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹)
          * (maxUtility R S logUtility).toENNReal
        + ((2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹)
          * (maxUtility R T logUtility).toENNReal := by
      simp_rw [add_mul]
      have h_eq : ((((2 : ℝ≥0∞)⁻¹ : ℝ≥0∞) : EReal)).toENNReal = (2 : ℝ≥0∞)⁻¹ := by
        rw [EReal.toENNReal_coe]
      rw [EReal.toENNReal_add, EReal.toENNReal_add, EReal.toENNReal_mul, EReal.toENNReal_mul]
      rotate_left
      · positivity
      · positivity
      · exact mul_nonneg (by positivity) (maxUtility_nonneg _)
      · exact mul_nonneg (by positivity) (maxUtility_nonneg _)
      · exact mul_nonneg (by positivity) (maxUtility_nonneg _)
      · exact mul_nonneg (by positivity) (maxUtility_nonneg _)
      simp_rw [h_eq]
      ring
    _ = (2 : ℝ≥0∞)⁻¹ * (maxUtility R S logUtility).toENNReal
        + (2 : ℝ≥0∞)⁻¹ * (maxUtility R T logUtility).toENNReal := by
      rw [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

lemma erenyiDiv_of_involutive {S T : Set (Measure 𝓧)} {φ : 𝓧 → 𝓧} (hφ : Measurable φ)
    (hφ_inv : φ ∘ φ = id)
    (hφST : {μ.map φ | μ ∈ S} = T) :
    erenyiDiv 2⁻¹ S T = 2 *
      ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R) (_ : R.map φ = R),
        (maxUtility R S logUtility).toENNReal := by
  rw [erenyiDiv_of_involutive_aux hφ hφ_inv hφST]
  congr with R
  congr with hR
  congr with hRφ
  rw [← hφST, maxUtility_involutive _ _ hφ hφ_inv, hRφ, ← add_mul]
  have h_eq := ENNReal.add_halves 1
  simp only [one_div] at h_eq
  simp [h_eq]

lemma echernoffDiv_of_involutive_aux {S T : Set (Measure 𝓧)}
    {φ : 𝓧 → 𝓧} (hφ : Measurable φ) (hφ_inv : φ ∘ φ = id)
    (hφST : {μ.map φ | μ ∈ S} = T) :
    echernoffDiv S T =
      ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R) (_ : R.map φ = R),
        max (maxUtility R S logUtility).toENNReal (maxUtility R T logUtility).toENNReal := by
  rw [echernoffDiv, iInf₃_eq_sInf, iInf₂_eq_sInf]
  apply le_antisymm
  · refine sInf_le_sInf fun y hy ↦ ?_
    simp only [Set.mem_setOf_eq] at hy ⊢
    obtain ⟨R, hR, hRφ, rfl⟩ := hy
    refine ⟨R, hR, ?_⟩
    simp
  · refine sInf_le_sInf_of_isCoinitialFor fun y hy ↦ ?_
    simp only [Set.mem_setOf_eq] at hy ⊢
    obtain ⟨R, hR, rfl⟩ := hy
    let R' := (2 : ℝ≥0∞)⁻¹ • (R + R.map φ)
    have hR' : IsProbabilityMeasure R' := by
      constructor
      have : IsProbabilityMeasure (R.map φ) := R.isProbabilityMeasure_map hφ.aemeasurable
      simpa [R'] using ENNReal.add_halves 1
    have hR'φ : R'.map φ = R' := by
      unfold R'
      rw [Measure.map_smul, Measure.map_add _ _ (by fun_prop), Measure.map_map hφ hφ,
        hφ_inv, Measure.map_id, add_comm]
    refine ⟨max (maxUtility R' S logUtility).toENNReal
      (maxUtility R' T logUtility).toENNReal, ⟨R', hR', hR'φ, rfl⟩, ?_⟩
    calc max (maxUtility R' S logUtility).toENNReal (maxUtility R' T logUtility).toENNReal
    _ ≤ max ((2 : ℝ≥0∞)⁻¹ * maxUtility R S logUtility
          + (2 : ℝ≥0∞)⁻¹ * maxUtility (R.map φ) S logUtility).toENNReal
        ((2 : ℝ≥0∞)⁻¹ * maxUtility R T logUtility
          + (2 : ℝ≥0∞)⁻¹ * maxUtility (R.map φ) T logUtility).toENNReal := by
      gcongr
      · refine EReal.toENNReal_le_toENNReal ?_
        have h_conv := (convexOn_maxUtility S (U := logUtility)).2 (by simp : R ∈ Set.univ)
          (by simp : R.map φ ∈ Set.univ) (zero_le : 0 ≤ (2 : ℝ≥0∞)⁻¹)
          (zero_le : 0 ≤ (2 : ℝ≥0∞)⁻¹) (by simpa using ENNReal.add_halves 1)
        unfold R'
        rwa [smul_add]
      · refine EReal.toENNReal_le_toENNReal ?_
        have h_conv := (convexOn_maxUtility T (U := logUtility)).2 (by simp : R ∈ Set.univ)
          (by simp : R.map φ ∈ Set.univ) (zero_le : 0 ≤ (2 : ℝ≥0∞)⁻¹)
          (zero_le : 0 ≤ (2 : ℝ≥0∞)⁻¹) (by simpa using ENNReal.add_halves 1)
        unfold R'
        rwa [smul_add]
    _ ≤ max ((2 : ℝ≥0∞)⁻¹ * max (maxUtility R S logUtility) (maxUtility R T logUtility)
          + (2 : ℝ≥0∞)⁻¹ *
            max (maxUtility (R.map φ) S logUtility) (maxUtility (R.map φ) T logUtility)).toENNReal
        ((2 : ℝ≥0∞)⁻¹ * max (maxUtility R S logUtility) (maxUtility R T logUtility)
          + (2 : ℝ≥0∞)⁻¹ *
            max (maxUtility (R.map φ) S logUtility)
              (maxUtility (R.map φ) T logUtility)).toENNReal := by
      gcongr
      · refine EReal.toENNReal_le_toENNReal ?_
        gcongr
        · exact le_max_left _ _
        · exact le_max_left _ _
      · refine EReal.toENNReal_le_toENNReal ?_
        gcongr
        · exact le_max_right _ _
        · exact le_max_right _ _
    _ = ((2 : ℝ≥0∞)⁻¹ * max (maxUtility R S logUtility) (maxUtility R T logUtility)
          + (2 : ℝ≥0∞)⁻¹ * max (maxUtility (R.map φ) S logUtility)
            (maxUtility (R.map φ) T logUtility)).toENNReal := by
      simp
    _ = ((2 : ℝ≥0∞)⁻¹ * max (maxUtility R S logUtility) (maxUtility R T logUtility)
          + (2 : ℝ≥0∞)⁻¹ * max (maxUtility R S logUtility)
            (maxUtility R T logUtility)).toENNReal := by
      rw [max_comm]
      congr 4
      · rw [← maxUtility_involutive _ _ hφ hφ_inv, hφST]
      · rw [← hφST, maxUtility_involutive _ _ hφ hφ_inv, Measure.map_map hφ hφ, hφ_inv,
          Measure.map_id]
    _ = (2 : ℝ≥0∞)⁻¹ * (max (maxUtility R S logUtility) (maxUtility R T logUtility)).toENNReal
          + (2 : ℝ≥0∞)⁻¹ * (max (maxUtility R S logUtility)
            (maxUtility R T logUtility)).toENNReal := by
      have := maxUtility_nonneg R (S := S)
      have := maxUtility_nonneg R (S := T)
      rw [EReal.toENNReal_add (by positivity) (by positivity), EReal.toENNReal_mul (by positivity),
        EReal.toENNReal_coe]
    _ = (max (maxUtility R S logUtility) (maxUtility R T logUtility)).toENNReal := by
      rw [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
    _ = max (maxUtility R S logUtility).toENNReal (maxUtility R T logUtility).toENNReal := by
      rcases le_total (maxUtility R S logUtility) (maxUtility R T logUtility) with hle | hle
      · simp only [hle, sup_of_le_right, right_eq_sup]
        exact EReal.toENNReal_le_toENNReal hle
      · simp only [hle, sup_of_le_left, left_eq_sup]
        exact EReal.toENNReal_le_toENNReal hle

lemma echernoffDiv_of_involutive {S T : Set (Measure 𝓧)} {φ : 𝓧 → 𝓧} (hφ : Measurable φ)
    (hφ_inv : φ ∘ φ = id)
    (hφST : {μ.map φ | μ ∈ S} = T) :
    echernoffDiv S T =
      ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R) (_ : R.map φ = R),
        (maxUtility R S logUtility).toENNReal := by
  rw [echernoffDiv_of_involutive_aux hφ hφ_inv hφST]
  congr with R
  congr with hR
  congr with hRφ
  rw [← hφST, maxUtility_involutive _ _ hφ hφ_inv, hRφ, max_self]

lemma erenyiDiv_eq_two_mul_echernoffDiv_of_involutive {S T : Set (Measure 𝓧)} {φ : 𝓧 → 𝓧}
    (hφ : Measurable φ) (hφ_inv : φ ∘ φ = id)
    (hφST : {μ.map φ | μ ∈ S} = T) :
    erenyiDiv 2⁻¹ S T = 2 * echernoffDiv S T := by
  rw [erenyiDiv_of_involutive hφ hφ_inv hφST,
    echernoffDiv_of_involutive hφ hφ_inv hφST]

end ProbabilityTheory
