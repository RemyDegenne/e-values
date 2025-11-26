/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
import EValues.DPI
import EValues.Product
import EValues.Mathlib.iSup
import EValues.Mathlib.unitInterval
import Mathlib.MeasureTheory.Measure.GiryMonad
import EValues.FindAxioms

/-!
# E-Rényi divergence

An analogue of the Rényi and Chernoff divergences defined via maximal utilities of e-variables.

## Main definitions

* `ProbabilityTheory.erenyiDiv`: the e-Rényi divergence between two sets of measures, written in
  terms of maximal logarithmic utilities.
* `ProbabilityTheory.echernoffDiv`: the corresponding e-Chernoff divergence (order `∞`).
* `erenyiDiv_eq_sInf` / `echernoffDiv_eq_sInf`: infimum representations used to prove structural
  results.

## Main statements

* Monotonicity and data-processing lemmas such as `erenyiDiv_anti`, `echernoffDiv_anti`,
  `erenyiDiv_comp_le`, and `echernoffDiv_comp_le`.
* `erenyiDiv_add_eq_sInf` rewrites the divergence of products as a sum of divergences of the
  components.
* `erenyiDiv_prod` (and the analogous statements for `echernoffDiv`) identifies the divergence of
  product sets with the sum of the divergences of the factors.

-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {P : Measure 𝓧} [IsProbabilityMeasure P] {S T : Set (Measure 𝓧)}
  {α : ℝ≥0∞}

/-- The e-Rényi divergence between two sets of measures.

Note that the two maximal utilities are non-negative, so the application of `EReal.toENNReal`
does not truncate. -/
noncomputable
def erenyiDiv (α : ℝ≥0∞) (S T : Set (Measure 𝓧)) : ℝ≥0∞ :=
  (1 - α)⁻¹ * ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
    α * (maxUtility R S logUtility).toENNReal + (1 - α) * (maxUtility R T logUtility).toENNReal

lemma erenyiDiv_eq_sInf : erenyiDiv α S T =
    (1 - α)⁻¹ * sInf {y | ∃ R, IsProbabilityMeasure R ∧
    y = α * (maxUtility R S logUtility).toENNReal
      + (1 - α) * (maxUtility R T logUtility).toENNReal} := by
  simp [erenyiDiv, iInf₂_eq_sInf]

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


/-- Data processing inequality for the e-Rényi divergence. -/
lemma erenyiDiv_map_le {f : 𝓧 → 𝓨} (hf : Measurable f) :
    erenyiDiv α {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} ≤ erenyiDiv α S T := by
  simp_rw [← Measure.deterministic_comp_eq_map hf]
  exact erenyiDiv_comp_le <| Kernel.deterministic f hf

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

/-- Data processing inequality for the e-Chernoff divergence. -/
lemma echernoffDiv_map_le {f : 𝓧 → 𝓨} (hf : Measurable f) :
    echernoffDiv {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} ≤ echernoffDiv S T := by
  simp_rw [← Measure.deterministic_comp_eq_map hf]
  exact echernoffDiv_comp_le <| Kernel.deterministic f hf

lemma erenyiDiv_add_eq_sInf {S₁ S₂ : Set (Measure 𝓧)} {T₁ T₂ : Set (Measure 𝓨)}
    (hS₁ : ∀ μ ∈ S₁, IsProbabilityMeasure μ) (hS₂ : ∀ μ ∈ S₂, IsProbabilityMeasure μ)
    (hT₁ : ∀ μ ∈ T₁, IsProbabilityMeasure μ) (hT₂ : ∀ μ ∈ T₂, IsProbabilityMeasure μ) :
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
      · exact maxUtility_nonneg _ hS₂
      · exact maxUtility_nonneg _ hT₂
      · exact maxUtility_nonneg _ hS₁
      · exact maxUtility_nonneg _ hT₁
    · rw [Set.mem_add]
      rintro ⟨_, ⟨R₁, hR₁, rfl⟩, _, ⟨R₂, hR₂, rfl⟩, rfl⟩
      refine ⟨R₁, R₂, hR₁, hR₂, ?_⟩
      rw [EReal.mul_add_ENNReal, EReal.mul_add_ENNReal]
      · ring
      · exact maxUtility_nonneg _ hS₂
      · exact maxUtility_nonneg _ hT₂
      · exact maxUtility_nonneg _ hS₁
      · exact maxUtility_nonneg _ hT₁
  _ = erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := by
    rw [erenyiDiv_eq_sInf, erenyiDiv_eq_sInf]
    ring

lemma erenyiDiv_prod {S₁ S₂ : Set (Measure 𝓧)} {T₁ T₂ : Set (Measure 𝓨)}
    (hS₁ : ∀ μ ∈ S₁, IsProbabilityMeasure μ) (hS₂ : ∀ μ ∈ S₂, IsProbabilityMeasure μ)
    (hT₁ : ∀ μ ∈ T₁, IsProbabilityMeasure μ) (hT₂ : ∀ μ ∈ T₂, IsProbabilityMeasure μ) :
    erenyiDiv α (Measure.prod.uncurry '' (S₁ ×ˢ T₁)) (Measure.prod.uncurry '' (S₂ ×ˢ T₂))
      = erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := by
  set ST₁ := Measure.prod.uncurry '' (S₁ ×ˢ T₁)
  set ST₂ := Measure.prod.uncurry '' (S₂ ×ˢ T₂)
  refine le_antisymm ?_ ?_
  · calc
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
        rw [maxUtility_prod _ _ hS₁ hT₁, maxUtility_prod _ _ hS₂ hT₂]
        exact ⟨R₁, R₂, hR₁, hR₂, rfl⟩
      · rintro ⟨R₁, R₂, hR₁, hR₂, rfl⟩
        rw [← maxUtility_prod _ _ hS₁ hT₁, ← maxUtility_prod _ _ hS₂ hT₂]
        exact ⟨R₁, R₂, hR₁, hR₂, rfl⟩
    _ = erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := erenyiDiv_add_eq_sInf hS₁ hS₂ hT₁ hT₂

  · calc
    _ ≥ (1 - α)⁻¹ * ⨅ (R : Measure (𝓧 × 𝓨)) (_ : IsProbabilityMeasure R),
        α * (⨆ (X : 𝓧 → ℝ≥0∞) (Y : 𝓨 → ℝ≥0∞) (_ : IsEVar X S₁) (_ : IsEVar Y T₁),
              ∫ᵉ x, (logUtility ∘ (fun x ↦ X x.1 * Y x.2)) x ∂R).toENNReal +
          (1 - α) * (⨆ (X : 𝓧 → ℝ≥0∞) (Y : 𝓨 → ℝ≥0∞) (_ : IsEVar X S₂) (_ : IsEVar Y T₂),
              ∫ᵉ x, (logUtility ∘ (fun x ↦ X x.1 * Y x.2)) x ∂R).toENNReal := by
      unfold erenyiDiv
      gcongr 1
      refine iInf₂_mono fun R _ ↦ add_le_add ?_ ?_
      · gcongr 1
        exact EReal.toENNReal_le_toENNReal <| iSup_prod_le_maxUtility _ hT₁
      · gcongr 1
        exact EReal.toENNReal_le_toENNReal <| iSup_prod_le_maxUtility _ hT₂
    _ = (1 - α)⁻¹ * ⨅ (R) (_ : IsProbabilityMeasure R),
        α * (maxUtility (R.map Prod.fst) S₁ logUtility
            + maxUtility (R.map Prod.snd) T₁ logUtility).toENNReal +
          (1 - α) * (maxUtility (R.map Prod.fst) S₂ logUtility
            + maxUtility (R.map Prod.snd) T₂ logUtility).toENNReal := by
      congr with R
      congr with hR
      set R₁ := R.map Prod.fst
      set R₂ := R.map Prod.snd

      have sup_prod_sum : ∀ (S : Set (Measure 𝓧)) (T : Set (Measure 𝓨)),
          ⨆ X, ⨆ Y, ⨆ (_ : IsEVar X S), ⨆ (_ : IsEVar Y T),
            ∫ᵉ x, (logUtility ∘ fun x ↦ X x.1 * Y x.2) x ∂R =
          ⨆ X, ⨆ Y, ⨆ (_ : IsEVar X S), ⨆ (_ : IsEVar Y T),
            ∫ᵉ x, logUtility (X x) ∂R₁ + ∫ᵉ x, logUtility (Y x) ∂R₂ := by
        intro S T
        congr with X
        congr with Y
        congr with hX
        congr with hY
        calc
        _ = ∫ᵉ x, logUtility (X x.1) ∂R + ∫ᵉ x, logUtility (Y x.2) ∂R := by
          simp_rw [logUtility, Function.comp, ENNReal.log_mul_add]
          rw [eintegral_add]
          · have := hX.measurable
            fun_prop
          · have := hY.measurable
            fun_prop
          · sorry
          · sorry
          · refine .inl (EReal.ne_bot_of_nonneg ?_)
            sorry
          · refine .inr (EReal.ne_bot_of_nonneg ?_)
            sorry
        _ = ∫ᵉ x, logUtility (X x) ∂R₁ + ∫ᵉ x, logUtility (Y x) ∂R₂ := by
            congr
            · rw [eintegral_map ?_ measurable_fst]
              have : Measurable X := hX.measurable
              fun_prop
            · rw [eintegral_map ?_ measurable_snd]
              have : Measurable Y := hY.measurable
              fun_prop
      congr
      · rw [sup_prod_sum S₁ T₁, ← exists_iSup₂_EReal_add]
        · rfl
        · exact isEVar_numeraire R₁ S₁
        · exact numeraire R₂ T₁
        · exact isEVar_numeraire R₂ T₁
        · haveI := R.isProbabilityMeasure_map measurable_fst.aemeasurable
          exact (maxUtility_eq_integral_numeraire R₁ hS₁).symm
        · haveI := R.isProbabilityMeasure_map measurable_snd.aemeasurable
          exact (maxUtility_eq_integral_numeraire R₂ hT₁).symm
      · rw [sup_prod_sum S₂ T₂, ← exists_iSup₂_EReal_add]
        · rfl
        · exact isEVar_numeraire R₁ S₂
        · exact numeraire R₂ T₂
        · exact isEVar_numeraire R₂ T₂
        · haveI := R.isProbabilityMeasure_map measurable_fst.aemeasurable
          exact (maxUtility_eq_integral_numeraire R₁ hS₂).symm
        · haveI := R.isProbabilityMeasure_map measurable_snd.aemeasurable
          exact (maxUtility_eq_integral_numeraire R₂ hT₂).symm
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
    _ = erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := erenyiDiv_add_eq_sInf hS₁ hS₂ hT₁ hT₂

lemma echernoffDiv_prod_le {S₁ S₂ : Set (Measure 𝓧)} {T₁ T₂ : Set (Measure 𝓨)}
    (hS₁ : ∀ μ ∈ S₁, IsProbabilityMeasure μ) (hS₂ : ∀ μ ∈ S₂, IsProbabilityMeasure μ)
    (hT₁ : ∀ μ ∈ T₁, IsProbabilityMeasure μ) (hT₂ : ∀ μ ∈ T₂, IsProbabilityMeasure μ) :
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
      rw [maxUtility_prod _ _ hS₁ hT₁, maxUtility_prod _ _ hS₂ hT₂]
  _ ≤ echernoffDiv S₁ S₂ + echernoffDiv T₁ T₂ := by
    rw [← iInf₄_eq_sInf, echernoffDiv, echernoffDiv, iInf₂_add]
    refine iInf₂_mono fun R₁ R₂ ↦ iInf₂_mono fun hR₁ hR₂ ↦ ?_
    rw [EReal.toENNReal_add, EReal.toENNReal_add]
    · exact max_add_add_le_max_add_max
    · exact maxUtility_nonneg _ hS₂
    · exact maxUtility_nonneg _ hT₂
    · exact maxUtility_nonneg _ hS₁
    · exact maxUtility_nonneg _ hT₁

lemma erenyiDiv_of_involutive_aux {S T : Set (Measure 𝓧)}
    {φ : 𝓧 → 𝓧} (hφ : Measurable φ) (hφ_inv : φ ∘ φ = id)
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, IsProbabilityMeasure μ)
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
          (by simp : R.map φ ∈ Set.univ) (zero_le' : 0 ≤ (2 : ℝ≥0∞)⁻¹) (zero_le' : 0 ≤ (2 : ℝ≥0∞)⁻¹)
          (by simpa using ENNReal.add_halves 1)
        unfold R'
        rwa [smul_add]
      · refine EReal.toENNReal_le_toENNReal ?_
        have h_conv := (convexOn_maxUtility T (U := logUtility)).2 (by simp : R ∈ Set.univ)
          (by simp : R.map φ ∈ Set.univ) (zero_le' : 0 ≤ (2 : ℝ≥0∞)⁻¹) (zero_le' : 0 ≤ (2 : ℝ≥0∞)⁻¹)
          (by simpa using ENNReal.add_halves 1)
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
      · exact mul_nonneg (by positivity) (maxUtility_nonneg _ hT)
      · exact mul_nonneg (by positivity) (maxUtility_nonneg _ hS)
      · exact mul_nonneg (by positivity) (maxUtility_nonneg _ hS)
      · exact mul_nonneg (by positivity) (maxUtility_nonneg _ hT)
      simp_rw [h_eq]
      ring
    _ = (2 : ℝ≥0∞)⁻¹ * (maxUtility R S logUtility).toENNReal
        + (2 : ℝ≥0∞)⁻¹ * (maxUtility R T logUtility).toENNReal := by
      rw [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

lemma erenyiDiv_of_involutive {S T : Set (Measure 𝓧)} {φ : 𝓧 → 𝓧} (hφ : Measurable φ)
    (hφ_inv : φ ∘ φ = id)
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, IsProbabilityMeasure μ)
    (hφST : {μ.map φ | μ ∈ S} = T) :
    erenyiDiv 2⁻¹ S T = 2 *
      ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R) (_ : R.map φ = R),
        (maxUtility R S logUtility).toENNReal := by
  rw [erenyiDiv_of_involutive_aux hφ hφ_inv hS hT hφST]
  congr with R
  congr with hR
  congr with hRφ
  rw [← hφST, maxUtility_involutive _ _ hφ hφ_inv, hRφ, ← add_mul]
  have h_eq := ENNReal.add_halves 1
  simp only [one_div] at h_eq
  simp [h_eq]

lemma eq_bernoulli_half_of_map_eq {R : Measure ({0, 1} : Set ℝ)} [IsProbabilityMeasure R]
    (hRφ : Measure.map (fun x ↦ ⟨1 - x.1, by grind⟩) R = R) :
    R = (2 : ℝ≥0∞)⁻¹ • Measure.dirac ⟨0, by simp⟩ + (2 : ℝ≥0∞)⁻¹ • Measure.dirac ⟨1, by simp⟩ := by
  have hR_eq : R = R {⟨0, by simp⟩} • Measure.dirac ⟨0, by simp⟩ +
      R {⟨1, by simp⟩} • Measure.dirac ⟨1, by simp⟩ := by
    refine Measure.ext_of_singleton fun x ↦ ?_
    by_cases hx : x = ⟨0, by simp⟩
    · simp [hx]
    · have hx' : x = ⟨1, by simp⟩ := by grind
      simp [hx']
  rw [hR_eq]
  suffices R {⟨0, by simp⟩} = R {⟨1, by simp⟩} by
    have h_one : R {⟨1, by simp⟩} = (2 : ℝ≥0∞)⁻¹ := by
      rw [Measure.ext_iff] at hR_eq
      specialize hR_eq Set.univ
      simp only [MeasurableSet.univ, measure_univ, this, Measure.coe_add, Measure.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, forall_const, ← two_mul] at hR_eq
      calc R {⟨1, by simp⟩}
      _ = 2⁻¹ * (2 * R {⟨1, by simp⟩}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
      _ = 2⁻¹ := by rw [← hR_eq, mul_one]
    rw [this, h_one]
  rw [hR_eq, Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul,
    Measure.map_dirac (by fun_prop), Measure.map_dirac (by fun_prop)] at hRφ
  simp only [sub_zero, sub_self, Measure.ext_iff_singleton] at hRφ
  simpa using hRφ ⟨1, by simp⟩

lemma map_bernoulli_half_eq :
    Measure.map (fun (x : ({0, 1} : Set ℝ)) ↦ (⟨1 - x.1, by grind⟩ : ({0, 1} : Set ℝ)))
        ((2 : ℝ≥0∞)⁻¹ • Measure.dirac ⟨0, by simp⟩ + (2 : ℝ≥0∞)⁻¹ • Measure.dirac ⟨1, by simp⟩) =
      (2 : ℝ≥0∞)⁻¹ • Measure.dirac ⟨0, by simp⟩ + (2 : ℝ≥0∞)⁻¹ • Measure.dirac ⟨1, by simp⟩ := by
  rw [Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul, add_comm]
  congr
  all_goals
    rw [Measure.map_dirac (by fun_prop)]
    simp

lemma erenyiDiv_bernoulli {δ : ℝ} (hδ_pos : 0 < δ) (hδ : δ ≤ 2⁻¹) :
    erenyiDiv 2⁻¹ {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ}
        {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ 1 - δ ≤ ∫ x, (x : ℝ) ∂μ}
      = ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ)))) := by
  let φ : ({0, 1} : Set ℝ) → ({0, 1} : Set ℝ) := fun x ↦ ⟨1 - x.1, by grind⟩
  have hφ_inv : φ ∘ φ = id := by ext; simp [φ]
  rw [erenyiDiv_of_involutive (by fun_prop) hφ_inv (by grind) (by grind)]
  swap
  · ext μ
    simp only [Set.mem_setOf_eq, tsub_le_iff_right]
    constructor
    · rintro ⟨ν, ⟨⟨hν, h_int⟩, rfl⟩⟩
      refine ⟨Measure.isProbabilityMeasure_map (by fun_prop), ?_⟩
      rw [integral_map (by fun_prop) (by fun_prop)]
      simp only [φ]
      rw [integral_sub (by fun_prop) (by fun_prop)]
      simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one]
      linarith
    · rintro ⟨hμ, h_int⟩
      refine ⟨μ.map φ, ⟨Measure.isProbabilityMeasure_map (by fun_prop), ?_⟩, ?_⟩
      · rw [integral_map (by fun_prop) (by fun_prop)]
        simp only [φ]
        rw [integral_sub (by fun_prop) (by fun_prop)]
        simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one]
        linarith
      · rw [Measure.map_map (by fun_prop) (by fun_prop), hφ_inv, Measure.map_id]
  have h_iff R (hR : IsProbabilityMeasure R) :
      R.map φ = R ↔ R =
        (2 : ℝ≥0∞)⁻¹ • Measure.dirac ⟨0, by simp⟩ + (2 : ℝ≥0∞)⁻¹ • Measure.dirac ⟨1, by simp⟩ := by
    constructor
    · exact eq_bernoulli_half_of_map_eq
    · rintro rfl
      exact map_bernoulli_half_eq
  calc 2 * ⨅ (R : Measure _) (_ : IsProbabilityMeasure R) (_ : Measure.map φ R = R),
      (maxUtility R {μ | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ} logUtility).toENNReal
  _ = 2 * ⨅ (R : Measure _) (_ : IsProbabilityMeasure R) (_ : Measure.map φ R = R),
      (maxUtility ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (⟨0, by simp⟩ : ({0, 1} : Set ℝ))
        + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (⟨1, by simp⟩ : ({0, 1} : Set ℝ)))
        {μ | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ} logUtility).toENNReal := by
    congr with R
    congr with hR
    congr with hRφ
    rw [h_iff R hR] at hRφ
    rw [hRφ]
  _ = 2 * (maxUtility ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (⟨0, by simp⟩ : ({0, 1} : Set ℝ))
        + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (⟨1, by simp⟩ : ({0, 1} : Set ℝ)))
        {μ | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ} logUtility).toENNReal := by
    rw [iInf₃_eq_sInf]
    congr 1
    suffices {y | ∃ x, IsProbabilityMeasure x ∧ x.map φ = x ∧
              y = (maxUtility ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (⟨0, by simp⟩ : ({0, 1} : Set ℝ))
                  + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (⟨1, by simp⟩ : ({0, 1} : Set ℝ)))
                  {μ | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ} logUtility).toENNReal}
        = { (maxUtility ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (⟨0, by simp⟩ : ({0, 1} : Set ℝ))
                  + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (⟨1, by simp⟩ : ({0, 1} : Set ℝ)))
                  {μ | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ} logUtility).toENNReal } by
      rw [this, sInf_singleton]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨fun ⟨μ, hμ, hμ_eq, hy_eq⟩ ↦ by rw [hy_eq], fun h ↦ ?_⟩
    refine ⟨((2 : ℝ≥0∞)⁻¹ • Measure.dirac (⟨0, by simp⟩ : ({0, 1} : Set ℝ))
              + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (⟨1, by simp⟩ : ({0, 1} : Set ℝ))), ?_, ?_, h⟩
    · constructor
      simpa using ENNReal.add_halves 1
    · exact map_bernoulli_half_eq
  _ = ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ)))) := by
    rw [maxUtility_bernoulli_half_le hδ_pos hδ, EReal.toENNReal_mul (by positivity),
      EReal.real_coe_toENNReal, ← mul_assoc]
    conv_rhs => rw [← one_mul (ENNReal.ofReal _)]
    congr
    have : (2 : EReal)⁻¹.toENNReal = 2⁻¹ := by
      have : (2 : EReal) = (2 : ℝ≥0∞) := rfl
      rw [this, EReal.toENNReal_inv (by simp)]
      simp
    rw [this, ENNReal.mul_inv_cancel (by simp) (by simp)]

open unitInterval in
lemma erenyiDiv_bounded_eq_erenyiDiv_bernoulli {a b : ℝ} :
    erenyiDiv 2⁻¹ {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ a}
        {μ : Measure I | IsProbabilityMeasure μ ∧ b ≤ ∫ x, (x : ℝ) ∂μ}
      = erenyiDiv 2⁻¹ {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ a}
        {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ b ≤ ∫ x, (x : ℝ) ∂μ} := by
  set D₁ := {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ a}
  set D₂ := {μ : Measure I | IsProbabilityMeasure μ ∧ b ≤ ∫ x, (x : ℝ) ∂μ}
  set B₁ := {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ a}
  set B₂ := {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ b ≤ ∫ x, (x : ℝ) ∂μ}
  refine le_antisymm ?_ ?_
  · trans erenyiDiv 2⁻¹ {μ.map doubleton | μ ∈ B₁} {μ.map doubleton | μ ∈ B₂}
    swap
    · exact erenyiDiv_map_le (by fun_prop)
    · refine erenyiDiv_anti ?_ ?_
      · rintro _ ⟨μ, hμ, rfl⟩
        refine ⟨?_, ?_⟩
        · haveI := hμ.1
          exact μ.isProbabilityMeasure_map measurable_doubleton.aemeasurable
        · have := hμ.2
          rw [integral_map (by fun_prop) (by fun_prop)]
          simp_all [doubleton]
      · rintro _ ⟨μ, hμ, rfl⟩
        refine ⟨?_, ?_⟩
        · haveI := hμ.1
          exact μ.isProbabilityMeasure_map measurable_doubleton.aemeasurable
        · have := hμ.2
          rw [integral_map (by fun_prop) (by fun_prop)]
          simp_all [doubleton]
  · let Ber (p : I) : Measure ({0, 1} : Set ℝ) :=
      (ENNReal.ofReal p) • Measure.dirac ⟨1, by simp⟩ +
        (ENNReal.ofReal (1 - p)) • Measure.dirac ⟨0, by simp⟩
    haveI Ber_is_prob : ∀ p, IsProbabilityMeasure (Ber p) := by
      intro p
      refine isProbabilityMeasure_iff.mpr ?_
      simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
        smul_eq_mul, mul_one, Ber]
      rw [← ENNReal.ofReal_add (by unit_interval) (by unit_interval)]
      simp
    let κ : Kernel I ({0, 1} : Set ℝ) := ⟨Ber, by fun_prop⟩
    haveI : IsMarkovKernel κ := ⟨Ber_is_prob⟩
    have κ_comp : ∀ μ, IsProbabilityMeasure μ → κ ∘ₘ (μ.map doubleton) = μ := by
      intro μ hμ
      ext S hS
      rw [Measure.bind_apply hS (by fun_prop),
        lintegral_map (Kernel.measurable_coe κ hS) (by fun_prop)]
      rw [doubleton_lintegral]
      simp only [doubleton, Set.Icc.mk_zero, Kernel.coe_mk, Set.Icc.coe_zero,
        ENNReal.ofReal_zero, zero_smul, sub_zero, ENNReal.ofReal_one, one_smul, zero_add,
        Measure.dirac_apply, Set.Icc.mk_one, Set.Icc.coe_one, sub_self, add_zero, κ, Ber]
      by_cases h0 : ⟨0, by simp⟩ ∈ S <;> by_cases h1 : ⟨1, by simp⟩ ∈ S
      · have : S = Set.univ := by grind
        rw [this]
        simp_all only [Set.mem_Icc, Subtype.forall, forall_and_index, MeasurableSet.univ,
          Set.mem_univ, Set.indicator_of_mem, Pi.one_apply, mul_one, measure_univ]
        rw [← measure_union (by simp) (by simp), doubleton_union_univ]
        simp
      · have : S = {⟨0, by simp⟩} := by grind
        simp_all
      · have : S = {⟨1, by simp⟩} := by grind
        simp_all
      · have : S = ∅ := by grind
        simp_all
    have B₁_eq_κ_comp : B₁ = {κ ∘ₘ μ | μ ∈ D₁} := by
      ext μ
      constructor
      · rintro ⟨hμ_prob, hμ_int⟩
        refine ⟨μ.map doubleton, ?_, κ_comp μ hμ_prob⟩
        · refine ⟨μ.isProbabilityMeasure_map measurable_doubleton.aemeasurable, ?_⟩
          rw [integral_map (by fun_prop) (by fun_prop)]
          simp_all [doubleton]
      · rintro ⟨ν, hν, rfl⟩
        refine ⟨?_, ?_⟩
        · have := hν.1
          infer_instance
        · obtain ⟨hν_prob, hν⟩ := hν
          rw [integral_eq_lintegral_of_nonneg_ae] at ⊢ hν
          · rw [Measure.lintegral_bind (by fun_prop) (by fun_prop)]
            trans (∫⁻ (x : I), ENNReal.ofReal x ∂ν).toReal
            · gcongr with b
              · apply ne_of_lt
                calc
                _ ≤ ∫⁻ x, 1 ∂ν := by
                  refine lintegral_mono fun x ↦ ?_
                  simp only [ENNReal.ofReal_le_one]
                  unit_interval
                _ = (1 : ℝ≥0∞) := by simp
                _ < ⊤ := by simp
              · rw [doubleton_lintegral]
                simp [κ, Ber]
            · exact hν
          · apply ae_of_all
            intro x
            cases x.2 with
            | inl hx0 => simp_all
            | inr hx1 => simp_all
          · fun_prop
          · apply ae_of_all
            intro x
            unit_interval
          · fun_prop
    rw [B₁_eq_κ_comp]
    have B₂_eq_κ_comp : B₂ = {κ ∘ₘ μ | μ ∈ D₂} := by
      ext μ
      constructor
      · rintro ⟨hμ_prob, hμ_int⟩
        refine ⟨μ.map doubleton, ?_, κ_comp μ hμ_prob⟩
        · refine ⟨μ.isProbabilityMeasure_map measurable_doubleton.aemeasurable, ?_⟩
          rw [integral_map (by fun_prop) (by fun_prop)]
          simp_all [doubleton]
      · rintro ⟨ν, hν, rfl⟩
        refine ⟨?_, ?_⟩
        · have := hν.1
          infer_instance
        · obtain ⟨hν_prob, hν⟩ := hν
          rw [integral_eq_lintegral_of_nonneg_ae] at ⊢ hν
          · rw [Measure.lintegral_bind (by fun_prop) (by fun_prop)]
            trans (∫⁻ (x : I), ENNReal.ofReal x ∂ν).toReal
            · exact hν
            · gcongr with b
              · apply ne_of_lt
                calc
                _ ≤ ∫⁻ x, ∫⁻ y, 1 ∂(κ x) ∂ν := by
                  refine lintegral_mono fun x ↦ lintegral_mono fun y ↦ ?_
                  rw [ENNReal.ofReal_le_one]
                  cases y.2 with
                  | inl hy0 => simp_all
                  | inr hy1 => simp_all
                _ = (1 : ℝ≥0∞) := by simp
                _ < ⊤ := by simp
              · rw [doubleton_lintegral]
                simp [κ, Ber]
          · apply ae_of_all
            intro x
            cases x.2 with
            | inl hx0 => simp_all
            | inr hx1 => simp_all
          · fun_prop
          · apply ae_of_all
            intro x
            unit_interval
          · fun_prop
    rw [B₂_eq_κ_comp]
    exact erenyiDiv_comp_le κ

open unitInterval in
lemma erenyiDiv_bounded {δ : ℝ} (hδ_pos : 0 < δ) (hδ : δ ≤ 2⁻¹) :
    erenyiDiv 2⁻¹ {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ}
        {μ : Measure I | IsProbabilityMeasure μ ∧ 1 - δ ≤ ∫ x, (x : ℝ) ∂μ} =
      ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ)))) := by
  rw [erenyiDiv_bounded_eq_erenyiDiv_bernoulli, erenyiDiv_bernoulli hδ_pos hδ]

open unitInterval in
theorem erenyiDiv_ge_of_separated {f : 𝓧 → I} (hf : Measurable f)
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, IsProbabilityMeasure μ)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ : δ ≤ 2⁻¹)
    (hSf : ∀ μ ∈ S, ∫ ω, (f ω : ℝ) ∂μ ≤ δ) (hTf : ∀ ν ∈ T, 1 - δ ≤ ∫ ω, (f ω : ℝ) ∂ν) :
    ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ)))) ≤ erenyiDiv 2⁻¹ S T :=
  calc ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ))))
  _ = erenyiDiv 2⁻¹ {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ}
        {μ : Measure I | IsProbabilityMeasure μ ∧ 1 - δ ≤ ∫ x, (x : ℝ) ∂μ} := by
    rw [← erenyiDiv_bounded hδ_pos hδ]
  _ ≤ erenyiDiv 2⁻¹ {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} := by
    refine erenyiDiv_anti ?_ ?_
    · rintro μ ⟨ν, hνS, rfl⟩
      constructor
      · have := hS ν hνS
        exact Measure.isProbabilityMeasure_map (hf.aemeasurable)
      rw [integral_map (hf.aemeasurable) (by fun_prop)]
      exact hSf ν hνS
    · rintro μ ⟨ν, hνT, rfl⟩
      constructor
      · have := hT ν hνT
        exact Measure.isProbabilityMeasure_map (hf.aemeasurable)
      rw [integral_map (hf.aemeasurable) (by fun_prop)]
      exact hTf ν hνT
  _ ≤ erenyiDiv 2⁻¹ S T := erenyiDiv_map_le hf

#axiom_blame erenyiDiv_ge_of_separated

end ProbabilityTheory
