/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
import EValues.DPI
import EValues.Product
import EValues.Mathlib.iSup


/-!
# E-Rényi divergence

An analogue of the Rényi divergence for e-variables.

-/

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
  · sorry

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
    rw [← iInf₃_eq_sInf', echernoffDiv, echernoffDiv, iInf₂_add]
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

-- todo: rename
theorem main_result_one_sample {f : 𝓧 → ℝ≥0∞} (hf : Measurable f) (hf_le : ∀ x, f x ≤ 1)
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, IsProbabilityMeasure μ)
    {δ : ℝ≥0∞}
    (hSf : ∀ μ ∈ S, ∫⁻ ω, f ω ∂μ ≤ δ) (hTf : ∀ ν ∈ T, 1 - δ ≤ ∫⁻ ω, f ω ∂ν) :
    ENNReal.ofReal (Real.log (1 / (4 * δ.toReal * (1 - δ).toReal))) ≤ erenyiDiv 2⁻¹ S T := by
  sorry

end ProbabilityTheory
