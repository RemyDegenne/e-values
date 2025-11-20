/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
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

/-- The e-Chernoff divergence between two sets of measures. -/
noncomputable
def echernoffDiv (S T : Set (Measure 𝓧)) : ℝ≥0∞ :=
  ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
    max (maxUtility R S logUtility).toENNReal (maxUtility R T logUtility).toENNReal

lemma echernoffDiv_eq_sInf : echernoffDiv S T =
    sInf {y | ∃ R, IsProbabilityMeasure R ∧
    y = max (maxUtility R S logUtility).toENNReal (maxUtility R T logUtility).toENNReal} :=
  iInf₂_eq_sInf (ι := ℝ≥0∞)

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

/-- Data processing inequality for the e-Rényi divergence. -/
lemma erenyiDiv_map_le {f : 𝓧 → 𝓨} (hf : Measurable f) :
    erenyiDiv α {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} ≤ erenyiDiv α S T := by
  unfold erenyiDiv
  gcongr 1
  set S' := {μ.map f | μ ∈ S}
  set T' := {μ.map f | μ ∈ T}
  calc
  _ ≤ ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
      α * (maxUtility (R.map f) S' logUtility).toENNReal +
        (1 - α) * (maxUtility (R.map f) T' logUtility).toENNReal := by
    rw [iInf₂_eq_sInf (ι := ℝ≥0∞), iInf₂_eq_sInf (ι := ℝ≥0∞)]
    refine sInf_le_sInf fun y ↦ ?_
    rintro ⟨R, hR, rfl⟩
    exact ⟨R.map f, R.isProbabilityMeasure_map hf.aemeasurable, rfl⟩
  _ ≤ ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R),
      α * (maxUtility R S logUtility).toENNReal +
        (1 - α) * (maxUtility R T logUtility).toENNReal := by
    refine iInf₂_mono fun R _ ↦ add_le_add ?_ ?_
    · gcongr 1
      exact EReal.toENNReal_le_toENNReal <| maxUtility_map_le R hf
    · gcongr 1
      exact EReal.toENNReal_le_toENNReal <| maxUtility_map_le R hf

/-- Data processing inequality for the e-Chernoff divergence. -/
lemma echernoffDiv_map_le {f : 𝓧 → 𝓨} (hf : Measurable f) :
    echernoffDiv {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} ≤ echernoffDiv S T := by
  set S' := {μ.map f | μ ∈ S}
  set T' := {μ.map f | μ ∈ T}
  calc echernoffDiv S' T'
  _ ≤ ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R), max
      (maxUtility (R.map f) S' logUtility).toENNReal
      (maxUtility (R.map f) T' logUtility).toENNReal := by
    rw [iInf₂_eq_sInf (ι := ℝ≥0∞), echernoffDiv_eq_sInf]
    refine sInf_le_sInf fun y ↦ ?_
    rintro ⟨R, hR, rfl⟩
    exact ⟨R.map f, R.isProbabilityMeasure_map hf.aemeasurable, rfl⟩
  _ ≤ echernoffDiv S T := by
    refine iInf₂_mono fun R _ ↦ max_le_max ?_ ?_
    all_goals exact (EReal.toENNReal_le_toENNReal <| maxUtility_map_le R hf)

lemma erenyiDiv_prod {S₁ S₂ : Set (Measure 𝓧)} {T₁ T₂ : Set (Measure 𝓨)}
    (hS₁ : ∀ μ ∈ S₁, IsProbabilityMeasure μ) (hS₂ : ∀ μ ∈ S₂, IsProbabilityMeasure μ)
    (hT₁ : ∀ μ ∈ T₁, IsProbabilityMeasure μ) (hT₂ : ∀ μ ∈ T₂, IsProbabilityMeasure μ) :
    erenyiDiv α (Measure.prod.uncurry '' (S₁ ×ˢ T₁)) (Measure.prod.uncurry '' (S₂ ×ˢ T₂))
      = erenyiDiv α S₁ S₂ + erenyiDiv α T₁ T₂ := by
  sorry

lemma echernoffDiv_prod_le {S₁ S₂ : Set (Measure 𝓧)} {T₁ T₂ : Set (Measure 𝓨)}
    (hS₁ : ∀ μ ∈ S₁, IsProbabilityMeasure μ) (hS₂ : ∀ μ ∈ S₂, IsProbabilityMeasure μ)
    (hT₁ : ∀ μ ∈ T₁, IsProbabilityMeasure μ) (hT₂ : ∀ μ ∈ T₂, IsProbabilityMeasure μ) :
    echernoffDiv (Measure.prod.uncurry '' (S₁ ×ˢ T₁)) (Measure.prod.uncurry '' (S₂ ×ˢ T₂))
      ≤ echernoffDiv S₁ S₂ + echernoffDiv T₁ T₂ := by
  sorry

lemma erenyiDiv_of_involutive (S T : Set (Measure 𝓧)) {φ : 𝓧 → 𝓧} (hφ : Measurable φ)
    (hφ_inv : φ ∘ φ = id) (hφST : {μ.map φ | μ ∈ S} = T) :
    erenyiDiv α S T = (1 - α)⁻¹ *
      ⨅ (R : Measure 𝓧) (_ : IsProbabilityMeasure R) (_ : R.map φ = R),
        (maxUtility R S logUtility).toENNReal := by
  rw [erenyiDiv, iInf₃_eq_sInf, iInf₂_eq_sInf]
  congr 1
  sorry

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
  rw [erenyiDiv_of_involutive _ _ (by fun_prop) hφ_inv]
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
  simp only [ENNReal.one_sub_inv_two, inv_inv]
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
