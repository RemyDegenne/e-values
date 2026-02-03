/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
import EValues.EValue
import EValues.Utility
import EValues.Mathlib.iSup
import EValues.Mathlib.unitInterval
import EValues.NumeraireExistence

open scoped ENNReal NNReal ProbabilityTheory

open MeasureTheory ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {S : Set (Measure 𝓧)}

namespace ProbabilityTheory

/-- The maximum utility `∫ᵉ x, (U ∘ X) x ∂P` of a measure `P` over all e-variables `X` for
a set of measures `S`. -/
noncomputable
def maxUtility (P : Measure 𝓧) (S : Set (Measure 𝓧)) (U : Utility) : EReal :=
  ⨆ (X : 𝓧 → ℝ≥0∞) (_hX : IsEVar X S), ∫ᵉ x, (U ∘ X) x ∂P

/-- The maximum randomized utility `∫ᵉ x, U x ∂(η ∘ₘ P)` of a measure `P` over all randomized
e-variables `η` for a set of measures `S`. -/
noncomputable
def maxRandUtility (P : Measure 𝓧) (S : Set (Measure 𝓧)) (U : Utility) : EReal :=
  ⨆ (η : Kernel 𝓧 ℝ≥0∞) (_hη₁ : IsMarkovKernel η) (_hη₂ : IsRandEVar η S), ∫ᵉ x, U x ∂(η ∘ₘ P)

variable {P : Measure 𝓧} {S T : Set (Measure 𝓧)} {U : Utility} {φ : 𝓧 → 𝓨}

lemma maxUtility_eq_sSup : maxUtility P S U =
    sSup {y | ∃ X, IsEVar X S ∧ y = ∫ᵉ x, (U ∘ X) x ∂P} := iSup₂_eq_sSup

lemma maxRandUtility_eq_sSup : maxRandUtility P S U =
      sSup {y | ∃ η, IsMarkovKernel η ∧ IsRandEVar η S ∧ y = ∫ᵉ x, U x ∂(η ∘ₘ P)} :=
  iSup₃_eq_sSup

lemma maxUtility_anti (hS : S ⊆ T) : maxUtility P T U ≤ maxUtility P S U := by
  rw [maxUtility_eq_sSup, maxUtility_eq_sSup]
  refine sSup_le_sSup ?_
  rintro y ⟨X, hX, hy⟩
  exact ⟨X, hX.anti_set hS, hy⟩

lemma maxRandUtility_anti (hS : S ⊆ T) : maxRandUtility P T U ≤ maxRandUtility P S U := by
  rw [maxRandUtility_eq_sSup, maxRandUtility_eq_sSup]
  refine sSup_le_sSup ?_
  rintro y ⟨η, hη₁, hη₂, hy⟩
  exact ⟨η, hη₁, hη₂.anti_set hS, hy⟩

/-- The maximum randomized utility equals the maximum utility. -/
lemma maxRandUtility_eq_maxUtility (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    maxRandUtility P S U = maxUtility P S U := by
  refine le_antisymm ?_ ?_
  · rw [maxRandUtility_eq_sSup]
    rw [sSup_le_iff]
    rintro y ⟨η, hη₁, hη₂, hy⟩
    obtain ⟨X, hX, h_le⟩ : ∃ X, IsEVar X S ∧ y ≤ ∫ᵉ x, (U ∘ X) x ∂P := by
      let X := fun x ↦ ∫⁻ y, y ∂(η x)
      refine ⟨X, ⟨by fun_prop, fun μ hμ ↦ ?_, fun μ hμ ↦ ?_⟩, ?_⟩
      · rw [isRandEVar_iff_isEVar] at hη₂
        exact hη₂.eintegral_ne_bot μ hμ
      · rw [isRandEVar_iff_isEVar] at hη₂
        exact hη₂.eintegral_nonpos μ hμ
      · rw [hy]
        refine (eintegral_comp_measure_le U.measurable).trans ?_
        refine eintegral_mono fun _ ↦ ?_
        exact U.eintegral_le_map (by fun_prop)
    trans ∫ᵉ x, (U ∘ X) x ∂P
    · exact h_le
    · rw [maxUtility_eq_sSup]
      refine le_sSup ?_
      exact ⟨X, hX, rfl⟩
  · rw [maxRandUtility_eq_sSup, maxUtility_eq_sSup]
    refine sSup_le_sSup ?_
    rintro y ⟨X, hX, hy⟩
    refine ⟨Kernel.deterministic X hX.measurable, inferInstance, ⟨fun μ hμ ↦ ?_, fun μ hμ ↦ ?_⟩, ?_⟩
    · simp only [Kernel.lintegral_deterministic]
      exact hX.eintegral_ne_bot μ hμ
    · simp only [Kernel.lintegral_deterministic]
      exact hX.eintegral_nonpos μ hμ
    · rw [hy, Measure.deterministic_comp_eq_map hX.measurable,
        eintegral_map U.measurable hX.measurable]
      rfl

/-- Data processing inequality for the maximum randomized utility and a Markov kernel. -/
lemma maxRandUtility_comp_le (P : Measure 𝓧) {S : Set (Measure 𝓧)} (κ : Kernel 𝓧 𝓨)
    [IsMarkovKernel κ] :
    maxRandUtility (κ ∘ₘ P) {κ ∘ₘ μ | μ ∈ S} U ≤ maxRandUtility P S U := by
  calc maxRandUtility (κ ∘ₘ P) {κ ∘ₘ μ | μ ∈ S} U
  _ = sSup {y | ∃ η, IsMarkovKernel η ∧ IsRandEVar η {κ ∘ₘ μ | μ ∈ S} ∧
      y = ∫ᵉ x, U x ∂(η ∘ₘ κ ∘ₘ P)} := maxRandUtility_eq_sSup
  _ = sSup {y | ∃ ξ, ∃ η, IsMarkovKernel η ∧ IsRandEVar η {κ ∘ₘ μ | μ ∈ S} ∧
      ξ = η ∘ₖ κ ∧ y = ∫ᵉ x, U x ∂(ξ ∘ₘ P)} := by
    congr with y
    constructor
    · rintro ⟨η, hη₁, hη₂, hη_int⟩
      refine ⟨η ∘ₖ κ, η, hη₁, hη₂, rfl, ?_⟩
      rw [hη_int, P.comp_assoc]
    · rintro ⟨ξ, η, hη₁, hη₂, hξ, hξ_int⟩
      refine ⟨η, hη₁, hη₂, ?_⟩
      rw [hξ_int, hξ, P.comp_assoc]
  _ ≤ maxRandUtility P S U := by
    rw [maxRandUtility_eq_sSup]
    refine sSup_le_sSup fun y ↦ ?_
    rintro ⟨ξ, η, hη₁, hη₂, hξ, hξ_int⟩
    haveI : IsMarkovKernel ξ := by
      rw [hξ]
      infer_instance
    refine ⟨ξ, this, ?_, hξ_int⟩
    rw [hξ]
    exact IsRandEVar.comp hη₂

/-- Data processing inequality for the maximum utility and a Markov kernel. -/
lemma maxUtility_comp_le (P : Measure 𝓧) {S : Set (Measure 𝓧)} (κ : Kernel 𝓧 𝓨)
    [IsMarkovKernel κ] : maxUtility (κ ∘ₘ P) {κ ∘ₘ μ | μ ∈ S} U ≤ maxUtility P S U := by
  rw [← maxRandUtility_eq_maxUtility _ _, ← maxRandUtility_eq_maxUtility _ _]
  exact maxRandUtility_comp_le P κ

/-- Data processing inequality for the maximum utility and a measurable function. -/
lemma maxUtility_map_le (P : Measure 𝓧) {S : Set (Measure 𝓧)} (hφ : Measurable φ) :
    maxUtility (P.map φ) {μ.map φ | μ ∈ S} U ≤ maxUtility P S U := by
  simp_rw [← Measure.deterministic_comp_eq_map hφ]
  exact maxUtility_comp_le P <| Kernel.deterministic φ hφ

/-- Equality case for the data processing inequality: mapping by a measurable embedding preserves
the maximum utility. -/
lemma _root_.MeasurableEmbedding.maxUtility_map_eq [Nonempty 𝓧] (φ : 𝓧 → 𝓨)
    (hφ : MeasurableEmbedding φ) (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    maxUtility (P.map φ) {μ.map φ | μ ∈ S} U = maxUtility P S U := by
  have hφ_inv : hφ.invFun ∘ φ = id := by -- extract lemma
    ext x
    simp only [Function.comp_apply, id_eq]
    rw [hφ.leftInverse_invFun]
  apply le_antisymm (maxUtility_map_le P hφ.measurable)
  have hP_eq : P = (P.map φ).map hφ.invFun := by
    rw [Measure.map_map hφ.measurable_invFun hφ.measurable, hφ_inv, Measure.map_id]
  have hS_eq : S = {μ.map hφ.invFun | μ ∈ {ν.map φ | ν ∈ S}} := by
    ext μ
    simp only [Set.mem_setOf_eq, exists_exists_and_eq_and]
    refine ⟨fun hμ ↦ ?_, fun hμ ↦ ?_⟩
    · refine ⟨μ, hμ, ?_⟩
      rw [Measure.map_map hφ.measurable_invFun hφ.measurable, hφ_inv, Measure.map_id]
    · obtain ⟨ν, hν, rfl⟩ := hμ
      rwa [Measure.map_map hφ.measurable_invFun hφ.measurable, hφ_inv, Measure.map_id]
  conv_lhs => rw [hP_eq, hS_eq]
  exact maxUtility_map_le (P.map φ) hφ.measurable_invFun

/-- If `X` is a numeraire e-variable, then the maximum utility is attained at `X`. -/
lemma IsNumeraire.maxUtility_eq_integral [IsProbabilityMeasure P]
    {X : 𝓧 → ℝ≥0∞} (hX : IsNumeraire X S P) :
    maxUtility P S logUtility = ∫ᵉ x, ENNReal.log (X x) ∂P := by
  refine le_antisymm ?_ ?_
  · simp only [maxUtility]
    refine iSup₂_le_iff.mpr fun Y hY ↦ ?_
    simp [logUtility, hX.eintegral_log_le hY]
  · rw [maxUtility_eq_sSup]
    refine le_sSup ?_
    exact ⟨X, hX.toIsEVar, rfl⟩

lemma maxUtility_eq_integral_numeraire (P : Measure 𝓧) [IsProbabilityMeasure P] :
    maxUtility P S logUtility = ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P :=
  (isNumeraire_numeraire P).maxUtility_eq_integral

/-- The maximum utility is nonnegative. -/
lemma maxUtility_nonneg (P : Measure 𝓧) :
    0 ≤ maxUtility P S logUtility := by
  calc 0
  _ ≤ ∫ᵉ (x : 𝓧), (logUtility.toFun ∘ (fun _ ↦ 1)) x ∂P := by simp [logUtility]
  _ ≤ maxUtility P S logUtility := by
    rw [maxUtility]
    refine le_iSup₂ (f := fun X _ ↦ ∫ᵉ (x : 𝓧), (logUtility.toFun ∘ X) x ∂P) (fun _ ↦ 1) ?_
    exact isEVar_fun_one S

/-- The maximum utility is a convex function of the measure. -/
lemma convexOn_maxUtility (S : Set (Measure 𝓧)) :
    ConvexOn ℝ≥0∞ Set.univ (fun P ↦ maxUtility P S U) := by
  refine ⟨convex_univ, fun P _ Q _ a b ha hb hab ↦ ?_⟩
  simp only
  rw [maxUtility]
  have ha : a ≠ ∞ := ne_top_of_le_ne_top (by simp : 1 ≠ ∞) (by simp [← hab])
  have hb : b ≠ ∞ := ne_top_of_le_ne_top (by simp : 1 ≠ ∞) (by simp [← hab])
  simp_rw [eintegral_add_measure, eintegral_smul_measure ha, eintegral_smul_measure hb]
  calc ⨆ X, ⨆ (_ : IsEVar X S), a * ∫ᵉ x, (U.toFun ∘ X) x ∂P + b * ∫ᵉ x, (U.toFun ∘ X) x ∂Q
  _ = ⨆ X, (a * ⨆ (_ : IsEVar X S), ∫ᵉ x, (U.toFun ∘ X) x ∂P)
      + b * ⨆ (_ : IsEVar X S), ∫ᵉ x, (U.toFun ∘ X) x ∂Q := by
    congr with X
    by_cases hX : IsEVar X S
    · simp [hX]
    · simp only [hX, Function.comp_apply, not_false_eq_true, iSup_neg]
      by_cases ha : a = 0
      · have hb : 0 < (b : EReal) := by
          simp only [EReal.coe_ennreal_pos]
          by_contra!
          have : b = 0 := by grind
          simp [ha, this] at hab
        rw [EReal.mul_bot_of_pos hb]
        simp
      · have ha' : 0 < (a : EReal) := by simp; grind
        rw [EReal.mul_bot_of_pos ha']
        simp
  _ ≤ (⨆ X, a * ⨆ (_ : IsEVar X S), ∫ᵉ x, (U.toFun ∘ X) x ∂P)
      + ⨆ X, b * ⨆ (_ : IsEVar X S), ∫ᵉ x, (U.toFun ∘ X) x ∂Q := EReal.iSup_add_le_add_iSup
  _ = a • maxUtility P S U + b • maxUtility Q S U := by
    simp_rw [maxUtility]
    simp only [EReal.smul_ennreal_eq_mul]
    rw [EReal.iSup_ennreal_mul, EReal.iSup_ennreal_mul]
    · exact ne_top_of_le_ne_top (by simp : 1 ≠ ∞) (by simp [← hab])
    · exact ne_top_of_le_ne_top (by simp : 1 ≠ ∞) (by simp [← hab])

lemma maxUtility_involutive (P : Measure 𝓧) (S : Set (Measure 𝓧)) {φ : 𝓧 → 𝓧} (hφ : Measurable φ)
    (hφ_inv : φ ∘ φ = id) :
    maxUtility P {μ.map φ | μ ∈ S} U = maxUtility (P.map φ) S U := by
  apply le_antisymm
  · calc maxUtility P {μ.map φ | μ ∈ S} U
    _ = maxUtility ((P.map φ).map φ) {μ.map φ | μ ∈ S} U := by
      rw [Measure.map_map hφ hφ, hφ_inv, Measure.map_id]
    _ ≤ maxUtility (P.map φ) S U := maxUtility_map_le _ hφ
  · calc maxUtility (P.map φ) S U
    _ = maxUtility (P.map φ) {(μ.map φ).map φ | μ ∈ S} U := by
      congr with μ
      simp_rw [Measure.map_map hφ hφ, hφ_inv, Measure.map_id]
      grind
    _ = maxUtility (P.map φ) {μ.map φ | μ ∈ {ν.map φ | ν ∈ S}} U := by congr with μ; simp
    _ ≤ maxUtility P {μ | μ ∈ {ν.map φ | ν ∈ S}} U := maxUtility_map_le _ hφ
    _ = maxUtility P {μ.map φ | μ ∈ S} U := rfl

end ProbabilityTheory
