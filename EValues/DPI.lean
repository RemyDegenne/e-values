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
      refine ⟨X, ⟨by fun_prop, fun μ hμ ↦ ?_⟩, ?_⟩
      · rw [isRandEVar_iff_isEVar] at hη₂
        exact hη₂.lintegral_le_one μ hμ
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
    refine ⟨Kernel.deterministic X hX.measurable, inferInstance, ⟨fun μ hμ ↦ ?_⟩, ?_⟩
    · rw [Measure.deterministic_comp_eq_map hX.measurable,
        lintegral_map (by fun_prop) hX.measurable]
      exact hX.lintegral_le_one μ hμ
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
    refine ⟨ξ, this, ⟨fun μ hμ ↦ ?_⟩, hξ_int⟩
    rw [hξ, ← μ.comp_assoc]
    exact hη₂.lintegral_le_one (κ ∘ₘ μ) ⟨μ, hμ, rfl⟩

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

lemma maxUtility_eq_integral_numeraire (P : Measure 𝓧) [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    maxUtility P S logUtility = ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P :=
  (isNumeraire_numeraire P hS).maxUtility_eq_integral

/-- The maximum utility is nonnegative. -/
lemma maxUtility_nonneg (P : Measure 𝓧) (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    0 ≤ maxUtility P S logUtility := by
  calc 0
  _ ≤ ∫ᵉ (x : 𝓧), (logUtility.toFun ∘ (fun _ ↦ 1)) x ∂P := by simp [logUtility]
  _ ≤ maxUtility P S logUtility := by
    rw [maxUtility]
    refine le_iSup₂ (f := fun X _ ↦ ∫ᵉ (x : 𝓧), (logUtility.toFun ∘ X) x ∂P) (fun _ ↦ 1) ?_
    exact isEVar_fun_one S hS

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

lemma quadratic_inequality {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (u : ℝ) :
    (1 - u * δ) * (1 + u * (1 - δ)) ≤ (1 - δ)⁻¹ * (δ⁻¹ * 4⁻¹) := by
  have : 0 ≤ (u - (δ⁻¹ - (1-δ)⁻¹)/2)^2 := by positivity -- complete square
  field_simp (disch := bound) at this ⊢ -- clear denominators
  linarith

lemma four_le_mul_inv {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    4 ≤ (1 - δ)⁻¹ * δ⁻¹ := by
  have : 0 < 1 - δ := by linarith
  have : (1 - δ) * δ ≤ 1 / 4 := by linarith [sq_nonneg (1 / 2 - δ)]
  rwa [← mul_inv, le_inv_comm₀ (by simp) (by positivity), ← one_div]

lemma maxUtility_bernoulli_half_le {δ : ℝ} (hδ_pos : 0 < δ) (hδ : δ ≤ 2⁻¹) :
    maxUtility ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (⟨0, by simp⟩ : ({0, 1} : Set ℝ))
          + (2 : ℝ≥0∞)⁻¹ • Measure.dirac ⟨1, by simp⟩)
        {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ} logUtility
      = 2⁻¹ * Real.log (1 / (4 * δ * (1 - δ))) := by
  have hδ_lt_one : δ < 1 := by grind
  have h_one_sub_δ_pos : 0 < 1 - δ := by grind
  let P := (2 : ℝ≥0∞)⁻¹ • Measure.dirac (⟨0, by simp⟩ : ({0, 1} : Set ℝ))
    + (2 : ℝ≥0∞)⁻¹ • Measure.dirac ⟨1, by simp⟩
  have hP_prob : IsProbabilityMeasure P := by
    constructor
    simpa [P] using ENNReal.add_halves 1
  change maxUtility P _ logUtility = 2⁻¹ * Real.log (1 / (4 * δ * (1 - δ)))
  rw [maxUtility]
  have hδ_le_one : δ ≤ 1 := by linarith
  simp_rw [isEVar_bernoulli_le_iff hδ_pos hδ_le_one]
  have : (2 : ℝ≥0∞)⁻¹ ≠ ∞ := by simp
  simp only [Subtype.forall, Set.mem_insert_iff, Set.mem_singleton_iff, exists_prop,
    logUtility, Function.comp_apply, eintegral_add_measure, eintegral_smul_measure this,
    eintegral_dirac, one_div, mul_inv_rev, P]
  refine le_antisymm ?_ ?_
  · simp only [iSup_exists, iSup_le_iff, and_imp]
    intro X u hu_nonneg hu_le hX
    have hX0 := hX 0 (by simp)
    have hX1 := hX 1 (by simp)
    simp only [zero_sub, mul_neg] at hX0 hX1
    have h1 : (2 : ℝ≥0∞)⁻¹ * ENNReal.log (X ⟨0, by simp⟩)
          + (2 : ℝ≥0∞)⁻¹ * ENNReal.log (X ⟨1, by simp⟩)
        ≤ (2 : ℝ≥0∞)⁻¹ * ENNReal.log (ENNReal.ofReal (1 + -(u * δ)))
          + (2 : ℝ≥0∞)⁻¹ * ENNReal.log (ENNReal.ofReal (1 + u * (1 - δ))) := by gcongr
    refine h1.trans ?_
    have h_pos : 0 < (2 : EReal)⁻¹ :=
      EReal.inv_pos_of_pos_ne_top (by simp) (Ne.symm (not_eq_of_beq_eq_false rfl))
    by_cases huδ : u = δ⁻¹
    · simp only [huδ, inv_mul_cancel₀ hδ_pos.ne', add_neg_cancel, ENNReal.ofReal_zero,
        ENNReal.log_zero, ENNReal.log_ofReal, mul_ite]
      rw [EReal.mul_bot_of_pos (by simp)]
      simp
    have hu_lt : u < δ⁻¹ := lt_of_le_of_ne hu_le huδ
    have h_u_mul_lt : u * δ < 1 := by
      calc u * δ < δ⁻¹ * δ := by gcongr
      _ = 1 := inv_mul_cancel₀ hδ_pos.ne'
    have : 0 < 1 + -(u * δ) := by grind
    have h_one_add_pos : 0 < 1 + u * (1 - δ) := by positivity
    calc (2 : ℝ≥0∞)⁻¹ * ENNReal.log (ENNReal.ofReal (1 + -(u * δ)))
        + (2 : ℝ≥0∞)⁻¹ * ENNReal.log (ENNReal.ofReal (1 + u * (1 - δ)))
    _ = 2⁻¹ * ENNReal.log (ENNReal.ofReal (1 + -(u * δ)))
        + 2⁻¹ * ENNReal.log (ENNReal.ofReal (1 + u * (1 - δ))) := by
      have : (2 : EReal) = (2 : ℝ≥0∞) := rfl
      rw [this, EReal.inv_coe_ennreal (by positivity)]
    _ ≤ 2⁻¹ * Real.log (1 + -(u * δ)) + 2⁻¹ * Real.log (1 + u * (1 - δ)) := by
      simp [not_le.mpr h_u_mul_lt, not_le.mpr h_one_add_pos]
    _ = 2⁻¹ * Real.log ((1 + -(u * δ)) * (1 + u * (1 - δ))) := by
      rw [Real.log_mul]
      rotate_left
      · positivity
      · positivity
      have : (2 : EReal)⁻¹ = (2⁻¹ : ℝ) := rfl
      rw [this]
      norm_cast
      rw [← mul_add]
    _ ≤ 2⁻¹ * Real.log ((1 - δ)⁻¹ * (δ⁻¹ * 4⁻¹)) := by
      gcongr 2
      by_cases hu_zero : u = 0
      · simp only [hu_zero, zero_mul, neg_zero, add_zero, mul_one, Real.log_one]
        refine Real.log_nonneg ?_
        rw [← mul_assoc, le_mul_inv_iff₀ (by positivity), one_mul]
        exact four_le_mul_inv hδ_pos hδ_lt_one
      gcongr 1
      exact quadratic_inequality hδ_pos hδ_lt_one u
  · let u : ℝ := 2⁻¹ * (δ⁻¹ - (1 - δ)⁻¹)
    have hu_nonneg : 0 ≤ u := by
      simp only [inv_pos, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, sub_nonneg, u]
      rcases lt_or_eq_of_le' hδ_le_one with hδ_lt | rfl
      · rw [inv_le_inv₀ (sub_pos.mpr hδ_lt) (by positivity)]
        grind
      · simp
    have hu_lt : u < δ⁻¹ := by
      suffices u < 2⁻¹ * δ⁻¹ by
        refine this.trans_le ?_
        rw [mul_comm, ← div_eq_mul_inv]
        exact half_le_self (by positivity)
      simp only [mul_sub, sub_lt_self_iff, inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left, sub_pos,
        u, hδ_lt_one]
    let X : ({0, 1} : Set ℝ) → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (1 + u * (x.1 - δ))
    refine le_trans (le_of_eq ?_) (le_iSup _ X)
    rw [iSup_pos ⟨u, hu_nonneg, hu_lt.le, by simp [X]⟩]
    have h_u_mul_lt : u * δ < 1 := by
      calc u * δ < δ⁻¹ * δ := by gcongr
      _ = 1 := inv_mul_cancel₀ hδ_pos.ne'
    have h_one_add_u_mul_pos : 0 < 1 + u * (1 - δ) := by positivity
    have : 0 < 1 + -(u * δ) := by grind
    simp only [zero_sub, mul_neg, ENNReal.log_ofReal, add_neg_le_iff_le_add, zero_add,
      not_le.mpr h_u_mul_lt, ↓reduceIte, not_le.mpr h_one_add_u_mul_pos, X]
    have h1 : (2 : EReal) = (2 : ℝ) := rfl
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [h1, h2, ← ENNReal.ofReal_inv_of_pos (by simp), ← EReal.coe_inv, EReal.coe_ennreal_ofReal]
    simp only [inv_nonneg, Nat.ofNat_nonneg, sup_of_le_left]
    norm_cast
    rw [← mul_add, ← Real.log_mul]
    rotate_left
    · positivity
    · positivity
    congr 2
    simp only [u]
    field_simp
    ring

end ProbabilityTheory
