/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import EValues.EValue
import EValues.Numeraire
import EValues.Utility

/-!
# Existence of the Numeraire

-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma ENNReal.log_div (a b : ℝ≥0∞) : ENNReal.log (a / b) = ENNReal.log a - ENNReal.log b := by
  simp_rw [div_eq_mul_inv, ENNReal.log_mul_add, ENNReal.log_inv, sub_eq_add_neg]

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {P : Measure 𝓧} {S : Set (Measure 𝓧)}

section

variable {U : ℝ≥0∞ → EReal}

-- `(u n).sum (fun i x ↦ x • X (n + i) ω)` is a convex combination of `X (n + i) ω` for `i` in the
-- support of `u n`.
lemma exists_convex_sum_tendsto_ae (X : ℕ → 𝓧 → ℝ≥0∞) :
    ∃ (u : ℕ → (ℕ →₀ ℝ≥0)) (Y : 𝓧 → ℝ≥0∞), (∀ n,  (u n).sum (fun _ x ↦ x) = 1) ∧
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ (u n).sum (fun i x ↦ x • X (n + i) ω)) atTop (𝓝 (Y ω)) := by
  sorry

lemma exists_eq_iSup_eintegral_of_le' (hU_ccv : ConcaveOn ℝ≥0 Set.univ U)
    {b : ℝ} (hU_mono : Monotone U) (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S → ∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (Y x) ∂P := by
  sorry

lemma exists_eq_iSup_eintegral_of_le (hU_ccv : ConcaveOn ℝ≥0 Set.univ U)
    {b : ℝ} (hU_mono : Monotone U) (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      (∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (Y x) ∂P) ∧ (∀ᵐ x ∂P, Y x < ∞ → X x < ∞) := by
  sorry

end

/-- The numeraire associated with a bounded utility function. -/
noncomputable
def numeraireOfBounded (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) (S : Set (Measure 𝓧)) : 𝓧 → ℝ≥0∞ :=
  Classical.choose (exists_eq_iSup_eintegral_of_le U.concave U.monotone hU_le P S)

lemma isEVar_numeraireOfBounded (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    IsEVar (numeraireOfBounded U hU_le P S) S :=
  (Classical.choose_spec (exists_eq_iSup_eintegral_of_le U.concave U.monotone hU_le P S)).1

lemma eintegral_le_numeraireOfBounded (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) (S : Set (Measure 𝓧)) {X : 𝓧 → ℝ≥0∞}
    (hX_evar : IsEVar X S) :
    ∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (numeraireOfBounded U hU_le P S x) ∂P :=
  ((Classical.choose_spec (exists_eq_iSup_eintegral_of_le U.concave U.monotone hU_le P S)).2
    X hX_evar).1

lemma lt_top_of_numeraireOfBounded_lt_top (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) (S : Set (Measure 𝓧)) {X : 𝓧 → ℝ≥0∞}
    (hX_evar : IsEVar X S) :
    ∀ᵐ x ∂P, (numeraireOfBounded U hU_le P S x) < ∞ → X x < ∞ :=
  ((Classical.choose_spec (exists_eq_iSup_eintegral_of_le U.concave U.monotone hU_le P S)).2
    X hX_evar).2

lemma eintegral_deriv_mul_le (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) (S : Set (Measure 𝓧)) {Y : 𝓧 → ℝ≥0∞} (hY : IsEVar Y S) :
    ∫ᵉ x, U.deriv (numeraireOfBounded U hU_le P S x)
      * (Y x - numeraireOfBounded U hU_le P S x) ∂P ≤ 0 := by
  sorry

lemma eintegral_deriv_log_mul_le (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      ∫ᵉ x, logUtility.deriv (Y x) * (X x - Y x) ∂P ≤ 0 := by
  sorry

lemma exists_numeraire (P : Measure 𝓧) [IsProbabilityMeasure P]
    (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      ∫⁻ x, X x / Y x ∂P ≤ ∫⁻ x, Y x / Y x ∂P := by -- todo change conclusion to most convenient
  obtain ⟨Y, hY_evar, h_opt⟩ := eintegral_deriv_log_mul_le P S
  refine ⟨Y, hY_evar, fun X hX_evar ↦ ?_⟩
  specialize h_opt X hX_evar
  simp_rw [deriv_logUtility_eq_ennreal] at h_opt
  sorry

open Classical in
/-- The numeraire e-variable. -/
noncomputable
def numeraire (P : Measure 𝓧) [IsProbabilityMeasure P]
    (S : Set (Measure 𝓧)) :
    𝓧 → ℝ≥0∞ :=
  if hS : ∀ μ ∈ S, IsProbabilityMeasure μ
    then Classical.choose (exists_numeraire P S hS)
    else 0

lemma isEVar_numeraire (P : Measure 𝓧) [IsProbabilityMeasure P] (S : Set (Measure 𝓧)) :
    IsEVar (numeraire P S) S := by
  by_cases hS : ∀ μ ∈ S, IsProbabilityMeasure μ
  · rw [numeraire, dif_pos hS]
    exact (Classical.choose_spec (exists_numeraire P S hS)).1
  · rw [numeraire, dif_neg hS]
    exact isEVar_zero

@[fun_prop]
lemma measurable_numeraire (P : Measure 𝓧) [IsProbabilityMeasure P] (S : Set (Measure 𝓧)) :
    Measurable (numeraire P S) := (isEVar_numeraire P S).measurable

lemma lintegral_div_numeraire_le (P : Measure 𝓧) [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫⁻ x, X x / (numeraire P S x) ∂P ≤ ∫⁻ x, (numeraire P S x) / (numeraire P S x) ∂P := by
  rw [numeraire, dif_pos hS]
  exact ((Classical.choose_spec (exists_numeraire P S hS)).2 X hX_evar)

lemma lintegral_div_numeraire_le_one (P : Measure 𝓧) [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫⁻ x, X x / (numeraire P S x) ∂P ≤ 1 := by
  refine (lintegral_div_numeraire_le P hS hX_evar).trans ?_
  calc ∫⁻ x, numeraire P S x / numeraire P S x ∂P
  _ ≤ ∫⁻ x, 1 ∂P := by
    gcongr with x
    exact ENNReal.div_self_le_one
  _ = 1 := by simp

/-- `numeraire` is a numeraire. -/
lemma isNumeraire_numeraire (P : Measure 𝓧) [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    IsNumeraire (numeraire P S) hS P :=
  ⟨isEVar_numeraire P S, fun _ ↦ lintegral_div_numeraire_le_one P hS⟩

-- todo: prove under IsNumeraire assumption, move to the other file
-- todo: prove that log-optimal implies numeraire
/-- The numeraire is log-optimal. -/
theorem eintegral_log_div_numeraire_nonpos (P : Measure 𝓧) [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫ᵉ x, ENNReal.log (X x / numeraire P S x) ∂P ≤ 0:= by
  calc ∫ᵉ x, ENNReal.log (X x / numeraire P S x) ∂P
  _ ≤ ENNReal.log (∫⁻ x, X x / numeraire P S x ∂P) := by
    refine Utility.eintegral_le_map logUtility ?_
    exact hX_evar.measurable.aemeasurable.div (by fun_prop)
  _ ≤ 0 := by
    simp only [ENNReal.log_le_zero_iff]
    exact lintegral_div_numeraire_le_one P hS hX_evar

-- todo: prove under IsNumeraire assumption, move to the other file
/-- The numeraire maximizes the integral of the logarithm. -/
theorem eintegral_log_le_numeraire (P : Measure 𝓧) [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫ᵉ x, ENNReal.log (X x) ∂P ≤ ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P := by
  have h_nonpos := eintegral_log_div_numeraire_nonpos P hS hX_evar
  simp_rw [ENNReal.log_div] at h_nonpos
  rwa [eintegral_sub, EReal.sub_nonpos] at h_nonpos

end ProbabilityTheory
