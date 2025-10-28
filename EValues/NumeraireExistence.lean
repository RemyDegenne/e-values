/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import EValues.Numeraire
<<<<<<< HEAD
import EValues.Utility
import EValues.Mathlib.Convex
import EValues.Mathlib.Jensen
=======
>>>>>>> e030b73 (min_imports)

/-!
# Existence of the Numeraire

-/

open MeasureTheory Filter Set ENNReal Function
open scoped ENNReal NNReal Topology

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

variable (P : Measure 𝓧)

lemma ae_pos_numeraire₀ {Y : 𝓧 → ℝ≥0∞} (hYᵢ : ∀ ⦃X⦄, IsEVar X S → ∫⁻ ω, X ω / Y ω ∂P ≤ 1)
    (hY_evar : IsEVar Y S) (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) : ∀ᵐ ω ∂P, Y ω ≠ 0 := by
  by_contra h
  suffices ∫⁻ ω, (Y ω)⁻¹ ∂P = ⊤ by
    have lintegral_ratio_le_one := hYᵢ (isEVar_one S hS)
    simp only [Pi.one_apply, one_div, this] at lintegral_ratio_le_one
    contradiction
  refine lintegral_eq_top_of_measure_eq_top_ne_zero (hY_evar.measurable.inv).aemeasurable ?_
  unfold Filter.Eventually at h
  simp [MeasureTheory.ae] at h
  suffices {ω | Y ω ≠ 0}ᶜ = {ω | (Y ω)⁻¹ = ⊤} by
    rwa [← this]
  ext ω
  simp

lemma lintegral_div_numeraire_eq_lintegral_fsupport₀ {Y X : 𝓧 → ℝ≥0∞}
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    (hYᵢ : ∀ ⦃X⦄, IsEVar X S → ∫⁻ ω, X ω / Y ω ∂P ≤ 1)
    (hY_evar : IsEVar Y S) (hX_evar : IsEVar X S) :
    ∫⁻ ω, X ω / Y ω ∂P = ∫⁻ ω in Y.fsupport, X ω / Y ω ∂P := by
  rw [← lintegral_add_compl _ hY_evar.measurable_fsupport]
  suffices ∫⁻ ω in Y.fsupportᶜ, X ω / Y ω ∂P = 0 by
    simp [this]
  rw [setLIntegral_eq_zero_iff hY_evar.measurable_fsupport.compl
    <| hX_evar.measurable.div <| hY_evar.measurable]
  filter_upwards [ae_pos_numeraire₀ P hYᵢ hY_evar hS] with ω hω hω₂
  rw [Y.fsupport_compl] at hω₂
  rcases hω₂ with hω₂ | hω₂
  · simp_all
  · contradiction

lemma evar_ae_top_imp_numeraire_ae_top₀ {Y X : 𝓧 → ℝ≥0∞}
    (hYᵢ : ∀ ⦃X⦄, IsEVar X S → ∫⁻ ω, X ω / Y ω ∂P ≤ 1)
    (hY_evar : IsEVar Y S) (hX_evar : IsEVar X S) :
    ∀ᵐ ω ∂P, X ω = ⊤ → Y ω = ⊤ := by
  by_contra h
  unfold Filter.Eventually at h
  replace h : P {ω | X ω = ⊤ ∧ Y ω ≠ ⊤} ≠ 0 := by
    suffices {ω | X ω = ⊤ ∧ Y ω ≠ ⊤} = {ω | X ω = ⊤ → Y ω = ⊤}ᶜ by
      rw [this]
      exact h
    ext ω
    simp
  have m : MeasurableSet {ω | X ω = ⊤ ∧ Y ω ≠ ⊤} := by
    suffices MeasurableSet {ω | X ω = ⊤} ∧ MeasurableSet {ω | Y ω ≠ ⊤} from this.1.inter this.2
    constructor
    · exact hX_evar.measurable <| measurableSet_singleton ⊤
    · rw [← MeasurableSet.compl_iff]
      suffices {ω | Y ω ≠ ⊤}ᶜ = {ω | Y ω = ⊤} by
        rw [this]
        exact hY_evar.measurable <| measurableSet_singleton ⊤
      ext ω
      simp
  specialize hYᵢ hX_evar
  rw [← lintegral_add_compl _ m] at hYᵢ
  suffices ∀ ω ∈ {ω | X ω = ⊤ ∧ Y ω ≠ ⊤}, X ω / Y ω = ⊤ by
    rw [setLIntegral_congr_fun m this] at hYᵢ
    simp only [ne_eq, lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
      univ_inter] at hYᵢ
    rw [top_mul h] at hYᵢ
    contradiction
  intro ω hω
  simp [hω.1, ENNReal.top_div, hω.2]

lemma lintegral_div_numeraire_eq_rev_lintegral_fsupport₀ {Y X : 𝓧 → ℝ≥0∞}
    (hYᵢ : ∀ ⦃X⦄, IsEVar X S → ∫⁻ ω, X ω / Y ω ∂P ≤ 1)
    (hY_evar : IsEVar Y S) (hX_evar : IsEVar X S) :
    ∫⁻ ω, X ω / Y ω ∂P = ∫⁻ ω in X.fsupport, X ω / Y ω ∂P := by
  rw [← lintegral_add_compl _ hX_evar.measurable_fsupport]
  suffices ∫⁻ ω in X.fsupportᶜ, X ω / Y ω ∂P = 0 by
    simp [this]
  rw [setLIntegral_eq_zero_iff (hX_evar.measurable_fsupport).compl
    <| hX_evar.measurable.div <| hY_evar.measurable]
  filter_upwards [evar_ae_top_imp_numeraire_ae_top₀ P hYᵢ hY_evar hX_evar] with ω hω hω₂
  rw [X.fsupport_compl] at hω₂
  rcases hω₂ with hω₂ | hω₂
  · rw [hω₂, hω hω₂]
    simp
  · rw [hω₂]
    simp

variable [IsProbabilityMeasure P]

lemma measure_fsupport_numeraire_ne_zero_or_ae_top₀ {Y : 𝓧 → ℝ≥0∞}
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    (hYᵢ : ∀ ⦃X⦄, IsEVar X S → ∫⁻ ω, X ω / Y ω ∂P ≤ 1)
    (hY_evar : IsEVar Y S) :
    P Y.fsupport ≠ 0 ∨ Y =ᵐ[P] ⊤ := by
  by_contra h
  push_neg at h
  have ratio_eq_zero : ∫⁻ ω, Y ω / Y ω ∂P = 0 := by
    rw [lintegral_div_numeraire_eq_lintegral_fsupport₀ P hS hYᵢ hY_evar hY_evar]
    exact setLIntegral_measure_zero _ _ h.1
  rw [lintegral_eq_zero_iff <| hY_evar.measurable.div hY_evar.measurable]
    at ratio_eq_zero
  have mₜ : MeasurableSet {ω | Y ω = ⊤} := hY_evar.measurable <| measurableSet_singleton ⊤
  have m₀ : MeasurableSet {ω | Y ω = 0} := hY_evar.measurable <| measurableSet_singleton 0
  replace ratio_eq_zero : P Y.fsupportᶜ = P univ := by
    rw [measure_univ, ← prob_compl_eq_zero_iff (hY_evar.measurable_fsupport).compl]
    suffices Y.fsupportᶜ ∈ ae P by
      simp_all [Y.fsupport_compl, MeasureTheory.ae]
    filter_upwards [ratio_eq_zero] with ω hω
    simp_all only [measurableSet_setOf, Y.fsupport_compl, Pi.zero_apply,
      ENNReal.div_eq_zero_iff, mem_union, mem_setOf_eq]
    exact hω.symm
  rw [Y.fsupport_compl, measure_union ?_ m₀] at ratio_eq_zero
  · have : {ω | Y ω = 0} = {ω | Y ω ≠ 0}ᶜ := by
      ext ω
      simp
    rw [this, ae_pos_numeraire₀ P hYᵢ hY_evar hS, add_zero, measure_univ,
      ← prob_compl_eq_zero_iff mₜ] at ratio_eq_zero
    exact h.2 ratio_eq_zero
  · rw [disjoint_iff_inter_eq_empty]
    ext ω
    simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro hω
    rw [hω]
    simp

lemma inv_lintegral_div_numeraire_eq_one {Y X : 𝓧 → ℝ≥0∞}
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    (hYᵢ : ∀ ⦃X⦄, IsEVar X S → ∫⁻ ω, X ω / Y ω ∂P ≤ 1)
    (hY_evar : IsEVar Y S)
    (hXᵢ : ∀ ⦃Y⦄, IsEVar Y S → ∫⁻ ω, Y ω / X ω ∂P ≤ 1)
    (hX_evar : IsEVar X S)
    (h : P Y.fsupport ≠ 0) : (∫⁻ ω, X ω / Y ω ∂P)⁻¹ = 1 := by
  set W := X / Y
  rw [lintegral_div_numeraire_eq_lintegral_fsupport₀ P hS hYᵢ hY_evar hX_evar]
  suffices 1 ≤ (∫⁻ ω in Y.fsupport, W ω ∂P)⁻¹ by
    refine le_antisymm ?_ this
    suffices (∫⁻ ω in Y.fsupport, W ω ∂P)⁻¹ ≤ ∫⁻ ω in Y.fsupport, (W ω)⁻¹ ∂P by
      trans ∫⁻ ω in Y.fsupport, (W ω)⁻¹ ∂P
      · assumption
      · rw [setLIntegral_congr_fun hY_evar.measurable_fsupport <| ENNReal.inv_div_fsupport X Y]
        rw [← lintegral_div_numeraire_eq_rev_lintegral_fsupport₀ P hXᵢ hX_evar hY_evar]
        exact hXᵢ hY_evar
    refine strictConvexOn_inv.convexOn.map_set_lintegral_le continuousOn_inv ?_ h ?_ ?_
    · exact isClosed_univ
    · simp
    · simp
  simp only [Pi.div_apply,
    ← lintegral_div_numeraire_eq_lintegral_fsupport₀ P hS hYᵢ hY_evar hX_evar, le_inv_iff_mul_le,
    one_mul, W]
  exact hYᵢ hX_evar

theorem ae_unique_numeraire {Y X : 𝓧 → ℝ≥0∞}
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    (hYᵢ : ∀ ⦃X⦄, IsEVar X S → ∫⁻ ω, X ω / Y ω ∂P ≤ 1)
    (hY_evar : IsEVar Y S)
    (hXᵢ : ∀ ⦃Y⦄, IsEVar Y S → ∫⁻ ω, Y ω / X ω ∂P ≤ 1)
    (hX_evar : IsEVar X S) : Y =ᵐ[P] X := by
  have strc_convex := strictConvexOn_inv
  rcases measure_fsupport_numeraire_ne_zero_or_ae_top₀ P hS hXᵢ hX_evar with μ_fsupport | hXₜ
  · let W := Y / X
    have inv_avg_eq_one : (∫⁻ ω in X.fsupport, W ω ∂P)⁻¹ = 1 := by
      simp only [Pi.div_apply,
        ← lintegral_div_numeraire_eq_lintegral_fsupport₀ P hS hXᵢ hX_evar hY_evar, W]
      exact inv_lintegral_div_numeraire_eq_one P hS hXᵢ hX_evar hYᵢ hY_evar μ_fsupport
    have avg_eq_one : ∫⁻ ω, W ω ∂P = 1 := by
      simp only [Pi.div_apply, ENNReal.inv_eq_one, W] at inv_avg_eq_one
      rwa [← lintegral_div_numeraire_eq_lintegral_fsupport₀ P hS hXᵢ hX_evar hY_evar]
        at inv_avg_eq_one
    have strict_Jensen : W =ᵐ[P] const 𝓧 (∫⁻ ω, W ω ∂P) ∨
        (∫⁻ ω in X.fsupport, W ω ∂P)⁻¹ < ∫⁻ ω in X.fsupport, (W ω)⁻¹ ∂P := by
      refine strc_convex.ae_eq_const_or_map_set_lintegral_lt continuousOn_inv ?_ μ_fsupport ?_ ?_
      · exact isClosed_univ
      · simp
      · simp
    rcases strict_Jensen with h | h
    · rw [avg_eq_one] at h
      filter_upwards [h] with ω hx
      simp only [Pi.div_apply, const_apply, W] at hx
      exact ENNReal.eq_of_div_eq_one hx
    · exfalso
      rw [inv_avg_eq_one] at h
      rw [setLIntegral_congr_fun hX_evar.measurable_fsupport <| ENNReal.inv_div_fsupport Y X] at h
      refine h.not_ge ?_
      rw [← lintegral_div_numeraire_eq_rev_lintegral_fsupport₀ P hYᵢ hY_evar hX_evar]
      exact hYᵢ hX_evar
  · filter_upwards [hXₜ, evar_ae_top_imp_numeraire_ae_top₀ P hYᵢ hY_evar hX_evar] with ω hω hω₂
    simp_all

lemma exists_numeraire (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
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
def numeraire (S : Set (Measure 𝓧)) : 𝓧 → ℝ≥0∞ :=
  if hS : ∀ μ ∈ S, IsProbabilityMeasure μ
    then Classical.choose (exists_numeraire P S hS)
    else 0

lemma isEVar_numeraire (S : Set (Measure 𝓧)) : IsEVar (numeraire P S) S := by
  by_cases hS : ∀ μ ∈ S, IsProbabilityMeasure μ
  · rw [numeraire, dif_pos hS]
    exact (Classical.choose_spec (exists_numeraire P S hS)).1
  · rw [numeraire, dif_neg hS]
    exact isEVar_zero

@[fun_prop]
lemma measurable_numeraire (S : Set (Measure 𝓧)) :
    Measurable (numeraire P S) := (isEVar_numeraire P S).measurable

lemma fsupport_measurable_numeraire (S : Set (Measure 𝓧)) :
    MeasurableSet (numeraire P S).fsupport :=
  (isEVar_numeraire P S).measurable_fsupport

lemma lintegral_div_numeraire_le (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫⁻ x, X x / (numeraire P S x) ∂P ≤ ∫⁻ x, (numeraire P S x) / (numeraire P S x) ∂P := by
  rw [numeraire, dif_pos hS]
  exact ((Classical.choose_spec (exists_numeraire P S hS)).2 X hX_evar)

lemma lintegral_div_numeraire_le_one (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
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

<<<<<<< HEAD
-- todo: prove under IsNumeraire assumption, move to the other file
-- todo: prove that log-optimal implies numeraire
/-- The numeraire is log-optimal. -/
theorem eintegral_log_div_numeraire_nonpos (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
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
theorem eintegral_log_le_numeraire (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫ᵉ x, ENNReal.log (X x) ∂P ≤ ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P := by
  have h_nonpos := eintegral_log_div_numeraire_nonpos P hS hX_evar
  simp_rw [ENNReal.log_div] at h_nonpos
  rwa [eintegral_sub, EReal.sub_nonpos] at h_nonpos
=======
lemma IsNumeraire.ae_eq_numeraire [IsProbabilityMeasure P] {X : 𝓧 → ℝ≥0∞}
    {hS : ∀ μ ∈ S, IsProbabilityMeasure μ} (hX : IsNumeraire X hS P) :
    X =ᵐ[P] numeraire P S :=
  hX.ae_unique (isNumeraire_numeraire P hS)
>>>>>>> ce82df3 (move lemmas to Numeraire.lean)

lemma ae_pos_numeraire (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) : ∀ᵐ ω ∂P, numeraire P S ω ≠ 0 :=
  ae_pos_numeraire₀ P (fun _ ↦ lintegral_div_numeraire_le_one P hS) (isEVar_numeraire P S) hS

lemma lintegral_div_numeraire_eq_lintegral_fsupport (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) : ∫⁻ ω, X ω / numeraire P S ω ∂P =
      ∫⁻ ω in (numeraire P S).fsupport, X ω / numeraire P S ω ∂P :=
  lintegral_div_numeraire_eq_lintegral_fsupport₀ P hS
    (fun _ ↦ lintegral_div_numeraire_le_one P hS) (isEVar_numeraire P S) hX_evar

lemma evar_ae_top_imp_numeraire_ae_top (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) : ∀ᵐ ω ∂P, X ω = ⊤ → numeraire P S ω = ⊤ :=
  evar_ae_top_imp_numeraire_ae_top₀ P
    (fun _ ↦ lintegral_div_numeraire_le_one P hS) (isEVar_numeraire P S) hX_evar

lemma lintegral_div_numeraire_eq_rev_lintegral_fsupport (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) : ∫⁻ ω, X ω / numeraire P S ω ∂P =
      ∫⁻ ω in X.fsupport, X ω / numeraire P S ω ∂P :=
  lintegral_div_numeraire_eq_rev_lintegral_fsupport₀ P
    (fun _ ↦ lintegral_div_numeraire_le_one P hS) (isEVar_numeraire P S) hX_evar

lemma measure_fsupport_numeraire_ne_zero_or_ae_top (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    P (numeraire P S).fsupport ≠ 0 ∨ numeraire P S =ᵐ[P] ⊤ :=
  measure_fsupport_numeraire_ne_zero_or_ae_top₀ P hS
    (fun _ ↦ lintegral_div_numeraire_le_one P hS) (isEVar_numeraire P S)

end ProbabilityTheory
