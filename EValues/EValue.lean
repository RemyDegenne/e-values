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

namespace MeasureTheory

-- was added to Mathlib. Remove in a future bump.
lemma Measure.integrable_comp_iff
    {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    [NormedAddCommGroup E] {κ : Kernel α β} {μ : Measure α} {f : β → E}
    (h_meas : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    Integrable f (κ ∘ₘ μ)
      ↔ (∀ᵐ x ∂μ, Integrable f (κ x)) ∧ Integrable (fun x ↦ ∫ y, ‖f y‖ ∂κ x) μ := by
  rw [Measure.comp_eq_comp_const_apply, ProbabilityTheory.integrable_comp_iff]
  · simp
  · simpa [Kernel.comp_apply]

/-- The almost everywhere filter with respect to a set of measures, defined as the supremum of the
almost everywhere filters of the measures in the set. -/
def aeSet (S : Set (Measure 𝓧)) : Filter 𝓧 := ⨆ m ∈ S, ae m

lemma mem_aeSet_iff {t : Set 𝓧} : t ∈ aeSet S ↔ ∀ m ∈ S, m tᶜ = 0 := by simp [aeSet, mem_ae_iff]

end MeasureTheory

namespace ProbabilityTheory

/-- A random variable `X` is an e-variable for a set of measures `S` if it is measurable and
its expectation is at most one for all measures in `S`. -/
structure IsEVar (X : 𝓧 → ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  measurable : Measurable X := by fun_prop
  lintegral_le_measure_univ : ∀ μ ∈ S, ∫⁻ ω, X ω ∂μ ≤ μ .univ

/-- A random variables `X` is an e-variable for a set of measures `S` if it is measurable and
its expectation is at most one for all measures in `S`. -/
structure IsRandEVar (κ : Kernel 𝓧 ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  [markov : IsMarkovKernel κ]
  lintegral_le_one : ∀ μ ∈ S, ∫⁻ ω, ω ∂(κ ∘ₘ μ) ≤ μ .univ

variable {X Y : 𝓧 → ℝ≥0∞} {κ η : Kernel 𝓧 ℝ≥0∞} [IsMarkovKernel κ] {S T : Set (Measure 𝓧)}

/-- A kernel `κ` is a randomized e-variable iff its mean function `x ↦ ∫⁻ y, y ∂κ x` is an
e-variable. -/
lemma isRandEVar_iff_isEVar : IsRandEVar κ S ↔ IsEVar (fun x ↦ ∫⁻ y, y ∂κ x) S := by
  refine ⟨fun h ↦ ⟨by fun_prop, fun μ hμ ↦ ?_⟩, fun h ↦ ⟨fun μ hμ ↦ ?_⟩⟩
  · have h' := h.lintegral_le_one μ hμ
    rwa [Measure.lintegral_bind (by fun_prop)] at h'
    exact measurable_id.aemeasurable
  · rw [Measure.lintegral_bind (by fun_prop)]
    · exact h.lintegral_le_measure_univ μ hμ
    · exact measurable_id.aemeasurable

lemma IsEVar.isRandEVar_deterministic (hX : IsEVar X S) :
    IsRandEVar (Kernel.deterministic X hX.measurable) S where
  lintegral_le_one μ hμ := by
    rw [Measure.lintegral_bind (Kernel.measurable _).aemeasurable]
    · simpa using hX.lintegral_le_measure_univ μ hμ
    · exact measurable_id.aemeasurable

lemma isEVar_of_isEmpty (hS : IsEmpty S) (hX : Measurable X) :
   IsEVar X S where
  lintegral_le_measure_univ := by simp_all

lemma isEVar_zero : IsEVar 0 S where lintegral_le_measure_univ μ hμ := by simp

lemma isEVar_one (S : Set (Measure 𝓧)) : IsEVar 1 S where lintegral_le_measure_univ μ hμ := by simp

lemma isEVar_fun_one (S : Set (Measure 𝓧)) : IsEVar (fun _ ↦ 1) S := isEVar_one S

lemma IsEVar.congr (hX : IsEVar X S) (hY : Measurable Y) (hXY : ∀ μ ∈ S, X =ᵐ[μ] Y) :
    IsEVar Y S where
  measurable := hY
  lintegral_le_measure_univ μ hμ := by
    rw [lintegral_congr_ae (hXY μ hμ).symm]
    exact hX.lintegral_le_measure_univ μ hμ

lemma IsEVar.ae_lt_top (hX : IsEVar X S) {μ : Measure 𝓧} [IsFiniteMeasure μ] (hμ : μ ∈ S) :
    ∀ᵐ ω ∂μ, X ω < ⊤ := by
  by_contra h
  suffices ∫⁻ ω, X ω ∂μ = ⊤ by
    have lintegral_le := hX.lintegral_le_measure_univ μ hμ
    simp [this] at lintegral_le
  refine lintegral_eq_top_of_measure_eq_top_ne_zero hX.measurable.aemeasurable ?_
  suffices ¬ μ {x | ¬ X x < ⊤} = 0 by simpa [lt_top_iff_ne_top] using this
  rwa [← ae_iff]

lemma IsEVar.ae_ne_top (hX : IsEVar X S) {μ : Measure 𝓧} [IsFiniteMeasure μ] (hμ : μ ∈ S) :
    ∀ᵐ ω ∂μ, X ω ≠ ⊤ := by
  filter_upwards [hX.ae_lt_top hμ] with ω hω using hω.ne

lemma IsEVar.measurable_fsupport (hX : IsEVar X S) :
    MeasurableSet X.fsupport := by
  suffices MeasurableSet {ω | X ω ≠ ⊤} ∧ MeasurableSet {ω | X ω ≠ 0} from this.1.inter this.2
  constructor
  · rw [← MeasurableSet.compl_iff]
    suffices {ω | X ω ≠ ⊤}ᶜ = {ω | X ω = ⊤} by
      rw [this]
      exact hX.measurable <| measurableSet_singleton ⊤
    ext ω
    simp
  · rw [← MeasurableSet.compl_iff]
    suffices {ω | X ω ≠ 0}ᶜ = {ω | X ω = 0} by
      rw [this]
      exact hX.measurable <| measurableSet_singleton 0
    ext ω
    simp

lemma IsEVar.mono (hY : IsEVar Y S) (hX : Measurable X) (hXY : X ≤ Y) : IsEVar X S where
  lintegral_le_measure_univ μ hμ := (lintegral_mono hXY).trans (hY.lintegral_le_measure_univ μ hμ)

lemma IsRandEVar.mono (hη : IsRandEVar η S) (hκη : κ ≤ η) : IsRandEVar κ S where
  lintegral_le_one μ hμ := by
    refine (lintegral_mono' ?_ le_rfl).trans (hη.lintegral_le_one μ hμ)
    rw [MeasureTheory.Measure.le_iff]
    intro A hA
    rw [μ.bind_apply hA κ.aemeasurable, μ.bind_apply hA η.aemeasurable]
    exact lintegral_mono fun x ↦ hκη x A

lemma IsEVar.anti_set (hST : S ⊆ T) (hX : IsEVar X T) : IsEVar X S where
  measurable := hX.measurable
  lintegral_le_measure_univ μ hμ := hX.lintegral_le_measure_univ μ (hST hμ)

lemma IsRandEVar.anti_set (hST : S ⊆ T) (hκ : IsRandEVar κ T) : IsRandEVar κ S where
  lintegral_le_one μ hμ := hκ.lintegral_le_one μ (hST hμ)

lemma IsEVar.comp {Y : 𝓨 → ℝ≥0∞} {S : Set (Measure 𝓧)} {φ : 𝓧 → 𝓨}
    (hφ : Measurable φ) (h : IsEVar Y {μ.map φ | μ ∈ S}) :
    IsEVar (Y ∘ φ) S where
  measurable := h.measurable.comp hφ
  lintegral_le_measure_univ μ hμ := by
    have h' := h.lintegral_le_measure_univ (μ.map φ) ⟨μ, hμ, rfl⟩
    rwa [lintegral_map h.measurable hφ, Measure.map_apply (by fun_prop) .univ] at h'

lemma IsRandEVar.comp {ξ : Kernel 𝓨 ℝ≥0∞} {S : Set (Measure 𝓧)}
    {κ : Kernel 𝓧 𝓨} [IsMarkovKernel κ] (h : IsRandEVar ξ {κ ∘ₘ μ | μ ∈ S}) :
    IsRandEVar (ξ ∘ₖ κ) S where
  markov := have := h.markov; inferInstance
  lintegral_le_one μ hμ := by
    have h' := h.lintegral_le_one (κ ∘ₘ μ) ⟨μ, hμ, rfl⟩
    rw [Measure.comp_assoc, Measure.bind_apply .univ (by fun_prop)] at h'
    simpa using h'

end ProbabilityTheory
