/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Notation

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

lemma Measure.integrable_comp_iff
    {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    [NormedAddCommGroup E] {κ : Kernel α β} {μ : Measure α} {f : β → E}
    (h_meas : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    Integrable f (κ ∘ₘ μ)
      ↔ (∀ᵐ x ∂μ, Integrable f (κ x)) ∧ Integrable (fun x ↦ ∫ y, ‖f y‖ ∂κ x) μ := by
  rw [Measure.comp_eq_comp_const_apply, ProbabilityTheory.integrable_comp_iff]
  · simp
  · simpa [Kernel.comp_apply]

def aeSet (S : Set (Measure 𝓧)) : Filter 𝓧 := ⨆ m ∈ S, ae m

lemma mem_aeSet_iff {t : Set 𝓧} : t ∈ aeSet S ↔ ∀ m ∈ S, m tᶜ = 0 := by simp [aeSet, mem_ae_iff]

noncomputable
def pairingFun (s : SignedMeasure 𝓧) (f : 𝓧 → ℝ) : ℝ :=
  ∫ ω, f ω ∂s.toJordanDecomposition.posPart
    - ∫ ω, f ω ∂s.toJordanDecomposition.negPart

def integrableFunctions (S : Set (Measure 𝓧)) :=
  {f : 𝓧 → ℝ // Measurable f ∧ ∀ μ ∈ S, Integrable f μ}

def integrableMeasures (L : Set (𝓧 → ℝ)) := {μ : Measure 𝓧 // ∀ f ∈ L, Integrable f μ}

def integrableSignedMeasures (L : Set (𝓧 → ℝ)) :=
  {s : SignedMeasure 𝓧 // ∀ f ∈ L, Integrable f s.totalVariation}
-- being integrable against `totalVariation` is equivalent to being integrable against both
-- positive and negative parts. That is, both parts are in `integrableMeasures L`.

end MeasureTheory

namespace ProbabilityTheory

structure IsEVar (X : 𝓧 → ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  measurable : Measurable X
  lintegral_le_one : ∀ μ ∈ S, ∫⁻ ω, X ω ∂μ ≤ 1

structure IsRandEVar (κ : Kernel 𝓧 ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  lintegral_le_one : ∀ μ ∈ S, ∫⁻ ω, ω ∂(κ ∘ₘ μ) ≤ 1

lemma isRandEVar_iff_isEVar (κ : Kernel 𝓧 ℝ≥0∞) (S : Set (Measure 𝓧)) :
    IsRandEVar κ S ↔ IsEVar (fun x ↦ ∫⁻ y, y ∂κ x) S := by
  refine ⟨fun h ↦ ⟨by fun_prop, fun μ hμ ↦ ?_⟩, fun h ↦ ⟨fun μ hμ ↦ ?_⟩⟩
  · have h' := h.lintegral_le_one μ hμ
    rwa [Measure.lintegral_bind (by fun_prop)] at h'
    exact measurable_id.aemeasurable
  · rw [Measure.lintegral_bind (by fun_prop)]
    · exact h.lintegral_le_one μ hμ
    · exact measurable_id.aemeasurable

structure IsRVar (X : 𝓧 → ℝ) (S : Set (Measure 𝓧)) : Prop where
  measurable : Measurable X
  integrable : ∀ μ ∈ S, Integrable X μ
  integral_nonpos : ∀ μ ∈ S, ∫ ω, X ω ∂μ ≤ 0

structure IsRandRVar (κ : Kernel 𝓧 ℝ) (S : Set (Measure 𝓧)) : Prop where
  integrable : ∀ μ ∈ S, Integrable (fun ω ↦ ω) (κ ∘ₘ μ)
  integral_nonpos : ∀ μ ∈ S, ∫ ω, ω ∂(κ ∘ₘ μ) ≤ 0

lemma isRandRVar_iff_isRVar (κ : Kernel 𝓧 ℝ) (S : Set (Measure 𝓧))
    (h_int : ∀ μ ∈ S, Integrable (fun x ↦ x) (κ ∘ₘ μ)) :
    IsRandRVar κ S ↔ IsRVar (fun x ↦ ∫ y, y ∂κ x) S := by
  refine ⟨fun h ↦ ⟨?_, fun μ hμ ↦ ?_, fun μ hμ ↦ ?_⟩, fun h ↦ ⟨fun μ hμ ↦ ?_, fun μ hμ ↦ ?_⟩⟩
  · refine StronglyMeasurable.measurable ?_
    exact StronglyMeasurable.integral_kernel stronglyMeasurable_id
  · have h_int := h.integrable μ hμ
    -- rw [Measure.integrable_comp_iff] at h_int
    sorry
  · have h' := h.integral_nonpos μ hμ
    have h_int := h.integrable μ hμ
    rwa [Measure.comp_eq_comp_const_apply, Kernel.integral_comp] at h'
    exact h_int
  · rw [Measure.integrable_comp_iff]
    swap; · exact Measurable.aestronglyMeasurable <| by fun_prop
    have h' := h.integrable μ hμ
    sorry
  · have h' := h.integral_nonpos μ hμ
    have h_int := h.integrable μ hμ
    rwa [Measure.comp_eq_comp_const_apply, Kernel.integral_comp]
    sorry
    --rw [Measure.lintegral_bind (by fun_prop) (by fun_prop)]

lemma isEVar_comp {Y : 𝓨 → ℝ≥0∞} {S : Set (Measure 𝓧)} {φ : 𝓧 → 𝓨}
    (hφ : Measurable φ) (h : IsEVar Y {μ.map φ | μ ∈ S}) :
    IsEVar (Y ∘ φ) S where
  measurable := h.measurable.comp hφ
  lintegral_le_one μ hμ := by
    have h' := h.lintegral_le_one (μ.map φ) ?_
    · rwa [lintegral_map h.measurable hφ] at h'
    · exact ⟨μ, hμ, rfl⟩

lemma isRandEVar_comp {ξ : Kernel 𝓨 ℝ≥0∞} {S : Set (Measure 𝓧)} {κ : Kernel 𝓧 𝓨}
    (h : IsRandEVar ξ {κ ∘ₘ μ | μ ∈ S}) :
    IsRandEVar (ξ ∘ₖ κ) S where
  lintegral_le_one μ hμ := by
    have h' := h.lintegral_le_one (κ ∘ₘ μ) ⟨μ, hμ, rfl⟩
    rwa [Measure.comp_assoc] at h'

lemma iSup_isRandEVar_eq_iSup_isEVar (P : Measure 𝓧) (S : Set (Measure 𝓧))
    {U : ℝ≥0∞ → ℝ} (hU : Measurable U) (hU_ccv : ConcaveOn ℝ≥0 Set.univ U) :
    ⨆ (η : Kernel 𝓧 ℝ≥0∞) (hX : IsRandEVar η S), (η ∘ₘ P)[U]
      = ⨆ (X : 𝓧 → ℝ≥0∞) (hX : IsEVar X S), P[U ∘ X] := by
  sorry

lemma iSup_integral_isEVar_le (P : Measure 𝓧) (S : Set (Measure 𝓧)) {φ : 𝓧 → 𝓨}
    (hφ : Measurable φ) {U : ℝ≥0∞ → ℝ} (hU : Measurable U) :
    ⨆ (Y : 𝓨 → ℝ≥0∞) (hY : IsEVar Y {μ.map φ | μ ∈ S}), (P.map φ)[U ∘ Y]
      ≤ ⨆ (X : 𝓧 → ℝ≥0∞) (hX : IsEVar X S), P[U ∘ X] := by
  sorry

lemma iSup_integral_isRandEVar_le (P : Measure 𝓧) (S : Set (Measure 𝓧)) (κ : Kernel 𝓧 𝓨)
    {U : ℝ≥0∞ → ℝ} (hU : Measurable U) :
    ⨆ (ξ : Kernel 𝓨 ℝ≥0∞) (hY : IsRandEVar ξ {κ ∘ₘ μ | μ ∈ S}), (ξ ∘ₘ κ ∘ₘ P)[U]
      ≤ ⨆ (η : Kernel 𝓧 ℝ≥0∞) (hX : IsRandEVar η S), (η ∘ₘ P)[U] := by
  sorry

lemma iSup_integral_isEVar_le' (P : Measure 𝓧) (S : Set (Measure 𝓧)) (κ : Kernel 𝓧 𝓨)
    {U : ℝ≥0∞ → ℝ} (hU : Measurable U) (hU_ccv : ConcaveOn ℝ≥0 Set.univ U) :
    ⨆ (Y : 𝓨 → ℝ≥0∞) (hY : IsEVar Y {κ ∘ₘ μ | μ ∈ S}), (κ ∘ₘ P)[U ∘ Y]
      ≤ ⨆ (X : 𝓧 → ℝ≥0∞) (hX : IsEVar X S), P[U ∘ X] := by
  sorry

end ProbabilityTheory
