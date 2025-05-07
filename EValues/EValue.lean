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

/-!
# E-variables



## Main definitions

* TODO

## Main statements

* TODO

-/

open scoped ENNReal

open MeasureTheory ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧} {S : Set (Measure 𝓧)}

namespace MeasureTheory

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

structure IsRVar (X : 𝓧 → ℝ) (S : Set (Measure 𝓧)) : Prop where
  measurable : Measurable X
  integrable : ∀ μ ∈ S, Integrable X μ
  integral_nonpos : ∀ μ ∈ S, ∫ ω, X ω ∂μ ≤ 0

structure IsRandRVar (κ : Kernel 𝓧 ℝ) (S : Set (Measure 𝓧)) : Prop where
  integrable : ∀ μ ∈ S, Integrable (fun ω ↦ ω) (κ ∘ₘ μ)
  integral_nonpos : ∀ μ ∈ S, ∫ ω, ω ∂(κ ∘ₘ μ) ≤ 0

lemma isRandEVar_iff_isEVar (κ : Kernel 𝓧 ℝ≥0∞) (S : Set (Measure 𝓧)) :
    IsRandEVar κ S ↔ IsEVar (fun x ↦ ∫⁻ y, y ∂κ x) S := by
  refine ⟨fun h ↦ ⟨by fun_prop, fun μ hμ ↦ ?_⟩, fun h ↦ ⟨fun μ hμ ↦ ?_⟩⟩
  · have h' := h.lintegral_le_one μ hμ
    rwa [Measure.lintegral_bind (by fun_prop) (by fun_prop)] at h'
  · rw [Measure.lintegral_bind (by fun_prop) (by fun_prop)]
    exact h.lintegral_le_one μ hμ

-- lemma isRandRVar_iff_isRVar (κ : Kernel 𝓧 ℝ) (S : Set (Measure 𝓧)) :
--     IsRandRVar κ S ↔ IsRVar (fun x ↦ ∫ y, y ∂κ x) S := by
--   refine ⟨fun h ↦ ⟨?_, fun μ hμ ↦ ?_, fun μ hμ ↦ ?_⟩, fun h ↦ ⟨fun μ hμ ↦ ?_, fun μ hμ ↦ ?_⟩⟩
--   · sorry
--   · sorry
--   · have h' := h.integral_nonpos μ hμ
--     sorry
--     --rwa [Measure.integral_bind (by fun_prop) (by fun_prop)] at h'
--   · rw [Measure.ae_integrable_of_integrable_comp]
--     sorry
--   · have h' := h.integral_nonpos μ hμ
--     sorry
--     --rw [Measure.lintegral_bind (by fun_prop) (by fun_prop)]

end ProbabilityTheory
