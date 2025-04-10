/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib

/-!
# Almost everywhere equality with respect to a set of measures



## Main definitions

* TODO

## Main statements

* TODO

-/

open scoped ENNReal

namespace MeasureTheory

namespace Measure

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

lemma sup_apply {s : Set α} (hs : MeasurableSet s) :
    (μ ⊔ ν) s = sSup {m | ∃ t, m = μ (t ∩ s) + ν (tᶜ ∩ s)} := by
  sorry

lemma le_ae_sup : ae μ ⊔ ae ν ≤ ae (μ ⊔ ν) := by
  intro t
  simp only [Filter.mem_sup, mem_ae_iff]
  intro h
  constructor
  · have h_le : μ ≤ μ ⊔ ν := le_sup_left
    refine le_antisymm ?_ zero_le'
    exact (h_le _).trans_eq h
  · have h_le : ν ≤ μ ⊔ ν := le_sup_right
    refine le_antisymm ?_ zero_le'
    exact (h_le _).trans_eq h

-- may not be true
lemma ae_sup : ae (μ ⊔ ν) = ae μ ⊔ ae ν := by
  refine le_antisymm ?_ le_ae_sup
  intro t
  simp only [Filter.mem_sup, mem_ae_iff]
  rintro ⟨hμ, hν⟩
  sorry

lemma sSup_apply {m : Set (Measure α)} {s : Set α} (hs : MeasurableSet s) (h : m.Nonempty) :
    sSup m s = ⨆ (t : ℕ → Set α) (_ : Set.iUnion t ⊆ s), ∑' n, ⨆ μ ∈ m, μ (t n) := by
  sorry

-- todo: probably needs a measurability hypothesis
lemma iSup_apply {ι} [Nonempty ι] (m : ι → Measure α) (s : Set α) :
    (⨆ i, m i) s = ⨆ (t : ℕ → Set α) (_ : Set.iUnion t ⊆ s), ∑' n, ⨆ i, m i (t n) := by
  sorry

@[simp]
lemma bot_eq_zero : (⊥ : Measure α) = 0 := rfl

end Measure

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧}
  {S : Set (Measure 𝓧)}

def aeSet (S : Set (Measure 𝓧)) : Filter 𝓧 := ⨆ m ∈ S, ae m

lemma mem_aeSet_iff {t : Set 𝓧} : t ∈ aeSet S ↔ ∀ m ∈ S, m tᶜ = 0 := by simp [aeSet, mem_ae_iff]

-- dubious (due to a sorry somewhere else)
theorem aeSet_eq (S : Set (Measure 𝓧)) : aeSet S = ae (⨆ m ∈ S, m) := by
  ext t
  simp only [aeSet, Filter.mem_iSup, mem_ae_iff]
  simp only [Measure.iSup_apply, ENNReal.iSup_eq_zero, ENNReal.tsum_eq_zero]
  constructor
  · intro h u hut i μ
    by_cases hμS : μ ∈ S
    · simp only [hμS, iSup_pos]
      specialize h μ hμS
      refine measure_mono_null ?_ h
      exact (Set.subset_iUnion u i).trans hut
    · simp [hμS]
  · intro h μ hμS
    specialize h (fun _ ↦ tᶜ) (by simp) 0 μ
    simpa [hμS] using h

end MeasureTheory
