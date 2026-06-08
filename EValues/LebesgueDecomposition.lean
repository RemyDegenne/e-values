/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensityFinite


/-!
# Lemma A1: Lebesgue decomposition with respect to a set of measures

-/

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {P : Measure 𝓧} {S : Set (Measure 𝓧)}

/-- The almost everywhere filter with respect to a set of measures, defined as the supremum of the
almost everywhere filters of the measures in the set. -/
def aeSet (S : Set (Measure 𝓧)) : Filter 𝓧 := ⨆ m ∈ S, ae m

lemma mem_aeSet_iff {t : Set 𝓧} : t ∈ aeSet S ↔ ∀ m ∈ S, m tᶜ = 0 := by simp [aeSet, mem_ae_iff]

/-- A set is null for a set of measures if it is measurable and has measure zero for all measures
in the set. -/
structure nullSet (s : Set 𝓧) (S : Set (Measure 𝓧)) : Prop where
  measurableSet : MeasurableSet s
  null : ∀ μ ∈ S, μ s = 0

@[simp]
lemma nullSet_empty : nullSet (∅ : Set 𝓧) S where
  measurableSet := MeasurableSet.empty
  null μ hμ := by simp

lemma nullSet.union {s t : Set 𝓧} (hs : nullSet s S) (ht : nullSet t S) :
    nullSet (s ∪ t) S where
  measurableSet := hs.measurableSet.union ht.measurableSet
  null μ hμ := by simp [hs.null μ hμ, ht.null μ hμ]

lemma compl_mem_aeSet_of_nullSet {s : Set 𝓧} {S : Set (Measure 𝓧)} (hs : nullSet s S) :
    sᶜ ∈ aeSet S := by
  simpa [mem_aeSet_iff] using hs.null

section A1Proof
/-! Copied and adapted from the exhaustion file. Should probably be generalized. -/

variable {α : Type*} {mα : MeasurableSpace α} {ν : Measure α} {S : Set (Measure α)}

lemma exists_auxMaxNullSet_measure_ge (ν : Measure α) [IsFiniteMeasure ν]
    (S : Set (Measure α)) (n : ℕ) :
    ∃ t, MeasurableSet t ∧ nullSet t S
      ∧ (⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s) - 1 / n ≤ ν t := by
  by_cases hC_lt : 1 / n < ⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s
  · have h_lt_top : ⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s < ∞ := by
      refine (?_ : ⨆ (s) (_ : MeasurableSet s)
        (_ : nullSet s S), ν s ≤ ν Set.univ).trans_lt (measure_lt_top _ _)
      refine iSup_le (fun s ↦ ?_)
      exact iSup_le (fun _ ↦ iSup_le (fun _ ↦ measure_mono (Set.subset_univ s)))
    obtain ⟨t, ht⟩ := exists_lt_of_lt_ciSup
      (ENNReal.sub_lt_self h_lt_top.ne hC_lt.ne_bot (by simp) :
          (⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s) - 1 / n
        < ⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s)
    have ht_meas : MeasurableSet t := by
      by_contra h_notMem
      simp only [h_notMem] at ht
      simp at ht
    have ht_mem : nullSet t S := by
      by_contra h_notMem
      simp only [h_notMem] at ht
      simp at ht
    refine ⟨t, ht_meas, ht_mem, ?_⟩
    simp only [ht_meas, ht_mem, iSup_true] at ht
    exact ht.le
  · refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
    push Not at hC_lt
    rw [tsub_eq_zero_of_le hC_lt]
    exact zero_le _

/-- A null set for `S` with close to maximal measure with respect to `ν`. -/
def _root_.MeasureTheory.Measure.auxMaxNullSet (ν : Measure α) [IsFiniteMeasure ν]
    (S : Set (Measure α)) (n : ℕ) : Set α :=
  (exists_auxMaxNullSet_measure_ge ν S n).choose

lemma measurableSet_auxMaxNullSet [IsFiniteMeasure ν] (n : ℕ) :
    MeasurableSet (ν.auxMaxNullSet S n) :=
  (exists_auxMaxNullSet_measure_ge ν S n).choose_spec.1

lemma nullSet_auxMaxNullSet (ν : Measure α) [IsFiniteMeasure ν]
    (S : Set (Measure α)) (n : ℕ) :
    nullSet (ν.auxMaxNullSet S n) S :=
  (exists_auxMaxNullSet_measure_ge ν S n).choose_spec.2.1

lemma measure_auxMaxNullSet_le (ν : Measure α) [IsFiniteMeasure ν] (S : Set (Measure α)) (n : ℕ) :
    ν (ν.auxMaxNullSet S n)
      ≤ ⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s := by
  refine (le_iSup (f := fun s ↦ _) (nullSet_auxMaxNullSet ν S n)).trans ?_
  exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : nullSet s S), ν s) (ν.auxMaxNullSet S n)
    (measurableSet_auxMaxNullSet n)

lemma measure_auxMaxNullSet_ge (ν : Measure α) [IsFiniteMeasure ν] (S : Set (Measure α)) (n : ℕ) :
    (⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s) - 1 / n
      ≤ ν (ν.auxMaxNullSet S n) :=
  (exists_auxMaxNullSet_measure_ge ν S n).choose_spec.2.2

lemma tendsto_measure_auxMaxNullSet (ν : Measure α) [IsFiniteMeasure ν] (S : Set (Measure α)) :
    Tendsto (fun n ↦ ν (ν.auxMaxNullSet S n)) atTop
      (𝓝 (⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_
    tendsto_const_nhds (measure_auxMaxNullSet_ge ν S) (measure_auxMaxNullSet_le ν S)
  nth_rewrite 2 [← tsub_zero (⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s)]
  refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ (Or.inr ENNReal.zero_ne_top)
  simp only [one_div]
  exact ENNReal.tendsto_inv_nat_nhds_zero

/-- A null set for `S` with maximal measure with respect to `ν`. -/
def Measure.maxNullSet (ν : Measure α) [IsFiniteMeasure ν] (S : Set (Measure α)) : Set α :=
  ⋃ n, ν.auxMaxNullSet S n

lemma measurableSet_maxNullSet [IsFiniteMeasure ν] : MeasurableSet (ν.maxNullSet S) :=
  MeasurableSet.iUnion measurableSet_auxMaxNullSet

lemma nullSet_maxNullSet (ν : Measure α) [IsFiniteMeasure ν] (S : Set (Measure α)) :
    nullSet (ν.maxNullSet S) S where
  measurableSet := measurableSet_maxNullSet
  null μ hμ := by
    unfold Measure.maxNullSet
    simp only [measure_iUnion_null_iff]
    intro n
    have h_mem := nullSet_auxMaxNullSet ν S n
    exact h_mem.null μ hμ

lemma measure_maxNullSet (ν : Measure α) [IsFiniteMeasure ν] (S : Set (Measure α)) :
    ν (ν.maxNullSet S) = ⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s := by
  apply le_antisymm
  · refine (le_iSup (f := fun _ ↦ _) (nullSet_maxNullSet ν S)).trans ?_
    exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : nullSet s S), ν s) (ν.maxNullSet S)
      measurableSet_maxNullSet
  · exact le_of_tendsto' (tendsto_measure_auxMaxNullSet ν S)
      (fun _ ↦ measure_mono (Set.subset_iUnion _ _))

end A1Proof

lemma A1_of_isFiniteMeasure (Q : Measure 𝓧) [IsFiniteMeasure Q] (S : Set (Measure 𝓧)) :
    ∃ (ρ : Measure 𝓧 × Measure 𝓧), (∀ t, nullSet t S → ρ.1 t = 0) ∧ (ρ.2 (Q.maxNullSet S)ᶜ = 0) ∧
      Q = ρ.1 + ρ.2 := by
  let N := Q.maxNullSet S
  have hN : MeasurableSet N := measurableSet_maxNullSet
  have hN_mem : nullSet N S := nullSet_maxNullSet Q S
  refine ⟨(Q.restrict Nᶜ, Q.restrict N), ?_, ?_, ?_⟩
  · simp only
    intro s hs
    by_contra h_pos
    suffices Q N < Q (N ∪ s) by
      unfold N at this
      rw [measure_maxNullSet] at this
      refine not_le.mpr this ?_
      refine le_iSup_of_le (Q.maxNullSet S ∪ s) ?_
      refine le_iSup_of_le (measurableSet_maxNullSet.union hs.measurableSet) ?_
      have h_mem : nullSet (Q.maxNullSet S ∪ s) S := hN_mem.union hs
      exact le_iSup_of_le h_mem le_rfl
    calc Q N
    _ < Q.restrict N N + Q.restrict Nᶜ s := by
      conv_lhs => rw [← add_zero (Q N)]
      refine ENNReal.add_lt_add_of_le_of_lt (by simp) (le_of_eq (by simp)) ?_
      exact lt_of_le_of_ne' (zero_le _) h_pos
    _ ≤ Q.restrict N (N ∪ s) + Q.restrict Nᶜ (N ∪ s) := by gcongr <;> simp
    _ = Q (N ∪ s) := by rw [← Measure.add_apply, Measure.restrict_add_restrict_compl hN]
  · simp [N, Measure.restrict_apply hN.compl]
  · simp only
    rw [add_comm, Measure.restrict_add_restrict_compl hN]

lemma A1 (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    ∃ (ρ : Measure 𝓧 × Measure 𝓧), (∀ t, nullSet t S → ρ.1 t = 0) ∧
      (∃ s, nullSet s S ∧ ρ.2 sᶜ = 0) ∧
      Q = ρ.1 + ρ.2 := by
  obtain ⟨ρ, h1, h2, h3⟩ := A1_of_isFiniteMeasure Q.toFinite S
  let f := Q.rnDeriv Q.toFinite
  refine ⟨(ρ.1.withDensity f, ρ.2.withDensity f), fun t ht ↦ ?_, ?_, ?_⟩
  · simp only
    specialize h1 t ht
    rw [withDensity_apply_eq_zero (Measure.measurable_rnDeriv _ _)]
    refine measure_mono_null ?_ h1
    exact Set.inter_subset_right
  · refine ⟨Q.toFinite.maxNullSet S, nullSet_maxNullSet _ _, ?_⟩
    rw [withDensity_apply_eq_zero (Measure.measurable_rnDeriv _ _)]
    exact measure_mono_null Set.inter_subset_right h2
  · simp only
    rw [← withDensity_add_measure, ← h3, Measure.withDensity_rnDeriv_eq]
    exact absolutelyContinuous_toFinite Q

/-- Absolutely continuous part of a measure with respect to a set of measures. -/
noncomputable
def Measure.acSetPart (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) : Measure 𝓧 :=
  (A1 Q S).choose.1

/-- Singular part of a measure with respect to a set of measures. -/
noncomputable
def Measure.singularSetPart (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) : Measure 𝓧 :=
  (A1 Q S).choose.2

/-- A null set for `S` such that `Q.acSetPart S (acSet Q S) = 0` and
`Q.singularSetPart S (Q.acSet Q S)ᶜ = 0` and -/
def acSet (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) : Set 𝓧 :=
  (A1 Q S).choose_spec.2.1.choose

lemma acSetPart_nullSet (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) {t : Set 𝓧}
    (ht : nullSet t S) :
    Q.acSetPart S t = 0 := (A1 Q S).choose_spec.1 t ht

lemma nullSet_acSet (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    nullSet (acSet Q S) S :=
  (A1 Q S).choose_spec.2.1.choose_spec.1

lemma measurableSet_acSet (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    MeasurableSet (acSet Q S) := (nullSet_acSet Q S).measurableSet

@[simp]
lemma acSetPart_acSet (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    Q.acSetPart S (acSet Q S) = 0 :=
  acSetPart_nullSet Q S (nullSet_acSet Q S)

@[simp]
lemma singularSetPart_acSet_compl (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    Q.singularSetPart S (acSet Q S)ᶜ = 0 := (A1 Q S).choose_spec.2.1.choose_spec.2

lemma singular_singularSetPart (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    Q.acSetPart S ⟂ₘ Q.singularSetPart S := by
  refine ⟨acSet Q S, measurableSet_acSet Q S, by simp, by simp⟩

lemma acSetPart_add_singularSetPart (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    Q.acSetPart S + Q.singularSetPart S = Q := (A1 Q S).choose_spec.2.2.symm
lemma measure_acSet_diff {Q : Measure 𝓧} [SFinite Q] {S : Set (Measure 𝓧)}
    {s : Set 𝓧} (hs : nullSet s S) :
    Q (s \ acSet Q S) = 0 := by
  refine le_antisymm ?_ (zero_le _)
  calc Q (s \ acSet Q S)
  _ = Q.acSetPart S (s \ acSet Q S) + Q.singularSetPart S (s \ acSet Q S) := by
    rw [← Measure.add_apply, acSetPart_add_singularSetPart Q S]
  _ ≤ Q.acSetPart S s + Q.singularSetPart S (acSet Q S)ᶜ := by gcongr <;> grind
  _ = 0 := by
    simp only [singularSetPart_acSet_compl, add_zero]
    exact acSetPart_nullSet Q S hs

lemma ae_imp_mem_acSet (Q : Measure 𝓧) [SFinite Q] {S : Set (Measure 𝓧)}
    {s : Set 𝓧} (hs : nullSet s S) :
    ∀ᵐ x ∂Q, x ∈ s → x ∈ acSet Q S := by
  have h_diff := measure_acSet_diff (Q := Q) hs
  simpa [measure_eq_zero_iff_ae_notMem] using h_diff

lemma measure_acSet {Q μ : Measure 𝓧} [SFinite Q] (hS : μ ∈ S) :
    μ (acSet Q S) = 0 := by
  rw [← compl_compl (x := acSet Q S), ← mem_ae_iff]
  have h_le : ae μ ≤ aeSet S := le_iSup₂ μ hS (f := fun μ _ ↦ ae μ)
  exact h_le (compl_mem_aeSet_of_nullSet (nullSet_acSet Q S))

lemma ae_mem_compl_acSet (Q : Measure 𝓧) [SFinite Q] {μ : Measure 𝓧} (hS : μ ∈ S) :
    ∀ᵐ x ∂μ, x ∈ (acSet Q S)ᶜ := by
  simp only [Set.mem_compl_iff, ae_iff, not_not, Set.setOf_mem_eq]
  exact measure_acSet hS

end MeasureTheory
