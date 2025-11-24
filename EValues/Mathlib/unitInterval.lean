/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

open unitInterval MeasureTheory ENNReal

lemma doubleton_eq (s : Set ({0, 1} : Set ℝ)) :
    s = ∅ ∨ s = {⟨0, by simp⟩} ∨ s = {⟨1, by simp⟩} ∨ s = {⟨0, by simp⟩, ⟨1, by simp⟩} := by
  grind

lemma doubleton_univ : ({⟨0, by simp⟩, ⟨1, by simp⟩} : Set ({0, 1} : Set ℝ)) = Set.univ := by
  grind

lemma doubleton_union_univ : ({⟨0, by simp⟩} : Set ({0, 1} : Set ℝ)) ∪ {⟨1, by simp⟩}
    = Set.univ := by
  grind

lemma measure_doubleton_eq_add (μ : Measure ({0, 1} : Set ℝ)) :
    μ = μ {⟨0, by simp⟩} • Measure.dirac (⟨0, by simp⟩ : ({0, 1} : Set ℝ)) +
      μ {⟨1, by simp⟩} • Measure.dirac (⟨1, by simp⟩ : ({0, 1} : Set ℝ)) := by
  rw [Measure.ext_iff_singleton]
  intro x
  by_cases hx0 : x = ⟨0, by simp⟩
  · simp [hx0]
  · have hx1 : x = ⟨1, by simp⟩ := by grind
    simp [hx1]

lemma doubleton_lintegral {μ : Measure ({0, 1} : Set ℝ)} {f : ({0, 1} : Set ℝ) → ℝ≥0∞} :
    ∫⁻ x, f x ∂μ = μ {⟨0, by simp⟩} * f ⟨0, by simp⟩ + μ {⟨1, by simp⟩} * f ⟨1, by simp⟩ := by
  conv_lhs => rw [measure_doubleton_eq_add μ]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, lintegral_smul_measure,
    lintegral_dirac]
  abel

namespace unitInterval

lemma zero_one_mem {x : ({0, 1} : Set ℝ)} : x.1 ∈ I := by grind

/-- Define the embedding from the doubleton set {0, 1} into the unit interval I -/
def doubleton (x : ({0, 1} : Set ℝ)) := (⟨x.1, zero_one_mem⟩ : I)

lemma doubleton_emb : MeasurableEmbedding doubleton where
  injective := by
    intro x y hxy
    simp_all only [doubleton, Subtype.mk.injEq]
    ext
    trivial
  measurable := by fun_prop
  measurableSet_image' := by
    intro s hs
    by_cases h0 : ⟨0, by simp⟩ ∈ s <;> by_cases h1 : ⟨1, by simp⟩ ∈ s
    · suffices doubleton '' s = ({0, 1} : Set I) by simp [this]
      have : s = Set.univ := by grind
      simp only [doubleton, this, Set.image_univ]
      ext x
      simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases hx : x = 0
      · simp only [hx, zero_ne_one, or_false, iff_true]
        exact ⟨0, by simp, rfl⟩
      · simp only [hx, false_or]
        refine ⟨fun ⟨a, ha, h_eq⟩ ↦ ?_, fun h ↦ ⟨1, by simp, h.symm⟩⟩
        rw [← h_eq]
        rcases ha with rfl | rfl
        · simp_all
        · rfl
    · have : s = {⟨0, by simp⟩} := by grind
      simp [this]
    · have : s = {⟨1, by simp⟩} := by grind
      simp [this]
    · have : s = ∅ := by grind
      simp [this]

@[fun_prop]
lemma measurable_doubleton : Measurable doubleton := doubleton_emb.measurable

/-- Define an inverse from the unit interval I to the doubleton set {0, 1} -/
noncomputable def doubleton_inv (x : I) : ({0, 1} : Set ℝ) :=
  if h : (x : ℝ) = 0 then ⟨0, by simp⟩ else ⟨1, by simp⟩

@[fun_prop]
lemma measurable_doubleton_inv : Measurable doubleton_inv := by
  unfold doubleton_inv
  refine Measurable.ite ?_ ?_ ?_ <;> simp

lemma doubleton_left_inv : Function.LeftInverse doubleton_inv doubleton := by
  intro x
  simp only [doubleton, doubleton_inv]
  grind

end unitInterval
