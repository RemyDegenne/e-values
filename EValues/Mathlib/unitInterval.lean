/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

open unitInterval

lemma doubleton_eq (s : Set ({0, 1} : Set ℝ)) :
    s = ∅ ∨ s = {⟨0, by simp⟩} ∨ s = {⟨1, by simp⟩} ∨ s = {⟨0, by simp⟩, ⟨1, by simp⟩} := by
  sorry

namespace unitInterval

lemma zero_one_mem {x : ({0, 1} : Set ℝ)} : x.1 ∈ I := by
  obtain ⟨x, hx⟩ := x
  cases hx with
  | inl hx =>
    simp_all
  | inr hx =>
    simp_all only [Set.mem_Icc]
    simp_all

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
    simp only [Set.image]
    by_cases hsₐ : s = ∅
    · simp [hsₐ]
    · by_cases hs₀ : s = {⟨0, by simp⟩}
      · simp [hs₀]
      · by_cases hs₁ : s = {⟨1, by simp⟩}
        · simp [hs₁]
        · suffices {x | ∃ a ∈ s, ⟨a, zero_one_mem⟩ = x} = ({0, 1} : Set I) by
            unfold doubleton
            rw [this]
            simp
          push_neg at hsₐ hs₀ hs₁
          have : s = {⟨0, by simp⟩, ⟨1, by simp⟩} := by
            by_contra hc
            push_neg at hc
            --have h := ⟨hsₐ, hs₀, hs₁, hc⟩
            cases doubleton_eq s with
            | inl hs_empty => simp_all
            | inr h =>
              cases h with
              | inl hs_single_0 => simp_all
              | inr h =>
                cases h with
                | inl hs_single_1 => simp_all
                | inr hs_both => simp_all
          aesop

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
  obtain ⟨x, hx⟩ := x
  cases hx with
  | inl hx => simp_all
  | inr hx =>
    rw [Set.mem_singleton_iff] at hx
    simp_all

end unitInterval
