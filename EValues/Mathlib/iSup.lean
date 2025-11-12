/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic

lemma iSup₂_eq_sSup {α ι : Type*} [CompleteLattice ι] {P : α → Prop} {g : α → ι} :
    ⨆ (x : α) (_ : P x), g x = sSup {y | ∃ x, P x ∧ y = g x} := by
  rw [sSup_eq_iSup]
  simp_rw [Set.mem_setOf_eq, iSup_exists, iSup_and]
  suffices ⨆ a, ⨆ x, ⨆ (_ : P x), ⨆ (_ : a = g x), a =
      ⨆ x, ⨆ (_ : P x), ⨆ a, ⨆ (_ : a = g x), a by
    simp_rw [this, iSup_iSup_eq_left]
  rw [iSup_comm]
  refine iSup_congr fun i => ?_
  rw [iSup_comm]

lemma iSup₃_eq_sSup {α ι : Type*} [CompleteLattice ι] {P₁ P₂ : α → Prop} {g : α → ι} :
    ⨆ (x : α) (_ : P₁ x) (_ : P₂ x), g x = sSup {y | ∃ x, P₁ x ∧ P₂ x ∧ y = g x} := by
  rw [sSup_eq_iSup]
  simp_rw [Set.mem_setOf_eq, iSup_exists, iSup_and]
  suffices ⨆ a, ⨆ x, ⨆ (_ : P₁ x), ⨆ (_ : P₂ x), ⨆ (_ : a = g x), a =
      ⨆ x, ⨆ (_ : P₁ x), ⨆ (_ : P₂ x), ⨆ a, ⨆ (_ : a = g x), a by
    simp_rw [this, iSup_iSup_eq_left]
  rw [iSup_comm]
  refine iSup_congr fun i => ?_
  rw [iSup_comm]
  refine iSup_congr fun i => ?_
  rw [iSup_comm]

lemma iInf₂_eq_sInf {α ι : Type*} [CompleteLattice ι] {P : α → Prop} {g : α → ι} :
    ⨅ (x : α) (_ : P x), g x = sInf {y | ∃ x, P x ∧ y = g x} := by
  rw [sInf_eq_iInf]
  simp_rw [Set.mem_setOf_eq, iInf_exists, iInf_and]
  suffices ⨅ a, ⨅ x, ⨅ (_ : P x), ⨅ (_ : a = g x), a =
      ⨅ x, ⨅ (_ : P x), ⨅ a, ⨅ (_ : a = g x), a by
    simp_rw [this, iInf_iInf_eq_left]
  rw [iInf_comm]
  refine iInf_congr fun i => ?_
  rw [iInf_comm]

lemma iInf₃_eq_sInf {α ι : Type*} [CompleteLattice ι] {P₁ P₂ : α → Prop} {g : α → ι} :
    ⨅ (x : α) (_ : P₁ x) (_ : P₂ x), g x = sInf {y | ∃ x, P₁ x ∧ P₂ x ∧ y = g x} := by
  rw [sInf_eq_iInf]
  simp_rw [Set.mem_setOf_eq, iInf_exists, iInf_and]
  suffices ⨅ a, ⨅ x, ⨅ (_ : P₁ x), ⨅ (_ : P₂ x), ⨅ (_ : a = g x), a =
      ⨅ x, ⨅ (_ : P₁ x), ⨅ (_ : P₂ x), ⨅ a, ⨅ (_ : a = g x), a by
    simp_rw [this, iInf_iInf_eq_left]
  rw [iInf_comm]
  refine iInf_congr fun i => ?_
  rw [iInf_comm]
  refine iInf_congr fun i => ?_
  rw [iInf_comm]
