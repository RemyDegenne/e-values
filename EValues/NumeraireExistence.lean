/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
import EValues.Numeraire
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Existence of the Numeraire

-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

-- proved in the Brownian motion project
lemma komlos_ennreal {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → ℝ≥0∞}
    (hX : ∀ n, Measurable (X n)) (P : Measure Ω) [IsFiniteMeasure P] :
    ∃ (Y : ℕ → Ω → ℝ≥0∞) (Y_lim : Ω → ℝ≥0∞),
      (∀ n, Y n ∈ convexHull ℝ≥0∞ (Set.range fun m ↦ X (n + m))) ∧ Measurable Y_lim ∧
      ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (Y_lim ω)) := by
  sorry

lemma komlos_ennreal' {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → ℝ≥0∞}
    (hX : ∀ n, Measurable (X n)) (P : Measure Ω) [SFinite P] :
    ∃ (Y : ℕ → Ω → ℝ≥0∞) (Y_lim : Ω → ℝ≥0∞),
      (∀ n, Y n ∈ convexHull ℝ≥0∞ (Set.range fun m ↦ X (n + m))) ∧ Measurable Y_lim ∧
      ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (Y_lim ω)) := by
  obtain ⟨Y, Ylim, hY_cvx, hYlim_meas, hY_tendsto⟩ := komlos_ennreal hX P.toFinite
  exact ⟨Y, Ylim, hY_cvx, hYlim_meas, absolutelyContinuous_toFinite P hY_tendsto⟩

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {P : Measure 𝓧} {S : Set (Measure 𝓧)}

section

variable {U : ℝ≥0∞ → EReal}

-- needs only two things about IsEVar: convex and closed under a.e. limits
/-- There exists a utility-maximizing e-variable which is infinite whenever another e-variable
is infinite. -/
lemma exists_eq_iSup_eintegral_of_le' (hU_ccv : ConcaveOn ℝ≥0 Set.univ U)
    {b : ℝ} (hU_cont : Continuous U) (hU_mono : Monotone U) (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [SFinite P] (S : Set (Measure 𝓧)) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S → ∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (Y x) ∂P := by
  let S' := {y | ∃ X, IsEVar X S ∧ y = ∫ᵉ x, U (X x) ∂P}
  have hS' : S'.Nonempty := ⟨∫ᵉ x, U 1 ∂P, ⟨1, isEVar_one _, rfl⟩⟩
  have hS'_bdd : BddAbove S' := ⟨⊤, by simp [mem_upperBounds]⟩
  obtain ⟨u, hu_mono, hu_tendsto, hu_mem⟩ := exists_seq_tendsto_sSup hS' hS'_bdd
  simp only [Set.mem_setOf_eq, S'] at hu_mem
  choose X hX_evar hu_eq using hu_mem
  obtain ⟨Y, Ylim, hY_mem, HY_lim_meas, hY_tendsto⟩ :=
    komlos_ennreal' (fun n ↦ (hX_evar n).measurable) P
  refine ⟨Ylim, ?_, ?_⟩
  · -- todo: isEvar_of_mem_convexHull
    sorry
  · suffices ⨆ n, ∫ᵉ x, U (X n x) ∂P ≤ ∫ᵉ x, U (Ylim x) ∂P by
      intro Z hZ_evar
      refine le_trans ?_ this
      simp_rw [← hu_eq]
      rw [iSup_eq_of_tendsto hu_mono hu_tendsto]
      exact le_sSup ⟨Z, hZ_evar, rfl⟩
    calc ⨆ n, ∫ᵉ x, U (X n x) ∂P
    _ = limsup (fun n ↦ ∫ᵉ x, U (X n x) ∂P) atTop := by
      sorry
    _ ≤ limsup (fun n ↦ ∫ᵉ x, U (Y n x) ∂P) atTop := by
      refine limsup_le_limsup (.of_forall fun n ↦ ?_)
      simp only
      sorry  -- concavity of U, Jensen
    _ ≤ ∫ᵉ x, limsup (fun n => U (Y n x)) atTop ∂P := by
      -- eintegral version of Fatou's lemma `limsup_lintegral_le`
      sorry
    _ = ∫ᵉ x, U (Ylim x) ∂P := by
      refine eintegral_congr_ae ?_
      filter_upwards [hY_tendsto] with x hx
      rw [Tendsto.limsup_eq]
      exact (hU_cont.tendsto _).comp hx

section A1Proof
/-! Copied and adapted from the exhaustion file. Should probably be generalized. -/

variable {α : Type*} {mα : MeasurableSpace α} {ν : Measure α} {S : Set (Measure α)}

/-- Let `C` be the supremum of `ν s` over all measurable sets `s` such that `μ.restrict s` is
sigma-finite. `C` is finite since `ν` is a finite measure. Then there exists a measurable set `t`
with `μ.restrict t` sigma-finite such that `ν t ≥ C - 1/n`. -/
lemma exists_todoSet_measure_ge (ν : Measure α) [IsFiniteMeasure ν]
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
    push_neg at hC_lt
    rw [tsub_eq_zero_of_le hC_lt]
    exact zero_le _

/-- A measurable set such that `μ.restrict (μ.sigmaFiniteSetGE ν n)` is sigma-finite and
for `C` the supremum of `ν s` over all measurable sets `s` with `μ.restrict s` sigma-finite,
`ν (μ.sigmaFiniteSetGE ν n) ≥ C - 1/n`. -/
def _root_.MeasureTheory.Measure.todoSet (ν : Measure α) [IsFiniteMeasure ν]
    (S : Set (Measure α)) (n : ℕ) : Set α :=
  (exists_todoSet_measure_ge ν S n).choose

lemma measurableSet_todoSet [IsFiniteMeasure ν] (n : ℕ) :
    MeasurableSet (ν.todoSet S n) :=
  (exists_todoSet_measure_ge ν S n).choose_spec.1

lemma nullSet_todoSet (ν : Measure α) [IsFiniteMeasure ν]
    (S : Set (Measure α)) (n : ℕ) :
    nullSet (ν.todoSet S n) S :=
  (exists_todoSet_measure_ge ν S n).choose_spec.2.1

lemma measure_todoSet_le (ν : Measure α) [IsFiniteMeasure ν] (S : Set (Measure α)) (n : ℕ) :
    ν (ν.todoSet S n)
      ≤ ⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s := by
  refine (le_iSup (f := fun s ↦ _) (nullSet_todoSet ν S n)).trans ?_
  exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : nullSet s S), ν s) (ν.todoSet S n)
    (measurableSet_todoSet n)

lemma measure_todoSet_ge (ν : Measure α) [IsFiniteMeasure ν] (S : Set (Measure α)) (n : ℕ) :
    (⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s) - 1 / n
      ≤ ν (ν.todoSet S n) :=
  (exists_todoSet_measure_ge ν S n).choose_spec.2.2

lemma tendsto_measure_todoSet (ν : Measure α) [IsFiniteMeasure ν] (S : Set (Measure α)) :
    Tendsto (fun n ↦ ν (ν.todoSet S n)) atTop
      (𝓝 (⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_
    tendsto_const_nhds (measure_todoSet_ge ν S) (measure_todoSet_le ν S)
  nth_rewrite 2 [← tsub_zero (⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s)]
  refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ (Or.inr ENNReal.zero_ne_top)
  simp only [one_div]
  exact ENNReal.tendsto_inv_nat_nhds_zero

/-- A measurable set such that `μ.restrict (μ.sigmaFiniteSetWRT' ν)` is sigma-finite and
`ν (μ.sigmaFiniteSetWRT' ν)` has maximal measure among such sets. -/
def _root_.MeasureTheory.Measure.todoSet' (ν : Measure α) [IsFiniteMeasure ν]
    (S : Set (Measure α)) :
    Set α :=
  ⋃ n, ν.todoSet S n

lemma measurableSet_todoSet' [IsFiniteMeasure ν] :
    MeasurableSet (ν.todoSet' S) :=
  MeasurableSet.iUnion measurableSet_todoSet

lemma todoSet'_nullSet (ν : Measure α) [IsFiniteMeasure ν] (S : Set (Measure α)) :
    nullSet (ν.todoSet' S) S where
  measurableSet := measurableSet_todoSet'
  null μ hμ := by
    unfold Measure.todoSet'
    simp only [measure_iUnion_null_iff]
    intro n
    have h_mem := nullSet_todoSet ν S n
    exact h_mem.null μ hμ

/-- `μ.sigmaFiniteSetWRT' ν` has maximal `ν`-measure among all measurable sets `s` with sigma-finite
`μ.restrict s`. -/
lemma measure_todoSet' (ν : Measure α) [IsFiniteMeasure ν] (S : Set (Measure α)) :
    ν (ν.todoSet' S)
      = ⨆ (s) (_ : MeasurableSet s) (_ : nullSet s S), ν s := by
  apply le_antisymm
  · refine (le_iSup (f := fun _ ↦ _) (todoSet'_nullSet ν S)).trans ?_
    exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : nullSet s S), ν s) (ν.todoSet' S)
      measurableSet_todoSet'
  · exact le_of_tendsto' (tendsto_measure_todoSet ν S)
      (fun _ ↦ measure_mono (Set.subset_iUnion _ _))

end A1Proof

lemma A1' (Q : Measure 𝓧) [IsFiniteMeasure Q] (S : Set (Measure 𝓧)) :
    ∃ (ρ : Measure 𝓧 × Measure 𝓧), (∀ t, nullSet t S → ρ.1 t = 0) ∧
      (∃ s, nullSet s S ∧ ρ.2 sᶜ = 0) ∧
      Q = ρ.1 + ρ.2 := by
  let N := Q.todoSet' S
  have hN : MeasurableSet N := measurableSet_todoSet'
  have hN_mem : nullSet N S := todoSet'_nullSet Q S
  refine ⟨(Q.restrict Nᶜ, Q.restrict N), ?_, ?_, ?_⟩
  · simp only
    intro s hs
    by_contra h_pos
    suffices Q N < Q (N ∪ s) by
      unfold N at this
      rw [measure_todoSet'] at this
      refine not_le.mpr this ?_
      refine le_iSup_of_le (Q.todoSet' S ∪ s) ?_
      refine le_iSup_of_le (measurableSet_todoSet'.union hs.measurableSet) ?_
      have h_mem : nullSet (Q.todoSet' S ∪ s) S := hN_mem.union hs
      exact le_iSup_of_le h_mem le_rfl
    calc Q N
    _ < Q.restrict N N + Q.restrict Nᶜ s := by
      conv_lhs => rw [← add_zero (Q N)]
      refine ENNReal.add_lt_add_of_le_of_lt (by simp) (le_of_eq (by simp)) ?_
      exact lt_of_le_of_ne' (zero_le _) h_pos
    _ ≤ Q.restrict N (N ∪ s) + Q.restrict Nᶜ (N ∪ s) := by gcongr <;> simp
    _ = Q (N ∪ s) := by rw [← Measure.add_apply, Measure.restrict_add_restrict_compl hN]
  · refine ⟨N, hN_mem, ?_⟩
    simp [Measure.restrict_apply hN.compl]
  · simp only
    rw [add_comm, Measure.restrict_add_restrict_compl hN]

lemma A1 (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    ∃ (ρ : Measure 𝓧 × Measure 𝓧), (∀ t, nullSet t S → ρ.1 t = 0) ∧
      (∃ s, nullSet s S ∧ ρ.2 sᶜ = 0) ∧
      Q = ρ.1 + ρ.2 := by
  obtain ⟨ρ, h1, h2, h3⟩ := A1' Q.toFinite S
  let f := Q.rnDeriv Q.toFinite
  refine ⟨(ρ.1.withDensity f, ρ.2.withDensity f), fun t ht ↦ ?_, ?_, ?_⟩
  · simp only
    specialize h1 t ht
    rw [withDensity_apply_eq_zero (Measure.measurable_rnDeriv _ _)]
    refine measure_mono_null ?_ h1
    exact Set.inter_subset_right
  · obtain ⟨s, hs_null, hs_eq⟩ := h2
    refine ⟨s,  hs_null, ?_⟩
    rw [withDensity_apply_eq_zero (Measure.measurable_rnDeriv _ _)]
    refine measure_mono_null ?_ hs_eq
    exact Set.inter_subset_right
  · simp only
    rw [← withDensity_add_measure, ← h3, Measure.withDensity_rnDeriv_eq]
    exact absolutelyContinuous_toFinite Q

noncomputable
def _root_.MeasureTheory.Measure.acPartSet (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    Measure 𝓧 :=
  (A1 Q S).choose.1

noncomputable
def _root_.MeasureTheory.Measure.singularPartSet (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    Measure 𝓧 :=
  (A1 Q S).choose.2

def a1Event (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) : Set 𝓧 :=
  (A1 Q S).choose_spec.2.1.choose

lemma ae_acPartSet_le_aeSet (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    ∀ t, nullSet t S → Q.acPartSet S t = 0 := (A1 Q S).choose_spec.1

lemma nullSet_a1Event (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    nullSet (a1Event Q S) S :=
  (A1 Q S).choose_spec.2.1.choose_spec.1

lemma measurableSet_a1Event (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    MeasurableSet (a1Event Q S) := (nullSet_a1Event Q S).measurableSet

@[simp]
lemma acPartSet_a1Event (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    Q.acPartSet S (a1Event Q S) = 0 :=
  ae_acPartSet_le_aeSet Q S _ (nullSet_a1Event Q S)

@[simp]
lemma singularPartSet_a1Event_compl (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    Q.singularPartSet S (a1Event Q S)ᶜ = 0 := (A1 Q S).choose_spec.2.1.choose_spec.2

lemma singular_singularPartSet (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    Q.acPartSet S ⟂ₘ Q.singularPartSet S := by
  refine ⟨a1Event Q S, measurableSet_a1Event Q S, by simp, by simp⟩

lemma acPartSet_add_singularPartSet (Q : Measure 𝓧) [SFinite Q] (S : Set (Measure 𝓧)) :
    Q.acPartSet S + Q.singularPartSet S = Q := (A1 Q S).choose_spec.2.2.symm

lemma measure_a1Event_diff {Q : Measure 𝓧} [SFinite Q] {S : Set (Measure 𝓧)}
    {s : Set 𝓧} (hs : nullSet s S) :
    Q (s \ a1Event Q S) = 0 := by
  refine le_antisymm ?_ (zero_le _)
  calc Q (s \ a1Event Q S)
  _ = Q.acPartSet S (s \ a1Event Q S) + Q.singularPartSet S (s \ a1Event Q S) := by
    rw [← Measure.add_apply, acPartSet_add_singularPartSet Q S]
  _ ≤ Q.acPartSet S s + Q.singularPartSet S (a1Event Q S)ᶜ := by gcongr <;> grind
  _ = 0 := by
    simp only [singularPartSet_a1Event_compl, add_zero]
    exact ae_acPartSet_le_aeSet Q S _ hs

lemma ae_imp_mem_a1Event (Q : Measure 𝓧) [SFinite Q] {S : Set (Measure 𝓧)}
    {s : Set 𝓧} (hs : nullSet s S) :
    ∀ᵐ x ∂Q, x ∈ s → x ∈ a1Event Q S := by
  have h_diff := measure_a1Event_diff (Q := Q) hs
  simpa [measure_eq_zero_iff_ae_notMem] using h_diff

lemma measure_a1Event {Q μ : Measure 𝓧} [SFinite Q] (hS : μ ∈ S) :
    μ (a1Event Q S) = 0 := by
  rw [← compl_compl (x := a1Event Q S), ← mem_ae_iff]
  have h_le : ae μ ≤ aeSet S := le_iSup₂ μ hS (f := fun μ _ ↦ ae μ)
  exact h_le (compl_mem_aeSet_of_nullSet (nullSet_a1Event Q S))

lemma ae_mem_compl_a1Event (Q : Measure 𝓧) [SFinite Q] {μ : Measure 𝓧} (hS : μ ∈ S) :
    ∀ᵐ x ∂μ, x ∈ (a1Event Q S)ᶜ := by
  simp only [Set.mem_compl_iff, ae_iff, not_not, Set.setOf_mem_eq]
  exact measure_a1Event hS

lemma setEIntegral_measure_zero {μ : Measure 𝓧} (s : Set 𝓧) (f : 𝓧 → EReal) (hs' : μ s = 0) :
    ∫ᵉ x in s, f x ∂μ = 0 := by
  simp [eintegral, setLIntegral_measure_zero s _ hs']

/-- There exists a utility-maximizing e-variable which is infinite whenever another e-variable
is infinite. -/
lemma exists_eq_iSup_eintegral_of_le (hU_ccv : ConcaveOn ℝ≥0 Set.univ U)
    {b : ℝ} (hU_cont : Continuous U) (hU_mono : Monotone U) (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [SFinite P] (S : Set (Measure 𝓧)) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      (∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (Y x) ∂P) ∧ (∀ᵐ x ∂P, Y x < ∞ → X x < ∞) := by
  obtain ⟨Y, hY_evar, h_opt⟩ := exists_eq_iSup_eintegral_of_le' hU_ccv hU_cont hU_mono hU_le P S
  classical
  let Y' := fun x ↦ if x ∈ a1Event P S then ∞ else Y x
  have hY' : Measurable Y' :=
    Measurable.ite (measurableSet_a1Event P S) measurable_const hY_evar.measurable
  have hY'_evar : IsEVar Y' S := by
    refine hY_evar.congr hY' fun μ hμ ↦ ?_
    filter_upwards [ae_mem_compl_a1Event P hμ] with x hx
    simp only [Set.mem_compl_iff] at hx
    simp [Y', hx]
  refine ⟨Y', hY'_evar, fun X hX_evar ↦ ⟨?_, ?_⟩⟩
  · refine (h_opt X hX_evar).trans ?_
    gcongr
    intro x
    refine hU_mono ?_
    simp only [Y']
    split_ifs with hx <;> simp
  · let s := {x | X x = ∞}
    have hs : MeasurableSet s := (measurableSet_singleton _).preimage hX_evar.measurable
    have hs_compl : nullSet s S := by
      refine ⟨hs, fun μ hμ ↦ ?_⟩
      have h_ne_top := hX_evar.ae_ne_top hμ
      simpa only [ne_eq, ae_iff, Decidable.not_not] using h_ne_top
    have h_diff := ae_imp_mem_a1Event P hs_compl
    filter_upwards [h_diff] with x hx h_lt_top
    by_contra! h_eq_top
    simp only [top_le_iff] at h_eq_top
    refine h_lt_top.ne ?_
    simp [Y', hx h_eq_top]

end

/-- The numeraire associated with a bounded utility function. -/
noncomputable
def numeraireOfBounded (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [SFinite P] (S : Set (Measure 𝓧)) :
    𝓧 → ℝ≥0∞ :=
  (exists_eq_iSup_eintegral_of_le U.concave U.continuous U.monotone hU_le P S).choose

lemma isEVar_numeraireOfBounded (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [SFinite P] (S : Set (Measure 𝓧)) :
    IsEVar (numeraireOfBounded U hU_le P S) S :=
  (Classical.choose_spec
    (exists_eq_iSup_eintegral_of_le U.concave U.continuous U.monotone hU_le P S)).1

lemma eintegral_le_numeraireOfBounded (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [SFinite P] (S : Set (Measure 𝓧))
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (numeraireOfBounded U hU_le P S x) ∂P :=
  ((Classical.choose_spec
    (exists_eq_iSup_eintegral_of_le U.concave U.continuous U.monotone hU_le P S)).2 X hX_evar).1

lemma lt_top_of_numeraireOfBounded_lt_top (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [SFinite P] (S : Set (Measure 𝓧))
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∀ᵐ x ∂P, (numeraireOfBounded U hU_le P S x) < ∞ → X x < ∞ :=
  ((Classical.choose_spec
    (exists_eq_iSup_eintegral_of_le U.concave U.continuous U.monotone hU_le P S)).2 X hX_evar).2

-- first order optimality condition for bounded utility functions
lemma eintegral_deriv_mul_le (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [SFinite P] (S : Set (Measure 𝓧))
    {Y : 𝓧 → ℝ≥0∞} (hY : IsEVar Y S) :
    ∫ᵉ x, U.deriv (numeraireOfBounded U hU_le P S x)
      * (Y x - numeraireOfBounded U hU_le P S x) ∂P ≤ 0 := by
  sorry

-- first order optimality condition for log utility
lemma eintegral_deriv_log_mul_le (P : Measure 𝓧) [SFinite P] (S : Set (Measure 𝓧)) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      ∫ᵉ x, logUtility.deriv (Y x) * (X x - Y x) ∂P ≤ 0 := by
  sorry

lemma exists_numeraire' (P : Measure 𝓧) [SFinite P] (S : Set (Measure 𝓧)) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      ∫ᵉ x, (X x / Y x : ℝ≥0∞) - (Y x / Y x : ℝ≥0∞) ∂P ≤ 0 := by
  obtain ⟨Y, hY_evar, h_opt⟩ := eintegral_deriv_log_mul_le P S
  refine ⟨Y, hY_evar, fun X hX_evar ↦ ?_⟩
  specialize h_opt X hX_evar
  simp_rw [deriv_logUtility_eq_ennreal] at h_opt
  have h_sub x : ((1 / Y x : ℝ≥0∞) : EReal) * (↑(X x) - ↑(Y x)) =
      (X x / Y x : ℝ≥0∞) - (Y x / Y x : ℝ≥0∞) := by
    by_cases hY : Y x = 0
    · simp only [hY, one_div, ENNReal.inv_zero, EReal.coe_ennreal_top, EReal.coe_ennreal_zero,
        sub_zero, ENNReal.zero_div]
      by_cases hX : X x = 0
      · simp [hX]
      rw [ENNReal.div_zero hX, EReal.top_mul_of_pos]
      · simp
      · simp only [EReal.coe_ennreal_pos]
        exact lt_of_le_of_ne' (zero_le _) hX
    rw [EReal.mul_sub_of_nonneg_of_ne_top]
    rotate_left
    · positivity
    · simp [hY]
    rw [EReal.coe_ennreal_div hY, EReal.coe_ennreal_div hY, EReal.coe_ennreal_div hY,
      mul_comm _ (X _ : EReal), mul_comm _ (Y _ : EReal)]
    simp only [EReal.coe_ennreal_one, one_div]
    congr
  simp_rw [h_sub] at h_opt
  exact h_opt

lemma exists_numeraire (P : Measure 𝓧) [IsFiniteMeasure P] (S : Set (Measure 𝓧)) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      ∫⁻ x, X x / Y x ∂P ≤ ∫⁻ x, Y x / Y x ∂P := by -- todo change conclusion to most convenient
  obtain ⟨Y, hY_evar, h_opt⟩ := exists_numeraire' P S
  refine ⟨Y, hY_evar, fun X hX_evar ↦ ?_⟩
  specialize h_opt X hX_evar
  rw [eintegral_sub_of_nonneg] at h_opt
  rotate_left
  · exact fun _ ↦ by positivity
  · exact fun _ ↦ by positivity
  · have := hX_evar.measurable; have := hY_evar.measurable; fun_prop
  · have := hY_evar.measurable; fun_prop
  · refine ne_top_of_le_ne_top (b := ∫ᵉ x, (Y x / Y x : ℝ≥0∞) ∂P) ?_ ?_
    · refine ne_top_of_le_ne_top (b := ∫ᵉ x, (1 : ℝ≥0∞) ∂P) ?_ ?_
      · simp
      · gcongr
        intro x
        simp only [EReal.coe_ennreal_one]
        norm_cast
        exact ENNReal.div_self_le_one
    · gcongr
      intro x
      exact min_le_right _ _
  rw [EReal.sub_nonpos, eintegral_eq_lintegral, eintegral_eq_lintegral] at h_opt
  norm_cast at h_opt

open Classical in
/-- The numeraire e-variable. -/
noncomputable
def numeraire (P : Measure 𝓧) (S : Set (Measure 𝓧)) : 𝓧 → ℝ≥0∞ :=
  if _ : IsFiniteMeasure P then (exists_numeraire P S).choose else 1

lemma isEVar_numeraire (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    IsEVar (numeraire P S) S := by
  unfold numeraire
  split_ifs with _
  · exact (exists_numeraire P S).choose_spec.1
  · exact isEVar_one _

@[fun_prop]
lemma measurable_numeraire (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    Measurable (numeraire P S) := (isEVar_numeraire P S).measurable

lemma lintegral_div_numeraire_le (P : Measure 𝓧) {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫⁻ x, X x / (numeraire P S x) ∂P ≤ ∫⁻ x, (numeraire P S x) / (numeraire P S x) ∂P := by
  unfold numeraire
  split_ifs with h_fin
  · exact (exists_numeraire P S).choose_spec.2 X hX_evar
  · simp only [Pi.one_apply, div_one, lintegral_const, one_mul]
    have : P .univ = ∞ := by rwa [not_isFiniteMeasure_iff] at h_fin
    simp [this]

lemma lintegral_div_numeraire_le_measure_fsupport (P : Measure 𝓧)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫⁻ x, X x / (numeraire P S x) ∂P ≤ P (numeraire P S).fsupport := by
  refine (lintegral_div_numeraire_le P hX_evar).trans_eq ?_
  rw [lintegral_div_self_eq_measure_fsupport (by fun_prop)]

lemma lintegral_div_numeraire_le_measure_univ (P : Measure 𝓧)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫⁻ x, X x / (numeraire P S x) ∂P ≤ P .univ := by
  calc
  _ ≤ P (numeraire P S).fsupport := lintegral_div_numeraire_le_measure_fsupport P hX_evar
  _ ≤ P Set.univ := measure_mono (by simp)

lemma lintegral_div_numeraire_le_one (P : Measure 𝓧) [IsProbabilityMeasure P]
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫⁻ x, X x / (numeraire P S x) ∂P ≤ 1 := by
  simpa using lintegral_div_numeraire_le_measure_univ P hX_evar

/-- `numeraire` is a numeraire. -/
lemma isNumeraire_numeraire (P : Measure 𝓧) :
    IsNumeraire (numeraire P S) S P :=
  ⟨isEVar_numeraire P S, fun _ ↦ lintegral_div_numeraire_le_measure_fsupport P⟩

lemma IsNumeraire.ae_eq_numeraire [IsFiniteMeasure P] {X : 𝓧 → ℝ≥0∞}
    (hX : IsNumeraire X S P) :
    X =ᵐ[P] numeraire P S :=
  hX.ae_unique (isNumeraire_numeraire P)

end ProbabilityTheory
