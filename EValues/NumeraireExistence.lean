/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
import EValues.Numeraire

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
  rw [← sum_sfiniteSeq P]
  simp only [Measure.ae_sum_eq, eventually_iSup, exists_and_left]
  sorry -- not clear

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {P : Measure 𝓧} {S : Set (Measure 𝓧)}

section

variable {U : ℝ≥0∞ → EReal}

/-- There exists a utility-maximizing e-variable which is infinite whenever another e-variable -/
lemma exists_eq_iSup_eintegral_of_le' (hU_ccv : ConcaveOn ℝ≥0 Set.univ U)
    {b : ℝ} (hU_cont : Continuous U) (hU_mono : Monotone U) (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (S : Set (Measure 𝓧)) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S → ∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (Y x) ∂P := by
  let S' := {y | ∃ X, IsEVar X S ∧ y = ∫ᵉ x, U (X x) ∂P}
  have hS' : S'.Nonempty := ⟨∫ᵉ x, U 0 ∂P, ⟨0, isEVar_zero, rfl⟩⟩
  have hS'_bdd : BddAbove S' := ⟨⊤, by simp [mem_upperBounds]⟩
  obtain ⟨u, hu_mono, hu_tendsto, hu_mem⟩ := exists_seq_tendsto_sSup hS' hS'_bdd
  simp only [Set.mem_setOf_eq, S'] at hu_mem
  choose X hX_evar hu_eq using hu_mem
  obtain ⟨Y, Ylim, hY_mem, HY_lim_meas, hY_tendsto⟩ :=
    komlos_ennreal (fun n ↦ (hX_evar n).measurable) P
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

lemma A1 (Q : Measure 𝓧) (S : Set (Measure 𝓧)) :
    ∃ (ρ : Measure 𝓧 × Measure 𝓧), ae ρ.1 ≤ aeSet S ∧
      (∃ s, MeasurableSet s ∧ sᶜ ∈ aeSet S ∧ ρ.2 sᶜ = 0) ∧
      Q = ρ.1 + ρ.2 := by
  sorry

noncomputable
def _root_.MeasureTheory.Measure.acPartSet (Q : Measure 𝓧) (S : Set (Measure 𝓧)) :
    Measure 𝓧 :=
  (A1 Q S).choose.1

noncomputable
def _root_.MeasureTheory.Measure.singularPartSet (Q : Measure 𝓧) (S : Set (Measure 𝓧)) :
    Measure 𝓧 :=
  (A1 Q S).choose.2

def a1Event (Q : Measure 𝓧) (S : Set (Measure 𝓧)) : Set 𝓧 :=
  (A1 Q S).choose_spec.2.1.choose

lemma ae_acPartSet_le_aeSet (Q : Measure 𝓧) (S : Set (Measure 𝓧)) :
    ae (Q.acPartSet S) ≤ aeSet S := (A1 Q S).choose_spec.1

lemma measurableSet_a1Event (Q : Measure 𝓧) (S : Set (Measure 𝓧)) :
    MeasurableSet (a1Event Q S) := (A1 Q S).choose_spec.2.1.choose_spec.1

lemma compl_a1Event_mem_aeSet (Q : Measure 𝓧) (S : Set (Measure 𝓧)) :
    (a1Event Q S)ᶜ ∈ aeSet S :=
  (A1 Q S).choose_spec.2.1.choose_spec.2.1

@[simp]
lemma acPartSet_a1Event (Q : Measure 𝓧) (S : Set (Measure 𝓧)) :
    Q.acPartSet S (a1Event Q S) = 0 := by
  rw [← compl_compl (x := a1Event Q S), ← mem_ae_iff]
  exact ae_acPartSet_le_aeSet Q S (compl_a1Event_mem_aeSet Q S)

@[simp]
lemma singularPartSet_a1Event_compl (Q : Measure 𝓧) (S : Set (Measure 𝓧)) :
    Q.singularPartSet S (a1Event Q S)ᶜ = 0 := (A1 Q S).choose_spec.2.1.choose_spec.2.2

lemma singular_singularPartSet (Q : Measure 𝓧) (S : Set (Measure 𝓧)) :
    Q.acPartSet S ⟂ₘ Q.singularPartSet S := by
  refine ⟨a1Event Q S, measurableSet_a1Event Q S, by simp, by simp⟩

lemma acPartSet_add_singularPartSet (Q : Measure 𝓧) (S : Set (Measure 𝓧)) :
    Q.acPartSet S + Q.singularPartSet S = Q := (A1 Q S).choose_spec.2.2.symm

lemma measure_a1Event_diff {Q : Measure 𝓧} {S : Set (Measure 𝓧)} {s : Set 𝓧} (hs : sᶜ ∈ aeSet S) :
    Q (s \ a1Event Q S) = 0 := by
  refine le_antisymm ?_ (zero_le _)
  calc Q (s \ a1Event Q S)
  _ = Q.acPartSet S (s \ a1Event Q S) + Q.singularPartSet S (s \ a1Event Q S) := by
    rw [← Measure.add_apply, acPartSet_add_singularPartSet Q S]
  _ ≤ Q.acPartSet S s + Q.singularPartSet S (a1Event Q S)ᶜ := by gcongr <;> grind
  _ = 0 := by
    simp only [singularPartSet_a1Event_compl, add_zero]
    suffices sᶜ ∈ ae (Q.acPartSet S) by rwa [mem_ae_iff, compl_compl] at this
    exact ae_acPartSet_le_aeSet Q S hs

lemma measure_a1Event {Q μ : Measure 𝓧} (hS : μ ∈ S) :
    μ (a1Event Q S) = 0 := by
  rw [← compl_compl (x := a1Event Q S), ← mem_ae_iff]
  have h_le : ae μ ≤ aeSet S := by
    simp only [aeSet]
    sorry
  exact h_le (compl_a1Event_mem_aeSet Q S)

/-- There exists a utility-maximizing e-variable which is infinite whenever another e-variable
is infinite. -/
lemma exists_eq_iSup_eintegral_of_le (hU_ccv : ConcaveOn ℝ≥0 Set.univ U)
    {b : ℝ} (hU_cont : Continuous U) (hU_mono : Monotone U) (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      (∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (Y x) ∂P) ∧ (∀ᵐ x ∂P, Y x < ∞ → X x < ∞) := by
  obtain ⟨Y, hY_evar, h_opt⟩ := exists_eq_iSup_eintegral_of_le' hU_ccv hU_cont hU_mono hU_le P S
  classical
  let Y' := fun x ↦ if x ∈ a1Event P S then ∞ else Y x
  have hY' : Measurable Y' :=
    Measurable.ite (measurableSet_a1Event P S) measurable_const hY_evar.measurable
  have hY'_evar : IsEVar Y' S := by
    refine ⟨hY', fun μ hμ ↦ ?_⟩
    rw [← lintegral_add_compl _ (measurableSet_a1Event P S),
      setLIntegral_measure_zero _ _ (measure_a1Event hμ), zero_add]
    calc ∫⁻ x in (a1Event P S)ᶜ, Y' x ∂μ
    _ = ∫⁻ x in (a1Event P S)ᶜ, Y x ∂μ := by
      refine setLIntegral_congr_fun (measurableSet_a1Event P S).compl fun x hx ↦ ?_
      simp only [Set.mem_compl_iff] at hx
      simp [Y', hx]
    _ ≤ ∫⁻ x, Y x ∂μ := setLIntegral_le_lintegral (a1Event P S)ᶜ Y
    _ ≤ μ .univ := hY_evar.lintegral_le_measure_univ μ hμ
  refine ⟨Y', hY'_evar, fun X hX_evar ↦ ⟨?_, ?_⟩⟩
  · refine (h_opt X hX_evar).trans ?_
    gcongr
    intro x
    refine hU_mono ?_
    simp only [Y']
    split_ifs with hx <;> simp
  · let s := {x | X x = ∞}
    have hs_compl : sᶜ ∈ aeSet S := by
      simp only [aeSet, mem_iSup, s]
      intro μ hμ
      specialize hS μ hμ
      rw [mem_ae_iff, compl_compl]
      have h_ne_top := hX_evar.ae_ne_top hμ
      simpa only [ne_eq, ae_iff, Decidable.not_not] using h_ne_top
    have h_diff := measure_a1Event_diff hs_compl (Q := P)
    rw [measure_eq_zero_iff_ae_notMem] at h_diff
    simp only [Set.mem_diff, Set.mem_setOf_eq, not_and, Decidable.not_not, s] at h_diff
    filter_upwards [h_diff] with x hx h_lt_top
    by_contra! h_eq_top
    simp only [top_le_iff] at h_eq_top
    refine h_lt_top.ne ?_
    simp [Y', hx h_eq_top]

end

/-- The numeraire associated with a bounded utility function. -/
noncomputable
def numeraireOfBounded (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    𝓧 → ℝ≥0∞ :=
  Classical.choose (exists_eq_iSup_eintegral_of_le U.concave U.continuous U.monotone hU_le P S hS)

lemma isEVar_numeraireOfBounded (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    IsEVar (numeraireOfBounded U hU_le P S hS) S :=
  (Classical.choose_spec
    (exists_eq_iSup_eintegral_of_le U.concave U.continuous U.monotone hU_le P S hS)).1

lemma eintegral_le_numeraireOfBounded (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (numeraireOfBounded U hU_le P S hS x) ∂P :=
  ((Classical.choose_spec
    (exists_eq_iSup_eintegral_of_le U.concave U.continuous U.monotone hU_le P S hS)).2 X hX_evar).1

lemma lt_top_of_numeraireOfBounded_lt_top (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∀ᵐ x ∂P, (numeraireOfBounded U hU_le P S hS x) < ∞ → X x < ∞ :=
  ((Classical.choose_spec
    (exists_eq_iSup_eintegral_of_le U.concave U.continuous U.monotone hU_le P S hS)).2 X hX_evar).2

lemma eintegral_deriv_mul_le (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {Y : 𝓧 → ℝ≥0∞} (hY : IsEVar Y S) :
    ∫ᵉ x, U.deriv (numeraireOfBounded U hU_le P S hS x)
      * (Y x - numeraireOfBounded U hU_le P S hS x) ∂P ≤ 0 := by
  sorry

lemma eintegral_deriv_log_mul_le (P : Measure 𝓧) [IsFiniteMeasure P] (S : Set (Measure 𝓧))
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      ∫ᵉ x, logUtility.deriv (Y x) * (X x - Y x) ∂P ≤ 0 := by
  sorry

lemma exists_numeraire (P : Measure 𝓧) [IsFiniteMeasure P]
    (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      ∫⁻ x, X x / Y x ∂P ≤ ∫⁻ x, Y x / Y x ∂P := by -- todo change conclusion to most convenient
  obtain ⟨Y, hY_evar, h_opt⟩ := eintegral_deriv_log_mul_le P S hS
  refine ⟨Y, hY_evar, fun X hX_evar ↦ ?_⟩
  specialize h_opt X hX_evar
  simp_rw [deriv_logUtility_eq_ennreal] at h_opt
  sorry

open Classical in
/-- The numeraire e-variable. -/
noncomputable
def numeraire (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    𝓧 → ℝ≥0∞ :=
  if _ : IsFiniteMeasure P then
    if hS : ∀ μ ∈ S, IsFiniteMeasure μ then Classical.choose (exists_numeraire P S hS)
    else 0
  else 1

lemma isEVar_numeraire (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    IsEVar (numeraire P S) S := by
  unfold numeraire
  split_ifs with _ h
  · exact (Classical.choose_spec (exists_numeraire P S h)).1
  · exact isEVar_zero
  · exact isEVar_one _

@[fun_prop]
lemma measurable_numeraire (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    Measurable (numeraire P S) := (isEVar_numeraire P S).measurable

lemma lintegral_div_numeraire_le (P : Measure 𝓧) {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫⁻ x, X x / (numeraire P S x) ∂P ≤ ∫⁻ x, (numeraire P S x) / (numeraire P S x) ∂P := by
  unfold numeraire
  split_ifs with h_fin h
  · exact (Classical.choose_spec (exists_numeraire P S h)).2 X hX_evar
  · sorry -- not true.
  · simp only [Pi.one_apply, div_one, lintegral_const, one_mul]
    have : P .univ = ∞ := by rwa [not_isFiniteMeasure_iff] at h_fin
    simp [this]

lemma lintegral_div_numeraire_le_measure_fsupport (P : Measure 𝓧)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫⁻ x, X x / (numeraire P S x) ∂P ≤ P (numeraire P S).fsupport := by
  refine (lintegral_div_numeraire_le P hX_evar).trans_eq ?_
  have m_fsupport : MeasurableSet (numeraire P S).fsupport :=
      (isEVar_numeraire P S).measurable_fsupport
  rw [← lintegral_add_compl _ m_fsupport, ← add_zero <| P (numeraire P S).fsupport]
  congr
  · suffices ∀ x ∈ (numeraire P S).fsupport, (numeraire P S x) / (numeraire P S x) = 1 by
      rw [setLIntegral_congr_fun m_fsupport this]
      simp
    intro x hx
    exact (ENNReal.div_eq_one_iff hx.2 hx.1).mpr rfl
  · refine (setLIntegral_eq_zero_iff m_fsupport.compl (by fun_prop)).mpr ?_
    filter_upwards with x hx
    rw [Function.fsupport_compl] at hx
    rcases hx with (hx_top | hx_zero)
    · simp_all
    · simp_all

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

/-- For a given e-variable `Y`, the property of being a numeraire is equivalent to the property
that the expectation of the ratio of any e-variable `X` over `Y` is less
than the expectation of the ratio of `Y` over itself. -/
lemma lintegral_div_self_le_iff_IsNumeraire [IsFiniteMeasure P]
    {Y : 𝓧 → ℝ≥0∞} (hY_evar : IsEVar Y S) :
    (∀ X, IsEVar X S → ∫⁻ ω, X ω / Y ω ∂P ≤ ∫⁻ ω, Y ω / Y ω ∂P) ↔ IsNumeraire Y S P := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine ⟨hY_evar, fun X hX_evar ↦ (h X hX_evar).trans_eq ?_⟩
    have m_fsupport : MeasurableSet Y.fsupport :=hY_evar.measurable_fsupport
    rw [← lintegral_add_compl _ m_fsupport, ← add_zero <| P Y.fsupport]
    congr
    · suffices ∀ x ∈ Y.fsupport, Y x / Y x = 1 by
        rw [setLIntegral_congr_fun m_fsupport this]
        simp
      intro x hx
      exact (ENNReal.div_eq_one_iff hx.2 hx.1).mpr rfl
    · refine (setLIntegral_eq_zero_iff m_fsupport.compl ?_).mpr ?_
      · have := hY_evar.measurable
        fun_prop
      · filter_upwards with x hx
        rw [Function.fsupport_compl] at hx
        rcases hx with (hx_top | hx_zero)
        · simp_all
        · simp_all
  · intro X hX_evar
    have ae_eq_numeraire := h.ae_eq_numeraire
    calc ∫⁻ ω, X ω / Y ω ∂P
    _ = ∫⁻ ω, X ω / (numeraire P S ω) ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_eq_numeraire] with ω hω
      rw [hω]
    _ ≤ ∫⁻ ω, (numeraire P S ω) / (numeraire P S ω) ∂P := lintegral_div_numeraire_le P hX_evar
    _ = ∫⁻ ω, Y ω / Y ω ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_eq_numeraire] with ω hω
      rw [hω]

end ProbabilityTheory
