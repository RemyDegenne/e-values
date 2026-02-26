/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
import EValues.LebesgueDecomposition
import EValues.Numeraire
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Existence of the Numeraire

-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology unitInterval

namespace ProbabilityTheory

-- proved in the Brownian motion project
lemma komlos_ennreal {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → ℝ≥0∞}
    (hX : ∀ n, Measurable (X n)) (P : Measure Ω) [SFinite P] :
    ∃ (Y : ℕ → Ω → ℝ≥0∞) (Y_lim : Ω → ℝ≥0∞),
      (∀ n, Y n ∈ convexHull ℝ≥0∞ (Set.range fun m ↦ X (n + m))) ∧ Measurable Y_lim ∧
      ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (Y_lim ω)) := by
  sorry

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {P : Measure 𝓧} {S : Set (Measure 𝓧)}

section

variable {U : ℝ≥0∞ → EReal}

lemma eintegrable_of_le {f : 𝓧 → EReal} {b : EReal} (hf : ∀ x, f x ≤ b) (hb : b ≠ ⊤)
    (P : Measure 𝓧) [IsFiniteMeasure P] : eintegrable f P := by
  refine .inl (ne_of_lt ?_)
  calc ∫⁻ x, (f x).toENNReal ∂P
  _ ≤ ∫⁻ x, b.toENNReal ∂P := by
    gcongr
    exact EReal.toENNReal_le_toENNReal (hf _) -- missing gcongr
  _ = b.toENNReal * P .univ := by simp [lintegral_const]
  _ < ⊤ := by simp [hb, lt_top_iff_ne_top, ENNReal.mul_eq_top]

lemma eintegral_lt_top_of_le {f : 𝓧 → EReal} {b : EReal} (hf : ∀ x, f x ≤ b) (hb : b ≠ ⊤)
    (P : Measure 𝓧) [IsFiniteMeasure P] :
    ∫ᵉ x, f x ∂P < ⊤ := by
  rw [eintegral]
  calc (∫⁻ x, (f x).toENNReal ∂P : EReal) - ∫⁻ x, (-f x).toENNReal ∂P
  _ ≤ ∫⁻ x, (f x).toENNReal ∂P - 0 := EReal.sub_le_sub le_rfl (by positivity)
  _ ≤ ∫⁻ x, b.toENNReal ∂P := by
    simp only [sub_zero]
    refine EReal.coe_ennreal_le_coe_ennreal_iff.mpr ?_ -- missing gcongr
    gcongr
    exact EReal.toENNReal_le_toENNReal (hf _)
  _ = b.toENNReal * P .univ := by simp [lintegral_const]
  _ < ⊤ := by
    norm_cast
    rw [lt_top_iff_ne_top, ne_eq, EReal.coe_ennreal_eq_top_iff]
    simp [hb, ENNReal.mul_eq_top]

lemma todo' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (u : EReal) : (a + b) * u = a * u + b * u := by
  cases u with
  | bot =>
    by_cases ha_zero : a = 0
    · simp [ha_zero]
    rw [EReal.mul_bot_of_pos (by positivity), EReal.mul_bot_of_pos (by positivity)]
    simp
  | coe u => norm_cast; ring
  | top =>
    by_cases ha_zero : a = 0
    · simp [ha_zero]
    rw [EReal.mul_top_of_pos (by positivity), EReal.mul_top_of_pos (by positivity)]
    by_cases hb_zero : b = 0
    · simp [hb_zero]
    rw [EReal.mul_top_of_pos (by positivity)]
    simp

lemma todo (a b : ℝ≥0∞) (u : EReal) : (a + b) * u = a * u + b * u := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have ha_pos : 0 < a := by positivity
  have hb_pos : 0 < b := by positivity
  by_cases ha_top : a = ∞
  · simp only [ha_top, EReal.coe_ennreal_top, ne_eq, EReal.coe_ennreal_ne_bot, not_false_eq_true,
      EReal.top_add_of_ne_bot]
    rcases lt_trichotomy u 0 with (hu_neg | rfl | hu_pos)
    · rw [EReal.top_mul_of_neg (by simpa)]; simp
    · simp
    · rw [EReal.top_mul_of_pos (by simpa), EReal.top_add_of_ne_bot]
      simp only [ne_eq, EReal.mul_eq_bot, EReal.coe_ennreal_ne_bot, false_and,
        EReal.coe_ennreal_pos, hb_pos, true_and, EReal.coe_ennreal_eq_top_iff, false_or, not_or,
        not_and, not_lt, hu_pos.le, implies_true]
      refine ⟨fun h ↦ by simp [h] at hu_pos, fun h ↦ ?_⟩
      norm_cast at h
      exact absurd hb_pos.le (not_le.mpr h)
  by_cases hb_top : b = ∞
  · simp only [hb_top, EReal.coe_ennreal_top, ne_eq, EReal.coe_ennreal_ne_bot, not_false_eq_true,
      EReal.add_top_of_ne_bot]
    rcases lt_trichotomy u 0 with (hu_neg | rfl | hu_pos)
    · rw [EReal.top_mul_of_neg (by simpa)]; simp
    · simp
    · rw [EReal.top_mul_of_pos (by simpa), EReal.add_top_of_ne_bot]
      simp only [ne_eq, EReal.mul_eq_bot, EReal.coe_ennreal_ne_bot, false_and,
        EReal.coe_ennreal_pos, ha_pos, true_and, EReal.coe_ennreal_eq_top_iff, false_or, not_or,
        not_and, not_lt, hu_pos.le, implies_true]
      refine ⟨fun h ↦ by simp [h] at hu_pos, fun h ↦ ?_⟩
      norm_cast at h
      exact absurd ha_pos.le (not_le.mpr h)
  have ha_real : (a : EReal) = a.toReal := by rw [EReal.coe_ennreal_toReal ha_top]
  have hb_real : (b : EReal) = b.toReal := by rw [EReal.coe_ennreal_toReal hb_top]
  rw [ha_real, hb_real, todo' (by simp) (by simp)]

lemma convex_eintegral_utility_ge [IsFiniteMeasure P] (u : EReal)
    (hU_ccv : ConcaveOn ℝ≥0 Set.univ U)
    (hU_meas : Measurable U) {B : EReal} (hU_le : ∀ x : ℝ≥0∞, U x ≤ B) (hB : B ≠ ⊤) :
    Convex ℝ≥0∞ {Z | Measurable Z ∧ u ≤ ∫ᵉ ω, U (Z ω) ∂P} := by
  intro Y ⟨hY_meas, hY⟩ Z ⟨hZ_meas, hZ⟩ a b ha hb hab
  refine ⟨by fun_prop, ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hY hZ ⊢
  have ha_ne_top : a ≠ ∞ := fun ha_top ↦ by simp [ha_top] at hab
  have hb_ne_top : b ≠ ∞ := fun hb_top ↦ by simp [hb_top] at hab
  have h_int (Y : 𝓧 → ℝ≥0∞) : eintegrable (fun ω ↦ U (Y ω)) P :=
    eintegrable_of_le (fun _ ↦ hU_le _) (by simpa) P
  calc u
  _ = a * u + b * u := by
    conv_lhs => rw [← one_mul u]
    have : (1 : EReal) = (1 : ℝ≥0∞) := rfl
    rw [this, ← hab]
    simp only [EReal.coe_ennreal_add]
    exact todo _ _ _
  _ ≤ a * ∫ᵉ ω, U (Y ω) ∂P + b * ∫ᵉ ω, U (Z ω) ∂P := by gcongr
  _ = ∫ᵉ ω, a • U (Y ω) + b • U (Z ω) ∂P := by
    rw [← eintegral_mul_const (by simp) (by simpa),
      ← eintegral_mul_const (by simp) (by simpa)]
    rotate_left
    · exact h_int _
    · exact h_int _
    rw [eintegral_add]
    · simp
    · simp only [EReal.smul_ennreal_eq_mul]; fun_prop
    · simp only [EReal.smul_ennreal_eq_mul]; fun_prop
    · simp only [EReal.smul_ennreal_eq_mul]
      exact eintegrable.const_mul (h_int _) (by simp) (by simpa)
    · simp only [EReal.smul_ennreal_eq_mul]
      exact eintegrable.const_mul (h_int _) (by simp) (by simpa)
    · right
      refine (eintegral_lt_top_of_le (b := b • B) (fun ω ↦ ?_) ?_ P).ne
      · simp only [EReal.smul_ennreal_eq_mul]
        gcongr
        exact hU_le _
      · simp [EReal.mul_eq_top, hb_ne_top, hB, not_lt.mpr (EReal.coe_ennreal_nonneg b)]
    · left
      refine (eintegral_lt_top_of_le (b := a • B) (fun ω ↦ ?_) ?_ P).ne
      · simp only [EReal.smul_ennreal_eq_mul]
        gcongr
        exact hU_le _
      · simp [EReal.mul_eq_top, ha_ne_top, not_lt.mpr (EReal.coe_ennreal_nonneg a), hB]
  _ ≤ ∫ᵉ ω, U (a * Y ω + b * Z ω) ∂P := by
    gcongr
    intro ω
    lift a to ℝ≥0 using ha_ne_top
    lift b to ℝ≥0 using hb_ne_top
    norm_cast at ha hb hab
    exact hU_ccv.2 (by simp : Y ω ∈ Set.univ) (by simp) ha hb hab

-- needs only two things about IsEVar: convex and closed under a.e. limits
/-- There exists a utility-maximizing e-variable which is infinite whenever another e-variable
is infinite. -/
lemma exists_eq_iSup_eintegral_of_le' (hU_ccv : ConcaveOn ℝ≥0 Set.univ U)
    {B : ℝ} (hU_cont : Continuous U) (hU_le : ∀ x : ℝ≥0∞, U x ≤ B)
    (P : Measure 𝓧) [IsFiniteMeasure P] (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S → ∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (Y x) ∂P := by
  let S' := {y | ∃ X, IsEVar X S ∧ y = ∫ᵉ x, U (X x) ∂P}
  have hS' : S'.Nonempty := ⟨∫ᵉ x, U 1 ∂P, ⟨1, isEVar_one _, rfl⟩⟩
  have hS'_bdd : BddAbove S' := ⟨⊤, by simp [mem_upperBounds]⟩
  obtain ⟨u, hu_mono, hu_tendsto, hu_mem⟩ := exists_seq_tendsto_sSup hS' hS'_bdd
  simp only [Set.mem_setOf_eq, S'] at hu_mem
  choose X hX_evar hu_eq using hu_mem
  obtain ⟨Y, Ylim, hY_mem, hY_lim_meas, hY_tendsto⟩ :=
    komlos_ennreal (fun n ↦ (hX_evar n).measurable) P
  have hY_evar n : IsEVar (Y n) S := by
    specialize hY_mem n
    rw [mem_convexHull_iff] at hY_mem
    refine hY_mem {Z | IsEVar Z S} ?_ (convex_isEVar S)
    rintro _ ⟨m, rfl⟩
    exact hX_evar (n + m)
  let Yliminf := fun x ↦ liminf (fun n ↦ Y n x) atTop
  have hYliminf_meas : Measurable Yliminf := Measurable.liminf fun n ↦ (hY_evar n).measurable
  refine ⟨Yliminf, ?_, ?_⟩
  · exact isEVar_liminf hY_evar hS
  · suffices ⨆ n, ∫ᵉ x, U (X n x) ∂P ≤ ∫ᵉ x, U (Ylim x) ∂P by
      intro Z hZ_evar
      refine le_trans ?_ (this.trans_eq ?_)
      · simp_rw [← hu_eq]
        rw [iSup_eq_of_tendsto hu_mono hu_tendsto]
        exact le_sSup ⟨Z, hZ_evar, rfl⟩
      · refine eintegral_congr_ae ?_
        filter_upwards [hY_tendsto] with x hx
        congr
        unfold Yliminf
        rwa [Tendsto.liminf_eq]
    calc ⨆ n, ∫ᵉ x, U (X n x) ∂P
    _ = limsup (fun n ↦ ∫ᵉ x, U (X n x) ∂P) atTop := by
      simp_rw [← hu_eq]
      rw [Tendsto.limsup_eq hu_tendsto, iSup_eq_of_tendsto hu_mono hu_tendsto]
    _ ≤ limsup (fun n ↦ ∫ᵉ x, U (Y n x) ∂P) atTop := by
      refine limsup_le_limsup (.of_forall fun n ↦ ?_)
      simp only
      specialize hY_mem n
      simp only [mem_convexHull_iff] at hY_mem
      refine (hY_mem {Z | Measurable Z ∧ ∫ᵉ ω, U (X n ω) ∂P ≤ ∫ᵉ ω, U (Z ω) ∂P} ?_ ?_).2
      · rintro _ ⟨m, rfl⟩
        simp only [Set.mem_setOf_eq]
        simp_rw [← hu_eq]
        exact ⟨(hX_evar _).measurable, hu_mono (by grind)⟩
      · exact convex_eintegral_utility_ge _ hU_ccv hU_cont.measurable hU_le (by simp)
    _ ≤ ∫ᵉ x, limsup (fun n ↦ U (Y n x)) atTop ∂P := by
      refine limsup_eintegral_le (g := fun _ ↦ .ofReal B) ?_ ?_ ?_ ?_
      · intro n
        have := (hY_evar n).measurable
        fun_prop
      · intro n
        refine ae_of_all _ fun x ↦ ?_
        simp only [Function.comp_apply]
        have : ENNReal.ofReal B = B.toEReal.toENNReal := by simp
        rw [this]
        exact EReal.toENNReal_le_toENNReal <| hU_le (Y n x)
      · simp only [lintegral_const]
        refine ENNReal.mul_ne_top (by simp) (by simp)
      · left
        rw [EReal.ne_top_exists_finite_iff]
        by_cases hB : B < 0
        · refine ⟨0, by simp, ?_⟩
          rw [Filter.limsup_le_iff']
          intro y hy
          refine .of_forall fun n ↦ LT.lt.le <| lt_of_le_of_lt (Eq.le ?_) hy
          suffices ∀ x, (U (Y n x)).toENNReal = 0 by
            simp_rw [this]
            simp
          intro x
          replace hB : B.toEReal < 0 := by simp [hB]
          replace hU_le := (lt_of_le_of_lt (hU_le (Y n x)) hB).le
          simp [hU_le]
        · refine ⟨B * P .univ, ?_, ?_⟩
          · exact (EReal.mul_ne_top _ _).mpr (by simp)
          · rw [Filter.limsup_le_iff']
            intro y hy
            refine .of_forall fun n ↦ LT.lt.le <| lt_of_le_of_lt ?_ hy
            have : B.toEReal = (ENNReal.ofReal B).toEReal := by
              push_neg at hB
              simp only [EReal.coe_ennreal_ofReal, hB, sup_of_le_left]
            rw [this]
            norm_cast
            suffices ∀ x, (U (Y n x)).toENNReal ≤ ENNReal.ofReal B by
              calc
              _ ≤ ∫⁻ x, ENNReal.ofReal B ∂P := lintegral_mono this
              _ = ENNReal.ofReal B * P .univ := by simp [lintegral_const]
            intro x
            have : ENNReal.ofReal B = B.toEReal.toENNReal := by simp
            rw [this]
            exact EReal.toENNReal_le_toENNReal (hU_le (Y n x))
    _ = ∫ᵉ x, U (Ylim x) ∂P := by
      refine eintegral_congr_ae ?_
      filter_upwards [hY_tendsto] with x hx
      rw [Tendsto.limsup_eq]
      exact (hU_cont.tendsto _).comp hx

/-- There exists a utility-maximizing e-variable which is infinite whenever another e-variable
is infinite. -/
lemma exists_eq_iSup_eintegral_of_le (hU_ccv : ConcaveOn ℝ≥0 Set.univ U)
    {b : ℝ} (hU_cont : Continuous U) (hU_mono : Monotone U) (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      (∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (Y x) ∂P) ∧ (∀ᵐ x ∂P, Y x < ∞ → X x < ∞) := by
  obtain ⟨Y, hY_evar, h_opt⟩ := exists_eq_iSup_eintegral_of_le' hU_ccv hU_cont hU_le P S hS
  classical
  let Y' := fun x ↦ if x ∈ acSet P S then ∞ else Y x
  have hY' : Measurable Y' :=
    Measurable.ite (measurableSet_acSet P S) measurable_const hY_evar.measurable
  have hY'_evar : IsEVar Y' S := by
    refine hY_evar.congr hY' fun μ hμ ↦ ?_
    filter_upwards [ae_mem_compl_acSet P hμ] with x hx
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
    have h_diff := ae_imp_mem_acSet P hs_compl
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
  (exists_eq_iSup_eintegral_of_le U.concave U.continuous U.monotone hU_le P S hS).choose

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


-- first order optimality condition for bounded utility functions
noncomputable instance inst_smul_I_ENNReal : SMul I ℝ≥0∞ where
  smul a x := ENNReal.ofReal a * x

instance : MeasurableConstSMul I ℝ≥0∞ where
  measurable_const_smul c := by
    change Measurable (fun x ↦ ENNReal.ofReal c * x)
    fun_prop

lemma eintegral_deriv_mul_le (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {Y : 𝓧 → ℝ≥0∞} (hY : IsEVar Y S) :
    ∫ᵉ x, U.deriv (numeraireOfBounded U hU_le P S hS x)
      * (Y x - numeraireOfBounded U hU_le P S hS x) ∂P ≤ 0 := by
  -- Lemma 2.9 of _Larsson et al._ (2025)?
  set X := numeraireOfBounded U hU_le P S hS
  -- Remove aesop
  let Z := fun (t : I) ↦ t • Y + (⟨1 - t, by aesop⟩ : I) • X

  have hZ (t : I) : IsEVar (Z t) S := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [Z]
      have := hY.measurable
      have : Measurable X := by sorry
      fun_prop
    · sorry
    · sorry

  have (t : I) (ht : 0 < t) : ∫ᵉ x, (t : EReal)⁻¹ * (U (Z t x) - U (Z 0 x)) ∂P ≤ 0 := by
    suffices ∫ᵉ x, (U (Z t x) - U (Z 0 x)) ∂P ≤ 0 by
      have : (t : EReal)⁻¹ ≠ ⊥ ∧ (t : EReal)⁻¹ ≠ ⊤ := by
        sorry
      rw [eintegral_mul_const this.1 this.2, ← mul_zero (t : EReal)⁻¹]
      · gcongr
        refine EReal.inv_nonneg_of_nonneg ?_
        simp [t.2.1]
      · sorry
    rw [eintegral_sub]
    · rw [EReal.sub_nonpos]
      have (x : 𝓧) : Z 0 x = X x := by
        simp only [Pi.add_apply, Pi.smul_apply, Set.Icc.coe_zero, sub_zero, Set.Icc.mk_one, Z]
        change ENNReal.ofReal (0 : I) * Y x + ENNReal.ofReal (1 : I) * X x = X x
        simp
      simp_rw [this]
      exact eintegral_le_numeraireOfBounded U hU_le P S hS (hZ t)
    · sorry
    · have := (hZ t).measurable
      fun_prop
    · sorry
    · have := (hZ 0).measurable
      fun_prop
    · sorry
    · sorry
  sorry

-- first order optimality condition for log utility
lemma eintegral_deriv_log_mul_le (P : Measure 𝓧) [IsFiniteMeasure P]
    (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      ∫ᵉ x, logUtility.deriv (Y x) * (X x - Y x) ∂P ≤ 0 := by
  sorry

lemma exists_numeraire' (P : Measure 𝓧) [IsFiniteMeasure P]
    (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      ∫ᵉ x, (X x / Y x : ℝ≥0∞) - (Y x / Y x : ℝ≥0∞) ∂P ≤ 0 := by
  obtain ⟨Y, hY_evar, h_opt⟩ := eintegral_deriv_log_mul_le P S hS
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

lemma exists_numeraire (P : Measure 𝓧) [IsFiniteMeasure P]
    (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      ∫⁻ x, X x / Y x ∂P ≤ ∫⁻ x, Y x / Y x ∂P := by -- todo change conclusion to most convenient
  obtain ⟨Y, hY_evar, h_opt⟩ := exists_numeraire' P S hS
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
  if _ : IsFiniteMeasure P then
    if hS : ∀ μ ∈ S, IsFiniteMeasure μ then
      (exists_numeraire P S hS).choose
    else 1
  else 1

lemma isEVar_numeraire (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    IsEVar (numeraire P S) S := by
  unfold numeraire
  split_ifs with _ hS
  · exact (exists_numeraire P S hS).choose_spec.1
  · exact isEVar_one _
  · exact isEVar_one _

@[fun_prop]
lemma measurable_numeraire (P : Measure 𝓧) (S : Set (Measure 𝓧)) :
    Measurable (numeraire P S) := (isEVar_numeraire P S).measurable

lemma lintegral_div_numeraire_le (P : Measure 𝓧) (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫⁻ x, X x / (numeraire P S x) ∂P ≤ ∫⁻ x, (numeraire P S x) / (numeraire P S x) ∂P := by
  unfold numeraire
  split_ifs with h_fin
  · exact (exists_numeraire P S hS).choose_spec.2 X hX_evar
  · simp only [Pi.one_apply, div_one, lintegral_const, one_mul]
    have : P .univ = ∞ := by rwa [not_isFiniteMeasure_iff] at h_fin
    simp [this]

lemma lintegral_div_numeraire_le_measure_fsupport (P : Measure 𝓧) (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫⁻ x, X x / (numeraire P S x) ∂P ≤ P (numeraire P S).fsupport := by
  refine (lintegral_div_numeraire_le P hS hX_evar).trans_eq ?_
  rw [lintegral_div_self_eq_measure_fsupport (by fun_prop)]

lemma lintegral_div_numeraire_le_measure_univ (P : Measure 𝓧) (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫⁻ x, X x / (numeraire P S x) ∂P ≤ P .univ := by
  calc
  _ ≤ P (numeraire P S).fsupport := lintegral_div_numeraire_le_measure_fsupport P hS hX_evar
  _ ≤ P Set.univ := measure_mono (by simp)

lemma lintegral_div_numeraire_le_one (P : Measure 𝓧) [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫⁻ x, X x / (numeraire P S x) ∂P ≤ 1 := by
  simpa using lintegral_div_numeraire_le_measure_univ P hS hX_evar

/-- `numeraire` is a numeraire. -/
lemma isNumeraire_numeraire (P : Measure 𝓧) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    IsNumeraire (numeraire P S) S P :=
  ⟨isEVar_numeraire P S, fun _ ↦ lintegral_div_numeraire_le_measure_fsupport P hS⟩

lemma IsNumeraire.ae_eq_numeraire [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX : IsNumeraire X S P) :
    X =ᵐ[P] numeraire P S :=
  hX.ae_unique (isNumeraire_numeraire P hS)

lemma neBotUtilityEVar_numeraire [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    NeBotUtilityEVar (numeraire P S) P S logUtility :=
  (isNumeraire_numeraire P hS).neBotUtilityEVar

lemma eintegrable_log_numeraire [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    eintegrable (fun x ↦ ENNReal.log (numeraire P S x)) P :=
  (isNumeraire_numeraire P hS).eintegrable_log

end ProbabilityTheory
