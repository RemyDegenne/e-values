/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
module

public import EValues.LebesgueDecomposition
public import EValues.Numeraire
public import Mathlib.MeasureTheory.Measure.WithDensityFinite
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Existence of the Numeraire

-/

@[expose] public section

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

lemma convex_eintegral_utility_ge [IsFiniteMeasure P] (u : EReal)
    (hU_ccv : ConcaveOn ℝ≥0 Set.univ U)
    (hU_meas : Measurable U) {B : EReal} (hU_le : ∀ x : ℝ≥0∞, U x ≤ B) (hB : B ≠ ⊤) :
    Convex ℝ≥0∞ {Z | Measurable Z ∧ u ≤ ∫ᵉ ω, U (Z ω) ∂P} := by
  intro Y ⟨hY_meas, hY⟩ Z ⟨hZ_meas, hZ⟩ a b ha hb hab
  refine ⟨by fun_prop, ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hY hZ ⊢
  have ha_ne_top : a ≠ ∞ := fun ha_top ↦ by simp [ha_top] at hab
  have hb_ne_top : b ≠ ∞ := fun hb_top ↦ by simp [hb_top] at hab
  have h_int (Y : 𝓧 → ℝ≥0∞) : EIntegrable (fun ω ↦ U (Y ω)) P :=
    eintegrable_of_le (fun _ ↦ hU_le _) (by simpa) P
  calc u
  _ = a * u + b * u := by
    conv_lhs => rw [← one_mul u]
    have : (1 : EReal) = (1 : ℝ≥0∞) := rfl
    rw [this, ← hab]
    simp only [EReal.coe_ennreal_add]
    exact EReal.distrib_ennreal _ _ _
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
      exact EIntegrable.const_mul (h_int _) (by simp) (by simpa)
    · simp only [EReal.smul_ennreal_eq_mul]
      exact EIntegrable.const_mul (h_int _) (by simp) (by simpa)
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
          suffices ∀ x, (U (Y n x)).toENNReal = 0 by simp [this]
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
              push Not at hB
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
def numeraireOfBounded {U : Utility} {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] {S : Set (Measure 𝓧)} (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    𝓧 → ℝ≥0∞ :=
  (exists_eq_iSup_eintegral_of_le U.concave U.continuous U.monotone hU_le P S hS).choose

lemma isEVar_numeraireOfBounded {U : Utility} {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] {S : Set (Measure 𝓧)} (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    IsEVar (numeraireOfBounded hU_le P hS) S :=
  (Classical.choose_spec
    (exists_eq_iSup_eintegral_of_le U.concave U.continuous U.monotone hU_le P S hS)).1

lemma eintegral_le_numeraireOfBounded {U : Utility} {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] {S : Set (Measure 𝓧)} (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∫ᵉ x, U (X x) ∂P ≤ ∫ᵉ x, U (numeraireOfBounded hU_le P hS x) ∂P :=
  ((Classical.choose_spec
    (exists_eq_iSup_eintegral_of_le U.concave U.continuous U.monotone hU_le P S hS)).2 X hX_evar).1

lemma eintegral_numeraireOfBounded_ge {U : Utility} {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] {S : Set (Measure 𝓧)} (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    U 1 * P .univ ≤ ∫ᵉ x, U (numeraireOfBounded hU_le P hS x) ∂P := calc
  U 1 * P .univ
  _ = ∫ᵉ x, U 1 ∂P := by simp
  _ ≤ ∫ᵉ x, U (numeraireOfBounded hU_le P hS x) ∂P :=
    eintegral_le_numeraireOfBounded hU_le P hS (isEVar_one _)

lemma eintegral_numeraireOfBounded_ne_bot {U : Utility} {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] {S : Set (Measure 𝓧)} (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ∫ᵉ x, U (numeraireOfBounded hU_le P hS x) ∂P ≠ ⊥ := by
  refine ne_bot_of_le_ne_bot ?_ (eintegral_numeraireOfBounded_ge hU_le P hS)
  rw [EReal.mul_ne_bot]
  have h : U 1 ≠ ⊥ ∧ U 1 ≠ ⊤ := U.eq_coe (by simp) (by simp)
  simp [h.1, h.2]

lemma eintegrable_utility_numeraireOfBounded {U : Utility} {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] {S : Set (Measure 𝓧)} (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    EIntegrable (fun x ↦ U (numeraireOfBounded hU_le P hS x)) P :=
  eintegrable_of_eintegral_ne_bot (eintegral_numeraireOfBounded_ne_bot hU_le P hS)

lemma lt_top_of_numeraireOfBounded_lt_top {U : Utility} {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] {S : Set (Measure 𝓧)} (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {X : 𝓧 → ℝ≥0∞} (hX_evar : IsEVar X S) :
    ∀ᵐ x ∂P, (numeraireOfBounded hU_le P hS x) < ∞ → X x < ∞ :=
  ((Classical.choose_spec
    (exists_eq_iSup_eintegral_of_le U.concave U.continuous U.monotone hU_le P S hS)).2 X hX_evar).2

noncomputable instance inst_smul_I_ENNReal : SMul I ℝ≥0∞ where
  smul a x := ENNReal.ofReal a * x

@[simp]
lemma smul_I_ENNReal (a : I) (x : ℝ≥0∞) : a • x = ENNReal.ofReal a * x := rfl

instance : MeasurableConstSMul I ℝ≥0∞ where
  measurable_const_smul c := by
    change Measurable (fun x ↦ ENNReal.ofReal c * x)
    fun_prop

section FirstOrderCondition

/-- **First order optimality condition**, for e-variables bounded below by a positive constant.
This is the main step in the proof of `eintegral_deriv_mul_le`. -/
lemma eintegral_deriv_mul_le_of_ge (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {Y : 𝓧 → ℝ≥0∞} (hY : IsEVar Y S) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcY : ∀ x, c ≤ Y x) :
    ∫ᵉ x, U.deriv (numeraireOfBounded hU_le P hS x)
        * ((Y x : EReal) - numeraireOfBounded hU_le P hS x) ∂P ≤ 0
      ∧ ∫ᵉ x, U.deriv (numeraireOfBounded hU_le P hS x)
        * ((Y x : EReal) - numeraireOfBounded hU_le P hS x) ∂P ≠ ⊥ := by
  set X := numeraireOfBounded hU_le P hS with hX_def
  have hX_evar : IsEVar X S := isEVar_numeraireOfBounded hU_le P hS
  have hX_meas : Measurable X := hX_evar.measurable
  have hY_meas : Measurable Y := hY.measurable
  have hY0 (x : 𝓧) : Y x ≠ 0 := fun h ↦ hc0 (le_antisymm (h ▸ hcY x) (by positivity))
  have hb_top : (b : EReal) ≠ ⊤ := by simp
  -- `k` is a finite lower bound for all the difference quotients below
  set k : EReal := U c - (b : EReal) with hk_def
  have hk_bot : k ≠ ⊥ := by
    rw [hk_def, ne_eq, EReal.sub_eq_bot]
    simp [U.ne_bot hc0]
  have hk_int {f : 𝓧 → EReal} (h : ∀ᵐ x ∂P, k ≤ f x) : ∫⁻ x, (-f x).toENNReal ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, (-k).toENNReal ∂P) ?_ (lintegral_mono_ae ?_)
    swap
    · filter_upwards [h] with x hx
      exact EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr hx)
    simp only [lintegral_const]
    refine ENNReal.mul_ne_top ?_ (measure_ne_top _ _)
    simp [hk_bot]
  -- the sequence of interpolation parameters
  set t : ℕ → ℝ := fun n ↦ 1 / (n + 2) with ht_def
  have ht0 (n : ℕ) : 0 < t n := by
    rw [ht_def]
    positivity
  have ht1 (n : ℕ) : t n < 1 := by
    rw [ht_def, div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have ht_tendsto : Tendsto t atTop (𝓝 0) := by
    refine Filter.Tendsto.const_div_atTop ?_ 1
    exact tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  -- the interpolating e-variables and the difference quotients
  set Z : ℕ → 𝓧 → ℝ≥0∞ :=
    fun n x ↦ ENNReal.ofReal (t n) * Y x + ENNReal.ofReal (1 - t n) * X x with hZ_def
  have hZ_evar (n : ℕ) : IsEVar (Z n) S :=
    convex_isEVar S hY hX_evar (by positivity) (by positivity)
      (by rw [← ENNReal.ofReal_add (ht0 n).le (by linarith [ht1 n])]; simp)
  have hZ_meas (n : ℕ) : Measurable (Z n) := (hZ_evar n).measurable
  set F : ℕ → 𝓧 → EReal := fun n x ↦ ((t n : ℝ) : EReal)⁻¹ * (U (Z n x) - U (X x)) with hF_def
  have hF_meas (n : ℕ) : Measurable (F n) := by
    have := hZ_meas n
    fun_prop
  -- the difference quotients are bounded below by the constant `k`
  have hF_lb (n : ℕ) (x : 𝓧) : k ≤ F n x := by
    refine le_trans ?_ (U.sub_le_inv_mul_sub (α := X x) (β := Y x) (hY0 x) (ht0 n) (ht1 n).le)
    exact EReal.sub_le_sub (U.monotone (hcY x)) (hU_le (X x))
  -- each difference quotient has nonpositive integral
  have hdiff_lb (n : ℕ) (x : 𝓧) :
      U (ENNReal.ofReal (t n) * c) - (b : EReal) ≤ U (Z n x) - U (X x) := by
    refine EReal.sub_le_sub (U.monotone ?_) (hU_le (X x))
    rw [hZ_def]
    exact le_add_right (by gcongr; exact hcY x)
  have hdiff_int (n : ℕ) : EIntegrable (fun x ↦ U (Z n x) - U (X x)) P := by
    refine .inr ?_
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x ↦
      EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hdiff_lb n x)))
    simp only [lintegral_const]
    refine ENNReal.mul_ne_top ?_ (measure_ne_top _ _)
    rw [ne_eq, EReal.toENNReal_eq_top_iff, EReal.neg_eq_top_iff, EReal.sub_eq_bot]
    simp only [not_or]
    refine ⟨U.ne_bot ?_, hb_top⟩
    simp only [ne_eq, mul_eq_zero, not_or, ENNReal.ofReal_eq_zero, not_le]
    exact ⟨ht0 n, hc0⟩
  have hF_nonpos (n : ℕ) : ∫ᵉ x, F n x ∂P ≤ 0 := by
    have h_sub : ∫ᵉ x, (U (Z n x) - U (X x)) ∂P ≤ 0 := by
      rw [eintegral_sub (eintegrable_of_le (b := (b : EReal)) (fun x ↦ hU_le _) hb_top P)
          (U.measurable.comp (hZ_meas n)).aemeasurable
          (eintegrable_of_le (b := (b : EReal)) (fun x ↦ hU_le _) hb_top P)
          (U.measurable.comp hX_meas).aemeasurable
          (.inl (eintegral_lt_top_of_le (fun x ↦ hU_le (Z n x)) hb_top P).ne)
          (.inr (eintegral_numeraireOfBounded_ne_bot hU_le P hS)),
        EReal.sub_nonpos]
      exact eintegral_le_numeraireOfBounded hU_le P hS (hZ_evar n)
    have ht_ne : ((t n : ℝ) : EReal)⁻¹ ≠ ⊥ ∧ ((t n : ℝ) : EReal)⁻¹ ≠ ⊤ := by
      simp [← EReal.coe_inv]
    rw [hF_def]
    simp only
    rw [eintegral_mul_const ht_ne.1 ht_ne.2 (hdiff_int n), ← mul_zero ((t n : ℝ) : EReal)⁻¹]
    gcongr
  -- the pointwise liminf bound
  set g : 𝓧 → EReal := fun x ↦ U.deriv (X x) * ((Y x : EReal) - X x) with hg_def
  have h_ptwise : ∀ᵐ x ∂P, g x ≤ liminf (fun n ↦ F n x) atTop := by
    filter_upwards [lt_top_of_numeraireOfBounded_lt_top hU_le P hS hY] with x hx
    exact U.deriv_mul_sub_le_liminf hU_le (hY0 x)
      (fun hX_top ↦ (hx (lt_top_iff_ne_top.mpr hX_top)).ne) ht0 ht1 ht_tendsto
  -- `g` is also bounded below by `k`
  have hg_lb : ∀ᵐ x ∂P, k ≤ g x := by
    filter_upwards [lt_top_of_numeraireOfBounded_lt_top hU_le P hS hY] with x hx
    by_cases hX0 : X x = 0
    · have hk_nonpos : k ≤ 0 := by
        rw [hk_def, EReal.sub_nonpos]
        exact hU_le c
      refine hk_nonpos.trans ?_
      change (0 : EReal) ≤ U.deriv (X x) * ((Y x : EReal) - X x)
      refine mul_nonneg (U.deriv_nonneg _) ?_
      rw [hX0]
      simpa using EReal.coe_ennreal_nonneg (Y x)
    · refine le_trans ?_ (U.sub_le_deriv_mul_sub hU_le hX0
        (fun hX_top ↦ (hx (lt_top_iff_ne_top.mpr hX_top)).ne))
      exact EReal.sub_le_sub (U.monotone (hcY x)) (hU_le (X x))
  refine ⟨?_, ?_⟩
  swap
  · rw [eintegral_ne_bot_iff_lintegral_ne_top]
    exact hk_int hg_lb
  rw [eintegral_nonpos_iff_lintegral_le]
  calc ∫⁻ x, (g x).toENNReal ∂P
  _ ≤ ∫⁻ x, liminf (fun n ↦ (F n x).toENNReal) atTop ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [h_ptwise] with x hx
    rw [← EReal.liminf_coe_ennreal]
    exact EReal.toENNReal_le_toENNReal hx
  _ ≤ liminf (fun n ↦ ∫⁻ x, (F n x).toENNReal ∂P) atTop :=
    lintegral_liminf_le fun n ↦ EReal.continuous_toENNReal.measurable.comp (hF_meas n)
  _ ≤ liminf (fun n ↦ ∫⁻ x, (-(F n x)).toENNReal ∂P) atTop :=
    liminf_le_liminf (.of_forall fun n ↦ eintegral_nonpos_iff_lintegral_le.mp (hF_nonpos n))
  _ ≤ limsup (fun n ↦ ∫⁻ x, (-(F n x)).toENNReal ∂P) atTop := liminf_le_limsup
  _ ≤ ∫⁻ x, limsup (fun n ↦ (-(F n x)).toENNReal) atTop ∂P := by
    refine limsup_lintegral_le (fun _ ↦ (-k).toENNReal)
      (fun n ↦ (EReal.continuous_toENNReal.measurable.comp (hF_meas n).neg))
      (fun n ↦ .of_forall fun x ↦
        EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hF_lb n x))) ?_
    simp only [lintegral_const]
    refine ENNReal.mul_ne_top ?_ (measure_ne_top _ _)
    simp [hk_bot]
  _ ≤ ∫⁻ x, (-g x).toENNReal ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [h_ptwise] with x hx
    rw [← EReal.limsup_coe_ennreal]
    refine EReal.toENNReal_le_toENNReal ?_
    have h_neg : limsup (fun n ↦ -(F n x)) atTop = -liminf (fun n ↦ F n x) atTop :=
      (EReal.neg_strictAnti.antitone.map_liminf_of_continuousAt _
        (continuous_neg (G := EReal)).continuousAt).symm
    rw [h_neg]
    exact EReal.neg_le_neg_iff.mpr hx

-- first order optimality condition for bounded utility functions
lemma eintegral_deriv_mul_le (U : Utility) {b : ℝ} (hU_le : ∀ x : ℝ≥0∞, U x ≤ b)
    (P : Measure 𝓧) [IsFiniteMeasure P] (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {Y : 𝓧 → ℝ≥0∞} (hY : IsEVar Y S) :
    ∫ᵉ x, U.deriv (numeraireOfBounded hU_le P hS x)
      * (Y x - numeraireOfBounded hU_le P hS x) ∂P ≤ 0 := by
  -- Lemma 2.9 of _Larsson et al._ (2025). We know the result for e-variables that are bounded
  -- below by a positive constant (`eintegral_deriv_mul_le_of_ge`); we apply it to the
  -- e-variables `Yδ n = δ n + (1 - δ n) * Y` and let `δ n` tend to `0`.
  set X := numeraireOfBounded hU_le P hS with hX_def
  have hX_meas : Measurable X := (isEVar_numeraireOfBounded hU_le P hS).measurable
  have hY_meas : Measurable Y := hY.measurable
  set g : 𝓧 → EReal := fun x ↦ U.deriv (X x) * ((Y x : EReal) - X x) with hg_def
  by_cases hg_bot : ∫ᵉ x, g x ∂P = ⊥
  · rw [hg_bot]
    exact bot_le
  have hg_int : EIntegrable g P := eintegrable_of_eintegral_ne_bot hg_bot
  have hg_meas : AEMeasurable g P := by
    rw [hg_def]
    have := U.measurable_deriv
    fun_prop
  -- the first order condition for the constant e-variable `1`
  have h1_evar : IsEVar (1 : 𝓧 → ℝ≥0∞) S := isEVar_one S
  obtain ⟨hg1_nonpos, hg1_bot⟩ :=
    eintegral_deriv_mul_le_of_ge U hU_le P S hS h1_evar (c := 1) one_ne_zero fun _ ↦ le_rfl
  simp only [Pi.one_apply, EReal.coe_ennreal_one] at hg1_nonpos hg1_bot
  set g1 : 𝓧 → EReal := fun x ↦ U.deriv (X x) * ((1 : EReal) - X x) with hg1_def
  have hg1_int : EIntegrable g1 P := eintegrable_of_eintegral_ne_bot hg1_bot
  have hg1_meas : AEMeasurable g1 P := by
    rw [hg1_def]
    have := U.measurable_deriv
    fun_prop
  have hg1_top : ∫ᵉ x, g1 x ∂P ≠ ⊤ := ne_top_of_le_ne_top (by simp) hg1_nonpos
  obtain ⟨m, hm⟩ : ∃ m : ℝ, ∫ᵉ x, g1 x ∂P = (m : EReal) :=
    ⟨_, (EReal.coe_toReal hg1_top hg1_bot).symm⟩
  -- the sequence of e-variables `Yδ n`
  set δ : ℕ → ℝ := fun n ↦ 1 / (n + 2) with hδ_def
  have hδ0 (n : ℕ) : 0 < δ n := by
    rw [hδ_def]
    positivity
  have hδ1 (n : ℕ) : δ n < 1 := by
    rw [hδ_def, div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hδ_tendsto : Tendsto δ atTop (𝓝 0) := by
    refine Filter.Tendsto.const_div_atTop ?_ 1
    exact tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  set Yδ : ℕ → 𝓧 → ℝ≥0∞ :=
    fun n ↦ ENNReal.ofReal (δ n) • (1 : 𝓧 → ℝ≥0∞) + ENNReal.ofReal (1 - δ n) • Y with hYδ_def
  have hYδ_evar (n : ℕ) : IsEVar (Yδ n) S :=
    convex_isEVar S h1_evar hY (by positivity) (by positivity)
      (by rw [← ENNReal.ofReal_add (hδ0 n).le (by linarith [hδ1 n])]; simp)
  have hYδ_ge (n : ℕ) (x : 𝓧) : ENNReal.ofReal (δ n) ≤ Yδ n x := by
    simp only [hYδ_def, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact le_add_right le_rfl
  -- the first order condition for `Yδ n`, rewritten as a convex combination
  have key (n : ℕ) : ((1 - δ n : ℝ) : EReal) * (∫ᵉ x, g x ∂P)
      + ((δ n : ℝ) : EReal) * (∫ᵉ x, g1 x ∂P) ≤ 0 := by
    obtain ⟨h1, -⟩ := eintegral_deriv_mul_le_of_ge U hU_le P S hS (hYδ_evar n)
      (c := ENNReal.ofReal (δ n)) (by simp [hδ0 n]) (hYδ_ge n)
    have h_eq : ∀ᵐ x ∂P, U.deriv (X x) * ((Yδ n x : EReal) - X x)
        = ((1 - δ n : ℝ) : EReal) * g x + ((δ n : ℝ) : EReal) * g1 x := by
      filter_upwards [lt_top_of_numeraireOfBounded_lt_top hU_le P hS hY] with x hx
      exact U.deriv_mul_sub_convex hU_le
        (fun hXt ↦ (hx (lt_top_iff_ne_top.mpr hXt)).ne) (hδ0 n) (hδ1 n)
    rw [eintegral_congr_ae h_eq] at h1
    have hδg1_eq : ∫ᵉ x, ((δ n : ℝ) : EReal) * g1 x ∂P = ((δ n * m : ℝ) : EReal) := by
      rw [eintegral_mul_const (EReal.coe_ne_bot _) (EReal.coe_ne_top _) hg1_int, hm,
        ← EReal.coe_mul]
    rwa [eintegral_add' (hg_meas.const_mul _) (hg1_meas.const_mul _)
        (by rw [hδg1_eq]; exact EReal.coe_ne_top _) (by rw [hδg1_eq]; exact EReal.coe_ne_bot _),
      eintegral_mul_const (EReal.coe_ne_bot _) (EReal.coe_ne_top _) hg_int,
      eintegral_mul_const (EReal.coe_ne_bot _) (EReal.coe_ne_top _) hg1_int] at h1
  -- the integral of `g` is finite
  have hg_top : ∫ᵉ x, g x ∂P ≠ ⊤ := by
    intro hG
    have h0 := key 0
    rw [hG, hm, EReal.coe_mul_top_of_pos (x := 1 - δ 0) (by positivity),
      EReal.top_add_of_ne_bot (by rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _)] at h0
    simp at h0
  obtain ⟨G, hG⟩ : ∃ G : ℝ, ∫ᵉ x, g x ∂P = (G : EReal) :=
    ⟨_, (EReal.coe_toReal hg_top hg_bot).symm⟩
  simp only [hG, hm] at key
  rw [hG]
  have key' (n : ℕ) : (1 - δ n) * G + δ n * m ≤ 0 := by
    have h := key n
    norm_cast at h
  have hG_nonpos : G ≤ 0 := by
    have h_tendsto : Tendsto (fun n ↦ (1 - δ n) * G + δ n * m) atTop (𝓝 ((1 - 0) * G + 0 * m)) :=
      ((tendsto_const_nhds.sub hδ_tendsto).mul_const G).add (hδ_tendsto.mul_const m)
    simpa using le_of_tendsto h_tendsto (.of_forall key')
  exact_mod_cast hG_nonpos

/-- The first order optimality condition for `boundedLogUtility`, in `ℝ≥0∞` form. -/
lemma lintegral_harmonicDeriv_mul_le {N : ℝ} (hN : 0 < N)
    (P : Measure 𝓧) [IsFiniteMeasure P] {S : Set (Measure 𝓧)} (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {Y : 𝓧 → ℝ≥0∞} (hY : IsEVar Y S) :
    ∫⁻ x, harmonicDeriv N (numeraireOfBounded (boundedLogUtility_le hN) P hS x) * Y x ∂P
      ≤ P {x | numeraireOfBounded (boundedLogUtility_le hN) P hS x ≠ ∞} := by
  set X := numeraireOfBounded (boundedLogUtility_le hN) P hS with hX_def
  have hX_meas : Measurable X :=
    (isEVar_numeraireOfBounded (boundedLogUtility_le hN) P hS).measurable
  have hY_meas : Measurable Y := hY.measurable
  have hA_meas : MeasurableSet {x | X x ≠ ∞} := (hX_meas (measurableSet_singleton ∞)).compl
  -- the integral of `harmonicDeriv N (X x) * X x` is at most `P {X ≠ ∞}`
  have h_bound : ∫⁻ x, harmonicDeriv N (X x) * X x ∂P ≤ P {x | X x ≠ ∞} := by
    rw [← lintegral_indicator_one hA_meas]
    refine lintegral_mono fun x ↦ ?_
    by_cases hx : X x = ∞
    · simp [hx]
    · rw [Set.indicator_of_mem hx]
      exact harmonicDeriv_mul_le_one N (X x)
  have h_ne_top : ∫⁻ x, harmonicDeriv N (X x) * X x ∂P ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top _ _) h_bound
  refine le_trans ?_ h_bound
  have h := eintegral_deriv_mul_le (boundedLogUtility hN) (boundedLogUtility_le hN) P S hS hY
  rw [← hX_def] at h
  have h_eq (x : 𝓧) : (boundedLogUtility hN).deriv (X x) * ((Y x : EReal) - X x)
      = ((harmonicDeriv N (X x) * Y x : ℝ≥0∞) : EReal)
        - ((harmonicDeriv N (X x) * X x : ℝ≥0∞) : EReal) := by
    rw [deriv_boundedLogUtility hN]
    exact EReal.coe_ennreal_mul_sub fun hc ↦ (harmonicDeriv_eq_top_iff hN).mp hc
  rw [eintegral_congr h_eq, eintegral_sub_of_nonneg] at h
  rotate_left
  · exact fun _ ↦ by positivity
  · exact fun _ ↦ by positivity
  · have := measurable_harmonicDeriv N; fun_prop
  · have := measurable_harmonicDeriv N; fun_prop
  · refine ne_top_of_le_ne_top (b := ∫ᵉ x, ((harmonicDeriv N (X x) * X x : ℝ≥0∞) : EReal) ∂P) ?_ ?_
    · rw [eintegral_eq_lintegral, ne_eq, EReal.coe_ennreal_eq_top_iff]
      exact h_ne_top
    · refine eintegral_mono fun x ↦ ?_
      exact min_le_right _ _
  rw [EReal.sub_nonpos, eintegral_eq_lintegral, eintegral_eq_lintegral] at h
  exact_mod_cast h

-- first order optimality condition for log utility
lemma eintegral_deriv_log_mul_le (P : Measure 𝓧) [IsFiniteMeasure P]
    {S : Set (Measure 𝓧)} (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      ∫ᵉ x, logUtility.deriv (Y x) * (X x - Y x) ∂P ≤ 0 := by
  -- Lemma 2.10 of _Larsson et al._ (2025).
  -- It suffices to produce a numeraire, in `ℝ≥0∞` form.
  suffices h : ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      ∫⁻ x, X x / Y x ∂P ≤ ∫⁻ x, Y x / Y x ∂P by
    obtain ⟨Y, hY_evar, hY⟩ := h
    refine ⟨Y, hY_evar, fun X hX ↦ ?_⟩
    have hY_meas := hY_evar.measurable
    have hX_meas := hX.measurable
    specialize hY X hX
    have h_ne_top : ∫⁻ x, Y x / Y x ∂P ≠ ∞ := by
      refine ne_top_of_le_ne_top (measure_ne_top P Set.univ) ?_
      rw [lintegral_div_self_eq_measure_fsupport hY_meas]
      exact measure_mono (Set.subset_univ _)
    have h_eq (x : 𝓧) : logUtility.deriv (Y x) * ((X x : EReal) - Y x)
        = ((X x / Y x : ℝ≥0∞) : EReal) - ((Y x / Y x : ℝ≥0∞) : EReal) := by
      have h1 : (1 / Y x : ℝ≥0∞) * X x = X x / Y x := by
        rw [one_div, ENNReal.div_eq_inv_mul]
      have h2 : (1 / Y x : ℝ≥0∞) * Y x = Y x / Y x := by
        rw [one_div, ENNReal.div_eq_inv_mul]
      rw [deriv_logUtility_eq_ennreal,
        EReal.coe_ennreal_mul_sub (c := (1 / Y x : ℝ≥0∞)) (fun hc ↦ by simpa using hc), h1, h2]
    rw [eintegral_congr h_eq, eintegral_sub_of_nonneg]
    rotate_left
    · exact fun _ ↦ by positivity
    · exact fun _ ↦ by positivity
    · fun_prop
    · fun_prop
    · refine ne_top_of_le_ne_top (b := ∫ᵉ x, ((Y x / Y x : ℝ≥0∞) : EReal) ∂P) ?_ ?_
      · rw [eintegral_eq_lintegral, ne_eq, EReal.coe_ennreal_eq_top_iff]
        exact h_ne_top
      · exact eintegral_mono fun x ↦ min_le_right _ _
    rw [EReal.sub_nonpos, eintegral_eq_lintegral, eintegral_eq_lintegral]
    exact_mod_cast hY
  -- the bounded approximations of the logarithm and their optimal e-variables
  have hN (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set Xo : ℕ → 𝓧 → ℝ≥0∞ :=
    fun n ↦ numeraireOfBounded (boundedLogUtility_le (hN n)) P hS with hXo_def
  have hXo_evar (n : ℕ) : IsEVar (Xo n) S := isEVar_numeraireOfBounded _ P hS
  have hXo_meas (n : ℕ) : Measurable (Xo n) := (hXo_evar n).measurable
  -- all the sets `{Xo n ≠ ∞}` agree up to null sets
  set A : Set 𝓧 := {x | Xo 0 x ≠ ∞} with hA_def
  have hA (n : ℕ) : P {x | Xo n x ≠ ∞} = P A := by
    refine measure_congr (Filter.EventuallyEq.symm ?_)
    rw [Filter.eventuallyEq_set]
    filter_upwards [lt_top_of_numeraireOfBounded_lt_top (boundedLogUtility_le (hN n)) P hS
        (hXo_evar 0), lt_top_of_numeraireOfBounded_lt_top (boundedLogUtility_le (hN 0)) P hS
        (hXo_evar n)] with x h1 h2
    exact ⟨fun h ↦ (h2 (lt_top_iff_ne_top.mpr h)).ne, fun h ↦ (h1 (lt_top_iff_ne_top.mpr h)).ne⟩
  have hPA : P A ≠ ∞ := measure_ne_top _ _
  -- the first order condition, in `ℝ≥0∞` form
  have hfoc (n : ℕ) {Y : 𝓧 → ℝ≥0∞} (hY : IsEVar Y S) :
      ∫⁻ x, harmonicDeriv ((n : ℝ) + 1) (Xo n x) * Y x ∂P ≤ P A := by
    rw [← hA n]
    exact lintegral_harmonicDeriv_mul_le (hN n) P hS hY
  -- the Komlós lemma applied to the sequence `Xo`
  obtain ⟨W, W_lim, hW_mem, hW_lim_meas, hW_tendsto⟩ := komlos_ennreal hXo_meas P
  have hW_evar (n : ℕ) : IsEVar (W n) S := by
    have h := hW_mem n
    rw [mem_convexHull_iff] at h
    refine h {Z | IsEVar Z S} ?_ (convex_isEVar S)
    rintro _ ⟨m, rfl⟩
    exact hXo_evar (n + m)
  set Xstar : 𝓧 → ℝ≥0∞ := fun x ↦ liminf (fun n ↦ W n x) atTop with hXstar_def
  have hXstar_evar : IsEVar Xstar S := isEVar_liminf hW_evar hS
  have hXstar_meas : Measurable Xstar := hXstar_evar.measurable
  have hXstar_eq : ∀ᵐ x ∂P, Xstar x = W_lim x := by
    filter_upwards [hW_tendsto] with x hx
    exact hx.liminf_eq
  -- the sequence of error terms
  have h_err : Tendsto (fun n : ℕ ↦ (ENNReal.ofReal ((n : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun n ↦ by positivity) (fun n ↦ ?_)
    gcongr
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- the key estimate
  have key : ∀ Y : 𝓧 → ℝ≥0∞, IsEVar Y S → ∫⁻ x, Y x ∂P ≠ ∞ →
      ∫⁻ x, Y x * (Xstar x)⁻¹ ∂P ≤ P A := by
    intro Y hY hY_int
    have hY_meas := hY.measurable
    have h5 (i : ℕ) : ∫⁻ x, Y x * (Xo i x)⁻¹ ∂P
        ≤ P A + (ENNReal.ofReal ((i : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P := by
      calc ∫⁻ x, Y x * (Xo i x)⁻¹ ∂P
      _ ≤ ∫⁻ x, (harmonicDeriv ((i : ℝ) + 1) (Xo i x) * Y x
            + (ENNReal.ofReal ((i : ℝ) + 1))⁻¹ * Y x) ∂P := by
        refine lintegral_mono fun x ↦ ?_
        rw [← add_mul, mul_comm (Y x)]
        gcongr
        exact inv_le_harmonicDeriv_add _ _
      _ = ∫⁻ x, harmonicDeriv ((i : ℝ) + 1) (Xo i x) * Y x ∂P
            + (ENNReal.ofReal ((i : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P := by
        rw [lintegral_add_left (by have := measurable_harmonicDeriv ((i : ℝ) + 1); fun_prop),
          lintegral_const_mul _ hY_meas]
      _ ≤ _ := by gcongr; exact hfoc i hY
    have h7 (n : ℕ) : ∫⁻ x, Y x * (W n x)⁻¹ ∂P
        ≤ P A + (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P := by
      have h := hW_mem n
      rw [mem_convexHull_iff] at h
      refine (h {Z | Measurable Z ∧ ∫⁻ x, Y x * (Z x)⁻¹ ∂P
          ≤ P A + (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P} ?_ ?_).2
      · rintro _ ⟨m, rfl⟩
        refine ⟨hXo_meas _, (h5 (n + m)).trans ?_⟩
        have hcoef : (ENNReal.ofReal (((n + m : ℕ) : ℝ) + 1))⁻¹
            ≤ (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ := by
          rw [ENNReal.inv_le_inv]
          exact ENNReal.ofReal_le_ofReal (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) m])
        exact add_le_add le_rfl (by gcongr)
      · rintro Z1 ⟨h1m, h1⟩ Z2 ⟨h2m, h2⟩ a b ha hb hab
        refine ⟨by fun_prop, ?_⟩
        calc ∫⁻ x, Y x * ((a • Z1 + b • Z2) x)⁻¹ ∂P
        _ ≤ ∫⁻ x, (a * (Y x * (Z1 x)⁻¹) + b * (Y x * (Z2 x)⁻¹)) ∂P := by
          refine lintegral_mono fun x ↦ ?_
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          calc Y x * (a * Z1 x + b * Z2 x)⁻¹
          _ ≤ Y x * (a * (Z1 x)⁻¹ + b * (Z2 x)⁻¹) := by
            gcongr
            exact convexOn_inv.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
          _ = a * (Y x * (Z1 x)⁻¹) + b * (Y x * (Z2 x)⁻¹) := by ring
        _ = a * ∫⁻ x, Y x * (Z1 x)⁻¹ ∂P + b * ∫⁻ x, Y x * (Z2 x)⁻¹ ∂P := by
          rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
            lintegral_const_mul _ (by fun_prop)]
        _ ≤ a * (P A + (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P)
              + b * (P A + (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P) := by gcongr
        _ = P A + (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P := by
          rw [← add_mul, hab, one_mul]
    -- Fatou
    calc ∫⁻ x, Y x * (Xstar x)⁻¹ ∂P
    _ ≤ ∫⁻ x, liminf (fun n ↦ Y x * (W n x)⁻¹) atTop ∂P := by
      refine lintegral_mono_ae ?_
      filter_upwards [hW_tendsto, hXstar_eq] with x hx hx_eq
      rw [hx_eq]
      exact ENNReal.const_mul_le_liminf ((continuous_inv.tendsto _).comp hx)
    _ ≤ liminf (fun n ↦ ∫⁻ x, Y x * (W n x)⁻¹ ∂P) atTop := by
      refine lintegral_liminf_le fun n ↦ ?_
      have := (hW_evar n).measurable
      fun_prop
    _ ≤ liminf (fun n : ℕ ↦ P A + (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P) atTop :=
      liminf_le_liminf (.of_forall h7)
    _ = P A := by
      refine Tendsto.liminf_eq ?_
      have h0 : Tendsto (fun n : ℕ ↦ (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * ∫⁻ x, Y x ∂P)
          atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.mul_const h_err (Or.inr hY_int)
      simpa using (tendsto_const_nhds (x := P A) (f := atTop (α := ℕ))).add h0
  -- `Xstar` is almost everywhere nonzero
  have hXstar_ne_zero : ∀ᵐ x ∂P, Xstar x ≠ 0 := by
    have h := key 1 (isEVar_one S) (by simp)
    simp only [Pi.one_apply, one_mul] at h
    have h_lt := ae_lt_top' (by fun_prop) (ne_top_of_le_ne_top hPA h)
    filter_upwards [h_lt] with x hx
    intro h0
    rw [h0] at hx
    simp at hx
  -- `Xstar` is almost everywhere finite on `A`
  have hXstar_ne_top : ∀ᵐ x ∂P, x ∈ A → Xstar x ≠ ∞ := by
    have h : ∫⁻ x, harmonicDeriv ((0 : ℝ) + 1) (Xo 0 x) * Xstar x ∂P ≤ P A := by
      calc ∫⁻ x, harmonicDeriv ((0 : ℝ) + 1) (Xo 0 x) * Xstar x ∂P
      _ ≤ ∫⁻ x, liminf (fun n ↦ harmonicDeriv ((0 : ℝ) + 1) (Xo 0 x) * W n x) atTop ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hW_tendsto, hXstar_eq] with x hx hx_eq
        rw [hx_eq]
        exact ENNReal.const_mul_le_liminf hx
      _ ≤ liminf (fun n ↦ ∫⁻ x, harmonicDeriv ((0 : ℝ) + 1) (Xo 0 x) * W n x ∂P) atTop := by
        refine lintegral_liminf_le fun n ↦ ?_
        have := (hW_evar n).measurable
        have := measurable_harmonicDeriv ((0 : ℝ) + 1)
        fun_prop
      _ ≤ P A := by
        refine liminf_le_of_frequently_le' (.of_forall fun n ↦ ?_)
        simpa using hfoc 0 (hW_evar n)
    have h_lt := ae_lt_top' (by
      have := measurable_harmonicDeriv ((0 : ℝ) + 1); fun_prop) (ne_top_of_le_ne_top hPA h)
    filter_upwards [h_lt] with x hx hxA
    intro h_top
    rw [h_top, ENNReal.mul_top (harmonicDeriv_ne_zero (by norm_num) hxA)] at hx
    simp at hx
  -- conclusion
  refine ⟨Xstar, hXstar_evar, fun X hX ↦ ?_⟩
  rw [lintegral_div_self_eq_measure_fsupport hXstar_meas]
  have hA_le : P A ≤ P Xstar.fsupport := by
    refine measure_mono_ae ?_
    filter_upwards [hXstar_ne_zero, hXstar_ne_top] with x h0 h_top hxA
    exact ⟨h_top hxA, h0⟩
  refine le_trans ?_ hA_le
  -- reduce to bounded e-variables
  have h_trunc (k : ℕ) : ∫⁻ x, (min (X x) k) / Xstar x ∂P ≤ P A := by
    have hk_evar : IsEVar (fun x ↦ min (X x) (k : ℝ≥0∞)) S :=
      IsEVar.mono hS hX (by have := hX.measurable; fun_prop) fun x ↦ min_le_left _ _
    have hk_int : ∫⁻ x, min (X x) (k : ℝ≥0∞) ∂P ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x ↦ min_le_right _ _)
      simp only [lintegral_const]
      exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
    have := key _ hk_evar hk_int
    simpa only [ENNReal.div_eq_inv_mul, mul_comm] using this
  have h_mono : Monotone fun k : ℕ ↦ fun x ↦ (min (X x) (k : ℝ≥0∞)) / Xstar x := by
    intro j k hjk x
    simp only
    refine ENNReal.div_le_div_right (min_le_min le_rfl ?_) _
    exact_mod_cast hjk
  have h_sup_min (a : ℝ≥0∞) : ⨆ k : ℕ, min a (k : ℝ≥0∞) = a := by
    refine le_antisymm (iSup_le fun k ↦ min_le_left _ _) ?_
    rcases eq_or_ne a ∞ with rfl | ha
    · calc (∞ : ℝ≥0∞) = ⨆ k : ℕ, (k : ℝ≥0∞) := ENNReal.iSup_natCast.symm
        _ ≤ ⨆ k : ℕ, min (∞ : ℝ≥0∞) (k : ℝ≥0∞) := by
          refine iSup_mono fun k ↦ ?_
          rw [min_eq_right le_top]
    · obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt ha
      exact le_iSup_of_le k (by simp [min_eq_left hk.le])
  have h_sup : ∀ x, ⨆ k : ℕ, (min (X x) (k : ℝ≥0∞)) / Xstar x = X x / Xstar x := by
    intro x
    rw [← ENNReal.iSup_div, h_sup_min]
  calc ∫⁻ x, X x / Xstar x ∂P
  _ = ∫⁻ x, ⨆ k : ℕ, (min (X x) (k : ℝ≥0∞)) / Xstar x ∂P := by simp_rw [h_sup]
  _ = ⨆ k : ℕ, ∫⁻ x, (min (X x) (k : ℝ≥0∞)) / Xstar x ∂P := by
    refine lintegral_iSup (fun k ↦ ?_) h_mono
    have := hX.measurable
    fun_prop
  _ ≤ P A := iSup_le h_trunc

end FirstOrderCondition

lemma exists_numeraire' (P : Measure 𝓧) [IsFiniteMeasure P]
    (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ∃ Y : 𝓧 → ℝ≥0∞, IsEVar Y S ∧ ∀ X, IsEVar X S →
      ∫ᵉ x, (X x / Y x : ℝ≥0∞) - (Y x / Y x : ℝ≥0∞) ∂P ≤ 0 := by
  obtain ⟨Y, hY_evar, h_opt⟩ := eintegral_deriv_log_mul_le P hS
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
        exact lt_of_le_of_ne' zero_le hX
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

/-- The canonical numeraire `numeraire P S` is indeed a numeraire for `S` and `P`. -/
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
    EIntegrable (fun x ↦ ENNReal.log (numeraire P S x)) P :=
  (isNumeraire_numeraire P hS).eintegrable_log

end ProbabilityTheory
