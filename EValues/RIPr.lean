/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import EValues.DPI
import EValues.NumeraireExistence
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Reverse Information Projection and duality

## Main definitions

* `KL`: a version of the Kullback-Leibler divergence between two measures, which differ from the
  one in Mathlib (`klDiv`) in that it has only the integral term. It does not compensate for the
  case where the measures are not probability measures.
* `MemEffectiveSet S μ`: a measure `μ` is in the effective set of a set of measures `S` if the
  expectation under `μ` of every e-variable for `S` is at most 1.
* `ripr P S`: Reverse Information Projection of the measure `P` on the set `S`.
  It is defined as `P.withDensity fun ω ↦ (numeraire P S ω)⁻¹`. It minimizes the Kullback-Leibler
  divergence `KL P μ` among measures in the effective set of `S`.

## Main statements

* `maxUtility_eq_KL_ripr`: if the numeraire is almost everywhere finite, then
  `maxUtility P S logUtility = KL P (ripr P S)`.
* `maxUtility_eq_iInf_KL_memEffectiveSet`: if the numeraire is almost everywhere finite, then
  `maxUtility P S logUtility = ⨅ (μ) (_hμ : MemEffectiveSet S μ), KL P μ`. This is the
  duality between maximal logarithmic utility and minimal Kullback-Leibler divergence.

-/

open scoped ENNReal NNReal ProbabilityTheory

open MeasureTheory ProbabilityTheory InformationTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {P : Measure 𝓧} {S : Set (Measure 𝓧)}

section Aux

lemma MeasureTheory.lintegral_rnDeriv_mul_le {μ : Measure 𝓧} {X : 𝓧 → ℝ≥0∞} (hX : Measurable X) :
    ∫⁻ ω, (∂μ/∂P) ω * X ω ∂P ≤ ∫⁻ ω, X ω ∂μ := by
  calc ∫⁻ ω, (∂μ/∂P) ω * X ω ∂P
  _ = ∫⁻ ω, X ω ∂(P.withDensity (∂μ/∂P)) := by
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hX]; simp
  _ ≤ ∫⁻ ω, X ω ∂μ := lintegral_mono' (μ.withDensity_rnDeriv_le P) le_rfl

-- lemma Integrable.eintegrable {f : 𝓧 → ℝ} (hf : Integrable f P) :
--     eintegrable (fun x ↦ f x) P := by
--   sorry

lemma eintegrable_rnDeriv_mul_iff {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : 𝓧 → EReal} (hμν : μ ≪ ν) (hf : Measurable f) :
    eintegrable (fun a ↦ (μ.rnDeriv ν a).toReal * f a) ν ↔ eintegrable f μ := by
  rw [eintegrable, eintegrable]
  congr! 1
  · nth_rw 2 [← Measure.withDensity_rnDeriv_eq μ ν hμν]
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
    congr! 1
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx
    simp only [Pi.mul_apply]
    rw [EReal.toENNReal_mul (by simp)]
    simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true, EReal.toENNReal_of_ne_top,
      EReal.toReal_coe]
    rw [ENNReal.ofReal_toReal hx]
  · nth_rw 2 [← Measure.withDensity_rnDeriv_eq μ ν hμν]
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
    congr! 1
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx
    simp only [Pi.mul_apply]
    rw [mul_comm, ← EReal.neg_mul, mul_comm]
    rw [EReal.toENNReal_mul (by simp)]
    simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true, EReal.toENNReal_of_ne_top,
      EReal.toReal_coe]
    rw [ENNReal.ofReal_toReal hx]

end Aux

namespace ProbabilityTheory

/-- Reverse Information Projection. -/
noncomputable
def ripr (P : Measure 𝓧) (S : Set (Measure 𝓧)) : Measure 𝓧 :=
  P.withDensity fun ω ↦ (numeraire P S ω)⁻¹

lemma ripr_univ (P : Measure 𝓧) : ripr P S .univ = ∫⁻ x, (numeraire P S x)⁻¹ ∂P := by
  rw [ripr, withDensity_apply _ .univ, setLIntegral_univ]

lemma ripr_univ_le_measure_fsupport (P : Measure 𝓧) (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    ripr P S .univ ≤ P (numeraire P S).fsupport := by
  rw [ripr_univ]
  simpa using (isNumeraire_numeraire P hS).lintegral_div_le_measure_fsupport (isEVar_fun_one S)

lemma ripr_univ_le_measure_univ (P : Measure 𝓧) :
    ripr P S .univ ≤ P .univ := by
  by_cases hS : ∀ μ ∈ S, IsFiniteMeasure μ
  · exact (ripr_univ_le_measure_fsupport P hS).trans (measure_mono (Set.subset_univ _))
  · unfold ripr numeraire
    simp [hS]

/-- The reverse information projection is a sub-probability measure
(its total mass is at most 1). -/
lemma ripr_univ_le_one (P : Measure 𝓧) [IsProbabilityMeasure P] :
    ripr P S .univ ≤ 1 := by simpa using ripr_univ_le_measure_univ P

instance isFiniteMeasure_ripr (P : Measure 𝓧) [IsFiniteMeasure P] : IsFiniteMeasure (ripr P S) where
  measure_univ_lt_top := by
    rw [lt_top_iff_ne_top]
    exact ne_top_of_le_ne_top (by simp) (ripr_univ_le_measure_univ P)

lemma absolutelyContinuous_ripr_of_ae_ne_top (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    P ≪ ripr P S := by
  refine withDensity_absolutelyContinuous' (by fun_prop) ?_
  simp only [ne_eq, ENNReal.inv_eq_zero, h_top]

lemma rnDeriv_div_ripr [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    P.rnDeriv (ripr P S) =ᵐ[P] numeraire P S := by
  refine (Measure.rnDeriv_withDensity_right _ _ (by fun_prop) ?_ ?_).trans ?_
  · simpa
  · simp only [ne_eq, ENNReal.inv_eq_top]
    exact IsNumeraire.ae_ne_zero (isNumeraire_numeraire P hS)
  simp only [inv_inv]
  filter_upwards [Measure.rnDeriv_self P] with x hx using by simp [hx]

lemma llr_div_ripr [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    llr P (ripr P S) =ᵐ[P] fun x ↦ Real.log (numeraire P S x).toReal := by
  unfold llr
  filter_upwards [rnDeriv_div_ripr hS h_top] with x hx using by simp [hx]

lemma llr_div_ripr' [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    llr P (ripr P S) =ᵐ[P] fun x ↦ (ENNReal.log (numeraire P S x)).toReal := by
  have h_ne_zero := (isNumeraire_numeraire P hS).ae_ne_zero
  filter_upwards [h_ne_zero, h_top, llr_div_ripr hS h_top] with x hx1 hx2
  unfold ENNReal.log
  simp [hx1, hx2]

open Classical in
/-- A version of the Kullback-Leibler divergence between two measures.
It takes value in `EReal` because it might be negative for non-probability measures. -/
noncomputable def KL (μ ν : Measure 𝓧) : EReal :=
  if μ ≪ ν ∧ Integrable (llr μ ν) μ then (∫ x, llr μ ν x ∂μ : ℝ) else ⊤

lemma eintegral_log_numeraire_eq_integral [IsFiniteMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤)
    (h_int : ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P ≠ ⊤) :
    ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P = ∫ x, Real.log (numeraire P S x).toReal ∂P := by
  rw [eintegral_eq_integral_toReal (by fun_prop) _ h_int]
  · congr 1
    refine integral_congr_ae ?_
    have h_ne_zero := (isNumeraire_numeraire P hS).ae_ne_zero
    filter_upwards [h_ne_zero, h_top] with x hx1 hx2
    unfold ENNReal.log
    simp [hx1, hx2]
  · exact (neBotUtilityEVar_numeraire hS).utility_ne_bot

lemma integrable_llr_div_ripr_iff [IsFiniteMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    Integrable (llr P (ripr P S)) P ↔ ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P ≠ ⊤ := by
  rw [integrable_congr (llr_div_ripr' hS h_top)]
  rw [integrable_ereal_toReal_iff (by fun_prop)]
  · have h_bot := (neBotUtilityEVar_numeraire (P := P) hS).utility_ne_bot
    simp only [Function.comp_apply, ne_eq, logUtility] at h_bot
    simp [h_bot]
  · simp only [ne_eq, ENNReal.log_eq_bot_iff]
    exact (isNumeraire_numeraire P hS).ae_ne_zero
  · simpa

lemma maxUtility_eq_KL_ripr [IsFiniteMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    maxUtility P S logUtility = KL P (ripr P S) := by
  have h_ac : P ≪ ripr P S := absolutelyContinuous_ripr_of_ae_ne_top h_top
  rw [maxUtility_eq_integral_numeraire _ hS, KL]
  by_cases h_int : Integrable (llr P (ripr P S)) P
  · simp only [h_ac, h_int, and_self, ↓reduceIte]
    rw [integral_congr_ae (llr_div_ripr hS h_top)]
    rw [integrable_congr (llr_div_ripr' hS h_top)] at h_int
    have h_int' := (integrable_ereal_toReal_iff (by fun_prop) ?_ ?_).mp h_int
    rotate_left
    · simp only [ne_eq, ENNReal.log_eq_bot_iff]
      exact (isNumeraire_numeraire P hS).ae_ne_zero
    · simpa
    rw [eintegral_log_numeraire_eq_integral hS h_top h_int'.2]
  · simp only [h_int, and_false, ↓reduceIte]
    rw [integrable_llr_div_ripr_iff hS h_top] at h_int
    simpa using h_int

/-- A measure `μ` is in the effective set of a set of measures `S` if the expectation under `μ` of
every e-variable for `S` is at most 1. -/
def MemEffectiveSet (S : Set (Measure 𝓧)) (μ : Measure 𝓧) : Prop :=
  ∀ X, IsEVar X S → ∫⁻ ω, X ω ∂μ ≤ 1

lemma MemEffectiveSet.measure_univ_le_one {μ : Measure 𝓧} (hμ : MemEffectiveSet S μ) :
    μ .univ ≤ 1 := by simpa using hμ (fun _ => 1) (isEVar_fun_one S)

lemma MemEffectiveSet.isFiniteMeasure {μ : Measure 𝓧} (hμ : MemEffectiveSet S μ) :
    IsFiniteMeasure μ := ⟨hμ.measure_univ_le_one.trans_lt (by simp)⟩

lemma memEffectiveSet_ripr (P : Measure 𝓧) [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    MemEffectiveSet S (ripr P S) := by
  intro X hX
  unfold ripr
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hX.measurable]
  have h_le := (isNumeraire_numeraire P hS).lintegral_div_le_one hX
  convert h_le with ω
  simp [ENNReal.div_eq_inv_mul]

lemma lintegral_mul_le_of_memEffectiveSet {μ : Measure 𝓧} (hμ : MemEffectiveSet S μ)
    {X : 𝓧 → ℝ≥0∞} (hX : IsEVar X S) :
    ∫⁻ ω, X ω * (μ.rnDeriv P) ω ∂P ≤ 1 := by
  have : IsFiniteMeasure μ := hμ.isFiniteMeasure
  simp_rw [mul_comm (X _)]
  calc ∫⁻ ω, (∂μ/∂P) ω * X ω ∂P
  _ ≤ ∫⁻ ω, X ω ∂μ := lintegral_rnDeriv_mul_le hX.measurable
  _ ≤ 1 := hμ X hX

lemma eintegral_log_mul_nonpos_of_memEffectiveSet [IsProbabilityMeasure P]
    {μ : Measure 𝓧} (hμ : MemEffectiveSet S μ)
    {X : 𝓧 → ℝ≥0∞} (hX : IsEVar X S) :
    ∫ᵉ ω, ENNReal.log (X ω * (μ.rnDeriv P) ω) ∂P ≤ 0 := by
  calc ∫ᵉ ω, ENNReal.log (X ω * (μ.rnDeriv P) ω) ∂P
  _ ≤ ENNReal.log (∫⁻ ω, X ω * (μ.rnDeriv P) ω ∂P) := by
    refine Utility.eintegral_le_map logUtility ?_
    have := hX.measurable
    fun_prop
  _ ≤ 0 := by
    simp only [ENNReal.log_le_zero_iff]
    exact lintegral_mul_le_of_memEffectiveSet hμ hX

lemma llr_ae_eq_log_inv_rnDeriv [IsFiniteMeasure P] {μ : Measure 𝓧} [IsFiniteMeasure μ]
    (h_ac : P ≪ μ) :
    llr P μ =ᵐ[P] fun x ↦ Real.log ((μ.rnDeriv P)⁻¹ x).toReal := by
  filter_upwards [Measure.inv_rnDeriv' h_ac] with a ha using by rw [llr, ha]

lemma eintegrable_klFun_rnDeriv (P μ : Measure 𝓧) :
    eintegrable (fun ω ↦ klFun (μ.rnDeriv P ω).toReal) P := by
  refine eintegrable_of_nonneg ?_
  simp only [EReal.coe_nonneg]
  exact fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg

lemma eintegrable_rnDeriv_mul_log_iff {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) :
    eintegrable (fun a ↦ (μ.rnDeriv ν a).toReal * Real.log (μ.rnDeriv ν a).toReal) ν
      ↔ eintegrable (fun a ↦ llr μ ν a) μ := eintegrable_rnDeriv_mul_iff hμν (by fun_prop)

lemma eintegrable_llr [IsFiniteMeasure P] {μ : Measure 𝓧} [IsFiniteMeasure μ]
    (h_ac : P ≪ μ) :
    eintegrable (fun ω ↦ llr P μ ω) P := by
  rw [← eintegrable_rnDeriv_mul_log_iff h_ac]
  have h_eq a : (((∂P/∂μ) a).toReal * Real.log ((∂P/∂μ) a).toReal : EReal) =
      ((klFun (P.rnDeriv μ a).toReal + (P.rnDeriv μ a).toReal - 1 : ℝ) : EReal) := by
    simp [klFun]
  rw [eintegrable_congr (ae_of_all _ h_eq)]
  have h_int := eintegrable_klFun_rnDeriv μ P
  simp only [EReal.coe_sub, EReal.coe_add, EReal.coe_one]
  simp_rw [sub_eq_add_neg]
  refine eintegrable_add_of_ne_bot (by fun_prop) (by fun_prop) ?_ (by simp)
  refine eintegral_add_ne_bot (by fun_prop) (by fun_prop) ?_ ?_
  · rw [eintegral_of_nonneg]
    · simp
    · simp only [EReal.coe_nonneg]
      exact fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg
  · rw [eintegral_of_nonneg]
    · simp
    · simp

lemma eintegrable_ennreal_log_rnDeriv [IsFiniteMeasure P] {μ : Measure 𝓧} [IsFiniteMeasure μ]
    (h_ac : P ≪ μ) :
    eintegrable (fun ω ↦ ENNReal.log ((μ.rnDeriv P)⁻¹ ω)) P := by
  have h_ae : (fun ω ↦ ENNReal.log ((μ.rnDeriv P)⁻¹ ω)) =ᵐ[P]
      (fun ω ↦ (Real.log ((μ.rnDeriv P)⁻¹ ω).toReal)) := by
    filter_upwards [Measure.rnDeriv_ne_top μ P, Measure.rnDeriv_pos' h_ac] with x hx1 hx2
    simp [ENNReal.log, hx1, hx2.ne']
  rw [eintegrable_congr h_ae]
  have h_ae' : (fun ω ↦ (llr P μ ω : EReal)) =ᵐ[P]
      fun x ↦ (Real.log ((μ.rnDeriv P)⁻¹ x).toReal : EReal) := by
    filter_upwards [llr_ae_eq_log_inv_rnDeriv h_ac] with x hx using by simp [hx]
  rw [eintegrable_congr h_ae'.symm]
  exact eintegrable_llr h_ac

lemma eintegral_log_isEVar_le_eintegral_rnDeriv [IsProbabilityMeasure P]
    {μ : Measure 𝓧} (hμ : MemEffectiveSet S μ) [IsFiniteMeasure μ] (h_ac : P ≪ μ)
    {X : 𝓧 → ℝ≥0∞} (hX : IsEVar X S) :
    ∫ᵉ ω, ENNReal.log (X ω) ∂P ≤ ∫ᵉ ω, ENNReal.log ((μ.rnDeriv P)⁻¹ ω) ∂P := by
  have hX_meas := hX.measurable
  by_cases hX_bot : ∫ᵉ ω, ENNReal.log (X ω) ∂P = ⊥
  · simp [hX_bot]
  by_cases h_top : ∫ᵉ ω, ENNReal.log ((μ.rnDeriv P)⁻¹ ω) ∂P = ⊤
  · simp only [Pi.inv_apply] at h_top
    simp [h_top]
  have hX_int : eintegrable (fun ω ↦ ENNReal.log (X ω)) P := by
    by_contra h_false
    simp [eintegral_of_not_eintegrable h_false] at hX_bot
  have h_int' : eintegrable (fun ω ↦ ENNReal.log ((μ.rnDeriv P)⁻¹ ω)) P :=
    eintegrable_ennreal_log_rnDeriv h_ac
  have h_nonpos := eintegral_log_mul_nonpos_of_memEffectiveSet hμ hX (P := P)
  simp_rw [ENNReal.log_mul_add] at h_nonpos
  have h_eq_sub : ∫ᵉ ω, ENNReal.log (X ω) + ENNReal.log ((∂μ/∂P) ω) ∂P =
      ∫ᵉ ω, ENNReal.log (X ω) - ENNReal.log ((∂μ/∂P)⁻¹ ω) ∂P := by
    congr with ω
    simp only [Pi.inv_apply, ENNReal.log_inv]
    rw [sub_eq_add_neg, neg_neg]
  rw [h_eq_sub, eintegral_sub hX_int (by fun_prop) h_int'] at h_nonpos
  rotate_left
  · simp only [Pi.inv_apply, ENNReal.log_inv]
    fun_prop
  · exact .inr h_top
  · exact .inl hX_bot
  rwa [EReal.sub_nonpos] at h_nonpos

lemma KL_eq_eintegral_log_inv_rnDeriv {μ : Measure 𝓧} [IsFiniteMeasure P] [IsFiniteMeasure μ]
    (h_ac : P ≪ μ) (h_int : Integrable (llr P μ) P) :
    KL P μ = ∫ᵉ x, ENNReal.log ((μ.rnDeriv P)⁻¹ x) ∂P := by
  simp only [KL, h_ac, h_int, and_self, ↓reduceIte]
  rw [integral_congr_ae (llr_ae_eq_log_inv_rnDeriv h_ac)]
  rw [← eintegral_eq_integral]
  swap; · rw [integrable_congr (llr_ae_eq_log_inv_rnDeriv h_ac)] at h_int; simpa using h_int
  refine eintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_ne_top μ P, Measure.rnDeriv_pos' h_ac] with x hx1 hx2
  simp [ENNReal.log, hx1, hx2.ne']

lemma maxUtility_le_KL_of_memEffectiveSet [IsProbabilityMeasure P] (hS : ∀ μ ∈ S, IsFiniteMeasure μ)
    {μ : Measure 𝓧} (hμ : MemEffectiveSet S μ) :
    maxUtility P S logUtility ≤ KL P μ := by
  by_cases h_ac : P ≪ μ
  swap; · simp [KL, h_ac]
  by_cases h_int : Integrable (llr P μ) P
  swap; · simp [KL, h_int]
  have : IsFiniteMeasure μ := hμ.isFiniteMeasure
  rw [KL_eq_eintegral_log_inv_rnDeriv h_ac h_int]
  rw [maxUtility_eq_integral_numeraire _ hS]
  exact eintegral_log_isEVar_le_eintegral_rnDeriv hμ h_ac (isEVar_numeraire P S)

lemma maxUtility_le_iInf_KL_memEffectiveSet [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    maxUtility P S logUtility ≤ ⨅ (μ) (_hμ : MemEffectiveSet S μ), KL P μ := by
  simp only [le_iInf_iff]
  exact fun _ ↦ maxUtility_le_KL_of_memEffectiveSet hS

/-- Duality between maximal logarithmic utility and minimal Kullback-Leibler divergence. -/
lemma maxUtility_eq_iInf_KL_memEffectiveSet [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, IsFiniteMeasure μ) (h_top : ∀ᵐ x ∂P, numeraire P S x ≠ ⊤) :
    maxUtility P S logUtility = ⨅ (μ) (_hμ : MemEffectiveSet S μ), KL P μ := by
  refine le_antisymm (maxUtility_le_iInf_KL_memEffectiveSet hS) ?_
  refine (iInf₂_le (ripr P S) (memEffectiveSet_ripr P hS)).trans_eq ?_
  rw [maxUtility_eq_KL_ripr hS h_top]

end ProbabilityTheory
