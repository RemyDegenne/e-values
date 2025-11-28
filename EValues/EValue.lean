/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Notation
import EValues.Mathlib.ENNReal
import EValues.Mathlib.unitInterval

/-!
# E-variables



## Main definitions

* TODO

## Main statements

* TODO

-/

open scoped ENNReal NNReal ProbabilityTheory

open MeasureTheory ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ : Measure 𝓧} {S : Set (Measure 𝓧)}

namespace MeasureTheory

-- was added to Mathlib. Remove in a future bump.
lemma Measure.integrable_comp_iff
    {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    [NormedAddCommGroup E] {κ : Kernel α β} {μ : Measure α} {f : β → E}
    (h_meas : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    Integrable f (κ ∘ₘ μ)
      ↔ (∀ᵐ x ∂μ, Integrable f (κ x)) ∧ Integrable (fun x ↦ ∫ y, ‖f y‖ ∂κ x) μ := by
  rw [Measure.comp_eq_comp_const_apply, ProbabilityTheory.integrable_comp_iff]
  · simp
  · simpa [Kernel.comp_apply]

/-- The almost everywhere filter with respect to a set of measures, defined as the supremum of the
almost everywhere filters of the measures in the set. -/
def aeSet (S : Set (Measure 𝓧)) : Filter 𝓧 := ⨆ m ∈ S, ae m

lemma mem_aeSet_iff {t : Set 𝓧} : t ∈ aeSet S ↔ ∀ m ∈ S, m tᶜ = 0 := by simp [aeSet, mem_ae_iff]

end MeasureTheory

namespace ProbabilityTheory

/-- A random variable `X` is an e-variable for a set of measures `S` if it is measurable and
its expectation is at most one for all measures in `S`. -/
structure IsEVar (X : 𝓧 → ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  measurable : Measurable X
  lintegral_le_one : ∀ μ ∈ S, ∫⁻ ω, X ω ∂μ ≤ 1

/-- A random variables `X` is an e-variable for a set of measures `S` if it is measurable and
its expectation is at most one for all measures in `S`. -/
structure IsRandEVar (κ : Kernel 𝓧 ℝ≥0∞) (S : Set (Measure 𝓧)) : Prop where
  [markov : IsMarkovKernel κ]
  lintegral_le_one : ∀ μ ∈ S, ∫⁻ ω, ω ∂(κ ∘ₘ μ) ≤ 1

variable {X Y : 𝓧 → ℝ≥0∞} {κ η : Kernel 𝓧 ℝ≥0∞} [IsMarkovKernel κ] {S T : Set (Measure 𝓧)}

/-- A kernel `κ` is a randomized e-variable iff its mean function `x ↦ ∫⁻ y, y ∂κ x` is an
e-variable. -/
lemma isRandEVar_iff_isEVar : IsRandEVar κ S ↔ IsEVar (fun x ↦ ∫⁻ y, y ∂κ x) S := by
  refine ⟨fun h ↦ ⟨by fun_prop, fun μ hμ ↦ ?_⟩, fun h ↦ ⟨fun μ hμ ↦ ?_⟩⟩
  · have h' := h.lintegral_le_one μ hμ
    rwa [Measure.lintegral_bind (by fun_prop)] at h'
    exact measurable_id.aemeasurable
  · rw [Measure.lintegral_bind (by fun_prop)]
    · exact h.lintegral_le_one μ hμ
    · exact measurable_id.aemeasurable

lemma IsEVar.isRandEVar_deterministic (hX : IsEVar X S) :
    IsRandEVar (Kernel.deterministic X hX.measurable) S where
  lintegral_le_one μ hμ := by
    rw [Measure.lintegral_bind (Kernel.measurable _).aemeasurable]
    · simpa using hX.lintegral_le_one μ hμ
    · exact measurable_id.aemeasurable

lemma isEVar_zero : IsEVar 0 S where
  measurable := measurable_const
  lintegral_le_one μ hμ := by simp

lemma isEVar_one (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    IsEVar 1 S where
  measurable := measurable_const
  lintegral_le_one μ hμ := by simp [hS μ hμ]

lemma isEVar_fun_one (S : Set (Measure 𝓧)) (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    IsEVar (fun _ ↦ 1) S := isEVar_one S hS

lemma IsEVar.ae_lt_top (hX : IsEVar X S) {μ : Measure 𝓧} (hμ : μ ∈ S) : ∀ᵐ ω ∂μ, X ω < ⊤ := by
  by_contra h
  suffices ∫⁻ ω, X ω ∂μ = ⊤ by
    have lintegral_le_one := hX.lintegral_le_one μ hμ
    rw [this] at lintegral_le_one
    contradiction
  refine lintegral_eq_top_of_measure_eq_top_ne_zero hX.measurable.aemeasurable ?_
  · unfold Filter.Eventually at h
    simp [MeasureTheory.ae] at h
    suffices {ω | X ω < ⊤}ᶜ = {ω | X ω = ⊤} by
      rwa [← this]
    ext ω
    simp

lemma IsEVar.ae_ne_top (hX : IsEVar X S) {μ : Measure 𝓧} (hμ : μ ∈ S) : ∀ᵐ ω ∂μ, X ω ≠ ⊤ := by
  filter_upwards [hX.ae_lt_top hμ] with ω hω using hω.ne

lemma IsEVar.measurable_fsupport (hX : IsEVar X S) :
    MeasurableSet X.fsupport := by
  suffices MeasurableSet {ω | X ω ≠ ⊤} ∧ MeasurableSet {ω | X ω ≠ 0} from this.1.inter this.2
  constructor
  · rw [← MeasurableSet.compl_iff]
    suffices {ω | X ω ≠ ⊤}ᶜ = {ω | X ω = ⊤} by
      rw [this]
      exact hX.measurable <| measurableSet_singleton ⊤
    ext ω
    simp
  · rw [← MeasurableSet.compl_iff]
    suffices {ω | X ω ≠ 0}ᶜ = {ω | X ω = 0} by
      rw [this]
      exact hX.measurable <| measurableSet_singleton 0
    ext ω
    simp

lemma IsEVar.mono (hY : IsEVar Y S) (hX : Measurable X) (hXY : X ≤ Y) : IsEVar X S where
  measurable := hX
  lintegral_le_one μ hμ := (lintegral_mono hXY).trans (hY.lintegral_le_one μ hμ)

lemma IsRandEVar.mono (hη : IsRandEVar η S) (hκη : κ ≤ η) : IsRandEVar κ S where
  lintegral_le_one μ hμ := by
    refine (lintegral_mono' ?_ le_rfl).trans (hη.lintegral_le_one μ hμ)
    rw [MeasureTheory.Measure.le_iff]
    intro A hA
    rw [μ.bind_apply hA κ.aemeasurable, μ.bind_apply hA η.aemeasurable]
    exact lintegral_mono fun x ↦ hκη x A

lemma IsEVar.anti_set (hST : S ⊆ T) (hX : IsEVar X T) : IsEVar X S where
  measurable := hX.measurable
  lintegral_le_one μ hμ := hX.lintegral_le_one μ (hST hμ)

lemma IsRandEVar.anti_set (hST : S ⊆ T) (hκ : IsRandEVar κ T) : IsRandEVar κ S where
  lintegral_le_one μ hμ := hκ.lintegral_le_one μ (hST hμ)

lemma IsEVar.comp {Y : 𝓨 → ℝ≥0∞} {S : Set (Measure 𝓧)} {φ : 𝓧 → 𝓨}
    (hφ : Measurable φ) (h : IsEVar Y {μ.map φ | μ ∈ S}) :
    IsEVar (Y ∘ φ) S where
  measurable := h.measurable.comp hφ
  lintegral_le_one μ hμ := by
    have h' := h.lintegral_le_one (μ.map φ) ?_
    · rwa [lintegral_map h.measurable hφ] at h'
    · exact ⟨μ, hμ, rfl⟩

lemma IsRandEVar.comp {ξ : Kernel 𝓨 ℝ≥0∞} {S : Set (Measure 𝓧)}
    {κ : Kernel 𝓧 𝓨} [IsMarkovKernel κ] (h : IsRandEVar ξ {κ ∘ₘ μ | μ ∈ S}) :
    IsRandEVar (ξ ∘ₖ κ) S where
  markov := have := h.markov; inferInstance
  lintegral_le_one μ hμ := by
    have h' := h.lintegral_le_one (κ ∘ₘ μ) ⟨μ, hμ, rfl⟩
    rwa [Measure.comp_assoc] at h'

/-- The e-variables for Bernoulli measures with mean at most `δ` are the functions `f` that satisfy
`f x ≤ 1 + u * (x - δ)` for `u ∈ [0, δ⁻¹]`. -/
lemma isEVar_bernoulli_le_iff {δ : ℝ} (hδ_pos : 0 < δ) (hδ : δ ≤ 1)
    (X : ({0, 1} : Set ℝ) → ℝ≥0∞) :
    IsEVar X {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ} ↔
      ∃ (u : ℝ) (_ : 0 ≤ u) (_ : u ≤ δ⁻¹),
        ∀ x, X x ≤ ENNReal.ofReal (1 + u * ((x : ℝ) - δ)) := by
  refine ⟨fun h_evar ↦ ?_, ?_⟩
  · have h_le := h_evar.lintegral_le_one
    simp only [Set.mem_setOf_eq, lintegral_fintype, and_imp] at h_le
    classical
    have h_le_zero := h_le (Measure.dirac ⟨0, by simp⟩) inferInstance
    simp only [integral_dirac, hδ_pos.le, MeasurableSet.singleton, Measure.dirac_apply',
      Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, forall_const] at h_le_zero
    have h_le_delta := h_le ((ENNReal.ofReal (1 - δ)) • Measure.dirac ⟨0, by simp⟩ +
      (ENNReal.ofReal δ) • Measure.dirac ⟨1, by simp⟩) ?_ ?_
    rotate_left
    · constructor
      simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
        smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add (by grind) (by grind)]
      simp
    · rw [integral_add_measure]
      · simp only [integral_smul_measure, integral_dirac, smul_eq_mul, mul_zero, mul_one, zero_add]
        rw [ENNReal.toReal_ofReal hδ_pos.le]
      · by_cases hδ : δ = 1
        · simp [hδ]
        rw [integrable_smul_measure (by simp; grind) (by simp)]
        simp
      · rw [integrable_smul_measure (by simp; grind) (by simp)]
        simp
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      MeasurableSet.singleton, Measure.dirac_apply', Set.indicator_apply, Set.mem_singleton_iff,
      Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at h_le_delta
    simp_rw [mul_add] at h_le_delta
    simp only [mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte] at h_le_delta
    refine ⟨δ⁻¹ * (1 - (X ⟨0, by simp⟩).toReal), ?_, ?_, fun ω ↦ ?_⟩
    · refine mul_nonneg (by positivity) (sub_nonneg.mpr ?_)
      refine ENNReal.toReal_le_of_le_ofReal (by simp) ?_
      simpa
    · conv_rhs => rw [← mul_one δ⁻¹]
      gcongr
      simp
    · have hX_ne_top : X ⟨0, by simp⟩ ≠ ⊤ := ne_top_of_le_ne_top (by simp) h_le_zero
      by_cases hω : ω = ⟨0, by simp⟩
      · simp only [hω, zero_sub, mul_neg]
        by_cases hδ_zero : δ = 0
        · simpa [hδ_zero]
        ring_nf
        rw [mul_inv_cancel₀ hδ_zero]
        ring_nf
        rw [ENNReal.ofReal_toReal hX_ne_top]
      have hω' : ω = ⟨1, by simp⟩ := by grind
      simp only [hω', ge_iff_le]
      have : 0 ≤ 1 - δ := sub_nonneg.mpr hδ
      have : 0 ≤ 1 - (X ⟨0, by simp⟩).toReal := by
        simp only [sub_nonneg]
        exact ENNReal.toReal_le_of_le_ofReal (by simp) (by simpa)
      rw [ENNReal.ofReal_add (by simp) (by positivity)]
      simp only [ENNReal.ofReal_one]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_inv_of_pos hδ_pos, ENNReal.ofReal_sub _ (by simp)]
      simp only [ENNReal.ofReal_one]
      suffices ENNReal.ofReal δ * X ⟨1, by simp⟩
          ≤ ENNReal.ofReal δ
            * (1 + (ENNReal.ofReal δ)⁻¹ * (1 - ENNReal.ofReal (X ⟨0, by simp⟩).toReal)
              * ENNReal.ofReal (1 - δ)) by
        rwa [ENNReal.mul_le_mul_left (by simp [hδ_pos]) (by simp)] at this
      ring_nf
      rw [ENNReal.mul_inv_cancel (by simp [hδ_pos]) (by simp), one_mul, mul_comm (1 - _),
        ENNReal.mul_sub (by simp), mul_one, add_comm, ENNReal.sub_add_eq_add_sub _ (by finiteness),
        ENNReal.ofReal_toReal hX_ne_top]
      swap
      · conv_rhs => rw [← mul_one (ENNReal.ofReal (1 - δ))]
        gcongr
        rwa [ENNReal.ofReal_toReal hX_ne_top]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      simp only [sub_add_cancel, ENNReal.ofReal_one]
      rwa [ENNReal.le_sub_iff_add_le_left, mul_comm (ENNReal.ofReal δ), mul_comm (ENNReal.ofReal _)]
      · finiteness
      · conv_rhs => rw [← mul_one 1]
        gcongr
        simp [hδ_pos.le]
  · rintro ⟨u, hu_nonneg, hu, hX_le⟩
    refine ⟨by fun_prop, fun μ ⟨hμ, hμ'⟩ ↦ ?_⟩
    calc ∫⁻ ω, X ω ∂μ
    _ ≤ ∫⁻ ω, ENNReal.ofReal (1 + u * (ω - δ)) ∂μ := lintegral_mono hX_le
    _ = ENNReal.ofReal (1 + u * (∫ ω, (ω : ℝ) ∂μ - δ)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (by fun_prop)]
      swap
      · filter_upwards [] with ω
        simp only [Pi.zero_apply]
        by_cases hω : ω = ⟨0, by simp⟩
        · simp only [hω, zero_sub, mul_neg, le_add_neg_iff_add_le, zero_add]
          calc u * δ ≤ δ⁻¹ * δ := by gcongr
          _ = 1 := by rw [inv_mul_cancel₀ hδ_pos.ne']
        have hω' : ω = ⟨1, by simp⟩ := by grind
        simp only [hω', ge_iff_le]
        exact add_nonneg (by simp) (mul_nonneg hu_nonneg (sub_nonneg.mpr hδ))
      congr
      rw [integral_add (by fun_prop) (by fun_prop), integral_const_mul]
      simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one, add_right_inj,
        mul_eq_mul_left_iff]
      rw [integral_sub (by fun_prop) (by fun_prop)]
      simp
    _ ≤ 1 := by
      conv_rhs => rw [← ENNReal.ofReal_one, ← add_zero 1]
      gcongr
      refine mul_nonpos_of_nonneg_of_nonpos hu_nonneg ?_
      simpa

end ProbabilityTheory
