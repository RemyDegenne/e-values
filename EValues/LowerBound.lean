/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/

module

public import EValues.Bernoulli

/-!
# Lower bound on e-Rényi and e-Chernoff divergences

This file contains proofs of lower bounds on the e-Rényi and e-Chernoff divergences between sets of
probability measures with bounded expectations.

## Results

* `ProbabilityTheory.erenyiDiv_bounded_eq_erenyiDiv_bernoulli`: The e-Rényi divergence between sets
  of probability measures on the unit interval with bounded expectations is equal to the
  e-Rényi divergence between corresponding sets of Bernoulli distributions.
* `ProbabilityTheory.erenyiDiv_bounded`: A closed-form expression for the e-Rényi divergence
  between sets of probability measures on the unit interval with bounded expectations.
* `ProbabilityTheory.echernoffDiv_bounded`: A closed-form expression for the e-Chernoff divergence
  between sets of probability measures on the unit interval with bounded expectations.
* `ProbabilityTheory.erenyiDiv_ge_of_separated`: A lower bound on the e-Rényi divergence between
  sets of probability measures with bounded expectations w.r.t. a measurable function.
* `ProbabilityTheory.echernoffDiv_ge_of_separated`: A lower bound on the e-Chernoff divergence
  between sets of probability measures with bounded expectations w.r.t. a measurable function.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {α : ℝ≥0∞}

open unitInterval in
lemma erenyiDiv_bounded_eq_erenyiDiv_bernoulli {a b : ℝ} :
    erenyiDiv α {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ a}
        {μ : Measure I | IsProbabilityMeasure μ ∧ b ≤ ∫ x, (x : ℝ) ∂μ}
      = erenyiDiv α {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ a}
        {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ b ≤ ∫ x, (x : ℝ) ∂μ} := by
  set D₁ := {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ a}
  set D₂ := {μ : Measure I | IsProbabilityMeasure μ ∧ b ≤ ∫ x, (x : ℝ) ∂μ}
  set B₁ := {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ a}
  set B₂ := {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ b ≤ ∫ x, (x : ℝ) ∂μ}
  refine le_antisymm ?_ ?_
  · trans erenyiDiv α {μ.map doubleton | μ ∈ B₁} {μ.map doubleton | μ ∈ B₂}
    swap; · exact erenyiDiv_map_le (by fun_prop)
    refine erenyiDiv_anti ?_ ?_
    · rintro _ ⟨μ, hμ, rfl⟩
      refine ⟨?_, ?_⟩
      · have := hμ.1
        exact μ.isProbabilityMeasure_map measurable_doubleton.aemeasurable
      · have := hμ.2
        rw [integral_map (by fun_prop) (by fun_prop)]
        simp_all [doubleton]
    · rintro _ ⟨μ, hμ, rfl⟩
      refine ⟨?_, ?_⟩
      · have := hμ.1
        exact μ.isProbabilityMeasure_map measurable_doubleton.aemeasurable
      · have := hμ.2
        rw [integral_map (by fun_prop) (by fun_prop)]
        simp_all [doubleton]
  · let BerI (p : I) : Measure ({0, 1} : Set ℝ) := Ber (ENNReal.ofReal p)
    have BerI_is_prob p : IsProbabilityMeasure (BerI p) := by unfold BerI; infer_instance
    let κ : Kernel I ({0, 1} : Set ℝ) := ⟨BerI, by unfold BerI Ber; fun_prop⟩
    have : IsMarkovKernel κ := ⟨BerI_is_prob⟩
    have κ_comp (μ : Measure ({0, 1} : Set ℝ)) (hμ : IsProbabilityMeasure μ) :
        κ ∘ₘ (μ.map doubleton) = μ := by
      refine Measure.ext_of_singleton fun x ↦ ?_
      rw [Measure.bind_apply (measurableSet_singleton _) (by fun_prop),
        lintegral_map (κ.measurable_coe (MeasurableSet.singleton _)) (by fun_prop)]
      by_cases hx0 : x = ⟨0, by simp⟩
      · rw [hx0]
        simp [doubleton, κ, BerI, doubleton_lintegral]
      · have hx1 : x = ⟨1, by simp⟩ := by grind
        rw [hx1]
        simp [doubleton, κ, BerI, doubleton_lintegral]
    have B₁_eq_κ_comp : B₁ = {κ ∘ₘ μ | μ ∈ D₁} := by
      ext μ
      constructor
      · rintro ⟨hμ_prob, hμ_int⟩
        refine ⟨μ.map doubleton, ?_, κ_comp μ hμ_prob⟩
        · refine ⟨μ.isProbabilityMeasure_map measurable_doubleton.aemeasurable, ?_⟩
          rw [integral_map (by fun_prop) (by fun_prop)]
          simpa [doubleton]
      · rintro ⟨ν, hν, rfl⟩
        refine ⟨?_, ?_⟩
        · have := hν.1
          infer_instance
        · obtain ⟨hν_prob, hν⟩ := hν
          rw [integral_eq_lintegral_of_nonneg_ae _ (by fun_prop)] at ⊢ hν
          · rw [Measure.lintegral_bind (by fun_prop) (by fun_prop)]
            refine le_trans ?_ hν
            gcongr with b
            · apply ne_of_lt
              calc
              _ ≤ ∫⁻ x, 1 ∂ν := by
                refine lintegral_mono fun x ↦ ?_
                simp only [ENNReal.ofReal_le_one]
                unit_interval
              _ = (1 : ℝ≥0∞) := by simp
              _ < ⊤ := by simp
            · rw [doubleton_lintegral]
              simp only [Kernel.coe_mk, ber_apply_singleton_zero, ENNReal.ofReal_zero, mul_zero,
                ber_apply_singleton_one, ENNReal.ofReal_one, mul_one, zero_add, tsub_le_iff_right,
                κ, BerI]
              rw [add_comm, ENNReal.sub_add_eq_add_sub _ (by simp),
                ENNReal.add_sub_cancel_right (by simp)]
              simp only [ENNReal.ofReal_le_one]
              unit_interval
          · filter_upwards with x
            simp only [Pi.zero_apply]
            grind
          · filter_upwards with x using by unit_interval
    rw [B₁_eq_κ_comp]
    have B₂_eq_κ_comp : B₂ = {κ ∘ₘ μ | μ ∈ D₂} := by
      ext μ
      constructor
      · rintro ⟨hμ_prob, hμ_int⟩
        refine ⟨μ.map doubleton, ?_, κ_comp μ hμ_prob⟩
        · refine ⟨μ.isProbabilityMeasure_map measurable_doubleton.aemeasurable, ?_⟩
          rw [integral_map (by fun_prop) (by fun_prop)]
          simp_all [doubleton]
      · rintro ⟨ν, hν, rfl⟩
        refine ⟨?_, ?_⟩
        · have := hν.1
          infer_instance
        · obtain ⟨hν_prob, hν⟩ := hν
          rw [integral_eq_lintegral_of_nonneg_ae _ (by fun_prop)] at ⊢ hν
          · rw [Measure.lintegral_bind (by fun_prop) (by fun_prop)]
            refine hν.trans ?_
            gcongr with b
            · apply ne_of_lt
              calc
              _ ≤ ∫⁻ x, ∫⁻ y, 1 ∂(κ x) ∂ν := by
                refine lintegral_mono fun x ↦ lintegral_mono fun y ↦ ?_
                rw [ENNReal.ofReal_le_one]
                grind
              _ = (1 : ℝ≥0∞) := by simp
              _ < ⊤ := by simp
            · simp only [Kernel.coe_mk, lintegral_ber, ENNReal.ofReal_zero, mul_zero,
                ENNReal.ofReal_one, mul_one, zero_add, κ, BerI]
              rw [ENNReal.sub_sub_cancel (by simp)]
              simp only [ENNReal.ofReal_le_one]
              unit_interval
          · filter_upwards with x
            simp only [Pi.zero_apply]
            grind
          · filter_upwards with x using by unit_interval
    rw [B₂_eq_κ_comp]
    exact erenyiDiv_comp_le κ

open unitInterval in
lemma erenyiDiv_bounded {δ : ℝ} (hδ_pos : 0 < δ) (hδ : δ ≤ 2⁻¹) :
    erenyiDiv 2⁻¹ {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ}
        {μ : Measure I | IsProbabilityMeasure μ ∧ 1 - δ ≤ ∫ x, (x : ℝ) ∂μ} =
      ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ)))) := by
  rw [erenyiDiv_bounded_eq_erenyiDiv_bernoulli, erenyiDiv_bernoulli hδ_pos hδ]

open unitInterval in
lemma echernoffDiv_bounded {δ : ℝ} (hδ_pos : 0 < δ) (hδ : δ ≤ 2⁻¹) :
    echernoffDiv {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ}
        {μ : Measure I | IsProbabilityMeasure μ ∧ 1 - δ ≤ ∫ x, (x : ℝ) ∂μ} =
      2⁻¹ * ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ)))) := by
  let φ : I → I := fun x ↦ ⟨1 - x.1, by grind⟩
  have hφ_inv : φ ∘ φ = id := by ext; simp [φ]
  rw [← erenyiDiv_bounded hδ_pos hδ,
    erenyiDiv_eq_two_mul_echernoffDiv_of_involutive (by fun_prop) hφ_inv,
    ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
  ext μ
  simp only [Set.mem_setOf_eq]
  have h_int (μ : Measure I) [IsFiniteMeasure μ] : Integrable (Subtype.val : I → ℝ) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_of_nonneg (by unit_interval)]
    unit_interval
  constructor
  · rintro ⟨ν, ⟨⟨hν, h_int⟩, rfl⟩⟩
    refine ⟨Measure.isProbabilityMeasure_map (by fun_prop), ?_⟩
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp only [φ]
    rw [integral_sub (by fun_prop) (by fun_prop)]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    linarith
  · rintro ⟨hμ, h_int⟩
    refine ⟨μ.map φ, ⟨Measure.isProbabilityMeasure_map (by fun_prop), ?_⟩, ?_⟩
    · rw [integral_map (by fun_prop) (by fun_prop)]
      simp only [φ]
      rw [integral_sub (by fun_prop) (by fun_prop)]
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
      linarith
    · rw [Measure.map_map (by fun_prop) (by fun_prop), hφ_inv, Measure.map_id]

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S T : Set (Measure 𝓧)}

open unitInterval in
theorem erenyiDiv_ge_of_separated {f : 𝓧 → I} (hf : Measurable f)
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, IsProbabilityMeasure μ)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ : δ ≤ 2⁻¹)
    (hSf : ∀ μ ∈ S, ∫ ω, (f ω : ℝ) ∂μ ≤ δ) (hTf : ∀ ν ∈ T, 1 - δ ≤ ∫ ω, (f ω : ℝ) ∂ν) :
    ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ)))) ≤ erenyiDiv 2⁻¹ S T :=
  calc ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ))))
  _ = erenyiDiv 2⁻¹ {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ}
        {μ : Measure I | IsProbabilityMeasure μ ∧ 1 - δ ≤ ∫ x, (x : ℝ) ∂μ} := by
    rw [← erenyiDiv_bounded hδ_pos hδ]
  _ ≤ erenyiDiv 2⁻¹ {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} := by
    refine erenyiDiv_anti ?_ ?_
    · rintro μ ⟨ν, hνS, rfl⟩
      constructor
      · have := hS ν hνS
        exact Measure.isProbabilityMeasure_map (hf.aemeasurable)
      rw [integral_map (hf.aemeasurable) (by fun_prop)]
      exact hSf ν hνS
    · rintro μ ⟨ν, hνT, rfl⟩
      constructor
      · have := hT ν hνT
        exact Measure.isProbabilityMeasure_map (hf.aemeasurable)
      rw [integral_map (hf.aemeasurable) (by fun_prop)]
      exact hTf ν hνT
  _ ≤ erenyiDiv 2⁻¹ S T := erenyiDiv_map_le hf

open unitInterval in
theorem echernoffDiv_ge_of_separated {f : 𝓧 → I} (hf : Measurable f)
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, IsProbabilityMeasure μ)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ : δ ≤ 2⁻¹)
    (hSf : ∀ μ ∈ S, ∫ ω, (f ω : ℝ) ∂μ ≤ δ) (hTf : ∀ ν ∈ T, 1 - δ ≤ ∫ ω, (f ω : ℝ) ∂ν) :
    2⁻¹ * ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ)))) ≤ echernoffDiv S T :=
  calc 2⁻¹ * ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ))))
  _ = echernoffDiv {μ : Measure I | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ}
        {μ : Measure I | IsProbabilityMeasure μ ∧ 1 - δ ≤ ∫ x, (x : ℝ) ∂μ} := by
    rw [← echernoffDiv_bounded hδ_pos hδ]
  _ ≤ echernoffDiv {μ.map f | μ ∈ S} {μ.map f | μ ∈ T} := by
    refine echernoffDiv_anti ?_ ?_
    · rintro μ ⟨ν, hνS, rfl⟩
      constructor
      · have := hS ν hνS
        exact Measure.isProbabilityMeasure_map (hf.aemeasurable)
      rw [integral_map (hf.aemeasurable) (by fun_prop)]
      exact hSf ν hνS
    · rintro μ ⟨ν, hνT, rfl⟩
      constructor
      · have := hT ν hνT
        exact Measure.isProbabilityMeasure_map (hf.aemeasurable)
      rw [integral_map (hf.aemeasurable) (by fun_prop)]
      exact hTf ν hνT
  _ ≤ echernoffDiv S T := echernoffDiv_map_le hf

end ProbabilityTheory
