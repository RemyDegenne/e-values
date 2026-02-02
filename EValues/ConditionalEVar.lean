/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import EValues.EValue

/-!
# Conditional E-variables

EXPERIMENTAL FILE.


## Main definitions

* TODO

## Main statements

* TODO

-/

open scoped ENNReal NNReal ProbabilityTheory

open MeasureTheory ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
    {X : 𝓧 → ℝ≥0∞} {Y : 𝓧 × 𝓨 → ℝ≥0∞} {S : Set (Measure 𝓧)} {T : Set (Kernel 𝓧 𝓨)}

namespace ProbabilityTheory

-- todo: ≤ κ x .univ ?
structure Kernel.IsEVar (Y : 𝓧 × 𝓨 → ℝ≥0∞) (T : Set (Kernel 𝓧 𝓨)) (S : Set (Measure 𝓧)) :
    Prop where
  measurable : Measurable Y := by fun_prop
  lintegral_le_one : ∀ μ ∈ S, ∀ᵐ x ∂μ, ∀ κ ∈ T, ∫⁻ ω, Y (x, ω) ∂(κ x) ≤ 1

structure Kernel.IsRandEVar (η : Kernel 𝓨 ℝ≥0∞) (T : Set (Kernel 𝓧 𝓨))
    (S : Set (Measure 𝓧)) : Prop where
  [markov : IsMarkovKernel η]
  lintegral_le_one : ∀ μ ∈ S, ∀ᵐ x ∂μ, ∀ κ ∈ T, ∫⁻ ω, ω ∂(η ∘ₘ κ x) ≤ 1

lemma isEvar_mul_of_kernel_isEvar
    (hS : ∀ μ ∈ S, SFinite μ) (hT : ∀ κ ∈ T, IsMarkovKernel κ)
    (hX : ProbabilityTheory.IsEVar X S) (hY : Kernel.IsEVar Y T S) :
    IsEVar (fun p ↦ X p.1 * Y p) {η : Measure (𝓧 × 𝓨) | ∃ μ ∈ S, ∃ κ ∈ T, η = μ ⊗ₘ κ} where
  measurable := by
    have hX_meas := hX.measurable
    have hY_meas := hY.measurable
    fun_prop
  lintegral_le_measure_univ := by
    rintro ρ ⟨μ, hμ, κ, hκ, rfl⟩
    have hX_meas := hX.measurable
    have hY_meas := hY.measurable
    specialize hS μ hμ
    specialize hT κ hκ
    rw [Measure.lintegral_compProd (by fun_prop)]
    calc ∫⁻ a, ∫⁻ b, X a * Y (a, b) ∂κ a ∂μ
    _ = ∫⁻ a, X a * ∫⁻ b, Y (a, b) ∂κ a ∂μ := by
      congr with a
      rw [lintegral_const_mul _ (by fun_prop)]
    _ ≤ ∫⁻ a, X a ∂μ := by
      refine lintegral_mono_ae ?_
      filter_upwards [hY.lintegral_le_one μ hμ] with a ha
      specialize ha κ hκ
      grw [ha]
      simp
    _ ≤ μ .univ := hX.lintegral_le_measure_univ μ hμ
    _ ≤ _ := by simp [Measure.compProd_apply .univ]

def todo (μ : Measure 𝓧) (E : Set (𝓧 → ℝ≥0∞)) : Prop := ∀ f ∈ E, ∫⁻ x, f x ∂μ ≤ 1

def Kernel.todo (κ : Kernel 𝓧 𝓨) (μ : Measure 𝓧) (E : Set (𝓧 × 𝓨 → ℝ≥0∞)) : Prop :=
    ∀ᵐ x ∂μ, ∀ g ∈ E, ∫⁻ y, g (x, y) ∂(κ x) ≤ 1

-- example: sub-Gaussian is the case of E = {x ↦ exp(t x - t^2 σ^2 / 2) | t ∈ ℝ}
-- in the kernel sub-Gaussian def, `g` depends only on `y`, not on `(x, y)`

lemma todo_compProd_mul {μ : Measure 𝓧} [SFinite μ] {κ : Kernel 𝓧 𝓨} [IsSFiniteKernel κ]
    {E : Set (𝓧 → ℝ≥0∞)} {F : Set (𝓧 × 𝓨 → ℝ≥0∞)}
    (hE : ∀ f ∈ E, Measurable f) (hF : ∀ g ∈ F, Measurable g)
    (hμ : todo μ E) (hκμ : Kernel.todo κ μ F) :
    todo (μ ⊗ₘ κ) {f' : 𝓧 × 𝓨 → ℝ≥0∞ | ∃ f ∈ E, ∃ g ∈ F, f' = fun p ↦ f p.1 * g p} := by
  rintro _ ⟨f, hf, g, hg, rfl⟩
  rw [Measure.lintegral_compProd]
  swap; · specialize hE f hf; specialize hF g hg; fun_prop
  simp only
  calc ∫⁻ a, ∫⁻ b, f a * g (a, b) ∂κ a ∂μ
  _ = ∫⁻ a, f a * ∫⁻ b, g (a, b) ∂κ a ∂μ := by
    congr with a
    rw [lintegral_const_mul]
    specialize hF g hg
    fun_prop
  _ ≤ ∫⁻ a, f a ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hκμ] with a ha
    specialize ha g hg
    grw [ha]
    simp
  _ ≤ 1 := hμ f hf

end ProbabilityTheory
