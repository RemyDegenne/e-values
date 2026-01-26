/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import EValues.DPI

/-!
# Numeraire of a product

-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {P : Measure 𝓧} [IsProbabilityMeasure P] {Q : Measure 𝓨} [IsProbabilityMeasure Q]
  {S : Set (Measure 𝓧)} {T : Set (Measure 𝓨)}

/-- The product of the two e-variables is an e-variable for the product measure
  with respect to the product of the two sets. -/
lemma IsEVar.prod {T : Set (Measure 𝓨)} (hT : ∀ μ ∈ T, SFinite μ)
    {X : 𝓧 → ℝ≥0∞} {Y : 𝓨 → ℝ≥0∞} (hX : IsEVar X S) (hY : IsEVar Y T) :
    IsEVar (fun (x : 𝓧 × 𝓨) ↦ X x.1 * Y x.2) (Measure.prod.uncurry '' (S ×ˢ T)) where
  measurable := by
    have hX_meas := hX.measurable
    have hY_meas := hY.measurable
    fun_prop
  lintegral_le_one := by
    have hX_meas := hX.measurable
    have hY_meas := hY.measurable
    rintro _ ⟨⟨μ, ν⟩, hμS, _, rfl⟩
    obtain ⟨hμS, hνT⟩ := Set.mem_prod.mp hμS
    specialize hT ν hνT
    have : Measure.prod.uncurry (μ, ν) = μ.prod ν := by rfl
    rw [this, lintegral_prod_mul (by fun_prop) (by fun_prop)]
    grw [hX.lintegral_le_one μ hμS, hY.lintegral_le_one ν hνT]
    rw [Measure.prod_apply .univ, mul_comm]
    simp

/-- The numeraire of a product measure with respect to a product of sets is the product
of the numeraires. -/
theorem isNumeraire_mul
    (P : Measure 𝓧) [IsFiniteMeasure P] (Q : Measure 𝓨) [IsFiniteMeasure Q]
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, SFinite μ)
    {X : 𝓧 → ℝ≥0∞} {Y : 𝓨 → ℝ≥0∞} (hX : IsNumeraire X S P) (hY : IsNumeraire Y T Q) :
    IsNumeraire (fun (x : 𝓧 × 𝓨) ↦ X x.1 * Y x.2)
      {ρ | ∃ μ ∈ S, ∃ ν ∈ T, μ.prod ν = ρ} (P.prod Q) := by
  have hX_meas := hX.measurable
  have hY_meas := hY.measurable
  refine ⟨⟨?_, ?_⟩, fun Z hZ_evar ↦ ?_⟩
  · fun_prop
  · rintro _ ⟨μ, hμS, ν, hνT, rfl⟩
    specialize hS μ hμS
    specialize hT ν hνT
    rw [lintegral_prod_mul (by fun_prop) (by fun_prop)]
    grw [hX.toIsEVar.lintegral_le_one μ hμS, hY.toIsEVar.lintegral_le_one ν hνT]
    rw [Measure.prod_apply .univ, mul_comm]
    simp
  · have hZ_meas := hZ_evar.measurable
    rw [lintegral_prod _ (by fun_prop)]
    simp_rw [mul_comm (X _)]
    have h_eq : ∫⁻ x, ∫⁻ y, Z (x, y) / (Y y * X x) ∂Q ∂P
        = ∫⁻ x, (∫⁻ y, Z (x, y) / Y y ∂Q) / X x ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hX.ae_ne_zero] with x hx
      simp_rw [div_eq_mul_inv]
      rw [← lintegral_mul_const _ (by fun_prop)]
      refine lintegral_congr_ae ?_
      filter_upwards [hY.ae_ne_zero] with y hy
      rw [ENNReal.mul_inv (.inl hy) (.inr hx), mul_assoc]
    have h_fsupport_mul : (fun x ↦ Y x.2 * X x.1).fsupport = X.fsupport ×ˢ Y.fsupport := by
      ext x
      constructor
      · simp only [Set.mem_inter_iff, ne_eq, Set.mem_setOf_eq, mul_eq_zero, not_or, Set.mem_prod,
          and_imp]
        intro h_mul_top hY_zero hX_zero
        rw [← ne_eq] at h_mul_top
        replace h_mul_top : Y x.2 * X x.1 < ⊤ := h_mul_top.symm.lt_top'
        rw [ENNReal.mul_lt_top_iff] at h_mul_top
        refine ⟨⟨?_, hX_zero⟩, ⟨?_, hY_zero⟩⟩
        · rcases h_mul_top with h_top | hX_zero | hY_zero
          · exact h_top.2.ne
          · contradiction
          · contradiction
        · rcases h_mul_top with h_top | hX_zero | hY_zero
          · exact h_top.1.ne
          · contradiction
          · contradiction
      · simp only [Set.mem_prod, Set.mem_inter_iff, ne_eq, Set.mem_setOf_eq, mul_eq_zero, not_or,
          and_imp]
        intro hX_top hX_zero hY_top hY_zero
        simp_all only [not_false_eq_true, and_self, and_true]
        exact ENNReal.mul_ne_top hY_top hX_top
    rw [h_eq, h_fsupport_mul, P.prod_prod]
    by_cases hY_top : Y =ᵐ[Q] fun _ ↦ ∞
    · have hQY : Q Y.fsupport = 0 := measure_fsupport_eq_zero_of_ae_eq_top hY_top
      refine le_of_eq ?_
      calc ∫⁻ x, (∫⁻ y, Z (x, y) / Y y ∂Q) / X x ∂P
      _ = ∫⁻ x, 0 / X x ∂P := by
        congr with x
        congr
        refine lintegral_eq_zero_of_ae_eq_zero ?_
        filter_upwards [hY_top] with y hy
        simp [hy]
      _ = 0 := by simp
      _ = P X.fsupport * Q Y.fsupport := by simp [hQY]
    suffices IsEVar (fun x ↦ (Q Y.fsupport)⁻¹ * ∫⁻ y, Z (x, y) / Y y ∂Q) S by
      have h_le := hX.lintegral_div_le_measure_fsupport this
      simp_rw [mul_div_assoc] at h_le
      rw [lintegral_const_mul _ (by fun_prop), ENNReal.inv_mul_le_iff _ (by simp), mul_comm] at h_le
      swap; · simpa [hY_top] using hY.measure_fsupport_ne_zero_or_ae_top
      exact h_le
    refine ⟨by fun_prop, ?_⟩
    intro μ hμS
    have := hS μ hμS
    suffices IsEVar (fun y ↦ ∫⁻ x, Z (x, y) ∂μ) T by
      have hY' := hY.lintegral_div_le_measure_fsupport this
      rw [lintegral_const_mul _ (by fun_prop), ENNReal.inv_mul_le_iff _ (by simp)]
      swap; · simpa [hY_top] using hY.measure_fsupport_ne_zero_or_ae_top
      simp only [measure_univ, mul_one]
      refine le_trans (le_of_eq ?_) hY'
      rw [lintegral_lintegral_swap (by fun_prop)]
      congr with y
      simp_rw [div_eq_mul_inv]
      rw [lintegral_mul_const _ (by fun_prop)]
    refine ⟨by fun_prop, ?_⟩
    intro ν hνT
    have := hT ν hνT
    rw [lintegral_lintegral_symm (by fun_prop)]
    refine (hZ_evar.lintegral_le_one (μ.prod ν) ⟨μ, hμS, ν, hνT, rfl⟩).trans ?_
    rw [Measure.prod_apply .univ]
    simp

/-- The numeraire of a product measure with respect to a product of sets is the product
of the numeraires. -/
theorem isNumeraire_mul_numeraire
    (P : Measure 𝓧) [IsProbabilityMeasure P] (Q : Measure 𝓨) [IsProbabilityMeasure Q]
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) (hT : ∀ μ ∈ T, SFinite μ) :
    IsNumeraire (fun (x : 𝓧 × 𝓨) ↦ numeraire P S x.1 * numeraire Q T x.2)
      {ρ | ∃ μ ∈ S, ∃ ν ∈ T, μ.prod ν = ρ} (P.prod Q) :=
  isNumeraire_mul P Q hS hT (isNumeraire_numeraire P) (isNumeraire_numeraire Q)

/-- The logarithmic utility of the numeraire on a product is the sum of the two logarithmic
utilities. -/
theorem logUtility_numeraire_prod (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    (hT : ∀ μ ∈ T, SFinite μ) :
    ∫ᵉ x, ENNReal.log (numeraire (P.prod Q) (Measure.prod.uncurry '' (S ×ˢ T)) x) ∂(P.prod Q)
      = ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P + ∫ᵉ x, ENNReal.log (numeraire Q T x) ∂Q := by
  have h_int1 : eintegrable (fun p ↦ (numeraire P S p.1).log) (P.prod Q) := by
    have hP : eintegrable (fun x ↦ ENNReal.log (numeraire P S x)) P :=
      (isNumeraire_numeraire P).eintegrable_log
    change eintegrable ((fun p ↦ (numeraire P S p).log) ∘ Prod.fst) (P.prod Q)
    rw [← eintegrable_map (by fun_prop) (by fun_prop)]
    simpa
  have h_int2 : eintegrable (fun p ↦ (numeraire Q T p.2).log) (P.prod Q) := by
    have hQ : eintegrable (fun y ↦ ENNReal.log (numeraire Q T y)) Q :=
      (isNumeraire_numeraire Q).eintegrable_log
    change eintegrable ((fun p ↦ (numeraire Q T p).log) ∘ Prod.snd) (P.prod Q)
    rw [← eintegrable_map (by fun_prop) (by fun_prop)]
    simpa
  have h_ae_eq : numeraire (P.prod Q) (Measure.prod.uncurry '' (S ×ˢ T))
      =ᵐ[P.prod Q] (fun x ↦ numeraire P S x.1 * numeraire Q T x.2) := by
    symm
    convert (isNumeraire_mul_numeraire P Q hS hT).ae_eq_numeraire
    ext
    simp
  calc ∫ᵉ p, ENNReal.log (numeraire (P.prod Q) (Function.uncurry Measure.prod '' S ×ˢ T) p)
      ∂P.prod Q
  _ = ∫ᵉ p, ENNReal.log (numeraire P S p.1 * numeraire Q T p.2) ∂P.prod Q := by
    refine eintegral_congr_ae ?_
    filter_upwards [h_ae_eq] with p hp
    rw [hp]
  _ = ∫ᵉ p, ENNReal.log (numeraire P S p.1) ∂P.prod Q +
      ∫ᵉ p, ENNReal.log (numeraire Q T p.2) ∂P.prod Q := by
    simp_rw [ENNReal.log_mul_add]
    rw [eintegral_add]
    · fun_prop
    · fun_prop
    · exact h_int1
    · exact h_int2
    · refine .inl (EReal.ne_bot_of_nonneg ?_)
      have : ∫ᵉ (x : 𝓧 × 𝓨), (numeraire P S x.1).log ∂P.prod Q
          = ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P := by
        rw [← eintegral_map (f := fun x ↦ (numeraire P S x).log) (by fun_prop) measurable_fst]
        simp
      rw [this]
      exact (isNumeraire_numeraire P).eintegral_log_nonneg
    · refine .inr (EReal.ne_bot_of_nonneg ?_)
      have : ∫ᵉ (y : 𝓧 × 𝓨), (numeraire Q T y.2).log ∂P.prod Q
          = ∫ᵉ y, ENNReal.log (numeraire Q T y) ∂Q := by
        rw [← eintegral_map (f := fun x ↦ (numeraire Q T x).log) (by fun_prop) measurable_snd]
        simp
      rw [this]
      exact (isNumeraire_numeraire Q).eintegral_log_nonneg
  _ = ∫ᵉ x, ENNReal.log (numeraire P S x) ∂P + ∫ᵉ y, ENNReal.log (numeraire Q T y) ∂Q := by
    rw [eintegral_prod _ (by fun_prop), eintegral_prod_symm _ (by fun_prop)]
    · simp
    · exact h_int2
    · exact h_int1

lemma maxUtility_prod (P : Measure 𝓧) (Q : Measure 𝓨) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {T : Set (Measure 𝓨)}
    (hS : ∀ μ ∈ S, IsProbabilityMeasure μ)
    (hT : ∀ μ ∈ T, SFinite μ) :
    maxUtility (P.prod Q) (Measure.prod.uncurry '' (S ×ˢ T)) logUtility =
      maxUtility P S logUtility + maxUtility Q T logUtility := by
  rw [maxUtility_eq_integral_numeraire (P.prod Q),
    maxUtility_eq_integral_numeraire, maxUtility_eq_integral_numeraire]
  exact logUtility_numeraire_prod hS hT

lemma iSup_prod_le_maxUtility (P : Measure (𝓧 × 𝓨)) {T : Set (Measure 𝓨)}
    (hT : ∀ μ ∈ T, IsProbabilityMeasure μ) :
    ⨆ (X : 𝓧 → ℝ≥0∞) (Y : 𝓨 → ℝ≥0∞) (_ : IsEVar X S) (_ : IsEVar Y T),
      ∫ᵉ x, (logUtility ∘ (fun x ↦ X x.1 * Y x.2)) x ∂P ≤
      maxUtility P (Measure.prod.uncurry '' (S ×ˢ T)) logUtility := by
  unfold maxUtility
  rw [iSup₂_eq_sSup, iSup₄_eq_sSup]
  refine sSup_le_sSup fun z ↦ ?_
  rintro ⟨X, Y, hX, hY, rfl⟩
  exact ⟨fun x ↦ X x.1 * Y x.2, hX.prod (fun μ hμ ↦ by specialize hT μ hμ; infer_instance) hY, rfl⟩

lemma isNumeraire_prod_numeraire_fintype {ι : Type*} {𝓧 : ι → Type*} [hι : Fintype ι]
    {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} {P : (i : ι) → Measure (𝓧 i)}
    {S : (i : ι) → Set (Measure (𝓧 i))} [∀ i, IsProbabilityMeasure (P i)]
    (hS : ∀ i, ∀ μ ∈ S i, IsProbabilityMeasure μ) :
    IsNumeraire (fun x ↦ ∏ i, numeraire (P i) (S i) (x i))
      (Measure.pi '' (Set.pi Set.univ S)) (Measure.pi P) := by
  sorry

lemma isNumeraire_prod_numeraire_finset {ι : Type*} {𝓧 : ι → Type*} {s : Finset ι}
    {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} {P : (i : ι) → Measure (𝓧 i)}
    {S : (i : ι) → Set (Measure (𝓧 i))} [∀ i, IsProbabilityMeasure (P i)]
    (hS : ∀ i ∈ s, ∀ μ ∈ S i, IsProbabilityMeasure μ) :
    IsNumeraire (fun x ↦ ∏ i : s, numeraire (P i) (S i) (x i))
      {μ | ∃ ν : (i : ι) → Measure (𝓧 i), (∀ i ∈ s, ν i ∈ S i) ∧ Measure.pi (fun i : s ↦ ν i) = μ}
      (Measure.pi (fun i : s ↦ P i)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    sorry
  | insert a s has hs =>
    sorry

end ProbabilityTheory
