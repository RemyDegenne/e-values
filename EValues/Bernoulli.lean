/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Gaëtan Serré
-/
import EValues.ERenyi

/-!
# Maximum utility and Bernoulli distributions

-/

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {p α : ℝ≥0∞}

/-- Bernoulli distribution on `{0, 1}`.
Using `1 - (1 - p)` ensures that we always have a probability measure. -/
noncomputable
def Ber (p : ℝ≥0∞) : Measure ({0, 1} : Set ℝ) :=
  (1 - p) • Measure.dirac ⟨0, by simp⟩ + (1 - (1 - p)) • Measure.dirac ⟨1, by simp⟩

@[simp] lemma ber_zero : Ber 0 = Measure.dirac ⟨0, by simp⟩ := by simp [Ber]
@[simp] lemma ber_one : Ber 1 = Measure.dirac ⟨1, by simp⟩ := by simp [Ber]

@[simp] lemma ber_apply_singleton_zero : Ber p {⟨0, by simp⟩} = 1 - p := by simp [Ber]
@[simp] lemma ber_apply_singleton_one : Ber p {⟨1, by simp⟩} = 1 - (1 - p) := by simp [Ber]

@[simp]
lemma lintegral_ber {f : ({0, 1} : Set ℝ) → ℝ≥0∞} :
    ∫⁻ x, f x ∂(Ber p) = (1 - p) * f ⟨0, by simp⟩ + (1 - (1 - p)) * f ⟨1, by simp⟩ := by
  simp [Ber]

instance : IsProbabilityMeasure (Ber p) := ⟨by simp [Ber]⟩

lemma apply_zero_add_apply_one_eq_one (R : Measure ({0, 1} : Set ℝ)) [IsProbabilityMeasure R] :
    R {⟨0, by simp⟩} + R {⟨1, by simp⟩} = 1 := by
  have h_univ : R Set.univ = 1 := measure_univ
  rw [measure_doubleton_eq_add R] at h_univ
  simpa using h_univ

@[simp]
lemma one_sub_apply_one (R : Measure ({0, 1} : Set ℝ)) [IsProbabilityMeasure R] :
    1 - R {⟨1, by simp⟩} = R {⟨0, by simp⟩} := by
  have h_add := apply_zero_add_apply_one_eq_one R
  symm
  exact ENNReal.eq_sub_of_add_eq (by simp) h_add

@[simp]
lemma one_sub_apply_zero (R : Measure ({0, 1} : Set ℝ)) [IsProbabilityMeasure R] :
    1 - R {⟨0, by simp⟩} = R {⟨1, by simp⟩}  := by
  have h_add := apply_zero_add_apply_one_eq_one R
  rw [add_comm] at h_add
  symm
  exact ENNReal.eq_sub_of_add_eq (by simp) h_add

@[simp]
lemma one_sub_one_sub_measure_apply (R : Measure ({0, 1} : Set ℝ)) [IsProbabilityMeasure R]
    (s : Set ({0, 1} : Set ℝ)) :
    1 - (1 - R s) = R s := by
  rw [ENNReal.sub_sub_cancel (by simp) prob_le_one]

lemma eq_ber_lintegral (R : Measure ({0, 1} : Set ℝ)) [IsProbabilityMeasure R] :
    R = Ber (∫⁻ x, ENNReal.ofReal x ∂R) := by
  have hR_eq : R = R {⟨0, by simp⟩} • Measure.dirac ⟨0, by simp⟩ +
      R {⟨1, by simp⟩} • Measure.dirac ⟨1, by simp⟩ := measure_doubleton_eq_add R
  rw [hR_eq]
  refine Measure.ext_of_singleton fun x ↦ ?_
  by_cases hx0 : x = ⟨0, by simp⟩
  · simp [hx0]
  · have hx1 : x = ⟨1, by simp⟩ := by grind
    simp [hx1]

/-- The e-variables for Bernoulli measures with mean at most `δ` are the functions `f` that satisfy
`f x ≤ 1 + u * (x - δ)` for `u ∈ [0, δ⁻¹]`. -/
lemma isEVar_bernoulli_le_iff {δ : ℝ} (hδ_pos : 0 < δ) (hδ : δ ≤ 1)
    (X : ({0, 1} : Set ℝ) → ℝ≥0∞) :
    IsEVar X {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ} ↔
      ∃ (u : ℝ) (_ : 0 ≤ u) (_ : u ≤ δ⁻¹),
        ∀ x, X x ≤ ENNReal.ofReal (1 + u * ((x : ℝ) - δ)) := by
  refine ⟨fun h_evar ↦ ?_, ?_⟩
  · have h_le := h_evar.lintegral_le_measure_univ
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
    simp only [measure_univ] at h_le_zero
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
        rwa [ENNReal.mul_le_mul_iff_right (by simp [hδ_pos]) (by simp)] at this
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
      rw [ENNReal.le_sub_iff_add_le_left, mul_comm (ENNReal.ofReal δ), mul_comm (ENNReal.ofReal _)]
      · convert h_le_delta
        simp only [measure_univ, mul_one]
        rw [← ENNReal.ofReal_add (by grind) (by grind)]
        simp
      · finiteness
      · conv_rhs => rw [← mul_one 1]
        gcongr
        simp [hδ_pos.le]
  · rintro ⟨u, hu_nonneg, hu, hX_le⟩
    refine .of_lintegral_le_measure_univ (fun μ hμ ↦ by have := hμ.1; infer_instance)
      (by fun_prop) ?_
    rintro μ ⟨h_prob, h_int⟩
    simp only [measure_univ]
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
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, add_right_inj,
        mul_eq_mul_left_iff]
      rw [integral_sub (by fun_prop) (by fun_prop)]
      simp
    _ ≤ 1 := by
      conv_rhs => rw [← ENNReal.ofReal_one, ← add_zero 1]
      gcongr
      refine mul_nonpos_of_nonneg_of_nonpos hu_nonneg ?_
      simpa

lemma quadratic_inequality {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (u : ℝ) :
    (1 - u * δ) * (1 + u * (1 - δ)) ≤ (1 - δ)⁻¹ * (δ⁻¹ * 4⁻¹) := by
  have : 0 ≤ (u - (δ⁻¹ - (1-δ)⁻¹)/2)^2 := by positivity -- complete square
  field_simp (disch := bound) at this ⊢ -- clear denominators
  linarith

lemma four_le_mul_inv {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    4 ≤ (1 - δ)⁻¹ * δ⁻¹ := by
  have : 0 < 1 - δ := by linarith
  have : (1 - δ) * δ ≤ 1 / 4 := by linarith [sq_nonneg (1 / 2 - δ)]
  rwa [← mul_inv, le_inv_comm₀ (by simp) (by positivity), ← one_div]

/-- Kullback-Leibler divergence between two Bernoulli distributions.
Meaningful only if `p, q ≤ 1`. -/
noncomputable
def klBer (p q : ℝ≥0∞) : ℝ≥0∞ :=
  ((p * ENNReal.log (p / q)) + ((1 - p) * ENNReal.log ((1 - p) / (1 - q)))).toENNReal

lemma klBer_half (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    klBer 2⁻¹ (ENNReal.ofReal δ) = ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ)))) := by
  sorry

lemma maxUtility_bernoulli_le {δ : ℝ} (hδ_pos : 0 < δ) (hδ : δ ≤ 2⁻¹) (hp : ENNReal.ofReal δ ≤ p) :
    maxUtility (Ber p) {Ber q | q ≤ ENNReal.ofReal δ} logUtility
      = 2⁻¹ * klBer p (ENNReal.ofReal δ) := by
  sorry

lemma maxUtility_bernoulli_half_le {δ : ℝ} (hδ_pos : 0 < δ) (hδ : δ ≤ 2⁻¹) :
    maxUtility (Ber 2⁻¹)
        {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ} logUtility
      = 2⁻¹ * Real.log (1 / (4 * δ * (1 - δ))) := by
  have hδ_lt_one : δ < 1 := by grind
  have h_one_sub_δ_pos : 0 < 1 - δ := by grind
  change maxUtility (Ber 2⁻¹) _ logUtility = 2⁻¹ * Real.log (1 / (4 * δ * (1 - δ)))
  rw [maxUtility]
  have hδ_le_one : δ ≤ 1 := by linarith
  simp_rw [isEVar_bernoulli_le_iff hδ_pos hδ_le_one]
  have h_one_sub : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by simp
  have : (2 : ℝ≥0∞)⁻¹ ≠ ∞ := by simp
  simp only [h_one_sub, Subtype.forall, Set.mem_insert_iff, Set.mem_singleton_iff, exists_prop,
    logUtility, Function.comp_apply, eintegral_add_measure, eintegral_smul_measure this,
    eintegral_dirac, one_div, mul_inv_rev, Ber]
  refine le_antisymm ?_ ?_
  · simp only [iSup_exists, iSup_le_iff, and_imp]
    intro X u hu_nonneg hu_le hX
    have hX0 := hX 0 (by simp)
    have hX1 := hX 1 (by simp)
    simp only [zero_sub, mul_neg] at hX0 hX1
    have h1 : (2 : ℝ≥0∞)⁻¹ * ENNReal.log (X ⟨0, by simp⟩)
          + (2 : ℝ≥0∞)⁻¹ * ENNReal.log (X ⟨1, by simp⟩)
        ≤ (2 : ℝ≥0∞)⁻¹ * ENNReal.log (ENNReal.ofReal (1 + -(u * δ)))
          + (2 : ℝ≥0∞)⁻¹ * ENNReal.log (ENNReal.ofReal (1 + u * (1 - δ))) := by gcongr
    refine h1.trans ?_
    have h_pos : 0 < (2 : EReal)⁻¹ :=
      EReal.inv_pos_of_pos_ne_top (by simp) (Ne.symm (not_eq_of_beq_eq_false rfl))
    by_cases huδ : u = δ⁻¹
    · simp only [huδ, inv_mul_cancel₀ hδ_pos.ne', add_neg_cancel, ENNReal.ofReal_zero,
        ENNReal.log_zero, ENNReal.log_ofReal, mul_ite]
      rw [EReal.mul_bot_of_pos (by simp)]
      simp
    have hu_lt : u < δ⁻¹ := lt_of_le_of_ne hu_le huδ
    have h_u_mul_lt : u * δ < 1 := by
      calc u * δ < δ⁻¹ * δ := by gcongr
      _ = 1 := inv_mul_cancel₀ hδ_pos.ne'
    have : 0 < 1 + -(u * δ) := by grind
    have h_one_add_pos : 0 < 1 + u * (1 - δ) := by positivity
    calc (2 : ℝ≥0∞)⁻¹ * ENNReal.log (ENNReal.ofReal (1 + -(u * δ)))
        + (2 : ℝ≥0∞)⁻¹ * ENNReal.log (ENNReal.ofReal (1 + u * (1 - δ)))
    _ = 2⁻¹ * ENNReal.log (ENNReal.ofReal (1 + -(u * δ)))
        + 2⁻¹ * ENNReal.log (ENNReal.ofReal (1 + u * (1 - δ))) := by
      have : (2 : EReal) = (2 : ℝ≥0∞) := rfl
      rw [this, EReal.inv_coe_ennreal (by positivity)]
    _ ≤ 2⁻¹ * Real.log (1 + -(u * δ)) + 2⁻¹ * Real.log (1 + u * (1 - δ)) := by
      simp [not_le.mpr h_u_mul_lt, not_le.mpr h_one_add_pos]
    _ = 2⁻¹ * Real.log ((1 + -(u * δ)) * (1 + u * (1 - δ))) := by
      rw [Real.log_mul]
      rotate_left
      · positivity
      · positivity
      have : (2 : EReal)⁻¹ = (2⁻¹ : ℝ) := rfl
      rw [this]
      norm_cast
      rw [← mul_add]
    _ ≤ 2⁻¹ * Real.log ((1 - δ)⁻¹ * (δ⁻¹ * 4⁻¹)) := by
      gcongr 2
      by_cases hu_zero : u = 0
      · simp only [hu_zero, zero_mul, neg_zero, add_zero, mul_one, Real.log_one]
        refine Real.log_nonneg ?_
        rw [← mul_assoc, le_mul_inv_iff₀ (by positivity), one_mul]
        exact four_le_mul_inv hδ_pos hδ_lt_one
      gcongr 1
      exact quadratic_inequality hδ_pos hδ_lt_one u
  · let u : ℝ := 2⁻¹ * (δ⁻¹ - (1 - δ)⁻¹)
    have hu_nonneg : 0 ≤ u := by
      simp only [inv_pos, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, sub_nonneg, u]
      rcases lt_or_eq_of_le' hδ_le_one with hδ_lt | rfl
      · rw [inv_le_inv₀ (sub_pos.mpr hδ_lt) (by positivity)]
        grind
      · simp
    have hu_lt : u < δ⁻¹ := by
      suffices u < 2⁻¹ * δ⁻¹ by
        refine this.trans_le ?_
        rw [mul_comm, ← div_eq_mul_inv]
        exact half_le_self (by positivity)
      simp only [mul_sub, sub_lt_self_iff, inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left, sub_pos,
        u, hδ_lt_one]
    let X : ({0, 1} : Set ℝ) → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (1 + u * (x.1 - δ))
    refine le_trans (le_of_eq ?_) (le_iSup _ X)
    rw [iSup_pos ⟨u, hu_nonneg, hu_lt.le, by simp [X]⟩]
    have h_u_mul_lt : u * δ < 1 := by
      calc u * δ < δ⁻¹ * δ := by gcongr
      _ = 1 := inv_mul_cancel₀ hδ_pos.ne'
    have h_one_add_u_mul_pos : 0 < 1 + u * (1 - δ) := by positivity
    have : 0 < 1 + -(u * δ) := by grind
    simp only [zero_sub, mul_neg, ENNReal.log_ofReal, add_neg_le_iff_le_add, zero_add,
      not_le.mpr h_u_mul_lt, ↓reduceIte, not_le.mpr h_one_add_u_mul_pos, X]
    have h1 : (2 : EReal) = (2 : ℝ) := rfl
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [h1, h2, ← ENNReal.ofReal_inv_of_pos (by simp), ← EReal.coe_inv, EReal.coe_ennreal_ofReal]
    simp only [inv_nonneg, Nat.ofNat_nonneg, sup_of_le_left]
    norm_cast
    rw [← mul_add, ← Real.log_mul]
    rotate_left
    · positivity
    · positivity
    congr 2
    simp only [u]
    field_simp
    ring

lemma eq_bernoulli_half_of_map_eq {R : Measure ({0, 1} : Set ℝ)} [IsProbabilityMeasure R]
    (hRφ : R.map (fun x ↦ ⟨1 - x.1, by grind⟩) = R) :
    R = Ber 2⁻¹ := by
  have hR_eq : R = R {⟨0, by simp⟩} • Measure.dirac ⟨0, by simp⟩ +
      R {⟨1, by simp⟩} • Measure.dirac ⟨1, by simp⟩ := measure_doubleton_eq_add R
  rw [hR_eq]
  suffices R {⟨0, by simp⟩} = R {⟨1, by simp⟩} by
    have h_one : R {⟨1, by simp⟩} = (2 : ℝ≥0∞)⁻¹ := by
      rw [Measure.ext_iff] at hR_eq
      specialize hR_eq Set.univ
      simp only [MeasurableSet.univ, measure_univ, this, Measure.coe_add, Measure.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, forall_const, ← two_mul] at hR_eq
      calc R {⟨1, by simp⟩}
      _ = 2⁻¹ * (2 * R {⟨1, by simp⟩}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
      _ = 2⁻¹ := by rw [← hR_eq, mul_one]
    simp [this, h_one, Ber]
  rw [hR_eq, Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul,
    Measure.map_dirac, Measure.map_dirac] at hRφ
  simp only [sub_zero, sub_self, Measure.ext_iff_singleton] at hRφ
  simpa using hRφ ⟨1, by simp⟩

lemma map_bernoulli_half_eq :
    (Ber 2⁻¹).map (fun x ↦ (⟨1 - x.1, by grind⟩ : ({0, 1} : Set ℝ))) = Ber 2⁻¹ := by
  rw [Ber, Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul, add_comm]
  simp only [ENNReal.one_sub_inv_two]
  congr
  all_goals simp [Measure.map_dirac]

lemma map_bernoulli_le_eq_bernoulli_ge (δ : ℝ) :
    letI φ : ({0, 1} : Set ℝ) → ({0, 1} : Set ℝ) := fun x ↦ ⟨1 - x.1, by grind⟩
    {x | ∃ μ ∈ {μ | IsProbabilityMeasure μ ∧ ∫ (x : ({0, 1} : Set ℝ)), ↑x ∂μ ≤ δ}, μ.map φ = x} =
      {μ | IsProbabilityMeasure μ ∧ 1 - δ ≤ ∫ (x : ({0, 1} : Set ℝ)), ↑x ∂μ} := by
  let φ : ({0, 1} : Set ℝ) → ({0, 1} : Set ℝ) := fun x ↦ ⟨1 - x.1, by grind⟩
  have hφ_inv : φ ∘ φ = id := by ext; simp [φ]
  ext μ
  simp only [Set.mem_setOf_eq, tsub_le_iff_right]
  constructor
  · rintro ⟨ν, ⟨⟨hν, h_int⟩, rfl⟩⟩
    refine ⟨Measure.isProbabilityMeasure_map (by fun_prop), ?_⟩
    rw [integral_map (by fun_prop) (by fun_prop), integral_sub (by fun_prop) (by fun_prop)]
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

lemma erenyiDiv_bernoulli {δ : ℝ} (hδ_pos : 0 < δ) (hδ : δ ≤ 2⁻¹) :
    erenyiDiv 2⁻¹ {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ}
        {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ 1 - δ ≤ ∫ x, (x : ℝ) ∂μ}
      = ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ)))) := by
  let φ : ({0, 1} : Set ℝ) → ({0, 1} : Set ℝ) := fun x ↦ ⟨1 - x.1, by grind⟩
  have hφ_inv : φ ∘ φ = id := by ext; simp [φ]
  rw [erenyiDiv_of_involutive (by fun_prop) hφ_inv]
  swap
  · exact map_bernoulli_le_eq_bernoulli_ge δ
  have h_iff R (hR : IsProbabilityMeasure R) :
      R.map φ = R ↔ R = Ber 2⁻¹ := by
    constructor
    · exact eq_bernoulli_half_of_map_eq
    · rintro rfl
      exact map_bernoulli_half_eq
  calc 2 * ⨅ (R : Measure _) (_ : IsProbabilityMeasure R) (_ : Measure.map φ R = R),
      (maxUtility R {μ | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ} logUtility).toENNReal
  _ = 2 * ⨅ (R : Measure _) (_ : IsProbabilityMeasure R) (_ : Measure.map φ R = R),
      (maxUtility (Ber 2⁻¹)
        {μ | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ} logUtility).toENNReal := by
    congr with R
    congr with hR
    congr with hRφ
    rw [h_iff R hR] at hRφ
    rw [hRφ]
  _ = 2 * (maxUtility (Ber 2⁻¹)
        {μ | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ} logUtility).toENNReal := by
    rw [iInf₃_eq_sInf]
    congr 1
    suffices {y | ∃ x, IsProbabilityMeasure x ∧ x.map φ = x ∧
              y = (maxUtility (Ber 2⁻¹)
                  {μ | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ} logUtility).toENNReal}
        = { (maxUtility (Ber 2⁻¹)
                  {μ | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ} logUtility).toENNReal } by
      rw [this, sInf_singleton]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨fun ⟨μ, hμ, hμ_eq, hy_eq⟩ ↦ by rw [hy_eq], fun h ↦ ?_⟩
    exact ⟨Ber 2⁻¹, inferInstance, map_bernoulli_half_eq, h⟩
  _ = ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ)))) := by
    rw [maxUtility_bernoulli_half_le hδ_pos hδ, EReal.toENNReal_mul (by positivity),
      EReal.real_coe_toENNReal, ← mul_assoc]
    conv_rhs => rw [← one_mul (ENNReal.ofReal _)]
    congr
    have : (2 : EReal)⁻¹.toENNReal = 2⁻¹ := by
      have : (2 : EReal) = (2 : ℝ≥0∞) := rfl
      rw [this, EReal.toENNReal_inv (by simp)]
      simp
    rw [this, ENNReal.mul_inv_cancel (by simp) (by simp)]

lemma echernoffDiv_bernoulli {δ : ℝ} (hδ_pos : 0 < δ) (hδ : δ ≤ 2⁻¹) :
    echernoffDiv {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ ∫ x, (x : ℝ) ∂μ ≤ δ}
        {μ : Measure ({0, 1} : Set ℝ) | IsProbabilityMeasure μ ∧ 1 - δ ≤ ∫ x, (x : ℝ) ∂μ}
      = 2⁻¹ * ENNReal.ofReal (Real.log (1 / (4 * δ * (1 - δ)))) := by
  let φ : ({0, 1} : Set ℝ) → ({0, 1} : Set ℝ) := fun x ↦ ⟨1 - x.1, by grind⟩
  have hφ_inv : φ ∘ φ = id := by ext; simp [φ]
  rw [← erenyiDiv_bernoulli hδ_pos hδ,
    erenyiDiv_eq_two_mul_echernoffDiv_of_involutive (by fun_prop) hφ_inv,
    ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
  exact map_bernoulli_le_eq_bernoulli_ge δ

end ProbabilityTheory
