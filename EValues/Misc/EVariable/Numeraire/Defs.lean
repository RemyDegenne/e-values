/-
 - Created in 2025 by Gaëtan Serré
-/

import EValues.Misc.EVariable.Utils.Integral
import EValues.Misc.EVariable.Defs
import EValues.Misc.EIntegral.Defs
import EValues.Misc.EVariable.Utils.Div

open MeasureTheory ENNReal Function

variable {α : Type*} [MeasurableSpace α]

structure Numeraire (P : Set (ProbabilityMeasure α)) (Q : Measure α) [IsProbabilityMeasure Q]
    extends EVariable P where
  private lintegral_ratio_le_one' : ∀ (e : EVariable P), ∫⁻ x, e x /ₑ toFun x ∂Q ≤ 1

namespace Numeraire

variable {P : Set (ProbabilityMeasure α)} {Q : Measure α} [IsProbabilityMeasure Q]

instance : FunLike (Numeraire P Q) α ℝ≥0∞ where
  coe f := f.toFun
  coe_injective' f g h := by
    have : f.toEVariable = g.toEVariable := by
      rw [←DFunLike.coe_fn_eq]
      exact h
    cases f; cases g
    simp_all

variable (e_n : Numeraire P Q)

variable (e : EVariable P)

/- lemma ratio_measurable : Measurable (fun x ↦ e x / e_n x) :=
  e.measurable.div e_n.measurable

lemma ratio_aemeasurable {μ : Measure α} : AEMeasurable (fun x ↦ e x / e_n x) μ :=
  (e_n.ratio_measurable e).aemeasurable

lemma ratio_aestronglymeasurable {μ : Measure α} : AEStronglyMeasurable (fun x ↦ e x / e_n x) μ :=
  (e_n.ratio_measurable e).aestronglyMeasurable -/

lemma lintegral_ratio_le_one : ∫⁻ x, e x /ₑ e_n x ∂Q ≤ 1 :=
  e_n.lintegral_ratio_le_one' e

/- lemma integrable_ratio : Integrable (fun x ↦ e x / e_n x) Q :=
  ⟨(e.measurable.div e_n.measurable).aestronglyMeasurable,
    lt_of_le_of_lt (e_n.lintegral_ratio_le_one e) (by simp)⟩ -/

lemma average_ratio_le_one : ⨍⁻ x, e x /ₑ e_n x ∂Q ≤ 1 := by
  simp only [laverage, measure_univ, inv_one, one_smul]
  exact e_n.lintegral_ratio_le_one e

/- variable (e : Numeraire P Q)

lemma ratio_ae_lbounded : ∃ ε > 0, (const α ε) <ᵐ[Q] fun x ↦ e x / e_n x := by
  obtain ⟨ε₁, ε₁_pos, hε₁⟩ := e_n.ae_ubounded
  obtain ⟨ε₂, ε₂_pos, hε₂⟩ := e.ae_lbounded
  obtain ⟨ε₃, ε₃_pos, hε₃⟩ := e_n.ae_lbounded
  let ε := ε₂ / ε₁
  have ε_pos : ε > 0 := div_pos ε₂_pos ε₁_pos
  use ε, ε_pos
  filter_upwards [hε₁, hε₂, hε₃] with a ha₁ ha₂ ha₃
  simp_all
  calc _ > ε₂ / ε₁ := by
        refine div_lt_div₀ ha₂ ha₁.le ?_ ?_
        · exact (gt_trans ha₂ ε₂_pos).le
        · exact gt_trans ha₃ ε₃_pos
  _ = ε := rfl

lemma ratio_ae_pos : 0 <ᵐ[Q] fun x ↦ e x / e_n x := by
  filter_upwards [e_n.ae_pos, e.ae_pos] with a ha₁ ha₂
  simp_all

lemma average_ratio_pos : 0 < ⨍ x, e x / e_n x ∂Q := by
  simp only [average, measure_univ, inv_one, one_smul]
  exact integral_pos (e_n.ratio_ae_pos e) <| e_n.integrable_ratio e.toEVariable -/

end Numeraire

variable (P : Set (ProbabilityMeasure α)) (Q : Measure α)

def is_numeraire [IsProbabilityMeasure Q] (e : α → ℝ≥0∞) : Prop :=
  is_evariable P e ∧ (∀ (f : EVariable P), ∫⁻ x, f x /ₑ e x ∂Q ≤ 1)

namespace is_numeraire

def to_Numeraire [IsProbabilityMeasure Q] {e : α → ℝ≥0∞}
    (he : is_numeraire P Q e) : Numeraire P Q := ⟨he.1.to_Evariable, he.2⟩

end is_numeraire

namespace Numeraire

variable {P : Set (ProbabilityMeasure α)} {Q : Measure α} [IsProbabilityMeasure Q]

variable {e : Numeraire P Q}

lemma is_numeraire : is_numeraire P Q e := ⟨e.toEVariable.is_evariable, e.lintegral_ratio_le_one⟩

end Numeraire
