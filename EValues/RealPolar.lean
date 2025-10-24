/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.CompletePartialOrder

/-!
# Real polar set

In this file we define the real polar set.
There are different notions of the polar, we will define the
*absolute polar*. The advantage over the real polar is that we can define the absolute polar for
any bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, where `𝕜` is a normed commutative ring and
`E` and `F` are modules over `𝕜`.

## Main definitions

* `LinearMap.realPolar`: The polar of a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`.

## Main statements

* `LinearMap.realPolar_eq_iInter`: The polar as an intersection.
* `LinearMap.subset_biRealPolar`: The polar is a subset of the bipolar.
* `LinearMap.realPolar_weak_closed`: The polar is closed in the weak topology induced by `B.flip`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

polar
-/

variable {𝕜 E F : Type*}

open Topology RCLike

namespace LinearMap

variable [RCLike 𝕜] [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- The real polar of `s : Set E` is given by the set of all `y : F` such that `re (B x y) ≤ 1`
for all `x ∈ s`. -/
def realPolar (s : Set E) : Set F :=
  { y : F | ∀ x ∈ s, re (B x y) ≤ 1 }

theorem realPolar_mem_iff (s : Set E) (y : F) : y ∈ B.realPolar s ↔ ∀ x ∈ s, re (B x y) ≤ 1 :=
  Iff.rfl

theorem realPolar_mem (s : Set E) (y : F) (hy : y ∈ B.realPolar s) : ∀ x ∈ s, re (B x y) ≤ 1 :=
  hy

theorem realPolar_eq_biInter_preimage (s : Set E) :
    B.realPolar s = ⋂ x ∈ s, ((B x) ⁻¹' (re ⁻¹' (Set.Iic 1))) := by aesop

theorem realPolar_isClosed (s : Set E) : IsClosed (X := WeakBilin B.flip) (B.realPolar s) := by
  rw [realPolar_eq_biInter_preimage]
  refine isClosed_biInter fun x hx ↦ ?_
  refine IsClosed.preimage (WeakBilin.eval_continuous B.flip x) ?_
  exact isClosed_Iic.preimage continuous_re

@[simp]
theorem zero_mem_realPolar (s : Set E) : (0 : F) ∈ B.realPolar s := fun _ _ ↦ by simp

theorem realPolar_nonempty (s : Set E) : Set.Nonempty (B.realPolar s) :=
  ⟨0, zero_mem_realPolar B s⟩

theorem realPolar_eq_iInter {s : Set E} : B.realPolar s = ⋂ x ∈ s, { y : F | re (B x y) ≤ 1 } := by
  ext
  simp [realPolar_mem_iff]

/-- The map `B.realPolar : Set E → Set F` forms an order-reversing Galois connection with
`B.flip.realPolar : Set F → Set E`. We use `OrderDual.toDual` and `OrderDual.ofDual` to express
that `realPolar` is order-reversing. -/
theorem realPolar_gc :
    GaloisConnection (OrderDual.toDual ∘ B.realPolar) (B.flip.realPolar ∘ OrderDual.ofDual) :=
  fun _ _ ↦ ⟨fun h _ hx _ hy ↦ h hy _ hx, fun h _ hx _ hy ↦ h hy _ hx⟩

@[simp]
theorem realPolar_iUnion {ι} {s : ι → Set E} : B.realPolar (⋃ i, s i) = ⋂ i, B.realPolar (s i) :=
  B.realPolar_gc.l_iSup

@[simp]
theorem realPolar_union {s t : Set E} : B.realPolar (s ∪ t) = B.realPolar s ∩ B.realPolar t :=
  B.realPolar_gc.l_sup

theorem realPolar_antitone : Antitone (B.realPolar : Set E → Set F) :=
  B.realPolar_gc.monotone_l

@[simp]
theorem realPolar_empty : B.realPolar ∅ = Set.univ :=
  B.realPolar_gc.l_bot

@[simp]
theorem realPolar_singleton {a : E} : B.realPolar {a} = { y | re (B a y) ≤ 1 } := le_antisymm
  (fun _ hy ↦ hy _ rfl)
  (fun y hy ↦ (realPolar_mem_iff _ _ _).mp (fun _ hb ↦ by rwa [Set.mem_singleton_iff.mp hb]))

theorem mem_realPolar_singleton {x : E} (y : F) : y ∈ B.realPolar {x} ↔ re (B x y) ≤ 1 := by
  simp only [realPolar_singleton, Set.mem_setOf_eq]

theorem realPolar_zero : B.realPolar ({0} : Set E) = Set.univ := by
  simp only [realPolar_singleton, map_zero, zero_apply, zero_le_one, Set.setOf_true]

theorem subset_biRealPolar (s : Set E) : s ⊆ B.flip.realPolar (B.realPolar s) := fun x hx y hy ↦ by
  rw [B.flip_apply]
  exact hy x hx

@[simp]
theorem triRealPolar_eq_realPolar (s : Set E) :
    B.realPolar (B.flip.realPolar (B.realPolar s)) = B.realPolar s :=
  (B.realPolar_antitone (B.subset_biRealPolar s)).antisymm
    (subset_biRealPolar B.flip (B.realPolar s))

/-- The real polar set is closed in the weak topology induced by `B.flip`. -/
theorem realPolar_weak_closed (s : Set E) :
    IsClosed[WeakBilin.instTopologicalSpace B.flip] (B.realPolar s) := by
  rw [realPolar_eq_iInter]
  refine isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦ ?_
  refine isClosed_le ?_ continuous_const
  -- TODO: make `fun_prop` work?
  exact continuous_re.comp (WeakBilin.eval_continuous B.flip x)

theorem sInter_realPolar_finite_subset_eq_realPolar (s : Set E) :
    ⋂₀ (B.realPolar '' { F | F.Finite ∧ F ⊆ s }) = B.realPolar s := by
  ext x
  simp only [Set.sInter_image, Set.mem_setOf_eq, Set.mem_iInter, and_imp]
  refine ⟨fun hx a ha ↦ ?_, fun hx F _ hF₂ ↦ realPolar_antitone _ hF₂ hx⟩
  simpa [mem_polar_singleton] using hx _ (Set.finite_singleton a) (Set.singleton_subset_iff.mpr ha)

lemma re_eq_zero_of_forall_smul_mem_of_mem_realPolar
    {s : Set E} (hs : ∀ x ∈ s, ∀ r : 𝕜, r • x ∈ s)
    {x : E} (hx : x ∈ s) {y : F} (hy : y ∈ B.realPolar s) :
    re (B x y) = 0 := by
  simp only [realPolar_mem_iff] at hy
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt_imp_ge_of_dense fun r hr ↦ ?_
    specialize hy (((r⁻¹ : ℝ) : 𝕜) • x) (hs x hx _)
    simp only [map_smul, smul_eq_mul, smul_apply, mul_re, ofReal_im, ofReal_re, zero_mul,
      sub_zero] at hy
    rwa [inv_mul_le_iff₀ (by positivity), mul_one] at hy
  · refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
    specialize hy (((r⁻¹ : ℝ) : 𝕜) • x) (hs x hx _)
    simp only [map_smul, smul_eq_mul, smul_apply, mul_re, ofReal_im, ofReal_re, zero_mul,
      sub_zero] at hy
    rwa [← smul_eq_mul, inv_smul_le_iff_of_neg hr, smul_eq_mul, mul_one] at hy

lemma eq_zero_of_forall_smul_mem_of_mem_realPolar
    {s : Set E} (hs : ∀ x ∈ s, ∀ r : 𝕜, r • x ∈ s)
    {x : E} (hx : x ∈ s) {y : F} (hy : y ∈ B.realPolar s) :
    B x y = 0 := by
  suffices re (B x y) = 0 ∧ im (B x y) = 0 by
    rw [← re_add_im (B x y)]
    simp [this]
  constructor
  · exact re_eq_zero_of_forall_smul_mem_of_mem_realPolar B hs hx hy
  · simp only [realPolar_mem_iff] at hy
    suffices - im (B x y) = 0 by simpa
    rw [← I_mul_re]
    have : I * B x y = B ((I : 𝕜) • x) y := by simp
    rw [this]
    exact re_eq_zero_of_forall_smul_mem_of_mem_realPolar B hs (hs x hx _) hy

theorem realPolar_univ (h : SeparatingRight B) : B.realPolar Set.univ = {(0 : F)} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨by simp only [zero_mem_realPolar], fun y hy ↦ h _ fun x ↦ ?_⟩
  exact eq_zero_of_forall_smul_mem_of_mem_realPolar B (fun _ _ _ ↦ Set.mem_univ _)
    (Set.mem_univ _) hy

theorem realPolar_subMulAction {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) :
    B.realPolar m = { y | ∀ x ∈ m, B x y = 0 } := by
  ext y
  constructor
  · intro hy x hx
    exact eq_zero_of_forall_smul_mem_of_mem_realPolar B (fun x hx r ↦ SMulMemClass.smul_mem r hx)
      hx hy
  · intro h x hx
    simp [h x hx]

/-- The polar of a set closed under scalar multiplication as a submodule -/
def realPolarSubmodule {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) : Submodule 𝕜 F :=
  .copy (⨅ x ∈ m, LinearMap.ker (B x)) (B.realPolar m) <| by ext; simp [realPolar_subMulAction]

end LinearMap
