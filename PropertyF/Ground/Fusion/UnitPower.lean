module
public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import PropertyF.Ground.Fusion.ObjectDimension
public import PropertyF.Ground.Modular.BraidIso
public import PropertyF.Ground.Cabling.UnitPower
public import PropertyF.Ground.Dimensions.Pivotal

/-! A finite balanced nonnegative flow cannot enter a closed set. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground

variable {k : Type*} [AddCommGroup k] [LinearOrder k] [IsOrderedAddMonoid k]
  {ι : Type*} [Fintype ι] {b : ι → ι → k}
variable (hb : ∀ i j, 0 ≤ b i j) (hbalance : ∀ i, (∑ j, b i j) = ∑ j, b j i)
include hb hbalance

/-- In a finite balanced flow, a set with no outgoing edges also has no
incoming edges. -/
theorem balanced_flow_no_entry {s : Finset ι} (hclosed : ∀ i ∈ s, ∀ j ∉ s, b i j = 0)
    {i j : ι} (hi : i ∉ s) (hj : j ∈ s) : b i j = 0 := by
  classical
  have hin : ∑ y ∈ s, ∑ x ∈ s, b x y = ∑ y ∈ s, ∑ x, b x y :=
    Finset.sum_comm.trans ((Finset.sum_congr rfl fun x hx ↦
      Finset.sum_subset (Finset.subset_univ s) (fun y _ hy ↦ hclosed x hx y hy)).trans
        (Finset.sum_congr rfl fun x _ ↦ hbalance x))
  have hrow (y : ι) (hy : y ∈ s) : ∑ x ∈ s, b x y = ∑ x, b x y :=
    (Finset.sum_eq_sum_iff_of_le (fun z _ ↦
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun x _ _ ↦ hb x z))).mp hin y hy
  have hzero : ∑ x ∈ Finset.univ \ s, b x j = 0 := by
    have h := Finset.sum_sdiff (f := fun x => b x j) (Finset.subset_univ s)
    rw [← hrow j hj] at h
    exact add_right_cancel (h.trans (zero_add _).symm)
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hb x j)).mp hzero i
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)

/-- Every vertex with an outgoing edge in a finite balanced nonnegative flow
lies on a directed cycle. -/
theorem balanced_flow_cycle {o : ι} (hout : ∃ j, 0 < b o j) :
    ∃ j, 0 < b o j ∧ Relation.ReflTransGen (fun i j => 0 < b i j) j o := by
  classical
  let r : ι → ι → Prop := fun i j => 0 < b i j
  let s : Finset ι := Finset.univ.filter (fun i => ¬ Relation.ReflTransGen r i o)
  have hc : ∀ i ∈ s, ∀ j ∉ s, b i j = 0 := by
    intro i hi j hj
    exact le_antisymm (not_lt.mp fun h ↦ (Finset.mem_filter.mp hi).2
      (Relation.ReflTransGen.head h (by simpa [s] using hj))) (hb i j)
  obtain ⟨j, hj⟩ := hout
  refine ⟨j, hj, ?_⟩
  simpa [s] using (show j ∉ s from fun hjs ↦
    (ne_of_gt hj) (balanced_flow_no_entry hb hbalance hc
      (by simp [s, Relation.ReflTransGen.refl]) hjs))

end PropertyF.Ground

end

/-! Every simple object has a positive tensor power containing the unit. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground
universe v u

variable (D : BraidedFusionCategory.{v,u})

/-- The FP-weighted directed fusion graph is a balanced flow. -/
def fusionFlow (i j k : Fin (rank D)) : ℝ :=
  fpSimple D j * (fusionCoeff D i j k : ℝ) * fpSimple D k

theorem fusionFlow_balance (i j : Fin (rank D)) :
    (∑ k, fusionFlow D i j k) = ∑ k, fusionFlow D i k j := by
  classical
  simp only [fusionFlow, fusionCoeff_dual_symmetry D i j]
  calc
    _ = fpSimple D j * (∑ k, (fusionCoeff D i j k : ℝ) * fpSimple D k) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = fpSimple D j * (∑ k, (fusionCoeff D (dualIndex D i) j k : ℝ) * fpSimple D k) := by
      rw [← fpSimple_mul, ← fpSimple_mul, fpSimple_dual]
    _ = _ := by simp only [Finset.mul_sum, mul_comm]

/-- A positive fusion coefficient gives an actual retract. -/
theorem fusionCoeff_retract
    {i j k : Fin (rank D)} (h : 0 < fusionCoeff D i j k) :
    Nonempty (Retract (simples D k) (simples D i ⊗ simples D j)) :=
  let : FiniteDimensional ℂ (simples D k ⟶ simples D i ⊗ simples D j) :=
    IsFusionCategory.hom_finite _ _
  let : Simple (simples D k) := simples_simple D k
  (Module.finrank_pos_iff_exists_ne_zero.mp h).elim fun f hf ↦
    (split_from_simple f hf).elim fun r hr ↦ ⟨{ i := f, r := r, retract := hr }⟩

/-- Along a fusion path beginning at i, the endpoint is a retract of a
positive tensor power of the simple i. -/
theorem fusionPath_retract {i k : Fin (rank D)}
    (h : Relation.ReflTransGen (fun j k => 0 < fusionFlow D i j k) i k) :
    ∃ n, Nonempty (Retract (simples D k) (tensorPower (simples D i) (n + 1))) := by
  induction h with
  | refl =>
    exact ⟨0, ⟨Retract.ofIso (ρ_ (simples D i)).symm⟩⟩
  | @tail j k h edge ih =>
    obtain ⟨n, ⟨r⟩⟩ := ih
    have hn : 0 < fusionCoeff D i j k := by
      change 0 < fpSimple D j * (fusionCoeff D i j k : ℝ) * fpSimple D k at edge
      exact_mod_cast (mul_pos_iff_of_pos_left (fpSimple_pos D j)).mp
        ((mul_pos_iff_of_pos_right (fpSimple_pos D k)).mp edge)
    obtain ⟨s⟩ := fusionCoeff_retract D hn
    let t : Retract (simples D i ⊗ simples D j)
        (simples D i ⊗ tensorPower (simples D i) (n + 1)) :=
      { i := 𝟙 _ ⊗ₘ r.i
        r := 𝟙 _ ⊗ₘ r.r
        retract := by rw [tensorHom_comp_tensorHom, Category.id_comp, r.retract, id_tensorHom_id] }
    exact ⟨n + 1, ⟨s.trans t⟩⟩

/-- A simple object has a positive tensor power containing the unit. -/
theorem unit_retract_tensorPower {E : Type u} [Category.{v} E] [MonoidalCategory E]
    [BraidedCategory E] [Abelian E] [Linear ℂ E] [RigidCategory E]
    [MonoidalPreadditive E] [MonoidalLinear ℂ E] [IsFusionCategory E]
    (X : E) [Simple X] : ∃ n, Nonempty (Retract (𝟙_ E) (tensorPower X (n + 1))) := by
  classical
  let D : BraidedFusionCategory := { Obj := E }
  obtain ⟨i, ⟨e⟩⟩ := exists_simple_iso D X
  obtain ⟨j, hj, hp⟩ := balanced_flow_cycle (b := fusionFlow D i) (o := unitIndex D)
    (fun j k ↦ mul_nonneg (mul_nonneg (fpSimple_pos D j).le (Nat.cast_nonneg _))
      (fpSimple_pos D k).le)
    (fusionFlow_balance D i) ⟨i, by
      simpa [fusionFlow, fusionCoeff_comm D i (unitIndex D), fusionCoeff_unit, fpSimple_unit] using
        fpSimple_pos D i⟩
  have hji : j = i := by
    simpa [fusionFlow, fusionCoeff_comm D i (unitIndex D), fusionCoeff_unit,
      fpSimple_unit, apply_ite, fpSimple_pos D] using hj
  subst j
  obtain ⟨n, ⟨r⟩⟩ := fusionPath_retract D hp
  obtain ⟨u⟩ := unitIndex_iso D
  exact ⟨n, ⟨(Retract.ofIso u.symm).trans (r.trans (Retract.ofIso (Modular.tensorPowerIso e.symm _)))⟩⟩

end PropertyF.Ground

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u

/-- The right dual of a simple object lies in its generated tensor closure. -/
theorem simple_generatedBy_rightDual {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] [Abelian D] [Linear ℂ D] [RigidCategory D]
    [MonoidalPreadditive D] [MonoidalLinear ℂ D] [IsFusionCategory D]
    (X : D) [Simple X] : GeneratedBy X (Xᘁ) :=
  (unit_retract_tensorPower X).elim fun _ ⟨r⟩ ↦ Cabling.generatedBy_rightDual_of_unit_power r

end PropertyF.Ground

namespace PropertyF.Ground

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
section
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]

/-- Duals commute with finite direct sums up to a retract, for any finite index. -/
def dualFiniteBiproductRetract {ι : Type} [Fintype ι]
    (V : ι → D) : Retract ((⨁ V)ᘁ) (⨁ fun i => (V i)ᘁ) where
  i := biproduct.lift fun i => (biproduct.ι V i)ᘁ
  r := biproduct.desc fun i => (biproduct.π V i)ᘁ
  retract := by
    rw [biproduct.lift_desc]
    simp only [← comp_rightAdjointMate, ← rightAdjointMate_sum, biproduct.total,
      rightAdjointMate_id]

end

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [Abelian D] [Linear ℂ D] [RigidCategory D] [MonoidalPreadditive D]
  [MonoidalLinear ℂ D] [IsFusionCategory D]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- In a fusion category the right dual of every object is generated by that
object using tensor products, finite sums, and retracts. -/
theorem generatedBy_rightDual (X : D) :
    GeneratedBy X (Xᘁ) := by
  classical
  obtain ⟨n, T, hsimple, _, hdecomp⟩ := IsFusionCategory.finite_semisimple (C := D)
  obtain ⟨m, ⟨e⟩⟩ := hdecomp X
  let V : (Σ i, Fin (m i)) → D := fun p => T p.1
  have hv (p : Σ i, Fin (m i)) : GeneratedBy X (V p) := by
    apply generatedBy_retract (generatedBy_self X)
    exact { i := biproduct.ι V p ≫ e.inv
            r := e.hom ≫ biproduct.π V p
            retract := by simp [Category.assoc] }
  exact generatedBy_of_iso
    (generatedBy_retract (generatedBy_finiteBiproduct _ fun p ↦
      letI : Simple (V p) := hsimple p.1
      generatedBy_trans (hv p) (simple_generatedBy_rightDual (V p)))
      (dualFiniteBiproductRetract V))
    (Dimensions.rightDualIsoMap e).symm

end PropertyF.Ground
