module
public import PropertyF.Ground.Fusion.GeneratedRigidity
public import PropertyF.Ground.Fusion.UnitPower
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Cabling.UnitPower
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF.Ground.Cabling
universe v u

/-- Every simple fusion matrix has a directed cycle through the unit. -/
theorem fusion_unit_cycle (D : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (rank D)) :
    ∃ j, 0 < fusionCoeff D i (unitIndex D) j ∧
      Relation.ReflTransGen (fun a b => 0 < fusionCoeff D i a b) j (unitIndex D) := by
  classical
  let v := fpSimple D
  let w : Fin (rank D) → Fin (rank D) → ℝ :=
    fun a b => v a * (fusionCoeff D i a b : ℝ) * v b
  have hw : ∀ a b, 0 ≤ w a b := fun a b =>
    mul_nonneg (mul_nonneg (fpSimple_pos D a).le (Nat.cast_nonneg _)) (fpSimple_pos D b).le
  have hleft (a b) : fusionCoeff D i b a = fusionCoeff D (dualIndex D i) a b := by
    have h := congrFun (congrFun (fusionMatrix_dual D i) b) a
    change (fusionCoeff D (dualIndex D i) a b : ℂ) = (fusionCoeff D i b a : ℂ) at h
    exact_mod_cast h.symm
  have hb : ∀ a, ∑ b, w a b = ∑ b, w b a := by
    intro a
    calc
      _ = v a * ∑ b, (fusionCoeff D i a b : ℝ) * v b := by simp [w, Finset.mul_sum, mul_assoc]
      _ = v a * (v i * v a) := by rw [← fpSimple_mul]
      _ = (v (dualIndex D i) * v a) * v a := by dsimp [v]; rw [fpSimple_dual]; ring
      _ = (∑ b, (fusionCoeff D (dualIndex D i) a b : ℝ) * v b) * v a := by rw [← fpSimple_mul]
      _ = _ := by simp only [w, Finset.sum_mul, ← hleft]; apply Finset.sum_congr rfl; intro b _; ring
  have hout : ∃ j, 0 < w (unitIndex D) j := by
    refine ⟨i, ?_⟩
    have hcoeff : fusionCoeff D i (unitIndex D) i = 1 := by
      rw [fusionCoeff_comm, fusionCoeff_unit]; simp
    simpa [w, v, hcoeff] using mul_pos (fpSimple_pos D (unitIndex D)) (fpSimple_pos D i)
  obtain ⟨j, hj, path⟩ := Ground.balanced_flow_cycle w hw hb (unitIndex D) hout
  have hp {a b} (h : 0 < w a b) : 0 < fusionCoeff D i a b := by
    by_contra hzero
    have : fusionCoeff D i a b = 0 := Nat.eq_zero_of_not_pos hzero
    simp [w, this] at h
  refine ⟨j, hp hj, ?_⟩
  have trans {a b} (p : Relation.ReflTransGen (fun a b => 0 < w a b) a b) :
      Relation.ReflTransGen (fun a b => 0 < fusionCoeff D i a b) a b := by
    induction p with
    | refl => exact .refl
    | tail _ he ih => exact ih.tail (hp he)
  exact trans path
/-- A positive fusion coefficient gives an actual split inclusion. -/
theorem fusionCoeffRetract (D : Ground.BraidedFusionCategory.{v,u})
    (i a b : Fin (rank D)) (h : 0 < fusionCoeff D i a b) :
    Nonempty (Retract (simples D b) (simples D i ⊗ simples D a)) :=
  Ground.fusionCoeff_retract D i a b h

/-- Along any fusion path, an occurrence of its initial label in a power
extends to an occurrence of its final label in a later power. -/
theorem fusion_path_retract (D : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (rank D)) {a b : Fin (rank D)}
    (path : Relation.ReflTransGen (fun a b => 0 < fusionCoeff D i a b) a b)
    (n : ℕ) (r : Retract (simples D a) (tensorPower (simples D i) (n + 1))) :
    ∃ m, Nonempty (Retract (simples D b) (tensorPower (simples D i) (m + 1))) := by
  induction path generalizing n with
  | refl => exact ⟨n, ⟨r⟩⟩
  | @tail b c p h ih =>
    obtain ⟨m, ⟨s⟩⟩ := ih n r
    obtain ⟨q⟩ := fusionCoeffRetract D i b c h
    let t := q.trans (s.map (tensorLeft (simples D i)))
    exact ⟨m + 1, ⟨t⟩⟩

/-- Taking tensor powers preserves retracts. -/
def powerRetract (D : Ground.BraidedFusionCategory.{v,u}) {X Y : D.Obj}
    (r : Retract X Y) : ∀ n, Retract (tensorPower X n) (tensorPower Y n)
  | 0 => Retract.refl _
  | n + 1 => (r.map (tensorRight (tensorPower X n))).trans
      ((powerRetract D r n).map (tensorLeft Y))

/-- A positive tensor power of every simple object contains the unit. -/
theorem unit_retract_power (D : Ground.BraidedFusionCategory.{v,u}) (X : D.Obj) [Simple X] :
    ∃ n, Nonempty (Retract (𝟙_ D.Obj) (tensorPower X (n + 1))) :=
  Ground.unit_retract_tensorPower D X

/-- The generated subcategory of a simple object is closed under duals. -/
theorem generatedBy_rightDual_of_simple (D : Ground.BraidedFusionCategory.{v,u})
    (X : D.Obj) [Simple X] : GeneratedBy X (Xᘁ) :=
  Ground.simple_generatedBy_rightDual D X

/-- The generated full subcategory of a simple object is rigid. -/
@[instance_reducible] def generatedCategoryRigidOfSimple
    (D : Ground.BraidedFusionCategory.{v,u}) (X : D.Obj) [Simple X] :
    RigidCategory (generatedCategory X) :=
  generatedCategoryRigidOfGeneratorDual X (generatedBy_rightDual_of_simple D X)
end PropertyF.Ground.Cabling
