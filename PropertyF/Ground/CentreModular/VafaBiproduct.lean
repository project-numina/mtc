module
public import PropertyF.Ground.CentreModular.VafaNatural
public import Mathlib.CategoryTheory.Preadditive.Biproducts

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Hom into a binary biproduct is the product of the two Hom spaces. -/
def homBiprodLinearEquiv (C : BraidedFusionCategory.{v,u}) (S X Y : C.Obj) :
    (S ⟶ X ⊞ Y) ≃ₗ[ℂ] ((S ⟶ X) × (S ⟶ Y)) where
  toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
  invFun f := f.1 ≫ biprod.inl + f.2 ≫ biprod.inr
  left_inv f := by ext <;> simp [Preadditive.add_comp, Category.assoc]
  right_inv f := by ext <;> simp [Preadditive.add_comp, Category.assoc]
  map_add' f g := by ext <;> simp
  map_smul' r f := by ext <;> simp

/-- The determinant on simple Hom spaces factors over a binary biproduct. -/
theorem simpleHomAction_det_biprod (C : BraidedFusionCategory.{v,u})
    (X Y : C.Obj) (a : X ≅ X) (b : Y ≅ Y) (i : Fin (rank C)) :
    (simpleHomAction C (X ⊞ Y) i (biprod.mapIso a b)).det =
      (simpleHomAction C X i a).det * (simpleHomAction C Y i b).det := by
  let : FiniteDimensional ℂ (simples C i ⟶ X) := IsFusionCategory.hom_finite _ _
  let : FiniteDimensional ℂ (simples C i ⟶ Y) := IsFusionCategory.hom_finite _ _
  let E := homBiprodLinearEquiv C (simples C i) X Y
  let A := simpleHomAction C (X ⊞ Y) i (biprod.mapIso a b)
  let L := simpleHomAction C X i a
  let R := simpleHomAction C Y i b
  have h : (E.symm.trans A).trans E = L.prodCongr R := by
    ext f <;> simp [E, A, L, R, homBiprodLinearEquiv, simpleHomAction,
      CategoryTheory.Linear.homCongr_apply, Category.assoc]
  apply Units.ext
  rw [← LinearEquiv.det_conj A E, h, LinearEquiv.coe_det]
  change LinearMap.det (L.toLinearMap.prodMap R.toLinearMap) = _
  rw [LinearMap.det_prodMap]
  simp only [Units.val_mul, LinearEquiv.coe_det]
  rfl

/-- FP determinants are additive over direct sums of automorphisms. -/
theorem fpDeterminant_biprod (C : BraidedFusionCategory.{v,u})
    (X Y : C.Obj) (a : X ≅ X) (b : Y ≅ Y) :
    fpDeterminant C (X ⊞ Y) (biprod.mapIso a b) =
      fpDeterminant C X a + fpDeterminant C Y b := by
  unfold fpDeterminant
  simp_rw [simpleHomAction_det_biprod, vafaUnitClass_mul, smul_add]
  rw [Finset.sum_add_distrib]

end PropertyF.Ground.CentreModular
