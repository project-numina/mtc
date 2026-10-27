module
public import PropertyF.Ground.CentreInduction.GlobalSquare
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! A linear adjunction supplies the multiplicities needed for the FP-square calculation. -/

@[expose] public noncomputable section
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreInduction
universe v u v' u'

/-- The reverse Hom equivalence of an adjunction is linear when its left
adjoint is linear. -/
def homLinearEquivOfAdjunction {A : Type u} {B : Type u'}
    [Category.{v} A] [Category.{v'} B] [Preadditive A] [Preadditive B]
    [Linear ℂ A] [Linear ℂ B] (F : A ⥤ B) (G : B ⥤ A)
    [F.Additive] [F.Linear ℂ] (adj : F ⊣ G) (X : A) (Y : B) :
    (X ⟶ G.obj Y) ≃ₗ[ℂ] (F.obj X ⟶ Y) := by
  refine { (adj.homAddEquiv X Y).symm with map_smul' := ?_ }
  intro r f
  change (adj.homEquiv X Y).symm (r • f) = r • (adj.homEquiv X Y).symm f
  simp [Adjunction.homEquiv_counit, Functor.map_smul, Linear.smul_comp]

/-- A linear right adjoint of the centre forgetful functor, with the stated
underlying objects, gives the actual centre global FP-square formula. -/
theorem globalFPDimension_square_of_adjunction
    (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (I : C.Obj ⥤ CategoryTheory.Center C.Obj)
    (adj : CategoryTheory.Center.forget C.Obj ⊣ I)
    (hI : ∀ i, Nonempty ((I.obj (simples C i)).1 ≅ underlying C (simples C i))) :
    globalFPDimension (Integrate.bundledCenter C) = (globalFPDimension C) ^ 2 := by
  apply globalFPDimension_square_of_induction C (fun i => I.obj (simples C i)) hI
  intro i j
  exact (homLinearEquivOfAdjunction (CategoryTheory.Center.forget C.Obj) I adj
    (simples (Integrate.bundledCenter C) j) (simples C i)).finrank_eq

end PropertyF.Ground.CentreInduction
