module
public import PropertyF.Ground.CentreInduction.PivotalLift
public import PropertyF.Ground.Centre.Product

/-! Pivotal components on canonical positive centre images. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]

def positiveDualIso (T : C.Obj) :
    ((CategoryTheory.Center.ofBraided C.Obj).obj T)ᘁ ≅
      (CategoryTheory.Center.ofBraided C.Obj).obj (Tᘁ) :=
  rightDualIso HasRightDual.exact (Centre.positiveExactPairing T (Tᘁ))

theorem positiveDualIso_forget (T : C.Obj) :
    (positiveDualIso C T).hom.f =
      (forgetDualIso C ((CategoryTheory.Center.ofBraided C.Obj).obj T)).hom := by
  let F := CategoryTheory.Center.ofBraided C.Obj
  have hc : (@ExactPairing.coevaluation (CategoryTheory.Center C.Obj) _ _ (F.obj T) (F.obj (Tᘁ))
      (Centre.positiveExactPairing T (Tᘁ))).f = η_ T (Tᘁ) := by
    change (ε F ≫ F.map (η_ T (Tᘁ)) ≫ δ F T (Tᘁ)).f = _
    simp [F]
  change (@ExactPairing.coevaluation (CategoryTheory.Center C.Obj) _ _
    ((CategoryTheory.Center.ofBraided C.Obj).obj T) ((CategoryTheory.Center.ofBraided C.Obj).obj (Tᘁ))
    (Centre.positiveExactPairing T (Tᘁ))).f = η_ T (Tᘁ) at hc
  have hc' : (@ExactPairing.coevaluation (CategoryTheory.Center C.Obj) _ _
      ((CategoryTheory.Center.ofBraided C.Obj).obj T) ((CategoryTheory.Center.ofBraided C.Obj).obj (Tᘁ))
      (Centre.positiveExactPairing T (Tᘁ))).f =
      η_ ((CategoryTheory.Center.ofBraided C.Obj).obj T).1
        (((CategoryTheory.Center.ofBraided C.Obj).obj T).1ᘁ) := by
    convert hc using 1 <;> rfl
  unfold positiveDualIso forgetDualIso rightDualIso rightAdjointMate
  simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.rightUnitor_inv_f,
    CategoryTheory.Center.leftUnitor_hom_f, CategoryTheory.Center.whiskerLeft_f,
    CategoryTheory.Center.whiskerRight_f, CategoryTheory.Center.associator_inv_f,
    CategoryTheory.Center.id_f, hc']
  rfl

def positiveDoubleDualIso (T : C.Obj) :
    (((CategoryTheory.Center.ofBraided C.Obj).obj T)ᘁ)ᘁ ≅
      (CategoryTheory.Center.ofBraided C.Obj).obj ((Tᘁ)ᘁ) :=
  Dimensions.rightDualIsoMap (positiveDualIso C T).symm ≪≫ positiveDualIso C (Tᘁ)

theorem positiveDualIso_inv_forget (T : C.Obj) :
    (positiveDualIso C T).inv.f =
      (forgetDualIso C ((CategoryTheory.Center.ofBraided C.Obj).obj T)).inv := by
  apply (cancel_mono (forgetDualIso C ((CategoryTheory.Center.ofBraided C.Obj).obj T)).hom).1
  rw [Iso.inv_hom_id]
  rw [← positiveDualIso_forget C T, ← CategoryTheory.Center.comp_f, Iso.inv_hom_id]
  rfl

theorem positiveDoubleDualIso_forget (T : C.Obj) :
    (positiveDoubleDualIso C T).hom.f =
      (forgetDoubleDualIso C ((CategoryTheory.Center.ofBraided C.Obj).obj T)).hom := by
  let F := CategoryTheory.Center.ofBraided C.Obj
  let Z := F.obj T
  let e := positiveDualIso C T
  have hnat := forgetDualIso_natural C e.inv
  have hi := positiveDualIso_inv_forget C T
  have ho := positiveDualIso_forget C (Tᘁ)
  simp only [positiveDoubleDualIso, Iso.trans_hom, Iso.symm_hom,
    Dimensions.rightDualIsoMap, CategoryTheory.Center.comp_f, forgetDoubleDualIso]
  change (e.invᘁ).f ≫ (positiveDualIso C (Tᘁ)).hom.f =
    (forgetDualIso C (Zᘁ)).hom ≫ (forgetDualIso C Z).invᘁ
  rw [ho]
  change (e.invᘁ).f ≫ (forgetDualIso C (F.obj (Tᘁ))).hom = _
  change (e.invᘁ).f ≫ (forgetDualIso C (F.obj (Tᘁ))).hom =
    (forgetDualIso C (Zᘁ)).hom ≫ e.inv.fᘁ at hnat
  rw [hnat, hi]


theorem positiveDoubleDualIso_inv_forget (T : C.Obj) :
    (positiveDoubleDualIso C T).inv.f =
      (forgetDoubleDualIso C ((CategoryTheory.Center.ofBraided C.Obj).obj T)).inv := by
  apply (cancel_mono (forgetDoubleDualIso C ((CategoryTheory.Center.ofBraided C.Obj).obj T)).hom).1
  rw [Iso.inv_hom_id]
  rw [← positiveDoubleDualIso_forget C T, ← CategoryTheory.Center.comp_f, Iso.inv_hom_id]
  rfl

def positivePivotalComponent (p : Dimensions.PivotalStructure (C := C.Obj)) (T : C.Obj) :
    (CategoryTheory.Center.ofBraided C.Obj).obj T ≅
      (((CategoryTheory.Center.ofBraided C.Obj).obj T)ᘁ)ᘁ :=
  (CategoryTheory.Center.ofBraided C.Obj).mapIso (p.iso T) ≪≫ (positiveDoubleDualIso C T).symm

theorem positivePivotalComponent_forget (p : Dimensions.PivotalStructure (C := C.Obj)) (T : C.Obj) :
    (positivePivotalComponent C p T).hom.f = (p.iso T).hom ≫
      (forgetDoubleDualIso C ((CategoryTheory.Center.ofBraided C.Obj).obj T)).inv := by
  simp [positivePivotalComponent, positiveDoubleDualIso_inv_forget]

end PropertyF.Ground.CentreInduction
