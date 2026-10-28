module
public import PropertyF.Ground.CentreInduction.ForgetDualUnit
public import PropertyF.Ground.CentreInduction.PivotalTransfer
public import PropertyF.Ground.Centre.Product

section
/-! Lift a pivotal structure once its transported components are central. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]

/-- The sole remaining obstruction to lifting the pivotal structure is the
half-braiding intertwining equation for the transported components. -/
def PivotalComponentsCentral (p : Dimensions.PivotalStructure (C := C.Obj)) : Prop :=
  ∀ (Z : CategoryTheory.Center C.Obj) (T : C.Obj),
    let u := (p.iso Z.1).hom ≫ (forgetDoubleDualIso Z).inv
    (u ▷ T) ≫ (((Zᘁ)ᘁ).2.β T).hom = (Z.2.β T).hom ≫ (T ◁ u)

/-- Central transported components assemble into a pivotal structure on the
actual centre; naturality, tensor and unit coherence are proved. -/
def liftedPivotalStructure (p : Dimensions.PivotalStructure (C := C.Obj))
    (hc : PivotalComponentsCentral C p) :
    Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj) where
  iso Z := by
    let u := (p.iso Z.1).hom ≫ (forgetDoubleDualIso Z).inv
    let f : Z ⟶ ((Zᘁ)ᘁ) := ⟨u, hc Z⟩
    letI : IsIso f.f := by change IsIso u; dsimp only [u]; infer_instance
    exact CategoryTheory.Center.isoMk f
  naturality f := by
    apply CategoryTheory.Center.ext
    simpa only [CategoryTheory.Center.comp_f, CategoryTheory.Center.isoMk_hom, Category.assoc] using
      transported_pivotal_natural p f
  tensor X Y := by
    apply CategoryTheory.Center.ext
    simpa only [CategoryTheory.Center.comp_f, CategoryTheory.Center.tensor_f,
      CategoryTheory.Center.isoMk_hom, CategoryTheory.Center.tensor_fst] using
      (transported_pivotal_tensor p X Y).symm
  unit := by
    apply CategoryTheory.Center.ext
    simp only [CategoryTheory.Center.isoMk_hom]
    convert transported_pivotal_unit p using 1
    all_goals rfl

/-- The lifted component agrees with the original pivotal component. -/
theorem liftedPivotalStructure_compatible (p : Dimensions.PivotalStructure (C := C.Obj))
    (hc : PivotalComponentsCentral C p) (Z : CategoryTheory.Center C.Obj) :
    ((liftedPivotalStructure C p hc).iso Z).hom.f ≫ (forgetDoubleDualIso Z).hom =
      (p.iso Z.1).hom := by
  simp [liftedPivotalStructure, Category.assoc]

/-- Centrality of the transported pivotal components yields centre fusion,
positive sphericality, pseudo-unitarity and the categorical dimension square. -/
theorem center_structure_of_pivotal_centrality
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (hc : PivotalComponentsCentral C p) :
    ∃ hFusion : IsFusionCategory (CategoryTheory.Center C.Obj),
      letI := hFusion
      let pZ := liftedPivotalStructure C p hc
      pZ.IsSpherical ∧
      (∀ i, Dimensions.pivotalDimension (Integrate.bundledCenter C) pZ
        (simples (Integrate.bundledCenter C) i) =
          (fpSimple (Integrate.bundledCenter C) i : ℂ)) ∧
      PseudoUnitary (Integrate.bundledCenter C) ∧
      globalDimension (Integrate.bundledCenter C) = (globalFPDimension C : ℂ) ^ 2 :=
  center_structure_of_compatible_pivotal C p hsimple (liftedPivotalStructure C p hc)
    (liftedPivotalStructure_compatible C p hc)

end PropertyF.Ground.CentreInduction

end
end

/-! Pivotal components on canonical positive centre images. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]

/-- The positive centre embedding preserves right duals up to the canonical isomorphism. -/
def positiveDualIso (T : C.Obj) :
    ((CategoryTheory.Center.ofBraided C.Obj).obj T)ᘁ ≅
      (CategoryTheory.Center.ofBraided C.Obj).obj (Tᘁ) :=
  rightDualIso HasRightDual.exact (Centre.positiveExactPairing T (Tᘁ))

theorem positiveDualIso_forget (T : C.Obj) :
    (positiveDualIso C T).hom.f =
      (forgetDualIso ((CategoryTheory.Center.ofBraided C.Obj).obj T)).hom := by
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
    convert hc using 1; rfl
  unfold positiveDualIso forgetDualIso rightDualIso rightAdjointMate
  simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.rightUnitor_inv_f,
    CategoryTheory.Center.leftUnitor_hom_f, CategoryTheory.Center.whiskerLeft_f,
    CategoryTheory.Center.whiskerRight_f, CategoryTheory.Center.associator_inv_f,
    CategoryTheory.Center.id_f, hc']
  rfl

/-- The comparison between the double duals of an object and its positive lift. -/
def positiveDoubleDualIso (T : C.Obj) :
    (((CategoryTheory.Center.ofBraided C.Obj).obj T)ᘁ)ᘁ ≅
      (CategoryTheory.Center.ofBraided C.Obj).obj ((Tᘁ)ᘁ) :=
  Dimensions.rightDualIsoMap (positiveDualIso C T).symm ≪≫ positiveDualIso C (Tᘁ)

theorem positiveDualIso_inv_forget (T : C.Obj) :
    (positiveDualIso C T).inv.f =
      (forgetDualIso ((CategoryTheory.Center.ofBraided C.Obj).obj T)).inv := by
  apply (cancel_mono (forgetDualIso ((CategoryTheory.Center.ofBraided C.Obj).obj T)).hom).1
  rw [Iso.inv_hom_id]
  rw [← positiveDualIso_forget C T, ← CategoryTheory.Center.comp_f, Iso.inv_hom_id]
  rfl

theorem positiveDoubleDualIso_forget (T : C.Obj) :
    (positiveDoubleDualIso C T).hom.f =
      (forgetDoubleDualIso ((CategoryTheory.Center.ofBraided C.Obj).obj T)).hom := by
  let F := CategoryTheory.Center.ofBraided C.Obj
  let Z := F.obj T
  let e := positiveDualIso C T
  have hnat := forgetDualIso_natural e.inv
  have hi := positiveDualIso_inv_forget C T
  have ho := positiveDualIso_forget C (Tᘁ)
  simp only [positiveDoubleDualIso, Iso.trans_hom, Iso.symm_hom,
    Dimensions.rightDualIsoMap, CategoryTheory.Center.comp_f, forgetDoubleDualIso]
  change (e.invᘁ).f ≫ (positiveDualIso C (Tᘁ)).hom.f =
    (forgetDualIso (Zᘁ)).hom ≫ (forgetDualIso Z).invᘁ
  rw [ho]
  change (e.invᘁ).f ≫ (forgetDualIso (F.obj (Tᘁ))).hom = _
  change (e.invᘁ).f ≫ (forgetDualIso (F.obj (Tᘁ))).hom =
    (forgetDualIso (Zᘁ)).hom ≫ e.inv.fᘁ at hnat
  rw [hnat, hi]


theorem positiveDoubleDualIso_inv_forget (T : C.Obj) :
    (positiveDoubleDualIso C T).inv.f =
      (forgetDoubleDualIso ((CategoryTheory.Center.ofBraided C.Obj).obj T)).inv := by
  apply (cancel_mono (forgetDoubleDualIso ((CategoryTheory.Center.ofBraided C.Obj).obj T)).hom).1
  rw [Iso.inv_hom_id]
  rw [← positiveDoubleDualIso_forget C T, ← CategoryTheory.Center.comp_f, Iso.inv_hom_id]
  rfl

/-- The pivotal component transported to the positive centre lift. -/
def positivePivotalComponent (p : Dimensions.PivotalStructure (C := C.Obj)) (T : C.Obj) :
    (CategoryTheory.Center.ofBraided C.Obj).obj T ≅
      (((CategoryTheory.Center.ofBraided C.Obj).obj T)ᘁ)ᘁ :=
  (CategoryTheory.Center.ofBraided C.Obj).mapIso (p.iso T) ≪≫ (positiveDoubleDualIso C T).symm

theorem positivePivotalComponent_forget (p : Dimensions.PivotalStructure (C := C.Obj)) (T : C.Obj) :
    (positivePivotalComponent C p T).hom.f = (p.iso T).hom ≫
      (forgetDoubleDualIso ((CategoryTheory.Center.ofBraided C.Obj).obj T)).inv := by
  simp [positivePivotalComponent, positiveDoubleDualIso_inv_forget]

end PropertyF.Ground.CentreInduction
