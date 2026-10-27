module
public import PropertyF.Ground.CentreInduction.ForgetDualUnit
public import PropertyF.Ground.CentreInduction.PivotalTransfer

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
    let u := (p.iso Z.1).hom ≫ (forgetDoubleDualIso C Z).inv
    (u ▷ T) ≫ (((Zᘁ)ᘁ).2.β T).hom = (Z.2.β T).hom ≫ (T ◁ u)

/-- Central transported components assemble into a pivotal structure on the
actual centre; naturality, tensor and unit coherence are proved. -/
def liftedPivotalStructure (p : Dimensions.PivotalStructure (C := C.Obj))
    (hc : PivotalComponentsCentral C p) :
    Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj) where
  iso Z := by
    let u := (p.iso Z.1).hom ≫ (forgetDoubleDualIso C Z).inv
    let f : Z ⟶ ((Zᘁ)ᘁ) := ⟨u, hc Z⟩
    letI : IsIso f.f := by change IsIso u; dsimp only [u]; infer_instance
    exact CategoryTheory.Center.isoMk f
  naturality f := by
    apply CategoryTheory.Center.ext
    simpa only [CategoryTheory.Center.comp_f, CategoryTheory.Center.isoMk_hom, Category.assoc] using
      transported_pivotal_natural C p f
  tensor X Y := by
    apply CategoryTheory.Center.ext
    simpa only [CategoryTheory.Center.comp_f, CategoryTheory.Center.tensor_f,
      CategoryTheory.Center.isoMk_hom, CategoryTheory.Center.tensor_fst] using
      (transported_pivotal_tensor C p X Y).symm
  unit := by
    apply CategoryTheory.Center.ext
    simp only [CategoryTheory.Center.isoMk_hom]
    convert transported_pivotal_unit C p using 1
    all_goals rfl

/-- The lifted component agrees with the original pivotal component. -/
theorem liftedPivotalStructure_compatible (p : Dimensions.PivotalStructure (C := C.Obj))
    (hc : PivotalComponentsCentral C p) (Z : CategoryTheory.Center C.Obj) :
    ((liftedPivotalStructure C p hc).iso Z).hom.f ≫ (forgetDoubleDualIso C Z).hom =
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
