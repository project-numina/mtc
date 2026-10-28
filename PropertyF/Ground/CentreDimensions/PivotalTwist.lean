module
public import PropertyF.Ground.Calculus.PartialTrace
public import PropertyF.Ground.Dimensions.FourthDualUnit

/-!
# Braiding traces and the pivotal twist.
-/

@[expose] public noncomputable section

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

omit [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- An endomorphism slides across the first self-braiding. -/
theorem braid_self_slide (X A : C) (t : X ⟶ X) :
    (α_ X X A).inv ≫ (β_ X X).hom ▷ A ≫ (α_ X X A).hom ≫ X ◁ (t ▷ A) =
      (t ▷ (X ⊗ A)) ≫ (α_ X X A).inv ≫ (β_ X X).hom ▷ A ≫ (α_ X X A).hom := by
  calc
    _ = (α_ X X A).inv ≫ (((β_ X X).hom ≫ X ◁ t) ▷ A) ≫ (α_ X X A).hom := by monoidal
    _ = (α_ X X A).inv ≫ ((t ▷ X ≫ (β_ X X).hom) ▷ A) ≫ (α_ X X A).hom := by
      rw [← braiding_naturality_left t X]
    _ = _ := by monoidal

omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- Closing a braided strand against its dual gives the identity. -/
theorem braided_self_close (X : C) :
    (ρ_ X).inv ≫ X ◁ η_ X (Xᘁ) ≫ (α_ X X (Xᘁ)).inv ≫
      (β_ X X).hom ▷ (Xᘁ) ≫ (α_ X X (Xᘁ)).hom ≫
      X ◁ (β_ X (Xᘁ)).hom ≫ X ◁ ε_ X (Xᘁ) ≫ (ρ_ X).hom = 𝟙 X := by
  slice_lhs 4 6 => rw [← hexagon_forward]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [braiding_naturality_right_assoc]
  rw [rightUnitor_inv_braiding_assoc, ExactPairing.evaluation_coevaluation_assoc,
    Iso.inv_hom_id, Iso.inv_hom_id_assoc]

omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- A double-dual map satisfies the Drinfeld evaluation identity. -/
abbrev HasDrinfeldEvaluation {X : C} (d : X ≅ (Xᘁ)ᘁ) : Prop :=
  d.hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) = (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ)

set_option backward.isDefEq.respectTransparency false in
/-- Closing self-braiding gives the pivotal twist determined by a compatible double-dual isomorphism. -/
theorem rightPartialTrace_braiding (p : PivotalStructure (C := C)) {X : C} (d : X ≅ (Xᘁ)ᘁ)
    (hd : HasDrinfeldEvaluation d) :
    Calculus.rightPartialTrace p (End.of (β_ X X).hom) =
      End.of ((p.iso X).hom ≫ d.inv) :=
  End.ext (by
    dsimp only [HasDrinfeldEvaluation] at hd
    simp only [Calculus.rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk]
    let t : X ⟶ X := (p.iso X).hom ≫ d.inv
    have hclose : (p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
        t ▷ (Xᘁ) ≫ (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ) := by
      dsimp [t]
      simp only [comp_whiskerRight_assoc]
      rw [← hd, ← Category.assoc, ← comp_whiskerRight]
      simp
    have hg : (ρ_ X).inv ≫ X ◁ η_ X (Xᘁ) ≫ (α_ X X (Xᘁ)).inv ≫
        (β_ X X).hom ▷ (Xᘁ) ≫ (α_ X X (Xᘁ)).hom ≫
        X ◁ ((p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ)) ≫ (ρ_ X).hom = t := by
      rw [hclose]
      simp only [whiskerLeft_comp]
      simp only [Category.assoc]
      slice_lhs 3 6 => rw [braid_self_slide]
      simp only [Category.assoc]
      rw [whisker_exchange_assoc]
      rw [← rightUnitor_inv_naturality_assoc]
      rw [braided_self_close, Category.comp_id]
    simpa only [whiskerLeft_comp, Category.assoc, t] using hg)
end PropertyF.Ground.Dimensions
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable (C : Ground.BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
/-- The pivotal/Drinfeld twist on an object. -/
def pivotalBraidedTwist (X : C.Obj) : X ≅ X :=
  p.iso X ≪≫ (Ground.doubleDualIso C X).symm

/-- The ratio of natural pivotal and double-dual isomorphisms is natural. -/
theorem pivotalBraidedTwist_natural {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [RightRigidCategory D] (p : PivotalStructure (C := D)) (d : ∀ X : D, X ≅ (Xᘁ)ᘁ)
    (hd : ∀ {X Y : D} (f : X ⟶ Y), f ≫ (d Y).hom = (d X).hom ≫ (fᘁ)ᘁ)
    {X Y : D} (f : X ⟶ Y) :
    f ≫ ((p.iso Y).hom ≫ (d Y).inv) = ((p.iso X).hom ≫ (d X).inv) ≫ f := by
  have hn : ((fᘁ)ᘁ) ≫ (d Y).inv = (d X).inv ≫ f := by
    apply (d X).eq_inv_comp.mpr
    simpa only [Category.assoc] using (d Y).comp_inv_eq.mpr (hd f).symm
  simpa only [Category.assoc, hn] using
    congrArg (fun g ↦ g ≫ (d Y).inv) (p.naturality f)
/-- The twist scalar of a simple object. -/
def pivotalBraidedTwistScalar (X : C.Obj) [Simple X] : ℂ :=
  letI : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  Ground.simpleEndScalar X (End.of (pivotalBraidedTwist C p X).hom)

local notation "θₚ" => pivotalBraidedTwistScalar C p

/-- On a simple object the twist acts by its scalar. -/
theorem pivotalBraidedTwist_simple (X : C.Obj) [Simple X] :
    (pivotalBraidedTwist C p X).hom = θₚ X • 𝟙 X :=
  let : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  congrArg End.asHom (show End.of (pivotalBraidedTwist C p X).hom = θₚ X • (1 : End X) from
    (Ground.simpleEndScalar X).injective (by simp [pivotalBraidedTwistScalar]))

/-- A simple twist scalar is nonzero. -/
theorem pivotalBraidedTwistScalar_ne_zero (X : C.Obj) [Simple X] :
    θₚ X ≠ 0 := fun hz ↦ id_nonzero X (by
      simpa [pivotalBraidedTwist_simple, hz] using (pivotalBraidedTwist C p X).hom_inv_id.symm)

/-- The trace of a simple self-braiding is twist scalar times dimension. -/
theorem pivotalTrace_selfBraiding (X : C.Obj) [Simple X] :
    Ground.unitScalar C (p.rightTrace (β_ X X).hom) =
      θₚ X * pivotalDimension C p X := by
  have h := rightTrace_partialTrace p (End.of (β_ X X).hom)
  rw [rightPartialTrace_braiding p (Ground.doubleDualIso C X) (drinfeld_eval C X)] at h
  change p.rightTrace (pivotalBraidedTwist C p X).hom = p.rightTrace (β_ X X).hom at h
  rw [pivotalBraidedTwist_simple, PivotalStructure.rightTrace_smul] at h
  rw [← h]
  simp only [Ground.unitScalar_eq_equiv, map_smul, smul_eq_mul, pivotalDimension]

/-- The actual pivotal/Drinfeld twists form a natural automorphism. -/
def pivotalBraidedTwistNaturalIso : 𝟭 C.Obj ≅ 𝟭 C.Obj :=
  NatIso.ofComponents (pivotalBraidedTwist C p) (fun f ↦ by
    simpa only [Functor.id_map, pivotalBraidedTwist, Iso.trans_hom, Iso.symm_hom] using
      pivotalBraidedTwist_natural p (Ground.doubleDualIso C) (fun f ↦ doubleDualIso_natural C f) f)


end PropertyF.Ground.Dimensions
end
