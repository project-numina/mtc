module
public import MTC.Braided.Trace.PartialTrace
public import MTC.CategoryTheory.Dimensions.FourthDualUnit

open MTC.Fusion

open MTC.Braided

/-!
# Braiding traces and the pivotal twist.
-/

@[expose] public noncomputable section

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.CategoryTheory.Dimensions
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
  rw [braiding_naturality_right_assoc, rightUnitor_inv_braiding_assoc,
    ExactPairing.evaluation_coevaluation_assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc]

omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- A double-dual map satisfies the Drinfeld evaluation identity. -/
abbrev HasDrinfeldEvaluation {X : C} (d : X ≅ (Xᘁ)ᘁ) : Prop :=
  d.hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) = (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ)

omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
set_option backward.isDefEq.respectTransparency false in
/-- Closing self-braiding gives the pivotal twist determined by a compatible double-dual isomorphism. -/
theorem rightPartialTrace_braiding (p : PivotalStructure (C := C)) {X : C} (d : X ≅ (Xᘁ)ᘁ)
    (hd : HasDrinfeldEvaluation d) :
    MTC.Braided.Trace.rightPartialTrace p (End.of (β_ X X).hom) =
      End.of ((p.iso X).hom ≫ d.inv) :=
  End.ext (by
    dsimp only [HasDrinfeldEvaluation] at hd
    simp only [MTC.Braided.Trace.rightPartialTrace]
    let t : X ⟶ X := (p.iso X).hom ≫ d.inv
    have hclose : (p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
        t ▷ (Xᘁ) ≫ (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ) := by
      dsimp [t]
      simp only [comp_whiskerRight_assoc]
      rw [← hd, ← Category.assoc, ← comp_whiskerRight]
      simp
    rw [← whiskerLeft_comp_assoc, hclose]
    simp only [whiskerLeft_comp, Category.assoc]
    slice_lhs 3 6 => rw [braid_self_slide]
    simp only [Category.assoc]
    rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc, braided_self_close, Category.comp_id])
end MTC.CategoryTheory.Dimensions
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.CategoryTheory.Dimensions
universe v u
variable (C : MTC.Fusion.BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
/-- The pivotal/Drinfeld twist on an object. -/
def pivotalBraidedTwist (X : C.Obj) : X ≅ X :=
  p.iso X ≪≫ (MTC.Fusion.doubleDualIso C X).symm

/-- The ratio of natural pivotal and double-dual isomorphisms is natural. -/
theorem pivotalBraidedTwist_natural {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [RightRigidCategory D] (p : PivotalStructure (C := D)) (d : ∀ X : D, X ≅ (Xᘁ)ᘁ)
    (hd : ∀ {X Y : D} (f : X ⟶ Y), f ≫ (d Y).hom = (d X).hom ≫ (fᘁ)ᘁ)
    {X Y : D} (f : X ⟶ Y) :
    f ≫ ((p.iso Y).hom ≫ (d Y).inv) = ((p.iso X).hom ≫ (d X).inv) ≫ f := by
  apply (cancel_mono (d Y).hom).1
  simpa [Category.assoc, hd f] using p.naturality f
/-- The twist scalar of a simple object. -/
def pivotalBraidedTwistScalar (X : C.Obj) [Simple X] : ℂ :=
  letI : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  MTC.Fusion.simpleEndScalar (k := ℂ) X (End.of (pivotalBraidedTwist C p X).hom)

local notation "θₚ" => pivotalBraidedTwistScalar C p

/-- On a simple object the twist acts by its scalar. -/
theorem pivotalBraidedTwist_simple (X : C.Obj) [Simple X] :
    (pivotalBraidedTwist C p X).hom = θₚ X • 𝟙 X :=
  let : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  congrArg End.asHom (show End.of (pivotalBraidedTwist C p X).hom = θₚ X • (1 : End X) from
    (MTC.Fusion.simpleEndScalar (k := ℂ) X).injective (by simp [pivotalBraidedTwistScalar]))

/-- A simple twist scalar is nonzero. -/
theorem pivotalBraidedTwistScalar_ne_zero (X : C.Obj) [Simple X] :
    θₚ X ≠ 0 := fun hz ↦ id_nonzero X (by
      simpa [pivotalBraidedTwist_simple, hz] using (pivotalBraidedTwist C p X).hom_inv_id.symm)

/-- The trace of a simple self-braiding is twist scalar times dimension. -/
theorem pivotalTrace_selfBraiding (X : C.Obj) [Simple X] :
    MTC.Fusion.unitScalar C (p.rightTrace (β_ X X).hom) =
      θₚ X * pivotalDimension C p X := by
  have h : p.rightTrace (pivotalBraidedTwist C p X).hom = p.rightTrace (β_ X X).hom := by
    simpa only [pivotalBraidedTwist, Iso.trans_hom, Iso.symm_hom,
      rightPartialTrace_braiding p (MTC.Fusion.doubleDualIso C X) (drinfeld_eval X)] using
      rightTrace_partialTrace p (End.of (β_ X X).hom)
  simpa only [pivotalBraidedTwist_simple, PivotalStructure.rightTrace_smul,
    MTC.unitScalar_eq_equiv, map_smul, smul_eq_mul, pivotalDimension] using
      congrArg (MTC.Fusion.unitScalar C) h.symm

/-- The actual pivotal/Drinfeld twists form a natural automorphism. -/
def pivotalBraidedTwistNaturalIso : 𝟭 C.Obj ≅ 𝟭 C.Obj :=
  NatIso.ofComponents (pivotalBraidedTwist C p) (fun f ↦ by
    simpa only [Functor.id_map, pivotalBraidedTwist, Iso.trans_hom, Iso.symm_hom] using
      pivotalBraidedTwist_natural p (MTC.Fusion.doubleDualIso C) (fun f ↦ drinfeldIso_natural f) f)


end MTC.CategoryTheory.Dimensions
end
