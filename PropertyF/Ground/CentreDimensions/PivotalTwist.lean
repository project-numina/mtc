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
set_option backward.isDefEq.respectTransparency false in
/-- Closing one strand of the self-braiding gives the pivotal/Drinfeld twist. -/
theorem rightPartialTrace_braiding (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) :
    Calculus.rightPartialTrace p X X (End.of (β_ X X).hom) =
      End.of ((p.iso X).hom ≫ (Ground.doubleDualIso C X).inv) := by
  apply End.ext
  simp only [Calculus.rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk]
  let t : X ⟶ X := (p.iso X).hom ≫ (Ground.doubleDualIso C X).inv
  have hclose : (p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      t ▷ (Xᘁ) ≫ (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ) := by
    dsimp [t]
    simp only [comp_whiskerRight_assoc]
    rw [← drinfeld_eval, ← Category.assoc, ← comp_whiskerRight]
    simp
  have hg : (ρ_ X).inv ≫ X ◁ η_ X (Xᘁ) ≫ (α_ X X (Xᘁ)).inv ≫
      (β_ X X).hom ▷ (Xᘁ) ≫ (α_ X X (Xᘁ)).hom ≫
      X ◁ ((p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ)) ≫ (ρ_ X).hom = t := by
    rw [hclose]
    simp only [whiskerLeft_comp]
    have hs : (α_ X X (Xᘁ)).inv ≫ (β_ X X).hom ▷ (Xᘁ) ≫ (α_ X X (Xᘁ)).hom ≫
        X ◁ (t ▷ (Xᘁ)) = (t ▷ (X ⊗ (Xᘁ))) ≫ (α_ X X (Xᘁ)).inv ≫
          (β_ X X).hom ▷ (Xᘁ) ≫ (α_ X X (Xᘁ)).hom := by
      have hb := braiding_naturality_left t X
      calc
        _ = (α_ X X (Xᘁ)).inv ≫ (((β_ X X).hom ≫ X ◁ t) ▷ (Xᘁ)) ≫
            (α_ X X (Xᘁ)).hom := by simp only [comp_whiskerRight]; monoidal
        _ = (α_ X X (Xᘁ)).inv ≫ ((t ▷ X ≫ (β_ X X).hom) ▷ (Xᘁ)) ≫
            (α_ X X (Xᘁ)).hom := by rw [← hb]
        _ = _ := by simp only [comp_whiskerRight]; monoidal
    simp only [Category.assoc]
    slice_lhs 3 6 => rw [hs]
    simp only [Category.assoc]
    rw [whisker_exchange_assoc]
    rw [← rightUnitor_inv_naturality_assoc]
    have hc : (ρ_ X).inv ≫ X ◁ η_ X (Xᘁ) ≫ (α_ X X (Xᘁ)).inv ≫
        (β_ X X).hom ▷ (Xᘁ) ≫ (α_ X X (Xᘁ)).hom ≫
        X ◁ (β_ X (Xᘁ)).hom ≫ X ◁ ε_ X (Xᘁ) ≫ (ρ_ X).hom = 𝟙 X := by
      slice_lhs 4 6 => rw [← hexagon_forward]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [braiding_naturality_right_assoc]
      rw [rightUnitor_inv_braiding_assoc, ExactPairing.evaluation_coevaluation_assoc]
      simp
    rw [hc, Category.comp_id]
  simpa only [whiskerLeft_comp, Category.assoc, t] using hg
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

/-- The pivotal/Drinfeld twist is natural. -/
theorem pivotalBraidedTwist_natural {X Y : C.Obj} (f : X ⟶ Y) :
    f ≫ (pivotalBraidedTwist C p Y).hom = (pivotalBraidedTwist C p X).hom ≫ f := by
  have hn : ((fᘁ)ᘁ) ≫ (Ground.doubleDualIso C Y).inv =
      (Ground.doubleDualIso C X).inv ≫ f := by
    apply (Ground.doubleDualIso C X).eq_inv_comp.mpr
    simpa only [Category.assoc] using
      (Ground.doubleDualIso C Y).comp_inv_eq.mpr (doubleDualIso_natural C f).symm
  simp only [pivotalBraidedTwist, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, p.naturality, Category.assoc, hn]
/-- The twist scalar of a simple object. -/
def pivotalBraidedTwistScalar (X : C.Obj) [Simple X] : ℂ :=
  letI : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  Ground.simpleEndScalar X (End.of (pivotalBraidedTwist C p X).hom)

/-- On a simple object the twist acts by its scalar. -/
theorem pivotalBraidedTwist_simple (X : C.Obj) [Simple X] :
    (pivotalBraidedTwist C p X).hom = pivotalBraidedTwistScalar C p X • 𝟙 X := by
  let : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  change (End.of (pivotalBraidedTwist C p X).hom).asHom =
    (pivotalBraidedTwistScalar C p X • (1 : End X)).asHom
  exact congrArg End.asHom ((Ground.simpleEndScalar X).injective (by simp [pivotalBraidedTwistScalar]))

/-- A simple twist scalar is nonzero. -/
theorem pivotalBraidedTwistScalar_ne_zero (X : C.Obj) [Simple X] :
    pivotalBraidedTwistScalar C p X ≠ 0 := by
  intro hz
  have ht := pivotalBraidedTwist_simple C p X
  rw [hz, zero_smul] at ht
  have hi := congrArg (fun f => f ≫ (pivotalBraidedTwist C p X).inv) ht
  simp at hi
  exact id_nonzero X hi

/-- The trace of a simple self-braiding is twist scalar times dimension. -/
theorem pivotalTrace_selfBraiding (X : C.Obj) [Simple X] :
    Ground.unitScalar C (p.rightTrace (β_ X X).hom) =
      pivotalBraidedTwistScalar C p X * pivotalDimension C p X := by
  have h := rightTrace_partialTrace p X X (End.of (β_ X X).hom)
  rw [rightPartialTrace_braiding] at h
  have ht : (p.iso X).hom ≫ (Ground.doubleDualIso C X).inv =
      pivotalBraidedTwistScalar C p X • 𝟙 X := pivotalBraidedTwist_simple C p X
  change p.rightTrace ((p.iso X).hom ≫ (Ground.doubleDualIso C X).inv) =
    p.rightTrace (β_ X X).hom at h
  rw [ht, PivotalStructure.rightTrace_smul] at h
  rw [← h]
  simp only [Ground.unitScalar_eq_equiv, map_smul, smul_eq_mul, pivotalDimension]

/-- The actual pivotal/Drinfeld twists form a natural automorphism. -/
def pivotalBraidedTwistNaturalIso : 𝟭 C.Obj ≅ 𝟭 C.Obj :=
  NatIso.ofComponents (pivotalBraidedTwist C p) (fun f => pivotalBraidedTwist_natural C p f)


end PropertyF.Ground.Dimensions
end
