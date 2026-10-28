module
public import PropertyF.Ground.CentreDimensions.PivotalTwist
public import PropertyF.Ground.CentreInduction.PositivePivotal
public import PropertyF.Ground.Dimensions.DualTensorNaturality
public import PropertyF.Ground.Dimensions.DualBraiding
public import PropertyF.Ground.Dimensions.PivotalDual
public import PropertyF.Ground.Fusion.Reciprocity
public import PropertyF.Ground.Dimensions.SphericalReal

/-! Compatibility of pivotal twists with duals in spherical categories. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreCabling
universe v u

/-- Self-braiding traces of an object and its right dual agree in a spherical
braided category. -/
theorem spherical_selfBraiding_trace_dual
    (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical) (X : C.Obj) :
    p.rightTrace (β_ X X).hom = p.rightTrace (β_ (Xᘁ) (Xᘁ)).hom := by
  let e := rightDualTensorIso X X
  have hb := Dimensions.rightDualTensorIso_braiding X X
  change ((β_ X X).homᘁ) ≫ e.hom = e.hom ≫ (β_ (Xᘁ) (Xᘁ)).hom at hb
  have hc := p.rightTrace_cyclic e.hom ((β_ (Xᘁ) (Xᘁ)).hom ≫ e.inv)
  have heq : ((β_ X X).homᘁ) = e.hom ≫ (β_ (Xᘁ) (Xᘁ)).hom ≫ e.inv := by
    rw [← Category.assoc, ← hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    _ = p.rightTrace ((β_ X X).homᘁ) := by
      rw [← hp (X ⊗ X) ((β_ X X).hom), Dimensions.leftTrace_eq_rightTraceWith_dual,
        ← Dimensions.pivotal_dual p (X ⊗ X)]
      rfl
    _ = p.rightTrace (e.hom ≫ (β_ (Xᘁ) (Xᘁ)).hom ≫ e.inv) := by rw [heq]
    _ = _ := by simpa [Category.assoc] using hc

/-- A spherical pivotal twist has equal simple scalars on an object and its
right dual. -/
theorem spherical_twistScalar_rightDual
    (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (i : Fin (rank C)) :
    let X := simples C i
    letI : Simple X := simples_simple C i
    letI : Simple (Xᘁ) := Ground.simple_rightDual C X
    Dimensions.pivotalBraidedTwistScalar C p (Xᘁ) =
      Dimensions.pivotalBraidedTwistScalar C p X := by
  let X := simples C i
  letI : Simple X := simples_simple C i
  letI : Simple (Xᘁ) := Ground.simple_rightDual C X
  have hb := congrArg (Ground.unitScalar C) (spherical_selfBraiding_trace_dual C p hp X)
  rw [Dimensions.pivotalTrace_selfBraiding, Dimensions.pivotalTrace_selfBraiding] at hb
  have hd : Dimensions.pivotalDimension C p (Xᘁ) = Dimensions.pivotalDimension C p X := by
    have h := Dimensions.pivotal_leftTrace_id_eq_rightTrace_dual p X
    rw [hp] at h
    exact (congrArg (Ground.unitScalar C) h).symm
  rw [hd] at hb
  have hn : Dimensions.pivotalDimension C p X ≠ 0 :=
    Dimensions.pivotalDimension_simple_ne_zero C p i
  exact (mul_right_cancel₀ hn hb).symm

end PropertyF.Ground.CentreCabling
