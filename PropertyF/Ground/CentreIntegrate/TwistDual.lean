module
public import PropertyF.Ground.CentreIntegrate.TwistSign
public import PropertyF.Ground.CentreIntegrate.MonodromyDual
public import PropertyF.Ground.Dimensions.PivotalDual
public import PropertyF.Ground.Dimensions.SphericalReal
public import PropertyF.Ground.Dimensions.DualBraiding
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open PropertyF.Ground PropertyF.Ground.Dimensions
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreIntegrate
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- Spherical traces are invariant under taking the right dual. -/
theorem spherical_rightTrace_rightDual {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    (p : PivotalStructure (C := C)) (hp : p.IsSpherical) {X : C} (f : X ⟶ X) :
    p.rightTrace (fᘁ) = p.rightTrace f := by
  have h := leftTrace_eq_rightTraceWith_dual p f
  rw [← pivotal_dual p X] at h
  change p.leftTrace f = p.rightTrace (fᘁ) at h
  exact h.symm.trans (hp X f)

/-- In a spherical category, a simple and its right dual have the same
pivotal twist scalar. -/
theorem pivotalTwistScalar_rightDual (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    (hp : p.IsSpherical) (i : Fin (rank C)) :
    letI : Simple (simples C i) := simples_simple C i
    letI : Simple ((simples C i)ᘁ) := simple_rightDual C (simples C i)
    pivotalBraidedTwistScalar C p ((simples C i)ᘁ) = pivotalBraidedTwistScalar C p (simples C i) := by
  let X := simples C i
  letI : Simple X := simples_simple C i
  letI : Simple (Xᘁ) := simple_rightDual C X
  let e := rightDualTensorIso X X
  have hb := rightDualTensorIso_braiding X X
  have hc : (β_ (Xᘁ) (Xᘁ)).hom = e.inv ≫ ((β_ X X).homᘁ) ≫ e.hom := by
    apply (cancel_epi e.hom).1
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, e] using hb.symm
  have ht := p.rightTrace_cyclic e.inv (((β_ X X).homᘁ) ≫ e.hom)
  have htr : p.rightTrace (β_ (Xᘁ) (Xᘁ)).hom = p.rightTrace (β_ X X).hom := by
    rw [hc, ht]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact spherical_rightTrace_rightDual p hp _
  have hd : pivotalDimension C p (Xᘁ) = pivotalDimension C p X := by
    unfold pivotalDimension
    rw [← rightAdjointMate_id (X := X), spherical_rightTrace_rightDual p hp]
  have h1 := pivotalTrace_selfBraiding C p X
  have h2 := pivotalTrace_selfBraiding C p (Xᘁ)
  rw [htr, hd, h1] at h2
  apply mul_right_cancel₀ _ h2.symm
  exact pivotalDimension_simple_ne_zero C p i

/-- The parity sign remains only the multiplicativity of the twist on the
simple/dual pair, for a spherical pivotal structure. -/
theorem twist_sign_of_spherical_dual_pair_tensor
    (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    (hp : p.IsSpherical) (i : Fin (rank C))
    (htensor : (pivotalBraidedTwist C p ((simples C i) ⊗ ((simples C i)ᘁ))).hom =
      (pivotalBraidedTwist C p (simples C i)).hom ⊗ₘ
        (pivotalBraidedTwist C p ((simples C i)ᘁ)).hom) :
    letI : Simple (simples C i) := simples_simple C i
    pivotalBraidedTwistScalar C p (simples C i) = 1 ∨
      pivotalBraidedTwistScalar C p (simples C i) = -1 := by
  letI : Simple (simples C i) := simples_simple C i
  letI : Simple ((simples C i)ᘁ) := simple_rightDual C (simples C i)
  apply twist_sign_of_dual_and_tensor C p i ?_ htensor
  rw [pivotalBraidedTwist_simple, pivotalTwistScalar_rightDual C p hp i]

/-- Once pivotal twist balancing is known on the simple/dual pair,
self-transparency gives the super-parity sign. -/
theorem twist_sign_of_spherical_self_transparency_and_balancing
    (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    (hp : p.IsSpherical) (i : Fin (rank C))
    (hself : Modular.doubleBraiding (simples C i) (simples C i) = 𝟙 _)
    (hbal : (pivotalBraidedTwist C p ((simples C i) ⊗ ((simples C i)ᘁ))).hom =
      Modular.doubleBraiding (simples C i) ((simples C i)ᘁ) ≫
        ((pivotalBraidedTwist C p (simples C i)).hom ⊗ₘ
          (pivotalBraidedTwist C p ((simples C i)ᘁ)).hom)) :
    letI : Simple (simples C i) := simples_simple C i
    pivotalBraidedTwistScalar C p (simples C i) = 1 ∨
      pivotalBraidedTwistScalar C p (simples C i) = -1 := by
  apply twist_sign_of_spherical_dual_pair_tensor C p hp i
  rw [hbal, self_doubleBraiding_eq_one_rightDual C (simples C i) hself, Category.id_comp]

end PropertyF.Ground.CentreIntegrate
