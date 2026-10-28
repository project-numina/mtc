module
public import PropertyF.Ground.CentreIntegrate.TwistSign
public import PropertyF.Ground.CentreCabling.TwistDual
public import PropertyF.Ground.Fusion.Reciprocity
public import PropertyF.Ground.CentreIntegrate.MonodromyDual
public import PropertyF.Ground.Dimensions.PivotalPseudoUnitary
public import PropertyF.Ground.Dimensions.PivotalPseudoUnitary
public import PropertyF.Ground.Dimensions.DualBraiding
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open PropertyF.Ground PropertyF.Ground.Dimensions
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreIntegrate
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- In a spherical category, a simple and its right dual have the same
pivotal twist scalar. -/
theorem pivotalTwistScalar_rightDual (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    (hp : p.IsSpherical) (i : Fin (rank C)) :
    letI : Simple (simples C i) := simples_simple C i
    letI : Simple ((simples C i)ᘁ) := Ground.simple_rightDual C (simples C i)
    pivotalBraidedTwistScalar C p ((simples C i)ᘁ) = pivotalBraidedTwistScalar C p (simples C i) :=
  CentreCabling.spherical_twistScalar_rightDual C p hp i

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
  letI : Simple ((simples C i)ᘁ) := Ground.simple_rightDual C (simples C i)
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
