module
public import PropertyF.Ground.Dimensions.SimpleHomBasis
public import PropertyF.Ground.Fusion.SemisimpleSplit
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Pairings with simple objects

Composition gives a nondegenerate linear pairing between morphism spaces to and from a simple object.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Composition induces the scalar-valued pairing between morphisms to and
from a simple object. -/
def simpleHomPairing (C : BraidedFusionCategory.{v,u})
    (S X : C.Obj) [Simple S] : (X ⟶ S) →ₗ[ℂ] Module.Dual ℂ (S ⟶ X) := by
  letI : FiniteDimensional ℂ (S ⟶ S) := IsFusionCategory.hom_finite _ _
  exact {
    toFun g := {
      toFun := fun f => Ground.simpleEndScalar S (End.of (f ≫ g))
      map_add' := by
        intro f f'
        simp only [Preadditive.add_comp]
        change Ground.simpleEndScalar S (End.of (f ≫ g) + End.of (f' ≫ g)) = _
        exact map_add _ _ _
      map_smul' := by
        intro z f
        simp only [Linear.smul_comp]
        change Ground.simpleEndScalar S (z • End.of (f ≫ g)) = z • _
        exact map_smul _ _ _ }
    map_add' := by
      intro g g'
      ext f
      simp only [Preadditive.comp_add]
      change Ground.simpleEndScalar S (End.of (f ≫ g) + End.of (f ≫ g')) = _
      exact map_add _ _ _
    map_smul' := by
      intro z g
      ext f
      simp only [Linear.comp_smul]
      change Ground.simpleEndScalar S (z • End.of (f ≫ g)) = z • _
      exact map_smul _ _ _
  }

set_option backward.isDefEq.respectTransparency false in
/-- The composition pairing is nondegenerate in the morphism-to-simple factor. -/
theorem simpleHomPairing_injective
    (S X : C.Obj) [Simple S] : Function.Injective (simpleHomPairing C S X) := by
  let : FiniteDimensional ℂ (S ⟶ S) := IsFusionCategory.hom_finite _ _
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro g hg
  by_contra hne
  obtain ⟨f, hf⟩ := Ground.split_to_simple C g hne
  have h := congrArg (fun F : Module.Dual ℂ (S ⟶ X) => F f) hg
  change Ground.simpleEndScalar S (End.of (f ≫ g)) = 0 at h
  rw [hf] at h
  have hh : Ground.simpleEndScalar S 1 = 0 := h
  simp at hh

/-- The composition pairing is perfect for each representative simple. -/
def simpleHomPairingEquiv (C : BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) (X : C.Obj) :
    (X ⟶ simples C i) ≃ₗ[ℂ] Module.Dual ℂ (simples C i ⟶ X) := by
  letI : Simple (simples C i) := simples_simple C i
  letI : FiniteDimensional ℂ (X ⟶ simples C i) := IsFusionCategory.hom_finite _ _
  letI : FiniteDimensional ℂ (simples C i ⟶ X) := IsFusionCategory.hom_finite _ _
  let p := simpleHomPairing C (simples C i) X
  have hi := simpleHomPairing_injective C (simples C i) X
  have hd : Module.finrank ℂ (X ⟶ simples C i) =
      Module.finrank ℂ (Module.Dual ℂ (simples C i ⟶ X)) := by
    rw [Subspace.dual_finrank_eq]
    exact finrank_to_simple_eq_from_simple C X i
  exact LinearEquiv.ofBijective p ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 hi⟩

/-- Composition pairs precomposition on one Hom space with postcomposition on
the other. -/
theorem simpleHomPairing_natural
    (S X : C.Obj) [Simple S] (g : X ⟶ S) (a : X ⟶ X) :
    simpleHomPairing C S X (a ≫ g) =
      Module.Dual.transpose (Linear.rightComp ℂ S a) (simpleHomPairing C S X g) := by
  ext f
  simp [simpleHomPairing, Module.Dual.transpose_apply, Linear.rightComp_apply, Category.assoc]

end PropertyF.Ground.Dimensions
