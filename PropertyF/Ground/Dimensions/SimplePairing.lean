module
public import PropertyF.Ground.Dimensions.SimpleHomBasis
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

/-- A nonzero morphism to a simple object splits in the genuine fusion category. -/
theorem split_to_simple
    (X S : C.Obj) [Simple S] (g : X ⟶ S) (hg : g ≠ 0) :
    ∃ f : S ⟶ X, f ≫ g = 𝟙 S := by
  classical
  let e := simpleDecomposition C X
  let V := simplePiecesObject C X
  have he : e.inv ≫ g ≠ 0 := by
    intro h
    apply hg
    simpa [Category.assoc] using (congrArg (fun z => e.hom ≫ z) h)
  have hp : ∃ a, biproduct.ι V a ≫ e.inv ≫ g ≠ 0 := by
    by_contra h
    push Not at h
    apply he
    apply biproduct.hom_ext'
    intro a
    simpa [Category.assoc] using h a
  obtain ⟨a, ha⟩ := hp
  let : Simple (V a) := simples_simple C a.1
  let h : V a ⟶ S := biproduct.ι V a ≫ e.inv ≫ g
  let : IsIso h := isIso_of_hom_simple ha
  refine ⟨inv h ≫ biproduct.ι V a ≫ e.inv, ?_⟩
  simp [h, Category.assoc]

/-- Schur's scalar isomorphism for any simple object. -/
def simpleEndScalarEquiv (C : BraidedFusionCategory.{v,u})
    (S : C.Obj) [Simple S] : End S ≃ₐ[ℂ] ℂ := by
  letI : FiniteDimensional ℂ (S ⟶ S) := IsFusionCategory.hom_finite _ _
  apply (AlgEquiv.ofBijective (Algebra.ofId ℂ (End S)) ?_).symm
  constructor
  · exact (algebraMap ℂ (End S)).injective
  · intro f
    obtain ⟨z, hz⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ f.asHom
    refine ⟨z, ?_⟩
    apply End.ext
    simpa [Algebra.algebraMap_eq_smul_one] using hz

/-- Composition induces the scalar-valued pairing between morphisms to and
from a simple object. -/
def simpleHomPairing (C : BraidedFusionCategory.{v,u})
    (S X : C.Obj) [Simple S] : (X ⟶ S) →ₗ[ℂ] Module.Dual ℂ (S ⟶ X) where
  toFun g := {
    toFun := fun f => simpleEndScalarEquiv C S (End.of (f ≫ g))
    map_add' := by
      intro f f'
      simp only [Preadditive.add_comp]
      change simpleEndScalarEquiv C S (End.of (f ≫ g) + End.of (f' ≫ g)) = _
      exact map_add _ _ _
    map_smul' := by
      intro z f
      simp only [Linear.smul_comp]
      change simpleEndScalarEquiv C S (z • End.of (f ≫ g)) = z • _
      exact map_smul _ _ _ }
  map_add' := by
    intro g g'
    ext f
    simp only [Preadditive.comp_add]
    change simpleEndScalarEquiv C S (End.of (f ≫ g) + End.of (f ≫ g')) = _
    exact map_add _ _ _
  map_smul' := by
    intro z g
    ext f
    simp only [Linear.comp_smul]
    change simpleEndScalarEquiv C S (z • End.of (f ≫ g)) = z • _
    exact map_smul _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The composition pairing is nondegenerate in the morphism-to-simple factor. -/
theorem simpleHomPairing_injective
    (S X : C.Obj) [Simple S] : Function.Injective (simpleHomPairing C S X) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro g hg
  by_contra hne
  obtain ⟨f, hf⟩ := split_to_simple C X S g hne
  have h := congrArg (fun F : Module.Dual ℂ (S ⟶ X) => F f) hg
  change simpleEndScalarEquiv C S (End.of (f ≫ g)) = 0 at h
  rw [hf] at h
  have hh : simpleEndScalarEquiv C S 1 = 0 := h
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
