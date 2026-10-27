module
public import PropertyF.Ground.Target
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-! Finite-dimensional complex vector spaces instantiate the ground category
interface. This checks that its categorical properties are simultaneously
satisfiable; it does not assert property F or pseudo-unitarity. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Example

attribute [local instance] Abelian.hasFiniteBiproducts

local instance : RigidCategory (FGModuleCat ℂ) :=
  BraidedCategory.rigidCategoryOfRightRigidCategory

abbrev V := FGModuleCat.{0} ℂ
abbrev F : V ⥤ ModuleCat ℂ := forget₂ _ _

theorem unitSimple : Simple (𝟙_ V) := by
  let : Simple (F.obj (𝟙_ V)) := by
    change Simple (ModuleCat.of ℂ ℂ)
    infer_instance
  exact Functor.simple_of_simple_obj F _

/-- Every finite-dimensional complex vector space is a finite direct sum of
copies of the tensor unit. The isomorphism is induced by a basis. -/
instance : IsFusionCategory V where
  hom_finite := by intro X Y; infer_instance
  unit_simple := unitSimple
  finite_semisimple := by
    refine ⟨1, fun _ => 𝟙_ V, ?_, ?_, ?_⟩
    · intro i; exact unitSimple
    · intro i j _; exact Subsingleton.elim i j
    · intro X
      classical
      let m : Fin 1 → ℕ := fun _ => Module.finrank ℂ X
      refine ⟨m, ?_⟩
      let J := Σ i, Fin (m i)
      let f : J → V := fun _ => 𝟙_ V
      let e : J ≃ Fin (Module.finrank ℂ X) := Equiv.uniqueSigma _
      let b := (Module.finBasis ℂ X).repr.trans (Finsupp.linearEquivFunOnFinite ℂ ℂ _)
      let p : (Fin (Module.finrank ℂ X) → ℂ) ≃ₗ[ℂ] (J → ℂ) :=
        LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) e.symm
      let v : F.obj X ≅ ModuleCat.of ℂ (J → ℂ) := (b.trans p).toModuleIso
      have h : F.obj (⨁ f) ≅ ModuleCat.of ℂ (J → ℂ) :=
        F.mapBiproduct f ≪≫ ModuleCat.biproductIsoPi _
      exact ⟨F.preimageIso (v ≪≫ h.symm)⟩

/-- An actual, nontrivial inhabitant of the category type in the target. -/
def complexVectorSpaces : BraidedFusionCategory.{0,1} where
  Obj := V

end PropertyF.Ground.Example
