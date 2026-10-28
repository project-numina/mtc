module
public import PropertyF.Ground.Centre.Abelian
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import PropertyF.Ground.Fusion.FunctorDimension

section
/-! Adjoint mates of centre half-braidings. The tensor law and the centrality
of the dual evaluation and coevaluation are not established here. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Integrate
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- A half-braiding is a natural isomorphism of the two tensor functors. -/
def halfBraidingIso (Z : CategoryTheory.Center C) : tensorLeft Z.1 ≅ tensorRight Z.1 :=
  NatIso.ofComponents Z.2.β (fun f => Z.2.naturality f)

/-- Mate the half-braiding through the left adjoints of the tensor functors. -/
def dualMateIso (Z : CategoryTheory.Center C) : tensorLeft (Z.1ᘁ) ≅ tensorRight (ᘁZ.1) := by
  let L := tensorLeftAdjunction Z.1 (Z.1ᘁ)
  let R := tensorRightAdjunction (ᘁZ.1) Z.1
  exact ((conjugateIsoEquiv L R).symm (halfBraidingIso Z)).symm

/-- Evaluating the mate at the unit identifies the chosen right and left duals. -/
def dualMateUnit (Z : CategoryTheory.Center C) : (Z.1ᘁ) ≅ (ᘁZ.1) :=
  (ρ_ (Z.1ᘁ)).symm ≪≫ (dualMateIso Z).app (𝟙_ C) ≪≫ (λ_ (ᘁZ.1))

/-- Normalize the mate using its unit component, obtaining a natural family
of isomorphisms on the chosen right dual. -/
def dualCrossingIso (Z : CategoryTheory.Center C) : tensorLeft (Z.1ᘁ) ≅ tensorRight (Z.1ᘁ) :=
  dualMateIso Z ≪≫ (tensoringRight C).mapIso (dualMateUnit Z).symm

/-- The normalized family is natural in the crossing object. -/
theorem dualCrossing_natural (Z : CategoryTheory.Center C) {U V : C} (f : U ⟶ V) :
    (Z.1ᘁ) ◁ f ≫ ((dualCrossingIso Z).app V).hom =
      ((dualCrossingIso Z).app U).hom ≫ f ▷ (Z.1ᘁ) :=
  (dualCrossingIso Z).hom.naturality f


end PropertyF.Ground.Integrate
end
end

/-! Bundle the actual centre conditionally on its remaining fusion proofs. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Integrate
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)]
variable [IsFusionCategory (CategoryTheory.Center C.Obj)]

/-- The actual centre, provided its unproved rigidity and finite
semisimplicity obligations are supplied as explicit instances. -/
def bundledCenter : BraidedFusionCategory.{v,max u v} where
  Obj := CategoryTheory.Center C.Obj

/-- The actual centre forgetful functor preserves FP dimension once the
centre is proved to be a rigid fusion category. -/
theorem center_forget_fpDimension (X : (bundledCenter C).Obj) :
    fpDimension C ((CategoryTheory.Center.forget C.Obj).obj X) = fpDimension (bundledCenter C) X :=
  let ha : (CategoryTheory.Center.forget C.Obj).Additive := Centre.centerForgetAdditive
  let hf : (CategoryTheory.Center.forget C.Obj).Faithful := Centre.centerForgetFaithful
  let hm : (CategoryTheory.Center.forget C.Obj).Monoidal := inferInstance
  @fpDimension_functor (bundledCenter C) C (CategoryTheory.Center.forget C.Obj) ha hf hm X

end PropertyF.Ground.Integrate
