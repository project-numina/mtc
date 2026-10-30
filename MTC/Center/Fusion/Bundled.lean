module
public import MTC.Center.Abelian
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import MTC.Fusion.ObjectDimension

open MTC.Fusion

open MTC.Braided

/-! # Dual half-braidings and the bundled centre

Adjoint mates of half-braidings give the candidate dual crossing. When rigidity
and fusion instances are available, the centre bundles as a braided fusion
category and its forgetful functor preserves Frobenius–Perron dimension.

## Main results

* `dualCrossingIso` constructs the natural crossing for a dual object.
* `bundledCenter` packages the centre using its rigidity and fusion instances.
* `center_forget_fpDimension` shows that forgetting preserves FP dimension. -/

section

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.PropertyF.Reduction
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [LeftRigidCategory C] [RightRigidCategory C]
variable (Z : CategoryTheory.Center C)

/-- A half-braiding is a natural isomorphism of the two tensor functors. -/
def halfBraidingIso : tensorLeft Z.1 ≅ tensorRight Z.1 :=
  NatIso.ofComponents Z.2.β (fun f => Z.2.naturality f)

/-- Mate the half-braiding through the left adjoints of the tensor functors. -/
def dualMateIso : tensorLeft (Z.1ᘁ) ≅ tensorRight (ᘁZ.1) := by
  let L := tensorLeftAdjunction Z.1 (Z.1ᘁ)
  let R := tensorRightAdjunction (ᘁZ.1) Z.1
  exact ((conjugateIsoEquiv L R).symm (halfBraidingIso Z)).symm

/-- Evaluating the mate at the unit identifies the chosen right and left duals. -/
def dualMateUnit : (Z.1ᘁ) ≅ (ᘁZ.1) :=
  (ρ_ (Z.1ᘁ)).symm ≪≫ (dualMateIso Z).app (𝟙_ C) ≪≫ (λ_ (ᘁZ.1))

/-- Normalize the mate using its unit component, obtaining a natural family
of isomorphisms on the chosen right dual. -/
def dualCrossingIso : tensorLeft (Z.1ᘁ) ≅ tensorRight (Z.1ᘁ) :=
  dualMateIso Z ≪≫ (tensoringRight C).mapIso (dualMateUnit Z).symm

/-- The normalized family is natural in the crossing object. -/
theorem dualCrossing_natural {U V : C} (f : U ⟶ V) :
    (Z.1ᘁ) ◁ f ≫ ((dualCrossingIso Z).app V).hom =
      ((dualCrossingIso Z).app U).hom ≫ f ▷ (Z.1ᘁ) :=
  (dualCrossingIso Z).hom.naturality f

end MTC.PropertyF.Reduction
end
end

/-! Bundle the actual centre conditionally on its remaining fusion proofs. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.PropertyF.Reduction
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)]
variable [IsFusionCategory (CategoryTheory.Center C.Obj)]

/-- The actual centre, equipped with supplied rigidity and fusion instances. -/
def bundledCenter : BraidedFusionCategory.{v,max u v} where
  Obj := CategoryTheory.Center C.Obj

/-- The actual centre forgetful functor preserves FP dimension once the
centre is proved to be a rigid fusion category. -/
theorem center_forget_fpDimension (X : (bundledCenter C).Obj) :
    fpDimension C X.1 = fpDimension (bundledCenter C) X :=
  @fpDimension_functor (bundledCenter C) C (CategoryTheory.Center.forget C.Obj)
    MTC.Center.centerForgetAdditive MTC.Center.centerForgetFaithful
    (show (CategoryTheory.Center.forget C.Obj).Monoidal from inferInstance) X

end MTC.PropertyF.Reduction
