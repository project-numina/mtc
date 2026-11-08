module
public import MTC.PropertyF.Pivotal.NondegeneracyHaarSnake

open MTC.Fusion MTC.Modular MTC.CategoryTheory.Dimensions MTC.Center.Induction MTC.Center.Trace
open scoped BigOperators
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
attribute [local instance] IsFusionCategory.hom_finite
local instance (j : Fin (rank C)) : Simple ((simples C j)ᘁ) := by
  let : Simple (simples C j) := simples_simple C j
  exact simple_rightDual _

/-- The rotated fusion block: open a pivotal cup for X, apply the
projection mate, the actual boxed morphism, and the inclusion mate, and
then close the X strand. -/
def haarRotatedBlock (X Y U V : C.Obj) (β : End (X ⊗ V))
    (a : (Yᘁ) ⟶ U ⊗ (Xᘁ)) (b : U ⊗ (Xᘁ) ⟶ (Yᘁ)) : U ⊗ V ⟶ U ⊗ V :=
  𝟙 (U ⊗ V) ⊗≫
    (U ◁ ((η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv) ▷ V)) ⊗≫
    (b ▷ (X ⊗ V)) ⊗≫ ((Yᘁ) ◁ β.asHom) ⊗≫ (a ▷ (X ⊗ V)) ⊗≫
    (U ◁ (ε_ X (Xᘁ) ▷ V)) ⊗≫ 𝟙 (U ⊗ V)

/-- The rotated block is bilinear in the two actual mate morphisms. -/
def haarRotatedBilinear (X Y U V : C.Obj) (β : End (X ⊗ V)) :
    ((Yᘁ) ⟶ U ⊗ (Xᘁ)) →ₗ[ℂ] (U ⊗ (Xᘁ) ⟶ (Yᘁ)) →ₗ[ℂ] (U ⊗ V ⟶ U ⊗ V) where
  toFun a := {
    toFun := fun b => haarRotatedBlock C p X Y U V β a b
    map_add' := by intro b c; simp [haarRotatedBlock, monoidalComp]
    map_smul' := by intro r b; simp [haarRotatedBlock, monoidalComp] }
  map_add' := by intro a b; ext c; simp [haarRotatedBlock, monoidalComp]
  map_smul' := by intro r a; ext b; simp [haarRotatedBlock, monoidalComp]

/-- The actual rotated-block contraction can be evaluated in any basis of
the dual-simple Hom space. -/
theorem haarRotatedBlock_contraction (U V : C.Obj) (i j : Fin (rank C))
    {I : Type} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℂ (((simples C j)ᘁ) ⟶ U ⊗ ((simples C i)ᘁ)))
    (β : End (simples C i ⊗ V)) :
    (∑ a, haarRotatedBlock C p (simples C i) (simples C j) U V β
      (haarInclusionMate C (simples C i) (simples C j) U
        (simpleInclusion C (simples C j ⊗ U) i a))
      (simpleDimension C p j • haarProjectionMate C p (simples C i) (simples C j) U
        (pivotalTraceDualProjection C p (simples C j ⊗ U) i a))) =
    ∑ a, haarRotatedBlock C p (simples C i) (simples C j) U V β (b a)
      ((simpleHomPairingEquiv ((simples C j)ᘁ) (U ⊗ ((simples C i)ᘁ))).symm (b.dualBasis a)) := by
  classical
  exact haar_mated_contraction_basis_independent C p U i j b
    (haarRotatedBilinear C p (simples C i) (simples C j) U V β)

end MTC.PropertyF.Pivotal
end
