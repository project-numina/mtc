module
public import PropertyF.Ground.CentreInduction.WeakHalfBraiding

/-! Unit normalization and invertibility of the proposed induction crossing. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
private def unitCanonical : underlyingFunctor C ⋙ tensorRight (𝟙_ C.Obj) ⟶
    underlyingFunctor C ⋙ tensorLeft (𝟙_ C.Obj) where
  app X := (ρ_ (underlying C X)).hom ≫ (λ_ (underlying C X)).inv
  naturality {X Y} f := by
    let g : underlying C X ⟶ underlying C Y := (underlyingFunctor C).map f
    change (g ▷ (𝟙_ C.Obj)) ≫
      ((ρ_ (underlying C Y)).hom ≫ (λ_ (underlying C Y)).inv) =
      ((ρ_ (underlying C X)).hom ≫ (λ_ (underlying C X)).inv) ≫
      ((𝟙_ C.Obj) ◁ g)
    rw [← Category.assoc, rightUnitor_naturality, Category.assoc,
      leftUnitor_inv_naturality]
    simp only [Category.assoc]


set_option backward.isDefEq.respectTransparency false in
/-- Unit normalization extends from the simple induction arguments. -/
theorem crossing_unit_of_simples
    (h : ∀ i, crossingCandidate C (simples C i) (𝟙_ C.Obj) =
      (ρ_ (underlying C (simples C i))).hom ≫ (λ_ (underlying C (simples C i))).inv) :
    ∀ X, crossingCandidate C X (𝟙_ C.Obj) = (ρ_ (underlying C X)).hom ≫ (λ_ (underlying C X)).inv := by
  have heq : crossingNaturalMiddle C (𝟙_ C.Obj) = unitCanonical C :=
    natTrans_ext_on_simples C _ _ _ _ (fun i => by simpa [crossingNaturalMiddle, unitCanonical] using h i)
  intro X
  simpa [crossingNaturalMiddle, unitCanonical] using NatTrans.congr_app heq X

/-- Rigidity supplies all crossing inverses from the unit and tensor checks. -/
theorem crossing_isIso_of_unit_tensor
    (hunit : ∀ i, crossingCandidate C (simples C i) (𝟙_ C.Obj) =
      (ρ_ (underlying C (simples C i))).hom ≫ (λ_ (underlying C (simples C i))).inv)
    (htensor : ∀ i j k, crossingCandidate C (simples C i) (simples C j ⊗ simples C k) =
      crossingTensorComposite C (simples C i) (simples C j) (simples C k)) :
    ∀ X T, IsIso (crossingCandidate C X T) := by
  intro X T
  apply weak_isIso (underlying C X) (crossingCandidate C X)
    (fun f => crossingCandidate_natural_test C X f)
    (fun T U => crossingCandidate_tensor_of_all_simples C htensor X T U)
    (crossing_unit_of_simples C hunit X) T (ᘁT)

end PropertyF.Ground.CentreInduction
