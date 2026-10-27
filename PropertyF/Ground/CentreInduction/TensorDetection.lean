module
public import PropertyF.Ground.CentreInduction.CrossingNaturality
public import PropertyF.Ground.CentreInduction.SimpleDetection

/-! The induction crossing tensor law is detected on pairs of simple objects. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

variable (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
local notation "A" => underlying C X
local notation "b" => crossingCandidate C X

/-- The composite of two crossings, with the associators inserted. -/
def crossingTensorComposite (T U : C.Obj) : A ⊗ (T ⊗ U) ⟶ (T ⊗ U) ⊗ A :=
  (α_ _ _ _).inv ≫ (b T ▷ U) ≫ (α_ _ _ _).hom ≫
    (T ◁ b U) ≫ (α_ _ _ _).inv

theorem crossingTensorComposite_natural_left {T T' : C.Obj} (f : T ⟶ T') (U : C.Obj) :
    (A ◁ (f ▷ U)) ≫ crossingTensorComposite C X T' U = crossingTensorComposite C X T U ≫ ((f ▷ U) ▷ A) := by
  dsimp [crossingTensorComposite]
  calc
    _ = 𝟙 _ ⊗≫ ((A ◁ f ≫ b T') ▷ U) ⊗≫ (T' ◁ b U) ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ ((b T ≫ f ▷ A) ▷ U) ⊗≫ (T' ◁ b U) ⊗≫ 𝟙 _ := by
      rw [crossingCandidate_natural_test C X f]
    _ = 𝟙 _ ⊗≫ (b T ▷ U) ⊗≫ ((f ▷ (A ⊗ U)) ≫ T' ◁ b U) ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ (b T ▷ U) ⊗≫ ((T ◁ b U) ≫ f ▷ (U ⊗ A)) ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = _ := by monoidal

theorem crossingTensorComposite_natural_right (T : C.Obj) {U U' : C.Obj} (f : U ⟶ U') :
    (A ◁ (T ◁ f)) ≫ crossingTensorComposite C X T U' = crossingTensorComposite C X T U ≫ ((T ◁ f) ▷ A) := by
  dsimp [crossingTensorComposite]
  calc
    _ = 𝟙 _ ⊗≫ (((A ⊗ T) ◁ f) ≫ b T ▷ U') ⊗≫ (T ◁ b U') ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ ((b T ▷ U) ≫ ((T ⊗ A) ◁ f)) ⊗≫ (T ◁ b U') ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (b T ▷ U) ⊗≫ (T ◁ (A ◁ f ≫ b U')) ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ (b T ▷ U) ⊗≫ (T ◁ (b U ≫ f ▷ A)) ⊗≫ 𝟙 _ := by
      rw [crossingCandidate_natural_test C X f]
    _ = _ := by monoidal

private def lhsLeft (U : C.Obj) : tensorRight U ⋙ tensorLeft A ⟶ tensorRight U ⋙ tensorRight A where
  app T := b (T ⊗ U)
  naturality {_ _} f := crossingCandidate_natural_test C X (f ▷ U)

private def rhsLeft (U : C.Obj) : tensorRight U ⋙ tensorLeft A ⟶ tensorRight U ⋙ tensorRight A where
  app T := crossingTensorComposite C X T U
  naturality {_ _} f := crossingTensorComposite_natural_left C X f U

private def lhsRight (T : C.Obj) : tensorLeft T ⋙ tensorLeft A ⟶ tensorLeft T ⋙ tensorRight A where
  app U := b (T ⊗ U)
  naturality {_ _} f := crossingCandidate_natural_test C X (T ◁ f)

private def rhsRight (T : C.Obj) : tensorLeft T ⋙ tensorLeft A ⟶ tensorLeft T ⋙ tensorRight A where
  app U := crossingTensorComposite C X T U
  naturality {_ _} f := crossingTensorComposite_natural_right C X T f

/-- The half-braiding tensor law needs to be checked only on pairs of simple
representatives. -/
theorem crossingCandidate_tensor_of_simples
    (h : ∀ i j, b (simples C i ⊗ simples C j) = crossingTensorComposite C X (simples C i) (simples C j)) :
    ∀ T U, b (T ⊗ U) = crossingTensorComposite C X T U := by
  have h' (i : Fin (rank C)) (U : C.Obj) :
      b (simples C i ⊗ U) = crossingTensorComposite C X (simples C i) U := by
    have heq : lhsRight C X (simples C i) = rhsRight C X (simples C i) :=
      natTrans_ext_on_simples C _ _ _ _ (fun j => by simpa [lhsRight, rhsRight] using h i j)
    simpa [lhsRight, rhsRight] using NatTrans.congr_app heq U
  intro T U
  have heq : lhsLeft C X U = rhsLeft C X U :=
    natTrans_ext_on_simples C _ _ _ _ (fun i => by simpa [lhsLeft, rhsLeft] using h' i U)
  simpa [lhsLeft, rhsLeft] using NatTrans.congr_app heq T

/-- The crossing is also a natural transformation in the crossed object. -/
def crossingNaturalTest : tensorLeft A ⟶ tensorRight A where
  app T := b T
  naturality {_ _} f := crossingCandidate_natural_test C X f

/-- To prove invertibility of the crossing everywhere, it suffices to test
simple representatives in both of its arguments. -/
theorem crossingCandidate_isIso_of_simples
    (h : ∀ i j, IsIso (crossingCandidate C (simples C i) (simples C j))) :
    ∀ X T, IsIso (crossingCandidate C X T) := by
  have hi (j : Fin (rank C)) (X : C.Obj) : IsIso (crossingCandidate C X (simples C j)) := by
    exact natTrans_isIso_of_simples C _ _ (crossingNaturalMiddle C (simples C j))
      (fun i => h i j) X
  intro X T
  exact natTrans_isIso_of_simples C _ _ (crossingNaturalTest C X) (hi · X) T

/-- The composite crossing is natural in the induction argument. -/
theorem crossingTensorComposite_natural_middle {X Y : C.Obj} (f : X ⟶ Y) (T U : C.Obj) :
  ((underlyingFunctor C).map f ▷ (T ⊗ U)) ≫ crossingTensorComposite C Y T U =
    crossingTensorComposite C X T U ≫ ((T ⊗ U) ◁ (underlyingFunctor C).map f) := by
  let g : underlying C X ⟶ underlying C Y := (underlyingFunctor C).map f
  change (g ▷ (T ⊗ U)) ≫ crossingTensorComposite C Y T U =
    crossingTensorComposite C X T U ≫ ((T ⊗ U) ◁ g)
  dsimp [crossingTensorComposite]
  calc
    _ = 𝟙 _ ⊗≫ ((g ▷ T ≫ crossingCandidate C Y T) ▷ U) ⊗≫
      (T ◁ crossingCandidate C Y U) ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ ((crossingCandidate C X T ≫ T ◁ g) ▷ U) ⊗≫
      (T ◁ crossingCandidate C Y U) ⊗≫ 𝟙 _ := by rw [show (g ▷ T) ≫ crossingCandidate C Y T = crossingCandidate C X T ≫ (T ◁ g) from crossingCandidate_natural_middle C f T]
    _ = 𝟙 _ ⊗≫ (crossingCandidate C X T ▷ U) ⊗≫
      (T ◁ (g ▷ U ≫ crossingCandidate C Y U)) ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ (crossingCandidate C X T ▷ U) ⊗≫
      (T ◁ (crossingCandidate C X U ≫ U ◁ g)) ⊗≫ 𝟙 _ := by
      rw [show (g ▷ U) ≫ crossingCandidate C Y U = crossingCandidate C X U ≫ (U ◁ g) from crossingCandidate_natural_middle C f U]
    _ = _ := by monoidal

private def middleLhs (T U : C.Obj) : underlyingFunctor C ⋙ tensorRight (T ⊗ U) ⟶
    underlyingFunctor C ⋙ tensorLeft (T ⊗ U) where
  app X := crossingCandidate C X (T ⊗ U)
  naturality {_ _} f := crossingCandidate_natural_middle C f (T ⊗ U)

private def middleRhs (T U : C.Obj) : underlyingFunctor C ⋙ tensorRight (T ⊗ U) ⟶
    underlyingFunctor C ⋙ tensorLeft (T ⊗ U) where
  app X := crossingTensorComposite C X T U
  naturality {_ _} f := crossingTensorComposite_natural_middle C f T U

set_option backward.isDefEq.respectTransparency false in
/-- The tensor law is determined by finitely many triples of simple representatives. -/
theorem crossingCandidate_tensor_of_all_simples
    (h : ∀ i j k, crossingCandidate C (simples C i) (simples C j ⊗ simples C k) =
      crossingTensorComposite C (simples C i) (simples C j) (simples C k)) :
    ∀ X T U, crossingCandidate C X (T ⊗ U) = crossingTensorComposite C X T U := by
  have hi (i : Fin (rank C)) (T U : C.Obj) :
      crossingCandidate C (simples C i) (T ⊗ U) = crossingTensorComposite C (simples C i) T U :=
    crossingCandidate_tensor_of_simples C _ (h i) T U
  intro X T U
  have heq : middleLhs C T U = middleRhs C T U := natTrans_ext_on_simples C _ _ _ _
    (fun i => by simpa [middleLhs, middleRhs] using hi i T U)
  simpa [middleLhs, middleRhs] using NatTrans.congr_app heq X

end PropertyF.Ground.CentreInduction
