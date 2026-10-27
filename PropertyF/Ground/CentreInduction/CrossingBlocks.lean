module
public import PropertyF.Ground.CentreInduction.Underlying
public import PropertyF.Ground.Dimensions.SimpleHomBasis

/-! Matrix entries of the proposed induction half-braiding. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Turn a map `T ⊗ S ⟶ R` into its right-dual mate
`R* ⊗ T ⟶ S*`. -/
def closeFusionMap (C : BraidedFusionCategory.{v,u})
    (T S R : C.Obj) (f : T ⊗ S ⟶ R) : Rᘁ ⊗ T ⟶ Sᘁ :=
  (fᘁ ▷ T) ≫ ((rightDualTensorIso T S).hom ▷ T) ≫
    (α_ (Sᘁ) (Tᘁ) T).hom ≫ (Sᘁ ◁ ε_ T (Tᘁ)) ≫ (ρ_ (Sᘁ)).hom

/-- The matrix entry associated to an inclusion `R ⟶ T ⊗ S` and a
projection `T ⊗ S ⟶ R`. -/
def crossingBlock (C : BraidedFusionCategory.{v,u}) (X T R S : C.Obj)
    (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    ((R ⊗ X) ⊗ Rᘁ) ⊗ T ⟶ T ⊗ ((S ⊗ X) ⊗ Sᘁ) :=
  (α_ (R ⊗ X) (Rᘁ) T).hom ≫ ((g ▷ X) ⊗ₘ closeFusionMap C T S R f) ≫
    (α_ (T ⊗ S) X (Sᘁ)).hom ≫ (α_ T S (X ⊗ Sᘁ)).hom ≫
      (T ◁ (α_ S X (Sᘁ)).inv)

/-- The inclusion attached to the canonical decomposition of `T ⊗ Sⱼ`. -/
def crossingInclusion (C : BraidedFusionCategory.{v,u}) (T : C.Obj)
    (i j : Fin (rank C))
    (a : Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j))) :
    simples C i ⟶ T ⊗ simples C j :=
  Dimensions.simpleInclusion C (T ⊗ simples C j) i a

/-- The corresponding projection from the same decomposition. -/
def crossingProjection (C : BraidedFusionCategory.{v,u}) (T : C.Obj)
    (i j : Fin (rank C))
    (a : Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j))) :
    T ⊗ simples C j ⟶ simples C i :=
  (Dimensions.simpleDecomposition C (T ⊗ simples C j)).hom ≫
    biproduct.π (Dimensions.simplePiecesObject C (T ⊗ simples C j)) ⟨i, a⟩

/-- Inclusion and projection of the same summand compose to the identity. -/
theorem crossingInclusion_projection (C : BraidedFusionCategory.{v,u}) (T : C.Obj)
    (i j : Fin (rank C))
    (a : Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j))) :
    crossingInclusion C T i j a ≫ crossingProjection C T i j a = 𝟙 (simples C i) := by
  simp [crossingInclusion, crossingProjection, Dimensions.simpleInclusion, Category.assoc]

/-- The finite matrix formula proposed for the induction half-braiding. This
is only a morphism; invertibility, naturality, the tensor law, and compatibility
with the induction functor are not yet proved. -/
def crossingCandidate (C : BraidedFusionCategory.{v,u}) (X T : C.Obj) :
    underlying C X ⊗ T ⟶ T ⊗ underlying C X := by
  classical
  let V : Fin (rank C) → C.Obj := fun i => (simples C i ⊗ X) ⊗ (simples C i)ᘁ
  refine (rightDistributor V T).hom ≫ biproduct.desc (fun i => ?_)
  exact ∑ j, ∑ a : Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j)),
    crossingBlock C X T (simples C i) (simples C j)
      (crossingInclusion C T i j a) (crossingProjection C T i j a) ≫
        (T ◁ biproduct.ι V j)

end PropertyF.Ground.CentreInduction
