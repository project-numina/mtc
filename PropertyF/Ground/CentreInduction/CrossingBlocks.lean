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

/-- A crossing matrix entry is natural in the middle induction factor. -/
@[reassoc]
theorem crossingBlock_natural_middle (C : BraidedFusionCategory.{v,u})
    {X Y : C.Obj} (h : X ⟶ Y) (T R S : C.Obj)
    (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    (((R ◁ h) ▷ Rᘁ) ▷ T) ≫ crossingBlock C Y T R S g f =
      crossingBlock C X T R S g f ≫ (T ◁ ((S ◁ h) ▷ Sᘁ)) := by
  dsimp [crossingBlock]
  simp only [Category.assoc]
  rw [associator_naturality_left_assoc]
  simp only [tensorHom_def, Category.assoc]
  rw [← comp_whiskerRight_assoc, whisker_exchange, comp_whiskerRight_assoc,
    ← whisker_exchange_assoc, associator_naturality_middle_assoc,
    associator_naturality_right_assoc]
  rw [associator_naturality_right_assoc]
  simp only [associator_naturality_right_assoc, Category.assoc]
  rw [← whiskerLeft_comp, associator_inv_naturality_middle,
    whiskerLeft_comp]

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

/-- Distinct summand inclusions and projections have zero composite. -/
theorem crossingInclusion_projection_ne (C : BraidedFusionCategory.{v,u}) (T : C.Obj)
    (j : Fin (rank C))
    (p q : Σ i : Fin (rank C), Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j)))
    (hne : p ≠ q) :
    crossingInclusion C T p.1 j p.2 ≫ crossingProjection C T q.1 j q.2 = 0 := by
  simp [crossingInclusion, crossingProjection, Dimensions.simpleInclusion, Category.assoc,
    biproduct.ι_π_ne _ hne]

set_option backward.isDefEq.respectTransparency false in
/-- The projection/inclusion pairs resolve the identity on `T ⊗ Sⱼ`.
This is the completeness relation used for changes of fusion bases. -/
theorem crossing_completeness (C : BraidedFusionCategory.{v,u}) (T : C.Obj)
    (j : Fin (rank C)) :
    (∑ p : Σ i : Fin (rank C),
        Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j)),
      crossingProjection C T p.1 j p.2 ≫ crossingInclusion C T p.1 j p.2) =
        𝟙 (T ⊗ simples C j) := by
  classical
  let e := Dimensions.simpleDecomposition C (T ⊗ simples C j)
  let V := Dimensions.simplePiecesObject C (T ⊗ simples C j)
  have hs : e.hom ≫ (𝟙 (⨁ V)) ≫ e.inv = 𝟙 (T ⊗ simples C j) := by
    dsimp [e, V]
    simp
  have ht := congrArg (fun k => e.hom ≫ k ≫ e.inv) (biproduct.total (f := V))
  rw [hs] at ht
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc] at ht
  calc
    _ = ∑ p, e.hom ≫ biproduct.π V p ≫ biproduct.ι V p ≫ e.inv := by
      apply Finset.sum_congr rfl
      intro p _
      cases p
      simp [crossingProjection, crossingInclusion, Dimensions.simpleInclusion, e, V, Category.assoc]
    _ = _ := ht

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

set_option backward.isDefEq.respectTransparency false in
/-- The proposed crossing has the stated matrix entries on each induced
simple summand. -/
@[reassoc]
theorem crossingCandidate_on_summand (C : BraidedFusionCategory.{v,u})
    (X T : C.Obj) (i : Fin (rank C)) :
    let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
    (biproduct.ι V i ▷ T) ≫ crossingCandidate C X T =
      ∑ j, ∑ a : Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j)),
        crossingBlock C X T (simples C i) (simples C j)
          (crossingInclusion C T i j a) (crossingProjection C T i j a) ≫
            (T ◁ biproduct.ι V j) := by
  classical
  simp only [crossingCandidate, Category.assoc, biproduct_ι_comp_rightDistributor_hom_assoc,
    biproduct.ι_desc]

set_option backward.isDefEq.respectTransparency false in
/-- The proposed crossing is natural in the induction argument. -/
theorem crossingCandidate_natural_middle (C : BraidedFusionCategory.{v,u})
    {X Y : C.Obj} (h : X ⟶ Y) (T : C.Obj) :
    ((underlyingFunctor C).map h ▷ T) ≫ crossingCandidate C Y T =
      crossingCandidate C X T ≫ (T ◁ (underlyingFunctor C).map h) := by
  classical
  let VX : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
  let VY : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ Y) ⊗ (simples C k)ᘁ
  have hi (i : Fin (rank C)) :
      (biproduct.ι VX i ▷ T) ≫ ((underlyingFunctor C).map h ▷ T) =
        (((simples C i ◁ h) ▷ (simples C i)ᘁ) ▷ T) ≫ (biproduct.ι VY i ▷ T) := by
    rw [← comp_whiskerRight, ← comp_whiskerRight]
    congr 1
    simp [underlyingFunctor, VX, VY]
  apply (cancel_epi (rightDistributor VX T).inv).1
  apply biproduct.hom_ext'
  intro i
  simp only [biproduct_ι_comp_rightDistributor_inv_assoc]
  dsimp [VX, VY, underlying] at *
  simp only [← Category.assoc, hi i]
  simp only [Category.assoc, crossingCandidate_on_summand, crossingCandidate_on_summand_assoc]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  have hj : biproduct.ι VX j ≫ (underlyingFunctor C).map h =
      ((simples C j ◁ h) ▷ (simples C j)ᘁ) ≫ biproduct.ι VY j := by
    simp [underlyingFunctor, VX, VY]
  have hj' : (T ◁ biproduct.ι VX j) ≫ (T ◁ (underlyingFunctor C).map h) =
      (T ◁ ((simples C j ◁ h) ▷ (simples C j)ᘁ)) ≫ (T ◁ biproduct.ι VY j) := by
    simpa only [whiskerLeft_comp] using congrArg (fun g => T ◁ g) hj
  have hblock := crossingBlock_natural_middle C h T (simples C i) (simples C j)
    (crossingInclusion C T i j a) (crossingProjection C T i j a)
  have hterm := congrArg (fun g => g ≫ (T ◁ biproduct.ι VY j)) hblock
  simp only [Category.assoc] at hterm ⊢
  rw [hj']
  exact hterm


end PropertyF.Ground.CentreInduction
