module
public import PropertyF.Ground.CentreInduction.Underlying
public import PropertyF.Ground.Dimensions.SimpleHomBasis

/-! Matrix entries of the proposed induction half-braiding. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Turn a map `T ⊗ S ⟶ R` into its right-dual mate
`R* ⊗ T ⟶ S*`. -/
def closeFusionMap (T S : D) {R : D} (f : T ⊗ S ⟶ R) : Rᘁ ⊗ T ⟶ Sᘁ :=
  (fᘁ ▷ T) ≫ ((rightDualTensorIso T S).hom ▷ T) ≫
    (α_ (Sᘁ) (Tᘁ) T).hom ≫ (Sᘁ ◁ ε_ T (Tᘁ)) ≫ (ρ_ (Sᘁ)).hom

/-- The matrix entry associated to an inclusion `R ⟶ T ⊗ S` and a
projection `T ⊗ S ⟶ R`. -/
def crossingBlock (X T S : D) {R : D} (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    ((R ⊗ X) ⊗ Rᘁ) ⊗ T ⟶ T ⊗ ((S ⊗ X) ⊗ Sᘁ) :=
  (α_ (R ⊗ X) (Rᘁ) T).hom ≫ ((g ▷ X) ⊗ₘ closeFusionMap T S f) ≫
    (α_ (T ⊗ S) X (Sᘁ)).hom ≫ (α_ T S (X ⊗ Sᘁ)).hom ≫
      (T ◁ (α_ S X (Sᘁ)).inv)

/-- A crossing matrix entry is natural in the middle induction factor. -/
@[reassoc]
theorem crossingBlock_natural_middle {X Y : D} (h : X ⟶ Y) {T R S : D}
    (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    (((R ◁ h) ▷ Rᘁ) ▷ T) ≫ crossingBlock Y T S g f =
      crossingBlock X T S g f ≫ (T ◁ ((S ◁ h) ▷ Sᘁ)) := by
  dsimp [crossingBlock]
  simp only [Category.assoc]
  rw [associator_naturality_left_assoc]
  simp only [tensorHom_def, Category.assoc]
  rw [← comp_whiskerRight_assoc, whisker_exchange, comp_whiskerRight_assoc,
    ← whisker_exchange_assoc, associator_naturality_middle_assoc,
    associator_naturality_right_assoc]
  rw [associator_naturality_right_assoc]
  simp only [associator_naturality_right_assoc]
  rw [← whiskerLeft_comp, associator_inv_naturality_middle,
    whiskerLeft_comp]

/-- The projection from the chosen simple decomposition of an object. -/
def simpleProjection (V : C.Obj) (i : Fin (rank C))
    (a : Fin (Module.finrank ℂ (simples C i ⟶ V))) : V ⟶ simples C i :=
  (Dimensions.simpleDecomposition C V).hom ≫ biproduct.π (Dimensions.simplePiecesObject C V) ⟨i,a⟩

/-- The multiplicity index for a simple summand of `T ⊗ Sⱼ`. -/
abbrev crossingIndex (T : C.Obj) (i j : Fin (rank C)) : Type :=
  Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j))

/-- The inclusion attached to the canonical decomposition of `T ⊗ Sⱼ`. -/
def crossingInclusion (T : C.Obj)
    (i j : Fin (rank C))
    (a : crossingIndex C T i j) :
    simples C i ⟶ T ⊗ simples C j :=
  Dimensions.simpleInclusion C (T ⊗ simples C j) i a

/-- The corresponding projection from the same decomposition. -/
def crossingProjection (T : C.Obj)
    (i j : Fin (rank C))
    (a : crossingIndex C T i j) :
    T ⊗ simples C j ⟶ simples C i :=
  simpleProjection C (T ⊗ simples C j) i a

/-- One simple-summand contribution to the induction crossing matrix. -/
abbrev crossingSummand (X T : C.Obj) (i j : Fin (rank C)) (a : crossingIndex C T i j) :=
  crossingBlock X T (simples C j)
    (crossingInclusion C T i j a) (crossingProjection C T i j a)

/-- The crossing block obtained by composing two simple-summand decompositions. -/
abbrev nestedCrossingBlock (X T U : C.Obj) (i k j : Fin (rank C))
    (a : crossingIndex C T i k) (b : crossingIndex C U k j) :=
  crossingBlock X (T ⊗ U) (simples C j)
    (crossingInclusion C T i k a ≫ (T ◁ crossingInclusion C U k j b) ≫
      (α_ T U (simples C j)).inv)
    ((α_ T U (simples C j)).hom ≫ (T ◁ crossingProjection C U k j b) ≫
      crossingProjection C T i k a)

/-- Inclusion and projection of the same summand compose to the identity. -/
theorem crossingInclusion_projection {C : BraidedFusionCategory.{v,u}} {T : C.Obj} {i j : Fin (rank C)}
    (a : crossingIndex C T i j) :
    crossingInclusion C T i j a ≫ crossingProjection C T i j a = 𝟙 (simples C i) := by
  simp [crossingInclusion, crossingProjection, simpleProjection, Dimensions.simpleInclusion, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The projection/inclusion pairs resolve the identity on `T ⊗ Sⱼ`.
This is the completeness relation used for changes of fusion bases. -/
theorem crossing_completeness (T : C.Obj)
    (j : Fin (rank C)) :
    (∑ p : Σ i : Fin (rank C),
        crossingIndex C T i j,
      crossingProjection C T p.1 j p.2 ≫ crossingInclusion C T p.1 j p.2) =
        𝟙 (T ⊗ simples C j) := by
  classical
  simp only [crossingProjection, simpleProjection, crossingInclusion, Dimensions.simpleInclusion,
    Category.assoc, ← Preadditive.comp_sum]
  simp_rw [← Category.assoc (biproduct.π _ _)]
  rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp, Iso.hom_inv_id]

/-- The finite matrix formula for the induction half-braiding. Its invertibility
and coherence are established in the subsequent induction modules. -/
def crossingCandidate (X T : C.Obj) :
    underlying C X ⊗ T ⟶ T ⊗ underlying C X := by
  classical
  let V := inductionSummand C X
  refine (rightDistributor V T).hom ≫ biproduct.desc (fun i => ?_)
  exact ∑ j, ∑ a : crossingIndex C T i j,
    crossingBlock X T (simples C j)
      (crossingInclusion C T i j a) (crossingProjection C T i j a) ≫
        (T ◁ biproduct.ι V j)

set_option backward.isDefEq.respectTransparency false in
/-- The proposed crossing has the stated matrix entries on each induced
simple summand. -/
@[reassoc]
theorem crossingCandidate_on_summand
    (X T : C.Obj) (i : Fin (rank C)) :
    let V := inductionSummand C X
    (biproduct.ι V i ▷ T) ≫ crossingCandidate C X T =
      ∑ j, ∑ a : crossingIndex C T i j,
        crossingSummand C X T i j a ≫ (T ◁ biproduct.ι V j) := by
  classical
  simp only [crossingCandidate, biproduct_ι_comp_rightDistributor_hom_assoc,
    biproduct.ι_desc]

set_option backward.isDefEq.respectTransparency false in
/-- The proposed crossing is natural in the induction argument. -/
theorem crossingCandidate_natural_middle
    {X Y : C.Obj} (h : X ⟶ Y) (T : C.Obj) :
    ((underlyingFunctor C).map h ▷ T) ≫ crossingCandidate C Y T =
      crossingCandidate C X T ≫ (T ◁ (underlyingFunctor C).map h) := by
  classical
  let VX := inductionSummand C X
  let VY := inductionSummand C Y
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
  simp only [Category.assoc, crossingCandidate_on_summand]
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
  have hblock := crossingBlock_natural_middle h
    (crossingInclusion C T i j a) (crossingProjection C T i j a)
  have hterm := congrArg (fun g => g ≫ (T ◁ biproduct.ι VY j)) hblock
  simp only [Category.assoc] at hterm ⊢
  rw [hj']
  exact hterm


end PropertyF.Ground.CentreInduction
