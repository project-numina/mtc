module
public import PropertyF.Ground.Fusion.ObjectDimension
public import PropertyF.Ground.Dimensions.SimpleHomBasis

open PropertyF.Ground.Dimensions

/-! The underlying object of the induction construction for the Drinfeld centre. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The simple-indexed summand of the underlying induction object. -/
abbrev inductionSummand (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
    (i : Fin (rank C)) : C.Obj := (simples C i ⊗ X) ⊗ (simples C i)ᘁ

/-- The finite direct sum underlying the induction object. No half-braiding is
claimed here. -/
def underlying (C : BraidedFusionCategory.{v,u}) (X : C.Obj) : C.Obj :=
  ⨁ (inductionSummand C X)

/-- The underlying induction object has FP dimension `FPdim(C) * FPdim(X)`.
This calculation does not require the centre to be fusion or the existence of
its induction half-braiding. -/
theorem fpDimension_underlying (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    fpDimension C (underlying C X) = globalFPDimension C * fpDimension C X := by
  simp [underlying, fpDimension_biproduct, fpDimension_tensor, fpDimension_rightDual,
    fpDimension_simple, globalFPDimension, Finset.mul_sum, pow_two, mul_left_comm, mul_comm]

end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- The induction sum is functorial in its middle factor. Its centre lift is
constructed from the induction half-braiding. -/
def underlyingFunctor (C : BraidedFusionCategory.{v,u}) : C.Obj ⥤ C.Obj where
  obj := underlying C
  map {X Y} f := CategoryTheory.Limits.biproduct.map
    (fun i : Fin (rank C) => (simples C i ◁ f) ▷ (simples C i)ᘁ)
  map_id X := biproduct.hom_ext' _ _ fun i => by simp [underlying]
  map_comp f g := biproduct.hom_ext' _ _ fun i => by
    simp [underlying, Category.assoc, whiskerLeft_comp, comp_whiskerRight]

end PropertyF.Ground.CentreInduction

end

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
  simp only [crossingBlock, tensorHom_def, Category.assoc]
  rw [associator_naturality_left_assoc, ← comp_whiskerRight_assoc, whisker_exchange, comp_whiskerRight_assoc,
    ← whisker_exchange_assoc, associator_naturality_middle_assoc]
  simp only [associator_naturality_right_assoc]
  rw [← whiskerLeft_comp, associator_inv_naturality_middle,
    whiskerLeft_comp]

/-- The projection from the chosen simple decomposition of an object. -/
def simpleProjection (V : C.Obj) (i : Fin (rank C))
    (a : Fin (Module.finrank ℂ (simples C i ⟶ V))) : V ⟶ simples C i :=
  (simpleDecomposition C V).hom ≫ biproduct.π (simplePiecesObject C V) ⟨i,a⟩

/-- The multiplicity index for a simple summand of `T ⊗ Sⱼ`. -/
abbrev crossingIndex (T : C.Obj) (i j : Fin (rank C)) : Type :=
  Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j))

/-- The inclusion attached to the canonical decomposition of `T ⊗ Sⱼ`. -/
def crossingInclusion (T : C.Obj)
    (i j : Fin (rank C))
    (a : crossingIndex C T i j) :
    simples C i ⟶ T ⊗ simples C j :=
  simpleInclusion C (T ⊗ simples C j) i a

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
  simp [crossingInclusion, crossingProjection, simpleProjection, simpleInclusion, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The projection/inclusion pairs resolve the identity on `T ⊗ Sⱼ`.
This is the completeness relation used for changes of fusion bases. -/
theorem crossing_completeness (T : C.Obj) (j : Fin (rank C)) :
    (∑ p : Σ i : Fin (rank C), crossingIndex C T i j,
      crossingProjection C T p.1 j p.2 ≫ crossingInclusion C T p.1 j p.2) = 𝟙 (T ⊗ simples C j) := by
  simp only [crossingProjection, simpleProjection, crossingInclusion, simpleInclusion,
    Category.assoc, ← Preadditive.comp_sum]
  simp_rw [← Category.assoc (biproduct.π _ _)]
  rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp, Iso.hom_inv_id]

variable (X T : C.Obj)

/-- The finite matrix formula for the induction half-braiding. Its invertibility
and coherence are established in the subsequent induction modules. -/
def crossingCandidate :
    underlying C X ⊗ T ⟶ T ⊗ underlying C X :=
  let V := inductionSummand C X
  (rightDistributor V T).hom ≫ biproduct.desc (fun i =>
    ∑ j, ∑ a : crossingIndex C T i j,
      crossingBlock X T (simples C j)
        (crossingInclusion C T i j a) (crossingProjection C T i j a) ≫
          (T ◁ biproduct.ι V j))

set_option backward.isDefEq.respectTransparency false in
/-- The proposed crossing has the stated matrix entries on each induced
simple summand. -/
@[reassoc]
theorem crossingCandidate_on_summand (i : Fin (rank C)) :
    let V := inductionSummand C X
    (biproduct.ι V i ▷ T) ≫ crossingCandidate C X T =
      ∑ j, ∑ a : crossingIndex C T i j, crossingSummand C X T i j a ≫ (T ◁ biproduct.ι V j) :=
  (biproduct_ι_comp_rightDistributor_hom_assoc (inductionSummand C X) T i _).trans
    (biproduct.ι_desc _ i)

set_option backward.isDefEq.respectTransparency false in
/-- The proposed crossing is natural in the induction argument. -/
theorem crossingCandidate_natural_middle {X Y : C.Obj} (h : X ⟶ Y) (T : C.Obj) :
    ((underlyingFunctor C).map h ▷ T) ≫ crossingCandidate C Y T =
      crossingCandidate C X T ≫ (T ◁ (underlyingFunctor C).map h) := by
  let VX := inductionSummand C X
  let VY := inductionSummand C Y
  apply (cancel_epi (rightDistributor VX T).inv).1
  refine biproduct.hom_ext' _ _ fun i => ?_
  rw [biproduct_ι_comp_rightDistributor_inv_assoc, biproduct_ι_comp_rightDistributor_inv_assoc]
  dsimp [VX, VY, underlying] at *
  simp only [← Category.assoc, ← comp_whiskerRight]
  simp only [underlyingFunctor, biproduct.ι_map, comp_whiskerRight, Category.assoc,
    crossingCandidate_on_summand, Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  rw [← whiskerLeft_comp]
  simp only [biproduct.ι_map, whiskerLeft_comp]
  simpa only [Category.assoc] using crossingBlock_natural_middle_assoc h
    (crossingInclusion C T i j a) (crossingProjection C T i j a) (T ◁ biproduct.ι VY j)

end PropertyF.Ground.CentreInduction
