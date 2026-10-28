module
public import PropertyF.Ground.Fusion.ObjectDimension
public import PropertyF.Ground.Dimensions.SimpleHomBasis

open PropertyF.Ground.Dimensions Module

/-! The underlying object of the induction construction for the Drinfeld centre. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- Tensor an object between an object and its right dual. -/
abbrev conjugate (R X : D) [HasRightDual R] : D := (R ⊗ X) ⊗ Rᘁ

variable (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
-- The chosen simple representatives of the base category.
local notation "Sᶜ" => simples C

variable {C} in
/-- The simple-indexed summand of the underlying induction object. -/
abbrev inductionSummand (i : Fin (rank C)) : C.Obj := conjugate (Sᶜ i) X

variable {C} in
/-- The finite direct sum underlying the induction object. No half-braiding is
claimed here. -/
def underlying : C.Obj :=
  ⨁ (inductionSummand X)

variable {C} in
/-- The underlying induction object has FP dimension `FPdim(C) * FPdim(X)`.
This calculation does not require the centre to be fusion or the existence of
its induction half-braiding. -/
theorem fpDimension_underlying :
    fpDimension C (underlying X) = globalFPDimension C * fpDimension C X := by
  simp [underlying, fpDimension_biproduct, fpDimension_tensor, fpDimension_rightDual,
    fpDimension_simple, globalFPDimension, Finset.mul_sum, pow_two, mul_left_comm, mul_comm]

/-- The induction sum is functorial in its middle factor. Its centre lift is
constructed from the induction half-braiding. -/
def underlyingFunctor : C.Obj ⥤ C.Obj where
  obj := underlying (C := C)
  map {X Y} f := CategoryTheory.Limits.biproduct.map
    (fun i : Fin (rank C) => (Sᶜ i ◁ f) ▷ (Sᶜ i)ᘁ)
  map_id X := biproduct.hom_ext' _ _ fun i => by simp [underlying]
  map_comp f g := biproduct.hom_ext' _ _ fun i => by
    simp [underlying, whiskerLeft_comp, comp_whiskerRight]

end PropertyF.Ground.CentreInduction

end

/-! Matrix entries of the proposed induction half-braiding. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u})
-- The chosen simple representatives of the base category.
local notation "Sᶜ" => simples C
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Turn a map `T ⊗ S ⟶ R` into its right-dual mate
`R* ⊗ T ⟶ S*`. -/
def closeFusionMap (T S : D) [HasRightDual S] {R : D} [HasRightDual R]
    (f : T ⊗ S ⟶ R) : Rᘁ ⊗ T ⟶ Sᘁ :=
  (tensorRightHomEquiv (Rᘁ ⊗ T) S Sᘁ (𝟙_ D))
    ((α_ Rᘁ T S).hom ≫ (Rᘁ ◁ f) ≫ ε_ R Rᘁ) ≫ (λ_ Sᘁ).hom

/-- A crossing block with different input and output test strands. -/
def mixedCrossing {D : Type u} [Category.{v} D] [MonoidalCategory D]
    (X T U : D) {R S : D} [HasRightDual R] [HasRightDual S] (g : R ⟶ U ⊗ S) (f : T ⊗ S ⟶ R) :
    conjugate R X ⊗ T ⟶ U ⊗ conjugate S X :=
  (α_ (R ⊗ X) (Rᘁ) T).hom ≫ ((g ▷ X) ⊗ₘ closeFusionMap T S f) ≫
    (α_ (U ⊗ S) X (Sᘁ)).hom ≫ (α_ U S (X ⊗ Sᘁ)).hom ≫
      (U ◁ (α_ S X (Sᘁ)).inv)

/-- The matrix entry associated to an inclusion `R ⟶ T ⊗ S` and a
projection `T ⊗ S ⟶ R`. -/
def crossingBlock (X T S : D) [HasRightDual S] {R : D} [HasRightDual R]
    (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    conjugate R X ⊗ T ⟶ T ⊗ conjugate S X :=
  mixedCrossing X T T g f

/-- A mixed crossing is natural in the middle induction factor. -/
@[reassoc]
theorem mixedCrossing_natural_middle {X Y : D} (h : X ⟶ Y) {T U R S : D}
    [HasRightDual R] [HasRightDual S] (g : R ⟶ U ⊗ S) (f : T ⊗ S ⟶ R) :
    (((R ◁ h) ▷ Rᘁ) ▷ T) ≫ mixedCrossing Y T U g f =
      mixedCrossing X T U g f ≫ (U ◁ ((S ◁ h) ▷ Sᘁ)) := by
  simp only [mixedCrossing, tensorHom_def, Category.assoc]
  rw [associator_naturality_left_assoc, ← comp_whiskerRight_assoc, whisker_exchange, comp_whiskerRight_assoc,
    ← whisker_exchange_assoc, associator_naturality_middle_assoc]
  simp only [associator_naturality_right_assoc, ← whiskerLeft_comp,
    associator_inv_naturality_middle]

variable {C} in
/-- The projection from the chosen simple decomposition of an object. -/
def simpleProjection (V : C.Obj) (i : Fin (rank C))
    (a : Fin (finrank ℂ (Sᶜ i ⟶ V))) : V ⟶ Sᶜ i :=
  (simpleDecomposition C V).hom ≫ biproduct.π (simplePiecesObject C V) ⟨i,a⟩

variable {C} in
/-- The multiplicity index for a simple summand of `T ⊗ Sⱼ`. -/
abbrev crossingIndex (T : C.Obj) (i j : Fin (rank C)) : Type :=
  Fin (finrank ℂ (Sᶜ i ⟶ T ⊗ Sᶜ j))

variable {C} in
/-- The inclusion attached to the canonical decomposition of `T ⊗ Sⱼ`. -/
def crossingInclusion (T : C.Obj)
    (i j : Fin (rank C))
    (a : crossingIndex T i j) :
    Sᶜ i ⟶ T ⊗ Sᶜ j :=
  simpleInclusion C (T ⊗ Sᶜ j) i a

variable {C} in
/-- The corresponding projection from the same decomposition. -/
def crossingProjection (T : C.Obj)
    (i j : Fin (rank C))
    (a : crossingIndex T i j) :
    T ⊗ Sᶜ j ⟶ Sᶜ i :=
  simpleProjection (T ⊗ Sᶜ j) i a

variable {C} in
/-- One simple-summand contribution to the induction crossing matrix. -/
abbrev crossingSummand (X T : C.Obj) (i j : Fin (rank C)) (a : crossingIndex T i j) :=
  crossingBlock X T (Sᶜ j)
    (crossingInclusion T i j a) (crossingProjection T i j a)

variable {C} in
/-- The crossing block obtained by composing two simple-summand decompositions. -/
abbrev nestedCrossingBlock (X T U : C.Obj) (i k j : Fin (rank C))
    (a : crossingIndex T i k) (b : crossingIndex U k j) :=
  crossingBlock X (T ⊗ U) (Sᶜ j)
    (crossingInclusion T i k a ≫ (T ◁ crossingInclusion U k j b) ≫
      (α_ T U (Sᶜ j)).inv)
    ((α_ T U (Sᶜ j)).hom ≫ (T ◁ crossingProjection U k j b) ≫
      crossingProjection T i k a)

/-- Inclusion and projection of the same summand compose to the identity. -/
theorem crossingInclusion_projection {C : BraidedFusionCategory.{v,u}} {T : C.Obj} {i j : Fin (rank C)}
    (a : crossingIndex T i j) :
    crossingInclusion T i j a ≫ crossingProjection T i j a = 𝟙 (simples C i) := by
  simp [crossingInclusion, crossingProjection, simpleProjection, simpleInclusion]

set_option backward.isDefEq.respectTransparency false in
/-- The projection/inclusion pairs resolve the identity on `T ⊗ Sⱼ`.
This is the completeness relation used for changes of fusion bases. -/
theorem crossing_completeness (T : C.Obj) (j : Fin (rank C)) :
    (∑ p : Σ i : Fin (rank C), crossingIndex T i j,
      crossingProjection T p.1 j p.2 ≫ crossingInclusion T p.1 j p.2) = 𝟙 (T ⊗ Sᶜ j) :=
  let e := simpleDecomposition C (T ⊗ Sᶜ j)
  by
    simpa [crossingProjection, simpleProjection, crossingInclusion, simpleInclusion,
      Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp, e, -biproduct.total] using
      congrArg (fun f => e.hom ≫ f ≫ e.inv)
        (biproduct.total (f := simplePiecesObject C (T ⊗ Sᶜ j)))

variable (X T : C.Obj)
-- The simple-indexed summands of the induced object.
local notation "Vᶜ" => inductionSummand X

variable {C} in
/-- The finite matrix formula for the induction half-braiding. Its invertibility
and coherence are established in the subsequent induction modules. -/
def crossingCandidate :
    underlying X ⊗ T ⟶ T ⊗ underlying X :=
  (rightDistributor Vᶜ T).hom ≫ biproduct.desc (fun i =>
    ∑ j, ∑ a : crossingIndex T i j,
      crossingBlock X T (Sᶜ j)
        (crossingInclusion T i j a) (crossingProjection T i j a) ≫
          (T ◁ biproduct.ι Vᶜ j))

variable {C} in
/-- The composite of two crossings, with the associators inserted. -/
def crossingTensorComposite (U : C.Obj) : underlying X ⊗ (T ⊗ U) ⟶ (T ⊗ U) ⊗ underlying X :=
  (α_ _ _ _).inv ≫ (crossingCandidate X T ▷ U) ≫ (α_ _ _ _).hom ≫
    (T ◁ crossingCandidate X U) ≫ (α_ _ _ _).inv

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- The proposed crossing has the stated matrix entries on each induced
simple summand. -/
@[reassoc]
theorem crossingCandidate_on_summand (i : Fin (rank C)) :
    (biproduct.ι Vᶜ i ▷ T) ≫ crossingCandidate X T =
      ∑ j, ∑ a : crossingIndex T i j, crossingSummand X T i j a ≫ (T ◁ biproduct.ι Vᶜ j) :=
  (biproduct_ι_comp_rightDistributor_hom_assoc Vᶜ T i _).trans
    (biproduct.ι_desc _ i)

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- The proposed crossing is natural in the induction argument. -/
theorem crossingCandidate_natural_middle {X Y : C.Obj} (h : X ⟶ Y) (T : C.Obj) :
    ((underlyingFunctor C).map h ▷ T) ≫ crossingCandidate Y T =
      crossingCandidate X T ≫ (T ◁ (underlyingFunctor C).map h) :=
  rightDistributor_ext_left (f := inductionSummand X) fun i => by
    dsimp [underlying] at *
    simp only [← Category.assoc, ← comp_whiskerRight]
    simp only [underlyingFunctor, biproduct.ι_map, comp_whiskerRight, Category.assoc,
      crossingCandidate_on_summand, Preadditive.comp_sum, Preadditive.sum_comp,
      ← whiskerLeft_comp, crossingBlock, mixedCrossing_natural_middle_assoc]

end PropertyF.Ground.CentreInduction
