module
public import PropertyF.Ground.CentreInduction.FirstTriangle
public import PropertyF.Ground.CentreInduction.Fusion

/-! Assembly of the induction adjunction from a half-braiding and its two
remaining coherence obligations. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
/-- A half-braiding on each underlying induction sum, natural in the
middle factor, lifts the underlying induction functor to the actual centre. -/
def inductionOfHalfBraiding (C : BraidedFusionCategory.{v,u})
    (b : ∀ X : C.Obj, HalfBraiding (underlying C X))
    (hb : ∀ {X Y : C.Obj} (f : X ⟶ Y) (T : C.Obj),
      ((underlyingFunctor C).map f ▷ T) ≫ ((b Y).β T).hom =
        ((b X).β T).hom ≫ (T ◁ (underlyingFunctor C).map f)) :
    C.Obj ⥤ CategoryTheory.Center C.Obj where
  obj X := ⟨underlying C X, b X⟩
  map f := ⟨(underlyingFunctor C).map f, hb f⟩
  map_id X := by
    apply CategoryTheory.Center.ext
    change (underlyingFunctor C).map (𝟙 X) = 𝟙 ((underlyingFunctor C).obj X)
    exact (underlyingFunctor C).map_id X
  map_comp f g := by apply CategoryTheory.Center.ext; simp

set_option backward.isDefEq.respectTransparency false in
/-- If the candidate unit is central for the proposed half-braiding, it lifts
to a natural transformation in the centre. -/
def inductionUnitOfCentrality (C : BraidedFusionCategory.{v,u})
    (b : ∀ X : C.Obj, HalfBraiding (underlying C X))
    (hb : ∀ {X Y : C.Obj} (f : X ⟶ Y) (T : C.Obj),
      ((underlyingFunctor C).map f ▷ T) ≫ ((b Y).β T).hom =
        ((b X).β T).hom ≫ (T ◁ (underlyingFunctor C).map f))
    (hunit : ∀ (Z : CategoryTheory.Center C.Obj) (T : C.Obj),
      (unitCandidate C Z ▷ T) ≫ ((b Z.1).β T).hom =
        (Z.2.β T).hom ≫ (T ◁ unitCandidate C Z)) :
    𝟭 (CategoryTheory.Center C.Obj) ⟶
      CategoryTheory.Center.forget C.Obj ⋙ inductionOfHalfBraiding C b hb where
  app Z := ⟨unitCandidate C Z, hunit Z⟩
  naturality {X Y} f := by
    apply CategoryTheory.Center.ext
    exact (unitCandidateNatural C).naturality f

set_option backward.isDefEq.respectTransparency false in
/-- A proposed induction half-braiding and its central unit give the
adjunction once the explicit second triangle is established. The first
triangle has already been proved from the actual half-braidings of centre
objects. Neither the proposed half-braiding, centrality, nor the second
triangle is assumed to exist by the ground target. -/
def adjunctionOfHalfBraiding (C : BraidedFusionCategory.{v,u})
    (b : ∀ X : C.Obj, HalfBraiding (underlying C X))
    (hb : ∀ {X Y : C.Obj} (f : X ⟶ Y) (T : C.Obj),
      ((underlyingFunctor C).map f ▷ T) ≫ ((b Y).β T).hom =
        ((b X).β T).hom ≫ (T ◁ (underlyingFunctor C).map f))
    (hunit : ∀ (Z : CategoryTheory.Center C.Obj) (T : C.Obj),
      (unitCandidate C Z ▷ T) ≫ ((b Z.1).β T).hom =
        (Z.2.β T).hom ≫ (T ◁ unitCandidate C Z))
    (htriangle : ∀ X : C.Obj,
      unitCandidate C ((inductionOfHalfBraiding C b hb).obj X) ≫
        (underlyingFunctor C).map ((underlyingCounit C).app X) = 𝟙 (underlying C X)) :
    CategoryTheory.Center.forget C.Obj ⊣ inductionOfHalfBraiding C b hb where
  unit := inductionUnitOfCentrality C b hb hunit
  counit := underlyingCounit C
  left_triangle_components Z := unitCandidate_counit C Z
  right_triangle_components X := by
    apply CategoryTheory.Center.ext
    exact htriangle X

/-- Once the displayed half-braiding coherences and loop sliding are proved,
the actual centre obtains its fusion structure and global FP-square identity.
Every still-unproved categorical condition is explicit in the statement. -/
theorem fusion_and_globalFPDimension_of_halfBraiding (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hne : globalDimension C ≠ 0) (hslide : SimpleLoopCentrality C p)
    (b : ∀ X : C.Obj, HalfBraiding (underlying C X))
    (hb : ∀ {X Y : C.Obj} (f : X ⟶ Y) (T : C.Obj),
      ((underlyingFunctor C).map f ▷ T) ≫ ((b Y).β T).hom =
        ((b X).β T).hom ≫ (T ◁ (underlyingFunctor C).map f))
    (hunit : ∀ (Z : CategoryTheory.Center C.Obj) (T : C.Obj),
      (unitCandidate C Z ▷ T) ≫ ((b Z.1).β T).hom =
        (Z.2.β T).hom ≫ (T ◁ unitCandidate C Z))
    (htriangle : ∀ X : C.Obj,
      unitCandidate C ((inductionOfHalfBraiding C b hb).obj X) ≫
        (underlyingFunctor C).map ((underlyingCounit C).app X) = 𝟙 (underlying C X)) :
    ∃ hFusion : IsFusionCategory (CategoryTheory.Center C.Obj),
      letI := hFusion
      globalFPDimension (Integrate.bundledCenter C) = (globalFPDimension C) ^ 2 := by
  let I := inductionOfHalfBraiding C b hb
  let adj := adjunctionOfHalfBraiding C b hb hunit htriangle
  let hFusion := fusion_of_adjunction_and_loop C p hp hslide hne I adj
  refine ⟨hFusion, ?_⟩
  letI : IsFusionCategory (CategoryTheory.Center C.Obj) := hFusion
  apply globalFPDimension_square_of_adjunction C I adj
  intro i
  exact ⟨Iso.refl _⟩

/-- It suffices to verify centrality of the proposed unit against the base
simple representatives. -/
def adjunctionOfSimpleUnitCentrality (C : BraidedFusionCategory.{v,u})
    (b : ∀ X : C.Obj, HalfBraiding (underlying C X))
    (hb : ∀ {X Y : C.Obj} (f : X ⟶ Y) (T : C.Obj),
      ((underlyingFunctor C).map f ▷ T) ≫ ((b Y).β T).hom =
        ((b X).β T).hom ≫ (T ◁ (underlyingFunctor C).map f))
    (hunit : ∀ (Z : CategoryTheory.Center C.Obj) (i : Fin (rank C)),
      (unitCandidate C Z ▷ simples C i) ≫ ((b Z.1).β (simples C i)).hom =
        (Z.2.β (simples C i)).hom ≫ (simples C i ◁ unitCandidate C Z))
    (htriangle : ∀ X : C.Obj,
      unitCandidate C ((inductionOfHalfBraiding C b hb).obj X) ≫
        (underlyingFunctor C).map ((underlyingCounit C).app X) = 𝟙 (underlying C X)) :
    CategoryTheory.Center.forget C.Obj ⊣ inductionOfHalfBraiding C b hb := by
  apply adjunctionOfHalfBraiding C b hb ?_ htriangle
  intro Z T
  exact comm_of_simples C Z ((inductionOfHalfBraiding C b hb).obj Z.1)
    (unitCandidate C Z) (hunit Z) T

set_option backward.isDefEq.respectTransparency false in
/-- The remaining induction triangle is determined by finitely many matrix
entries against the simple summands of the underlying induction object. -/
theorem secondTriangle_of_matrix_entries (C : BraidedFusionCategory.{v,u})
    (b : ∀ X : C.Obj, HalfBraiding (underlying C X))
    (hb : ∀ {X Y : C.Obj} (f : X ⟶ Y) (T : C.Obj),
      ((underlyingFunctor C).map f ▷ T) ≫ ((b Y).β T).hom =
        ((b X).β T).hom ≫ (T ◁ (underlyingFunctor C).map f))
    (hentries : ∀ (X : C.Obj) (i j : Fin (rank C)),
      let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
      biproduct.ι V i ≫
        (unitCandidate C ((inductionOfHalfBraiding C b hb).obj X) ≫
          (underlyingFunctor C).map ((underlyingCounit C).app X)) ≫ biproduct.π V j =
        biproduct.ι V i ≫ biproduct.π V j) :
    ∀ X : C.Obj,
      unitCandidate C ((inductionOfHalfBraiding C b hb).obj X) ≫
        (underlyingFunctor C).map ((underlyingCounit C).app X) = 𝟙 (underlying C X) := by
  intro X
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  simpa [underlying, Category.assoc] using hentries X i j

end PropertyF.Ground.CentreInduction
