module
public import PropertyF.Ground.CentreInduction.UnitDiagram

/-! The second induction triangle for the actual centre crossing. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.ExactPairing
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
/-- A unit component reduces to the corresponding counit-crossing matrix entry. -/
theorem unit_matrix_reduce (X : C.Obj) (i j : Fin (rank C)) :
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
  biproduct.ι V i ≫ unitComponent C ((induction C).obj X) j ≫
    ((simples C j ◁ (underlyingCounit C).app X) ▷ (simples C j)ᘁ) =
  𝟙 _ ⊗≫ ((V i) ◁ η_ (simples C j) ((simples C j)ᘁ)) ⊗≫
    (((biproduct.ι V i ▷ (simples C j)) ≫ crossingCandidate C X (simples C j) ≫
      ((simples C j) ◁ (underlyingCounit C).app X)) ▷ (simples C j)ᘁ) ⊗≫ 𝟙 _ := by
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
  let b : (⨁ V) ⊗ simples C j ⟶ simples C j ⊗ (⨁ V) := crossingCandidate C X (simples C j)
  let w : (⨁ V) ⟶ X := (underlyingCounit C).app X
  change biproduct.ι V i ≫ ((ρ_ (⨁ V)).inv ≫ ((⨁ V) ◁ η_ (simples C j) ((simples C j)ᘁ)) ≫
    (α_ (⨁ V) (simples C j) ((simples C j)ᘁ)).inv ≫ (b ▷ (simples C j)ᘁ)) ≫
      ((simples C j ◁ w) ▷ (simples C j)ᘁ) = _
  have h := unitComponent_reduce C (V i) (⨁ V) X (simples C j) b (biproduct.ι V i) w
  dsimp only [V, b, w, underlying] at *
  simpa [monoidalComp, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
/-- The off-diagonal components of the second triangle vanish. -/
theorem unit_offdiag (X : C.Obj) (i j : Fin (rank C)) (hne : i ≠ j) :
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
  biproduct.ι V i ≫ unitComponent C ((induction C).obj X) j ≫
    ((simples C j ◁ (underlyingCounit C).app X) ▷ (simples C j)ᘁ) = 0 := by
  have h := unit_matrix_reduce C X i j
  have hz := crossing_counit_offdiag C X i j hne
  dsimp only at h hz
  rw [hz] at h
  simpa [monoidalComp] using h

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal components of the second triangle are identities. -/
theorem unit_diag (X : C.Obj) (i : Fin (rank C)) :
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
  biproduct.ι V i ≫ unitComponent C ((induction C).obj X) i ≫
    ((simples C i ◁ (underlyingCounit C).app X) ▷ (simples C i)ᘁ) = 𝟙 (V i) := by
  have h := unit_matrix_reduce C X i i
  have hc := crossing_counit_diagonal C X i
  dsimp only at h hc
  rw [hc] at h
  let e : simples C (unitIndex C) ≅ 𝟙_ C.Obj := Classical.choice (unitIndex_iso C)
  have hb := crossingUnitBlock_eval C X (simples C i) (simples C (unitIndex C)) e
  change crossingBlock C X (simples C i) (simples C i) (simples C (unitIndex C))
      (simpleTensorUnitIso C i).inv (simpleTensorUnitIso C i).hom ≫
        (simples C i ◁ (unitSummandIso C X).hom) = _ at hb
  rw [hb] at h
  have ht : (𝟙 (((simples C i ⊗ X) ⊗ (simples C i)ᘁ)) ⊗≫
      (((simples C i ⊗ X) ⊗ (simples C i)ᘁ) ◁ η_ (simples C i) ((simples C i)ᘁ)) ⊗≫
      ((𝟙 ((((simples C i ⊗ X) ⊗ (simples C i)ᘁ) ⊗ simples C i)) ⊗≫
          ((simples C i ⊗ X) ◁ ε_ (simples C i) ((simples C i)ᘁ)) ⊗≫
            𝟙 (simples C i ⊗ X)) ▷
        (simples C i)ᘁ) ⊗≫ 𝟙 (((simples C i ⊗ X) ⊗ (simples C i)ᘁ))) = 𝟙 (((simples C i ⊗ X) ⊗ (simples C i)ᘁ)) := by
    calc
      _ = 𝟙 _ ⊗≫ ((simples C i ⊗ X) ◁ (((simples C i)ᘁ ◁ η_ (simples C i) ((simples C i)ᘁ)) ⊗≫
        (ε_ (simples C i) ((simples C i)ᘁ) ▷ (simples C i)ᘁ))) ⊗≫ 𝟙 _ := by monoidal
      _ = _ := by rw [coevaluation_evaluation'']; monoidal
  exact h.trans ht

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Projecting a mapped induction unit selects its corresponding component. -/
theorem unitCandidate_map_projection_general (Z : CategoryTheory.Center C.Obj) (X : C.Obj)
    (f : Z.1 ⟶ X) (j : Fin (rank C)) :
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
  (unitCandidate C Z ≫ (underlyingFunctor C).map f) ≫ biproduct.π V j =
    unitComponent C Z j ≫ ((simples C j ◁ f) ▷ (simples C j)ᘁ) := by
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
  let W : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ Z.1) ⊗ (simples C k)ᘁ
  let g : ∀ k, W k ⟶ V k := fun k => (simples C k ◁ f) ▷ (simples C k)ᘁ
  change (biproduct.lift (unitComponent C Z) ≫ biproduct.map g) ≫ biproduct.π V j =
    unitComponent C Z j ≫ g j
  calc
    _ = biproduct.lift (unitComponent C Z) ≫ (biproduct.map g ≫ biproduct.π V j) := by rw [Category.assoc]
    _ = biproduct.lift (unitComponent C Z) ≫ (biproduct.π W j ≫ g j) := by rw [biproduct.map_π]
    _ = _ := by rw [← Category.assoc, biproduct.lift_π]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every matrix entry of the second triangle has the expected value. -/
theorem secondTriangle_entry (X : C.Obj) (i j : Fin (rank C)) :
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
  biproduct.ι V i ≫
    (unitCandidate C ((induction C).obj X) ≫
      (underlyingFunctor C).map ((underlyingCounit C).app X)) ≫ biproduct.π V j =
      biproduct.ι V i ≫ biproduct.π V j := by
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
  have hp := unitCandidate_map_projection_general C ((induction C).obj X) X ((underlyingCounit C).app X) j
  have hh := congrArg (fun f => biproduct.ι V i ≫ f) hp
  simp only [Category.assoc] at hh
  change _ = _ at hh
  have hu : biproduct.ι V i ≫ unitComponent C ((induction C).obj X) j ≫
      ((simples C j ◁ (underlyingCounit C).app X) ▷ (simples C j)ᘁ) =
      biproduct.ι V i ≫ biproduct.π V j := by
    by_cases h : i = j
    · subst j
      simpa using unit_diag C X i
    · simpa [biproduct.ι_π_ne V h] using unit_offdiag C X i j h
  simpa [Category.assoc] using hh.trans hu

set_option backward.isDefEq.respectTransparency false in
/-- The proposed induction unit and counit satisfy the second triangle. -/
theorem secondTriangle (X : C.Obj) :
    unitCandidate C ((induction C).obj X) ≫
      (underlyingFunctor C).map ((underlyingCounit C).app X) = 𝟙 (underlying C X) := by
  apply secondTriangle_of_matrix_entries C (halfBraidingOfCrossingCandidate C)
    (halfBraidingOfCrossingCandidate_natural C) (secondTriangle_entry C) X

end PropertyF.Ground.CentreInduction
