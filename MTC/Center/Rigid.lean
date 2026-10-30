module
public import MTC.PropertyF.Reduction.CenterBundle

/-!
# Rigidity of the Drinfeld centre

The normalized mate of a centre object's half-braiding gives a half-braiding
on its right dual. Its tensor law and the centrality of evaluation and
coevaluation lift the underlying dual pair to the centre.

The main construction is `MTC.Center.Rigid.rigidCenter`. The intermediate
`dualObject` and `liftedPairing` make the coherence conditions explicit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Rigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

set_option backward.isDefEq.respectTransparency false in
omit [RigidCategory C] in
/-- The half-braiding of every centre object has its forced unit component. -/
theorem halfBraiding_unit (Z : CategoryTheory.Center C) :
    (Z.2.β (𝟙_ C)).hom = (ρ_ Z.1).hom ≫ (λ_ Z.1).inv := by
  have h := congrArg CategoryTheory.Center.Hom.f
    (CategoryTheory.braiding_tensorUnit_right Z)
  simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.rightUnitor_hom_f,
    CategoryTheory.Center.leftUnitor_inv_f] at h
  exact h

end MTC.Center.Rigid

/-! Lifting the underlying duality to the actual centre. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Rigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- The normalized dual crossing respects tensor products. -/
abbrev IsDualCrossingMonoidal (Z : CategoryTheory.Center C) : Prop :=
  ∀ U V : C, ((Integrate.dualCrossingIso Z).app (U ⊗ V)).hom =
    (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ V) ≫
      (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫
        (α_ _ _ _).inv

/-- If the normalized mate satisfies the half-braiding law, it defines an
object of the actual centre on the underlying right dual. -/
def dualObject (Z : CategoryTheory.Center C)
    (hTensor : IsDualCrossingMonoidal Z) : CategoryTheory.Center C :=
  ⟨Z.1ᘁ, {
    β := fun U => (Integrate.dualCrossingIso Z).app U
    monoidal := hTensor
    naturality := fun f => Integrate.dualCrossing_natural Z f }⟩

set_option backward.isDefEq.respectTransparency false in
/-- Once the underlying duality maps intertwine the lifted half-braidings,
their triangle identities lift through the faithful forgetful functor. -/
@[instance_reducible] def liftedPairing (Z : CategoryTheory.Center C)
    (hTensor : IsDualCrossingMonoidal Z)
    (hCo : ∀ U, ((η_ Z.1 Z.1ᘁ) ▷ U) ≫
      ((Z ⊗ dualObject Z hTensor).2.β U).hom =
      ((𝟙_ (CategoryTheory.Center C)).2.β U).hom ≫ (U ◁ η_ Z.1 Z.1ᘁ))
    (hEv : ∀ U, ((ε_ Z.1 Z.1ᘁ) ▷ U) ≫
      ((𝟙_ (CategoryTheory.Center C)).2.β U).hom =
      ((dualObject Z hTensor ⊗ Z).2.β U).hom ≫ (U ◁ ε_ Z.1 Z.1ᘁ)) :
    ExactPairing Z (dualObject Z hTensor) where
  coevaluation' := ⟨η_ Z.1 Z.1ᘁ, hCo⟩
  evaluation' := ⟨ε_ Z.1 Z.1ᘁ, hEv⟩
  coevaluation_evaluation' := by
    apply CategoryTheory.Center.ext
    simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.whiskerLeft_f,
      CategoryTheory.Center.whiskerRight_f, CategoryTheory.Center.associator_inv_f,
      CategoryTheory.Center.rightUnitor_hom_f, CategoryTheory.Center.leftUnitor_inv_f,
]
    exact ExactPairing.coevaluation_evaluation Z.1 Z.1ᘁ
  evaluation_coevaluation' := by
    apply CategoryTheory.Center.ext
    simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.whiskerLeft_f,
      CategoryTheory.Center.whiskerRight_f, CategoryTheory.Center.associator_hom_f,
      CategoryTheory.Center.leftUnitor_hom_f, CategoryTheory.Center.rightUnitor_inv_f,
]
    exact ExactPairing.evaluation_coevaluation Z.1 Z.1ᘁ

/-- If the mate satisfies its tensor law and both duality maps are central for
every object, the actual centre is rigid. These coherence equations remain
explicit hypotheses. -/
@[instance_reducible] def rigidOfMateCoherence
    (h : ∀ Z : CategoryTheory.Center C,
      ∃ (hTensor : IsDualCrossingMonoidal Z),
        (∀ U, ((η_ Z.1 Z.1ᘁ) ▷ U) ≫
          ((Z ⊗ dualObject Z hTensor).2.β U).hom =
          ((𝟙_ (CategoryTheory.Center C)).2.β U).hom ≫ (U ◁ η_ Z.1 Z.1ᘁ)) ∧
        (∀ U, ((ε_ Z.1 Z.1ᘁ) ▷ U) ≫
          ((𝟙_ (CategoryTheory.Center C)).2.β U).hom =
          ((dualObject Z hTensor ⊗ Z).2.β U).hom ≫ (U ◁ ε_ Z.1 Z.1ᘁ))) :
    RigidCategory (CategoryTheory.Center C) := by
  letI : RightRigidCategory (CategoryTheory.Center C) := {
    rightDual := fun Z => {
      rightDual := dualObject Z (Classical.choose (h Z))
      exact := liftedPairing Z (Classical.choose (h Z))
        (Classical.choose_spec (h Z)).1 (Classical.choose_spec (h Z)).2 } }
  exact BraidedCategory.rigidCategoryOfRightRigidCategory

end MTC.Center.Rigid

/-! The normalized dual candidate starts from an adjoint mate. These equations
expose its compatibility with the units and counits of the tensor adjunctions. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory MTC.Integrate
namespace MTC.Center.Rigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

theorem dualMate_unit (Z : CategoryTheory.Center C) (U : C) :
    (tensorLeftAdjunction Z.1 Z.1ᘁ).unit.app U ≫
      (Integrate.halfBraidingIso Z).hom.app
        ((tensorLeft Z.1ᘁ).obj U) =
    (tensorRightAdjunction (ᘁZ.1) Z.1).unit.app U ≫
      (tensorRight Z.1).map ((Integrate.dualMateIso Z).inv.app U) := by
  simpa [Integrate.dualMateIso] using unit_conjugateEquiv_symm
    (tensorLeftAdjunction Z.1 Z.1ᘁ) (tensorRightAdjunction (ᘁZ.1) Z.1) (halfBraidingIso Z).hom U

end MTC.Center.Rigid

/-! Componentwise cup and cap identities for the dual mate. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Rigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- The mate unit in terms of the actual base coevaluation maps. -/
theorem dualMate_unit_explicit (Z : Center C) (U : C) :
  (λ_ U).inv ≫ (η_ Z.1 Z.1ᘁ ▷ U) ≫ (α_ Z.1 Z.1ᘁ U).hom ≫ MTC.Center.halfBraidingHom Z (Z.1ᘁ ⊗ U) =
  (ρ_ U).inv ≫ (U ◁ η_ (ᘁZ.1) Z.1) ≫ (α_ U (ᘁZ.1) Z.1).inv ≫
    ((Integrate.dualMateIso Z).inv.app U ▷ Z.1) := by
  simpa [tensorRightAdjunction, tensorLeftAdjunction, tensorRightHomEquiv,
    tensorLeftHomEquiv, Integrate.halfBraidingIso] using MTC.Center.Rigid.dualMate_unit Z U

set_option backward.isDefEq.respectTransparency false in
/-- The unit component identifies the two chosen duals compatibly with the crossed cup. -/
theorem dualMateUnit_crossed_coevaluation (Z : Center C) :
  η_ Z.1 Z.1ᘁ ≫ (Z.2.β (Z.1ᘁ)).hom =
  η_ (ᘁZ.1) Z.1 ≫ ((Integrate.dualMateUnit Z).inv ▷ Z.1) := by
  have h := MTC.Center.Rigid.dualMate_unit_explicit Z (𝟙_ C)
  have hn := Z.2.naturality (ρ_ Z.1ᘁ).hom
  dsimp [Integrate.dualMateUnit]
  simp only [Category.assoc, comp_whiskerRight]
  calc
    _ = ((λ_ (𝟙_ C)).inv ≫ (η_ Z.1 Z.1ᘁ ▷ (𝟙_ C)) ≫
        (α_ Z.1 Z.1ᘁ (𝟙_ C)).hom ≫ (Z.2.β (Z.1ᘁ ⊗ (𝟙_ C))).hom) ≫
          ((ρ_ Z.1ᘁ).hom ▷ Z.1) := by rw [Category.assoc, Category.assoc, Category.assoc, ← hn]; monoidal
    _ = ((ρ_ (𝟙_ C)).inv ≫ ((𝟙_ C) ◁ η_ (ᘁZ.1) Z.1) ≫
        (α_ (𝟙_ C) (ᘁZ.1) Z.1).inv ≫ ((Integrate.dualMateIso Z).inv.app (𝟙_ C) ▷ Z.1)) ≫
          ((ρ_ Z.1ᘁ).hom ▷ Z.1) := by rw [h]
    _ = _ := by monoidal

end MTC.Center.Rigid

/-! Coevaluation centrality for the normalized dual crossing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Rigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- The normalized dual crossing intertwines the coevaluation. -/
theorem coevaluation_sliding (Z : Center C) (U : C) :
    𝟙 U ⊗≫ (η_ Z.1 Z.1ᘁ ▷ U) ⊗≫
      (Z.1 ◁ (show Z.1ᘁ ⊗ U ⟶ U ⊗ Z.1ᘁ from ((Integrate.dualCrossingIso Z).app U).hom)) ⊗≫
      ((Z.2.β U).hom ▷ Z.1ᘁ) ⊗≫ 𝟙 (U ⊗ (Z.1 ⊗ Z.1ᘁ)) =
    𝟙 U ⊗≫ (U ◁ η_ Z.1 Z.1ᘁ) ⊗≫ 𝟙 (U ⊗ (Z.1 ⊗ Z.1ᘁ)) := by
  let X := Z.1
  let D : C := Z.1ᘁ
  let L : C := ᘁZ.1
  let f : L ⟶ D := (Integrate.dualMateUnit Z).inv
  let m : D ⊗ U ⟶ U ⊗ L := (Integrate.dualMateIso Z).hom.app U
  let n : U ⊗ L ⟶ D ⊗ U := (Integrate.dualMateIso Z).inv.app U
  let c (T : C) : X ⊗ T ⟶ T ⊗ X := (Z.2.β T).hom
  have hm : n ≫ m = 𝟙 _ := by simp [n, m, L]
  have hf : (X ◁ f) ≫ c D = c L ≫ (f ▷ X) := Z.2.naturality f
  have hn : (X ◁ m) ≫ c (U ⊗ L) = c (D ⊗ U) ≫ (m ▷ X) := Z.2.naturality m
  have ht1 := Z.2.monoidal D U
  have ht2 := Z.2.monoidal U L
  change c (U ⊗ L) = (α_ X U L).inv ≫ (c U ▷ L) ≫ (α_ U X L).hom ≫ (U ◁ c L) ≫ (α_ U L X).inv at ht2
  have hu := MTC.Center.Rigid.dualMate_unit_explicit Z U
  change (λ_ U).inv ≫ (η_ X D ▷ U) ≫ (α_ X D U).hom ≫ c (D ⊗ U) = (ρ_ U).inv ≫ (U ◁ η_ L X) ≫ (α_ U L X).inv ≫ (n ▷ X) at hu
  have hc : η_ X D ≫ c D = η_ L X ≫ (f ▷ X) := MTC.Center.Rigid.dualMateUnit_crossed_coevaluation Z
  have hx : (show D ⊗ U ⟶ U ⊗ D from ((Integrate.dualCrossingIso Z).app U).hom) = m ≫ (U ◁ f) := by
    rfl
  rw [hx]
  apply (cancel_mono (U ◁ c D)).1
  calc
    _ = 𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ (X ◁ m) ⊗≫
      ((((X ⊗ U) ◁ f) ≫ (c U ▷ D))) ⊗≫ (U ◁ c D) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by monoidal
    _ = 𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ (X ◁ m) ⊗≫
      (((c U ▷ L) ≫ ((U ⊗ X) ◁ f))) ⊗≫ (U ◁ c D) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by rw [whisker_exchange]
    _ = 𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ (X ◁ m) ⊗≫ (c U ▷ L) ⊗≫
      (U ◁ ((X ◁ f) ≫ c D)) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by monoidal
    _ = 𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ (X ◁ m) ⊗≫ (c U ▷ L) ⊗≫
      (U ◁ (c L ≫ (f ▷ X))) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by rw [hf]
    _ = 𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ ((X ◁ m) ≫ c (U ⊗ L)) ⊗≫
      (U ◁ (f ▷ X)) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by rw [ht2]; monoidal
    _ = 𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ ((c (D ⊗ U)) ≫ (m ▷ X)) ⊗≫
      (U ◁ (f ▷ X)) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by rw [hn]
    _ = ((λ_ U).inv ≫ (η_ X D ▷ U) ≫ (α_ X D U).hom ≫ c (D ⊗ U)) ≫
      (m ▷ X) ≫ (α_ U L X).hom ≫ (U ◁ (f ▷ X)) := by monoidal
    _ = ((ρ_ U).inv ≫ (U ◁ η_ L X) ≫ (α_ U L X).inv ≫ (n ▷ X)) ≫
      (m ▷ X) ≫ (α_ U L X).hom ≫ (U ◁ (f ▷ X)) := by rw [hu]
    _ = 𝟙 U ⊗≫ (U ◁ η_ L X) ⊗≫ ((n ≫ m) ▷ X) ⊗≫ (U ◁ (f ▷ X)) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by monoidal
    _ = 𝟙 U ⊗≫ (U ◁ (η_ L X ≫ (f ▷ X))) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by rw [hm]; monoidal
    _ = _ := by rw [← hc]; monoidal

set_option backward.isDefEq.respectTransparency false in
/-- If the normalized crossing is monoidal, the chosen coevaluation is a
morphism in the actual centre, without further hypotheses. -/
theorem coevaluation_central {Z : Center C}
    (hTensor : IsDualCrossingMonoidal Z) (U : C) :
    ((η_ Z.1 Z.1ᘁ) ▷ U) ≫ ((Z ⊗ dualObject Z hTensor).2.β U).hom =
      ((𝟙_ (Center C)).2.β U).hom ≫ (U ◁ η_ Z.1 Z.1ᘁ) := by
  have h := coevaluation_sliding Z U
  change (η_ Z.1 Z.1ᘁ ▷ U) ≫
    ((α_ Z.1 Z.1ᘁ U).hom ≫ (Z.1 ◁ ((Integrate.dualCrossingIso Z).app U).hom) ≫
      (α_ Z.1 U Z.1ᘁ).inv ≫ ((Z.2.β U).hom ▷ Z.1ᘁ) ≫ (α_ U Z.1 Z.1ᘁ).hom) =
    ((λ_ U).hom ≫ (ρ_ U).inv) ≫ (U ◁ η_ Z.1 Z.1ᘁ)
  calc
    _ = (λ_ U).hom ≫ (𝟙 U ⊗≫ (η_ Z.1 Z.1ᘁ ▷ U) ⊗≫
      (Z.1 ◁ (show Z.1ᘁ ⊗ U ⟶ U ⊗ Z.1ᘁ from ((Integrate.dualCrossingIso Z).app U).hom)) ⊗≫
      ((Z.2.β U).hom ▷ Z.1ᘁ) ⊗≫ 𝟙 (U ⊗ (Z.1 ⊗ Z.1ᘁ))) := by monoidal
    _ = (λ_ U).hom ≫ (𝟙 U ⊗≫ (U ◁ η_ Z.1 Z.1ᘁ) ⊗≫ 𝟙 (U ⊗ (Z.1 ⊗ Z.1ᘁ))) := by rw [h]
    _ = _ := by monoidal

end MTC.Center.Rigid

/-! Tensor coherence of the normalized dual half-braiding. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Rigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- The normalized dual crossing satisfies the half-braiding tensor law. -/
theorem dualCrossing_tensor (Z : Center C) (U V : C) :
    ((Integrate.dualCrossingIso Z).app (U ⊗ V)).hom =
      (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ V) ≫
        (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫ (α_ _ _ _).inv := by
  let X := Z.1
  let D : C := Z.1ᘁ
  let c (T : C) : X ⊗ T ⟶ T ⊗ X := (Z.2.β T).hom
  let d (T : C) : D ⊗ T ⟶ T ⊗ D := ((Integrate.dualCrossingIso Z).app T).hom
  let p : D ⊗ (U ⊗ V) ⟶ (U ⊗ V) ⊗ D :=
    (α_ D U V).inv ≫ (d U ▷ V) ≫ (α_ U D V).hom ≫ (U ◁ d V) ≫ (α_ U V D).inv
  have hs (T : C) :
      𝟙 T ⊗≫ (η_ X D ▷ T) ⊗≫ (X ◁ d T) ⊗≫ (c T ▷ D) ⊗≫ 𝟙 (T ⊗ (X ⊗ D)) =
        𝟙 T ⊗≫ (T ◁ η_ X D) ⊗≫ 𝟙 (T ⊗ (X ⊗ D)) := MTC.Center.Rigid.coevaluation_sliding Z T
  have ht : c (U ⊗ V) = (α_ X U V).inv ≫ (c U ▷ V) ≫ (α_ U X V).hom ≫ (U ◁ c V) ≫ (α_ U V X).inv := Z.2.monoidal U V
  have hp :
      𝟙 (U ⊗ V) ⊗≫ (η_ X D ▷ (U ⊗ V)) ⊗≫ (X ◁ p) ⊗≫ (c (U ⊗ V) ▷ D) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) =
        𝟙 (U ⊗ V) ⊗≫ ((U ⊗ V) ◁ η_ X D) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by
    rw [ht]
    dsimp [p]
    calc
      _ = 𝟙 (U ⊗ V) ⊗≫ ((η_ X D ▷ U) ▷ V) ⊗≫ ((X ◁ d U) ▷ V) ⊗≫
        (((X ⊗ U) ◁ d V) ≫ (c U ▷ (V ⊗ D))) ⊗≫ (U ◁ (c V ▷ D)) ⊗≫
          𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by monoidal
      _ = 𝟙 (U ⊗ V) ⊗≫ ((η_ X D ▷ U) ▷ V) ⊗≫ ((X ◁ d U) ▷ V) ⊗≫
        ((c U ▷ (D ⊗ V)) ≫ ((U ⊗ X) ◁ d V)) ⊗≫ (U ◁ (c V ▷ D)) ⊗≫
          𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by rw [whisker_exchange]
      _ = 𝟙 (U ⊗ V) ⊗≫
        ((𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ (X ◁ d U) ⊗≫ (c U ▷ D) ⊗≫ 𝟙 (U ⊗ (X ⊗ D))) ▷ V) ⊗≫
        (U ◁ (X ◁ d V)) ⊗≫ (U ◁ (c V ▷ D)) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by monoidal
      _ = 𝟙 (U ⊗ V) ⊗≫
        ((𝟙 U ⊗≫ (U ◁ η_ X D) ⊗≫ 𝟙 (U ⊗ (X ⊗ D))) ▷ V) ⊗≫
        (U ◁ (X ◁ d V)) ⊗≫ (U ◁ (c V ▷ D)) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by rw [hs U]
      _ = 𝟙 (U ⊗ V) ⊗≫ (U ◁ (𝟙 V ⊗≫ (η_ X D ▷ V) ⊗≫ (X ◁ d V) ⊗≫ (c V ▷ D) ⊗≫ 𝟙 (V ⊗ (X ⊗ D)))) ⊗≫
        𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by monoidal
      _ = 𝟙 (U ⊗ V) ⊗≫ (U ◁ (𝟙 V ⊗≫ (V ◁ η_ X D) ⊗≫ 𝟙 (V ⊗ (X ⊗ D)))) ⊗≫
        𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by rw [hs V]
      _ = _ := by monoidal
  apply (tensorLeftHomEquiv (U ⊗ V) X D ((U ⊗ V) ⊗ D)).injective
  have eq1 : 𝟙 (U ⊗ V) ⊗≫ (η_ X D ▷ (U ⊗ V)) ⊗≫ (X ◁ d (U ⊗ V)) ⊗≫ (c (U ⊗ V) ▷ D) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) =
      𝟙 (U ⊗ V) ⊗≫ (η_ X D ▷ (U ⊗ V)) ⊗≫ (X ◁ p) ⊗≫ (c (U ⊗ V) ▷ D) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by
    calc
      _ = 𝟙 (U ⊗ V) ⊗≫ ((U ⊗ V) ◁ η_ X D) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by
        convert hs (U ⊗ V) using 1 <;> monoidal
      _ = _ := hp.symm
  change (λ_ (U ⊗ V)).inv ≫ (η_ X D ▷ (U ⊗ V)) ≫ (α_ X D (U ⊗ V)).hom ≫ (X ◁ d (U ⊗ V)) =
    (λ_ (U ⊗ V)).inv ≫ (η_ X D ▷ (U ⊗ V)) ≫ (α_ X D (U ⊗ V)).hom ≫ (X ◁ p)
  apply (cancel_mono ((α_ X (U ⊗ V) D).inv ≫ (c (U ⊗ V) ▷ D) ≫ (α_ (U ⊗ V) X D).hom)).1
  calc
    _ = 𝟙 (U ⊗ V) ⊗≫ (η_ X D ▷ (U ⊗ V)) ⊗≫ (X ◁ d (U ⊗ V)) ⊗≫ (c (U ⊗ V) ▷ D) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by monoidal
    _ = 𝟙 (U ⊗ V) ⊗≫ (η_ X D ▷ (U ⊗ V)) ⊗≫ (X ◁ p) ⊗≫ (c (U ⊗ V) ▷ D) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := eq1
    _ = _ := by monoidal

end MTC.Center.Rigid

/-! Evaluation centrality and rigidity of the Drinfeld centre. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.ExactPairing
namespace MTC.Center.Rigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- The normalized dual crossing intertwines the evaluation. -/
theorem evaluation_sliding (Z : Center C) (U : C) :
    𝟙 ((Z.1ᘁ ⊗ Z.1) ⊗ U) ⊗≫ (ε_ Z.1 Z.1ᘁ ▷ U) ⊗≫ 𝟙 (U ⊗ (𝟙_ C)) =
    𝟙 ((Z.1ᘁ ⊗ Z.1) ⊗ U) ⊗≫ (Z.1ᘁ ◁ (Z.2.β U).hom) ⊗≫
      (show Z.1ᘁ ⊗ U ⟶ U ⊗ Z.1ᘁ from ((Integrate.dualCrossingIso Z).app U).hom) ▷ Z.1 ⊗≫
      (U ◁ ε_ Z.1 Z.1ᘁ) ⊗≫ 𝟙 (U ⊗ (𝟙_ C)) := by
  let X := Z.1
  let D : C := Z.1ᘁ
  let c : X ⊗ U ⟶ U ⊗ X := (Z.2.β U).hom
  let cInv : U ⊗ X ⟶ X ⊗ U := (Z.2.β U).inv
  let d : D ⊗ U ⟶ U ⊗ D := ((Integrate.dualCrossingIso Z).app U).hom
  have hslide := MTC.Center.Rigid.coevaluation_sliding Z U
  have hc : cInv ≫ c = 𝟙 (U ⊗ X) := by simp [cInv, c, X]
  apply (cancel_epi (α_ D X U).inv).1
  apply (tensorLeftHomEquiv (X ⊗ U) X D (U ⊗ (𝟙_ C))).injective
  apply (cancel_epi cInv).1
  apply (cancel_mono ((X ◁ (ρ_ U).hom) ≫ c)).1
  dsimp only [tensorLeftHomEquiv, Equiv.coe_fn_mk]
  calc
    _ = 𝟙 (U ⊗ X) := by
      calc
        _ = 𝟙 (U ⊗ X) ⊗≫ cInv ⊗≫
          ((η_ X D ▷ X ⊗≫ X ◁ ε_ X D) ▷ U) ⊗≫ c ⊗≫ 𝟙 (U ⊗ X) := by monoidal
        _ = 𝟙 (U ⊗ X) ⊗≫ (cInv ≫ c) ⊗≫ 𝟙 (U ⊗ X) := by rw [evaluation_coevaluation'']; monoidal
        _ = _ := by rw [hc]; monoidal
    _ = _ := by
      symm
      change 𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ (X ◁ d) ⊗≫ (c ▷ D) ⊗≫ 𝟙 (U ⊗ (X ⊗ D)) =
        𝟙 U ⊗≫ (U ◁ η_ X D) ⊗≫ 𝟙 (U ⊗ (X ⊗ D)) at hslide
      calc
        _ = 𝟙 (U ⊗ X) ⊗≫ (((𝟙_ C) ◁ cInv) ≫ (η_ X D ▷ (X ⊗ U))) ⊗≫
          (X ◁ (D ◁ c)) ⊗≫ (X ◁ (d ▷ X)) ⊗≫ (X ◁ (U ◁ ε_ X D)) ⊗≫ c ⊗≫ 𝟙 (U ⊗ X) := by monoidal
        _ = 𝟙 (U ⊗ X) ⊗≫ ((η_ X D ▷ (U ⊗ X)) ≫ ((X ⊗ D) ◁ cInv)) ⊗≫
          (X ◁ (D ◁ c)) ⊗≫ (X ◁ (d ▷ X)) ⊗≫ (X ◁ (U ◁ ε_ X D)) ⊗≫ c ⊗≫ 𝟙 (U ⊗ X) := by rw [whisker_exchange]
        _ = 𝟙 (U ⊗ X) ⊗≫ (η_ X D ▷ (U ⊗ X)) ⊗≫
          (X ◁ (D ◁ (cInv ≫ c))) ⊗≫ (X ◁ (d ▷ X)) ⊗≫ (X ◁ (U ◁ ε_ X D)) ⊗≫ c ⊗≫ 𝟙 (U ⊗ X) := by monoidal
        _ = 𝟙 (U ⊗ X) ⊗≫ (η_ X D ▷ (U ⊗ X)) ⊗≫
          (X ◁ (d ▷ X)) ⊗≫ (X ◁ (U ◁ ε_ X D)) ⊗≫ c ⊗≫ 𝟙 (U ⊗ X) := by rw [hc]; monoidal
        _ = 𝟙 (U ⊗ X) ⊗≫ ((η_ X D ▷ U) ▷ X) ⊗≫ ((X ◁ d) ▷ X) ⊗≫
          (((X ⊗ U) ◁ ε_ X D) ≫ (c ▷ (𝟙_ C))) ⊗≫ 𝟙 (U ⊗ X) := by monoidal
        _ = 𝟙 (U ⊗ X) ⊗≫ ((η_ X D ▷ U) ▷ X) ⊗≫ ((X ◁ d) ▷ X) ⊗≫
          ((c ▷ (D ⊗ X)) ≫ ((U ⊗ X) ◁ ε_ X D)) ⊗≫ 𝟙 (U ⊗ X) := by rw [whisker_exchange]
        _ = 𝟙 (U ⊗ X) ⊗≫ ((𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ (X ◁ d) ⊗≫ (c ▷ D) ⊗≫ 𝟙 (U ⊗ (X ⊗ D))) ▷ X) ⊗≫
          (U ◁ (X ◁ ε_ X D)) ⊗≫ 𝟙 (U ⊗ X) := by monoidal
        _ = 𝟙 (U ⊗ X) ⊗≫ ((𝟙 U ⊗≫ (U ◁ η_ X D) ⊗≫ 𝟙 (U ⊗ (X ⊗ D))) ▷ X) ⊗≫
          (U ◁ (X ◁ ε_ X D)) ⊗≫ 𝟙 (U ⊗ X) := by rw [hslide]
        _ = 𝟙 (U ⊗ X) ⊗≫ (U ◁ (η_ X D ▷ X ⊗≫ X ◁ ε_ X D)) ⊗≫ 𝟙 (U ⊗ X) := by monoidal
        _ = _ := by rw [evaluation_coevaluation'']; monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The chosen base evaluation is a morphism of actual centre objects. -/
theorem evaluation_central {Z : Center C}
    (hTensor : IsDualCrossingMonoidal Z) (U : C) :
    ((ε_ Z.1 Z.1ᘁ) ▷ U) ≫ ((𝟙_ (Center C)).2.β U).hom =
      ((dualObject Z hTensor ⊗ Z).2.β U).hom ≫ (U ◁ ε_ Z.1 Z.1ᘁ) := by
  have h := evaluation_sliding Z U
  change (ε_ Z.1 Z.1ᘁ ▷ U) ≫ ((λ_ U).hom ≫ (ρ_ U).inv) =
    ((α_ Z.1ᘁ Z.1 U).hom ≫ (Z.1ᘁ ◁ (Z.2.β U).hom) ≫
      (α_ Z.1ᘁ U Z.1).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ Z.1) ≫
      (α_ U Z.1ᘁ Z.1).hom) ≫ (U ◁ ε_ Z.1 Z.1ᘁ)
  calc
    _ = (𝟙 ((Z.1ᘁ ⊗ Z.1) ⊗ U) ⊗≫ (ε_ Z.1 Z.1ᘁ ▷ U) ⊗≫ 𝟙 (U ⊗ (𝟙_ C))) := by monoidal
    _ = (𝟙 ((Z.1ᘁ ⊗ Z.1) ⊗ U) ⊗≫ (Z.1ᘁ ◁ (Z.2.β U).hom) ⊗≫
      (show Z.1ᘁ ⊗ U ⟶ U ⊗ Z.1ᘁ from ((Integrate.dualCrossingIso Z).app U).hom) ▷ Z.1 ⊗≫
      (U ◁ ε_ Z.1 Z.1ᘁ) ⊗≫ 𝟙 (U ⊗ (𝟙_ C))) := h
    _ = _ := by monoidal

/-- The actual Drinfeld centre of a rigid monoidal category is rigid. -/
@[instance_reducible] def rigidCenter : RigidCategory (Center C) := by
  apply rigidOfMateCoherence
  intro Z
  refine ⟨dualCrossing_tensor Z, coevaluation_central (dualCrossing_tensor Z),
    evaluation_central (dualCrossing_tensor Z)⟩

end MTC.Center.Rigid
