module
public import PropertyF.Ground.Centre.Zero
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-! Binary biproducts in the Drinfeld centre. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasBinaryBiproducts C]

local instance (U : C) : PreservesBinaryBiproducts (tensorRight U) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

local instance (U : C) : PreservesBinaryBiproducts (tensorLeft U) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- The distributive half-braiding of a binary direct sum. -/
def sumHalfIso (X Y : CategoryTheory.Center C) (U : C) :
    (X.1 ⊞ Y.1) ⊗ U ≅ U ⊗ (X.1 ⊞ Y.1) :=
  Functor.mapBiprod (tensorRight U) X.1 Y.1 ≪≫
    biprod.mapIso (X.2.β U) (Y.2.β U) ≪≫
      (Functor.mapBiprod (tensorLeft U) X.1 Y.1).symm

@[reassoc]
theorem inl_sumHalfIso (X Y : CategoryTheory.Center C) (U : C) :
    biprod.inl ▷ U ≫ (sumHalfIso X Y U).hom = (X.2.β U).hom ≫ U ◁ biprod.inl := by
  have h : biprod.inl ▷ U ≫ (Functor.mapBiprod (tensorRight U) X.1 Y.1).hom = biprod.inl := by
    apply (Iso.eq_comp_inv (Functor.mapBiprod (tensorRight U) X.1 Y.1)).mp
    simp only [Functor.mapBiprod_inv, biprod.inl_desc]
    rfl
  dsimp only [sumHalfIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [biprod.mapIso, biprod.inl_map]
  rw [Functor.mapBiprod_inv, Category.assoc, biprod.inl_desc]
  rfl

@[reassoc]
theorem inr_sumHalfIso (X Y : CategoryTheory.Center C) (U : C) :
    biprod.inr ▷ U ≫ (sumHalfIso X Y U).hom = (Y.2.β U).hom ≫ U ◁ biprod.inr := by
  have h : biprod.inr ▷ U ≫ (Functor.mapBiprod (tensorRight U) X.1 Y.1).hom = biprod.inr := by
    apply (Iso.eq_comp_inv (Functor.mapBiprod (tensorRight U) X.1 Y.1)).mp
    simp only [Functor.mapBiprod_inv, biprod.inr_desc]
    rfl
  dsimp only [sumHalfIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [biprod.mapIso, biprod.inr_map]
  rw [Functor.mapBiprod_inv, Category.assoc, biprod.inr_desc]
  rfl

/-- Naturality of the half-braiding of a direct sum. -/
theorem sumHalfIso_naturality (X Y : CategoryTheory.Center C) {U V : C} (f : U ⟶ V) :
    (X.1 ⊞ Y.1) ◁ f ≫ (sumHalfIso X Y V).hom =
      (sumHalfIso X Y U).hom ≫ f ▷ (X.1 ⊞ Y.1) := by
  apply (cancel_epi (Functor.mapBiprod (tensorRight U) X.1 Y.1).inv).mp
  apply biprod.hom_ext'
  · have hι : biprod.inl ≫ (Functor.mapBiprod (tensorRight U) X.1 Y.1).inv =
        biprod.inl ▷ U := by
      rw [Functor.mapBiprod_inv, biprod.inl_desc]
      rfl
    simp only [← Category.assoc, hι]
    simp [← whisker_exchange_assoc, inl_sumHalfIso]
    rw [HalfBraiding.naturality_assoc, ← Category.assoc, whisker_exchange]
    simp only [Category.assoc]
  · have hι : biprod.inr ≫ (Functor.mapBiprod (tensorRight U) X.1 Y.1).inv =
        biprod.inr ▷ U := by
      rw [Functor.mapBiprod_inv, biprod.inr_desc]
      rfl
    simp only [← Category.assoc, hι]
    simp [← whisker_exchange_assoc, inr_sumHalfIso]
    rw [HalfBraiding.naturality_assoc, ← Category.assoc, whisker_exchange]
    simp only [Category.assoc]

/-- Compatibility of the sum half-braiding with tensor products. -/
theorem sumHalfIso_monoidal (X Y : CategoryTheory.Center C) (U V : C) :
    (sumHalfIso X Y (U ⊗ V)).hom =
      (α_ _ _ _).inv ≫ ((sumHalfIso X Y U).hom ▷ V) ≫ (α_ _ _ _).hom ≫
        (U ◁ (sumHalfIso X Y V).hom) ≫ (α_ _ _ _).inv := by
  apply (cancel_epi (Functor.mapBiprod (tensorRight (U ⊗ V)) X.1 Y.1).inv).mp
  apply biprod.hom_ext'
  · have hι : biprod.inl ≫ (Functor.mapBiprod (tensorRight (U ⊗ V)) X.1 Y.1).inv =
        biprod.inl ▷ (U ⊗ V) := by
      rw [Functor.mapBiprod_inv, biprod.inl_desc]
      rfl
    simp only [← Category.assoc, hι]
    simp only [Category.assoc, associator_inv_naturality_left_assoc,
      ← comp_whiskerRight_assoc, inl_sumHalfIso, HalfBraiding.monoidal]
    simp only [comp_whiskerRight, Category.assoc, associator_naturality_middle_assoc,
      ← whiskerLeft_comp_assoc, inl_sumHalfIso]
    simp only [whiskerLeft_comp, Category.assoc, associator_inv_naturality_right]
  · have hι : biprod.inr ≫ (Functor.mapBiprod (tensorRight (U ⊗ V)) X.1 Y.1).inv =
        biprod.inr ▷ (U ⊗ V) := by
      rw [Functor.mapBiprod_inv, biprod.inr_desc]
      rfl
    simp only [← Category.assoc, hι]
    simp only [Category.assoc, associator_inv_naturality_left_assoc,
      ← comp_whiskerRight_assoc, inr_sumHalfIso, HalfBraiding.monoidal]
    simp only [comp_whiskerRight, Category.assoc, associator_naturality_middle_assoc,
      ← whiskerLeft_comp_assoc, inr_sumHalfIso]
    simp only [whiskerLeft_comp, Category.assoc, associator_inv_naturality_right]

/-- The centre object whose underlying object is a binary biproduct. -/
def centerBiprod (X Y : CategoryTheory.Center C) : CategoryTheory.Center C :=
  ⟨X.1 ⊞ Y.1,
    { β := sumHalfIso X Y
      monoidal := sumHalfIso_monoidal X Y
      naturality := fun f => sumHalfIso_naturality X Y f }⟩

/-- The usual inclusion is a centre morphism. -/
def centerBiprodInl (X Y : CategoryTheory.Center C) : X ⟶ centerBiprod X Y :=
  ⟨biprod.inl, fun U => inl_sumHalfIso X Y U⟩

/-- The other usual inclusion is a centre morphism. -/
def centerBiprodInr (X Y : CategoryTheory.Center C) : Y ⟶ centerBiprod X Y :=
  ⟨biprod.inr, fun U => inr_sumHalfIso X Y U⟩

/-- The first projection commutes with the sum half-braiding. -/
theorem sumHalfIso_fst (X Y : CategoryTheory.Center C) (U : C) :
    biprod.fst ▷ U ≫ (X.2.β U).hom = (sumHalfIso X Y U).hom ≫ U ◁ biprod.fst := by
  apply (cancel_epi (Functor.mapBiprod (tensorRight U) X.1 Y.1).inv).mp
  apply biprod.hom_ext'
  · have hι : biprod.inl ≫ (Functor.mapBiprod (tensorRight U) X.1 Y.1).inv =
        biprod.inl ▷ U := by
      rw [Functor.mapBiprod_inv, biprod.inl_desc]
      rfl
    simp only [← Category.assoc, hι]
    simp [← comp_whiskerRight, ← whiskerLeft_comp, inl_sumHalfIso]
  · have hι : biprod.inr ≫ (Functor.mapBiprod (tensorRight U) X.1 Y.1).inv =
        biprod.inr ▷ U := by
      rw [Functor.mapBiprod_inv, biprod.inr_desc]
      rfl
    simp only [← Category.assoc, hι]
    simp [← comp_whiskerRight, ← whiskerLeft_comp, inr_sumHalfIso]

/-- The second projection commutes with the sum half-braiding. -/
theorem sumHalfIso_snd (X Y : CategoryTheory.Center C) (U : C) :
    biprod.snd ▷ U ≫ (Y.2.β U).hom = (sumHalfIso X Y U).hom ≫ U ◁ biprod.snd := by
  apply (cancel_epi (Functor.mapBiprod (tensorRight U) X.1 Y.1).inv).mp
  apply biprod.hom_ext'
  · have hι : biprod.inl ≫ (Functor.mapBiprod (tensorRight U) X.1 Y.1).inv =
        biprod.inl ▷ U := by
      rw [Functor.mapBiprod_inv, biprod.inl_desc]
      rfl
    simp only [← Category.assoc, hι]
    simp [← comp_whiskerRight, ← whiskerLeft_comp, inl_sumHalfIso]
  · have hι : biprod.inr ≫ (Functor.mapBiprod (tensorRight U) X.1 Y.1).inv =
        biprod.inr ▷ U := by
      rw [Functor.mapBiprod_inv, biprod.inr_desc]
      rfl
    simp only [← Category.assoc, hι]
    simp [← comp_whiskerRight, ← whiskerLeft_comp, inr_sumHalfIso]


/-- The biproduct projections lift to centre morphisms. -/
def centerBiprodFst (X Y : CategoryTheory.Center C) : centerBiprod X Y ⟶ X :=
  ⟨biprod.fst, fun U => sumHalfIso_fst X Y U⟩

def centerBiprodSnd (X Y : CategoryTheory.Center C) : centerBiprod X Y ⟶ Y :=
  ⟨biprod.snd, fun U => sumHalfIso_snd X Y U⟩

/-- The underlying binary biproduct yields a bicone in the centre. -/
def centerBinaryBicone (X Y : CategoryTheory.Center C) : BinaryBicone X Y where
  pt := centerBiprod X Y
  fst := centerBiprodFst X Y
  snd := centerBiprodSnd X Y
  inl := centerBiprodInl X Y
  inr := centerBiprodInr X Y
  inl_fst := by
    apply CategoryTheory.Center.ext
    change biprod.inl ≫ biprod.fst = 𝟙 X.1
    exact biprod.inl_fst
  inl_snd := by
    apply CategoryTheory.Center.ext
    change biprod.inl ≫ biprod.snd = 0
    exact biprod.inl_snd
  inr_fst := by
    apply CategoryTheory.Center.ext
    change biprod.inr ≫ biprod.fst = 0
    exact biprod.inr_fst
  inr_snd := by
    apply CategoryTheory.Center.ext
    change biprod.inr ≫ biprod.snd = 𝟙 Y.1
    exact biprod.inr_snd

/-- The lifted bicone is a bilimit. -/
def centerBinaryBilimit (X Y : CategoryTheory.Center C) : (centerBinaryBicone X Y).IsBilimit :=
  isBinaryBilimitOfTotal _ (by
    apply CategoryTheory.Center.ext
    exact biprod.total)

instance centerHasBinaryBiproducts : HasBinaryBiproducts (CategoryTheory.Center C) where
  has_binary_biproduct X Y := ⟨⟨centerBinaryBicone X Y, centerBinaryBilimit X Y⟩⟩

/-- Zero and binary biproducts provide all finite biproducts in the centre. -/
instance centerHasFiniteBiproducts [HasZeroObject C] :
    HasFiniteBiproducts (CategoryTheory.Center C) := by
  let _ : HasFiniteProducts (CategoryTheory.Center C) :=
    hasFiniteProducts_of_has_binary_and_terminal
  exact HasFiniteBiproducts.of_hasFiniteProducts

end PropertyF.Ground.Centre
