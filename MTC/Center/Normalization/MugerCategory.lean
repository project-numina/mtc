module
public import MTC.Center.Normalization.MugerLabels
public import MTC.Center.Normalization.MugerAdjointNormalization
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import MTC.Fusion.SemisimpleSplit
public import MTC.Center.Induction.Representatives

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! # The actual symmetric rigid Müger-centre subcategory

The transparent objects form a full symmetric rigid monoidal subcategory.
The fusion structure, pivotal restriction, and dimension preservation are
constructed. Pseudo-unitarity of symmetric fusion categories is not established here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory CategoryTheory.Limits
open scoped ZeroObject
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The actual transparency property on objects of the braided fusion category. -/
def mugerProperty : ObjectProperty C.Obj := MTC.Center.Transparent

/-- Transparent objects form a full subcategory. -/
abbrev MugerCategory := (mugerProperty C).FullSubcategory

instance mugerProperty_monoidal : (mugerProperty C).IsMonoidal where
  prop_unit := transparent_unit
  prop_tensor _ _ hX hY := transparent_tensor hX hY

/-- The actual Müger centre is a symmetric monoidal category. -/
instance mugerCategory_symmetric : SymmetricCategory (MugerCategory C) where
  symmetry X Y := by
    apply ObjectProperty.hom_ext
    exact X.property Y.obj

/-- Transparent objects remain transparent under right duality. -/
theorem transparent_rightDual (X : C.Obj) (hX : MTC.Center.Transparent X) :
    MTC.Center.Transparent (Xᘁ) :=
  transparent_generatedBy hX (generatedBy_rightDual X)

/-- The right dual pairing in the full transparent subcategory is inherited
from the actual ambient duality. -/
instance mugerCategory_rightRigid : RightRigidCategory (MugerCategory C) where
  rightDual X :=
    { rightDual := ⟨X.objᘁ, transparent_rightDual C X.obj X.property⟩
      exact :=
        { coevaluation' := ObjectProperty.homMk (η_ X.obj (X.objᘁ))
          evaluation' := ObjectProperty.homMk (ε_ X.obj (X.objᘁ))
          coevaluation_evaluation' := by
            apply ObjectProperty.hom_ext
            exact ExactPairing.coevaluation_evaluation X.obj (X.objᘁ)
          evaluation_coevaluation' := by
            apply ObjectProperty.hom_ext
            exact ExactPairing.evaluation_coevaluation X.obj (X.objᘁ) } }

/-- Symmetry turns the constructed right dual into a left dual. -/
instance mugerCategory_leftRigid : LeftRigidCategory (MugerCategory C) where
  leftDual X :=
    { leftDual := Xᘁ
      exact := BraidedCategory.exactPairing_swap X (Xᘁ) }

instance mugerCategory_rigid : RigidCategory (MugerCategory C) where


/-- Transparent objects are closed under ambient subobjects. -/
instance mugerProperty_subobjects : (mugerProperty C).IsClosedUnderSubobjects where
  prop_of_mono f _ hY := by
    let : IsSplitMono f := mono_splits f
    exact transparent_of_retract ⟨f, retraction f, IsSplitMono.id f⟩ hY

/-- In a fusion category, every epimorphism splits. -/
theorem epi_splits_in_fusion {X Y : C.Obj} (f : X ⟶ Y) [Epi f] : IsSplitEpi f := by
  let s := Fork.ofι (kernel.ι f) ((kernel.condition f).trans comp_zero.symm)
  let : IsSplitMono s.ι := by
    change IsSplitMono (kernel.ι f)
    exact mono_splits (kernel.ι f)
  let b := binaryBiconeOfIsSplitMonoOfCokernel (Abelian.epiIsCokernelOfKernel s (kernelIsKernel f))
  exact IsSplitEpi.mk' ⟨b.inr, b.inr_snd⟩

/-- Transparent objects are closed under ambient quotients. -/
instance mugerProperty_quotients : (mugerProperty C).IsClosedUnderQuotients where
  prop_of_epi f _ hX := by
    let : IsSplitEpi f := epi_splits_in_fusion C f
    exact transparent_of_retract ⟨section_ f, f, IsSplitEpi.id f⟩ hX

/-- The zero object is transparent. -/
instance mugerProperty_containsZero : (mugerProperty C).ContainsZero where
  exists_zero := by
    let r : Retract ((0 : C.Obj)) (𝟙_ C.Obj) := ⟨0, 0, by simp⟩
    exact ⟨(0 : C.Obj), isZero_zero _, transparent_of_retract r transparent_unit⟩


/-- Finite products of transparent objects are transparent. -/
instance mugerProperty_finiteProducts : (mugerProperty C).IsClosedUnderFiniteProducts := by
  apply ObjectProperty.IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape
  intro J hJ
  let : Finite J := hJ
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let : Fintype J := Fintype.ofFinite J
  let V : J → C.Obj := fun j ↦ F.obj ⟨j⟩
  have hV : MTC.Center.Transparent (⨁ V) := transparent_biproduct V (fun j ↦ hF ⟨j⟩)
  let e : limit F ≅ ⨁ V :=
    (HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := F))) ≪≫ (biproduct.isoProduct V).symm
  exact transparent_of_retract (Retract.ofIso e) hV

/-- The actual full Müger-centre subcategory is abelian. -/
instance mugerCategory_abelian : Abelian (MugerCategory C) := inferInstance


/-- Every ambient simple summand of a transparent object is transparent. -/
theorem muger_piece_transparent (X : MugerCategory C)
    (a : MTC.CategoryTheory.Dimensions.simplePieces C X.obj) :
    MTC.Center.Transparent (simples C a.1) := by
  let V := MTC.CategoryTheory.Dimensions.simplePiecesObject C X.obj
  let e := MTC.CategoryTheory.Dimensions.simpleDecomposition C X.obj
  let r : Retract (simples C a.1) X.obj :=
    ((biproduct.bicone V).retract a).trans (Retract.ofIso e.symm)
  exact transparent_of_retract r X.property

/-- The ambient simple decomposition viewed in the full Müger category. -/
def mugerPieces (X : MugerCategory C)
    (a : MTC.CategoryTheory.Dimensions.simplePieces C X.obj) : MugerCategory C :=
  ⟨simples C a.1, muger_piece_transparent C X a⟩

/-- The full-subcategory inclusion preserves monomorphisms. -/
instance mugerInclusion_preservesMonos : (mugerProperty C).ι.PreservesMonomorphisms :=
  (mugerProperty C).preservesMonomorphisms_ι_of_isNormalEpiCategory

/-- The actual ambient simple decomposition lifts to the Müger category. -/
def mugerPiecesDecomposition (X : MugerCategory C) : X ≅ ⨁ (mugerPieces C X) := by
  let F := (mugerProperty C).ι
  let e := MTC.CategoryTheory.Dimensions.simpleDecomposition C X.obj
  let b : F.obj (⨁ (mugerPieces C X)) ≅ ⨁ (F.obj ∘ mugerPieces C X) :=
    F.mapBiproduct (mugerPieces C X)
  exact F.preimageIso (e ≪≫ b.symm)


/-- The finite type of actual transparent simple labels. -/
abbrev MugerSimpleIndex := {i : Fin (rank C) // i ∈ mugerLabels C}

/-- A transparent simple representative as an object of the Müger category. -/
def mugerSimple (i : MugerSimpleIndex C) : MugerCategory C :=
  ⟨simples C i, (mem_mugerLabels C i).mp i.property⟩

/-- Each chosen transparent simple remains simple in the full subcategory. -/
theorem mugerSimple_simple (i : MugerSimpleIndex C) : Simple (mugerSimple C i) := by
  let : Simple ((mugerProperty C).ι.obj (mugerSimple C i)) := by
    change Simple (simples C i)
    exact simples_simple C i
  exact Functor.simple_of_simple_obj (mugerProperty C).ι (mugerSimple C i)

/-- Each simple summand remains simple in the full Müger category. -/
theorem mugerPieces_simple (X : MugerCategory C)
    (a : MTC.CategoryTheory.Dimensions.simplePieces C X.obj) : Simple (mugerPieces C X a) :=
  mugerSimple_simple C ⟨a.1, (mem_mugerLabels C _).mpr (muger_piece_transparent C X a)⟩

/-- Distinct ambient simple labels remain nonisomorphic in the full subcategory. -/
theorem mugerSimple_injective {i j : MugerSimpleIndex C}
    (h : Nonempty (mugerSimple C i ≅ mugerSimple C j)) : i = j := by
  apply Subtype.ext
  apply simples_injective C
  obtain ⟨e⟩ := h
  exact ⟨(mugerProperty C).ι.mapIso e⟩

/-- The Müger category has a finite, pairwise nonisomorphic simple family,
and every object decomposes into these simples. -/
theorem mugerCategory_finiteSemisimple :
    ∃ (n : ℕ) (S : Fin n → MugerCategory C),
      (∀ i, Simple (S i)) ∧
      (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
      (∀ X, ∃ m : Fin n → ℕ,
        Nonempty (X ≅ ⨁ (fun p : Σ i, Fin (m i) => S p.1))) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (MugerSimpleIndex C)
  let S : Fin n → MugerCategory C := fun i ↦ mugerSimple C (e.symm i)
  refine ⟨n, S, fun i ↦ mugerSimple_simple C _, ?_, ?_⟩
  · intro i j hij
    apply e.symm.injective
    exact mugerSimple_injective C hij
  · intro X
    let I := MTC.CategoryTheory.Dimensions.simplePieces C X.obj
    let E := Fintype.equivFin I
    let V : Fin (Fintype.card I) → MugerCategory C := fun j ↦ mugerPieces C X (E.symm j)
    have hXV : Nonempty (X ≅ ⨁ V) := ⟨mugerPiecesDecomposition C X ≪≫
      biproduct.whiskerEquiv E (fun a ↦ eqToIso (by simp [V]))⟩
    have hcover (j : Fin (Fintype.card I)) : ∃ i, Nonempty (V j ≅ S i) := by
      let a := E.symm j
      let b : MugerSimpleIndex C := ⟨a.1, (mem_mugerLabels C _).mpr (muger_piece_transparent C X a)⟩
      refine ⟨e b, ⟨eqToIso ?_⟩⟩
      simp [V, S, b, a, mugerPieces, mugerSimple]
    obtain ⟨m, ⟨ev⟩⟩ := MTC.Center.Induction.regroup_biproduct hcover
    exact ⟨m, hXV.map fun e' ↦ e' ≪≫ ev⟩


/-- The actual Müger centre is a symmetric fusion category. -/
instance mugerCategory_fusion : IsFusionCategory (MugerCategory C) where
  hom_finite X Y := by
    let : FiniteDimensional ℂ ((mugerProperty C).ι.obj X ⟶ (mugerProperty C).ι.obj Y) := by
      change FiniteDimensional ℂ (X.obj ⟶ Y.obj)
      exact IsFusionCategory.hom_finite X.obj Y.obj
    exact FiniteDimensional.of_injective ((mugerProperty C).ι.mapLinearMap ℂ)
      (fun _ _ h ↦ (mugerProperty C).ι.map_injective h)
  unit_simple := by
    let F := (mugerProperty C).ι
    let : Simple (F.obj (𝟙_ (MugerCategory C))) := by
      change Simple (𝟙_ C.Obj)
      exact IsFusionCategory.unit_simple
    exact Functor.simple_of_simple_obj F _
  finite_semisimple := mugerCategory_finiteSemisimple C

/-- The Müger centre bundled with its constructed fusion structure. -/
def bundledMuger : BraidedFusionCategory.{v,u} where
  Obj := MugerCategory C


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual inclusion of the Müger fusion category preserves FP dimension. -/
theorem muger_forget_fpDimension (X : MugerCategory C) :
    fpDimension C X.obj = fpDimension (bundledMuger C) X := by
  let F : MugerCategory C ⥤ C.Obj := (mugerProperty C).ι
  let hAdd : F.Additive := ⟨by intros; rfl⟩
  let hFaithful : F.Faithful := inferInstance
  let hMonoidal : F.Monoidal := inferInstance
  exact @fpDimension_functor (bundledMuger C) C F hAdd hFaithful hMonoidal X


/-- A pivotal structure restricts to the actual Müger fusion category. -/
def mugerPivotal (p : PivotalStructure (C := C.Obj)) :
    PivotalStructure (C := MugerCategory C) where
  iso X := (mugerProperty C).isoMk (p.iso X.obj)
  naturality f := by
    apply ObjectProperty.hom_ext
    exact p.naturality f.hom
  tensor X Y := by
    apply ObjectProperty.hom_ext
    exact p.tensor X.obj Y.obj
  unit := by
    apply ObjectProperty.hom_ext
    exact p.unit


/-- The unit scalar in the Müger category is unchanged by inclusion. -/
theorem muger_unitScalar_forget (a : End (𝟙_ (MugerCategory C))) :
    unitScalar (bundledMuger C) a = unitScalar C (End.of a.asHom.hom) :=
  (unit_algebraMap_bijective C).1 <|
    (End.ext (congrArg (fun x : End (𝟙_ (MugerCategory C)) ↦ x.asHom.hom)
      (algebraMap_unitScalar (bundledMuger C) a))).trans (algebraMap_unitScalar C _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The restricted pivotal structure has the actual ambient dimensions. -/
theorem muger_pivotalDimension_forget (p : PivotalStructure (C := C.Obj))
    (X : MugerCategory C) :
    pivotalDimension (bundledMuger C) (mugerPivotal C p) X = pivotalDimension C p X.obj := by
  unfold pivotalDimension
  rw [muger_unitScalar_forget]
  rfl


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Pseudo-unitarity of the constructed actual Müger fusion category implies
FP norm saturation on every transparent simple of the base category. -/
theorem transparent_norm_saturation_of_muger_pseudoUnitary
    (p : PivotalStructure (C := C.Obj)) (hpu : PseudoUnitary (bundledMuger C))
    (i : Fin (rank C)) (hi : MTC.Center.Transparent (simples C i)) :
    ‖pivotalDimension C p (simples C i)‖ = fpSimple C i := by
  let M := bundledMuger C
  let pM := mugerPivotal C p
  have hsat := MTC.Center.Induction.pivotalDimension_norm_eq_fp_of_pseudoUnitary pM hpu
  let X : MugerCategory C := mugerSimple C ⟨i, (mem_mugerLabels C i).mpr hi⟩
  let : Simple X := mugerSimple_simple C _
  obtain ⟨j, ⟨e⟩⟩ := exists_simple_iso M X
  have heq := hsat j
  change ‖pivotalDimension M pM (simples M j)‖ = fpSimple M j at heq
  rw [← pivotalDimension_iso (C := M) pM e, muger_pivotalDimension_forget C p X] at heq
  have hfp : fpSimple M j = fpSimple C i := by
    rw [← fpDimension_simple j, ← fpDimension_iso e, ← muger_forget_fpDimension C X]
    exact fpDimension_simple i
  rw [hfp] at heq
  exact heq


/-- If the actual Müger fusion category is pseudo-unitary, adjoint positivity
normalizes an arbitrary ambient pivotal structure on the Müger centre. -/
theorem normalize_pivotal_of_muger_pseudoUnitary_and_adjoint_positivity
    (p : PivotalStructure (C := C.Obj)) (hpu : PseudoUnitary (bundledMuger C))
    (hpositive : ∀ i, MTC.Center.Transparent (simples C i) → IsAdjointLabel C i →
      ∃ r : ℝ, 0 < r ∧ pivotalDimension C p (simples C i) = r) :
    ∃ q : PivotalStructure (C := C.Obj), ∀ i,
      MTC.Center.Transparent (simples C i) →
      pivotalDimension C q (simples C i) = (fpSimple C i : ℂ) :=
  normalize_pivotal_on_muger_of_adjoint_positivity C p
    (transparent_norm_saturation_of_muger_pseudoUnitary C p hpu) hpositive

end MTC.Center.Normalization
end
