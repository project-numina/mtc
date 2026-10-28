module
public import PropertyF.Ground.Target
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Modular.FusionTransport
public import PropertyF.Ground.Fusion.ObjectDimension
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Calculus.PositiveWeights
public import PropertyF.Ground.Calculus.TensorPowerCoherence
public import PropertyF.Ground.Fusion.Agreement

section
/-! Scalar twisting along an arbitrary complex-field automorphism. The underlying
category, monoidal structure, braiding and duality are unchanged; only the
complex action on morphisms is precomposed with the inverse automorphism. -/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.ScalarTwist
universe v u

variable (C : BraidedFusionCategory.{v,u}) (σ : ℂ ≃+* ℂ)

/-- A typeclass synonym carrying the twisted linear structure. -/
def Obj (C : BraidedFusionCategory.{v,u}) (_σ : ℂ ≃+* ℂ) : Type u := C.Obj

instance : Category.{v} (Obj C σ) := inferInstanceAs (Category C.Obj)
instance : MonoidalCategory (Obj C σ) := inferInstanceAs (MonoidalCategory C.Obj)
instance : BraidedCategory (Obj C σ) := inferInstanceAs (BraidedCategory C.Obj)
instance : Abelian (Obj C σ) := inferInstanceAs (Abelian C.Obj)
instance : RigidCategory (Obj C σ) := inferInstanceAs (RigidCategory C.Obj)
instance : MonoidalPreadditive (Obj C σ) := inferInstanceAs (MonoidalPreadditive C.Obj)

instance twistedLinear : Linear ℂ (Obj C σ) where
  homModule X Y := by
    letI : Linear ℂ (Obj C σ) := C.linear
    exact Module.compHom (X ⟶ Y) σ.symm.toRingHom
  smul_comp X Y Z r f g := by
    letI : Linear ℂ (Obj C σ) := C.linear
    change (σ.symm r • f) ≫ g = σ.symm r • (f ≫ g)
    exact Linear.smul_comp _ _ _ _ _ _
  comp_smul X Y Z f r g := by
    letI : Linear ℂ (Obj C σ) := C.linear
    change f ≫ (σ.symm r • g) = σ.symm r • (f ≫ g)
    exact Linear.comp_smul _ _ _ _ _ _

instance : MonoidalLinear ℂ (Obj C σ) where
  whiskerLeft_smul X Y Z r f := by
    letI : Linear ℂ (Obj C σ) := C.linear
    letI : MonoidalLinear ℂ (Obj C σ) := C.monoidalLinear
    change X ◁ (σ.symm r • f) = σ.symm r • (X ◁ f)
    exact MonoidalLinear.whiskerLeft_smul _ _ _
  smul_whiskerRight r Y Z f X := by
    letI : Linear ℂ (Obj C σ) := C.linear
    letI : MonoidalLinear ℂ (Obj C σ) := C.monoidalLinear
    change (σ.symm r • f) ▷ X = σ.symm r • (f ▷ X)
    exact MonoidalLinear.smul_whiskerRight _ _ _

/-- Transport a finite basis across a field automorphism. -/
theorem finite_twist {K : Type*} [Field K] (M : Type*) [AddCommGroup M] [m : Module K M]
    [FiniteDimensional K M] (σ : K ≃+* K) :
    @FiniteDimensional K M _ _ (Module.compHom M σ.symm.toRingHom) :=
  let b := Module.finBasis K M
  let m' := Module.compHom M σ.symm.toRingHom
  let b' := @Module.Basis.mapCoeffs _ K M _ _ m b K _ m' σ (by
    intro a x
    conv_rhs => rw [← σ.symm_apply_apply a]
    rfl)
  @Module.Basis.finiteDimensional_of_finite K M _ _ m' _ _ b'

instance twistedFusion : IsFusionCategory (Obj C σ) where
  hom_finite X Y := by
    letI : Linear ℂ (Obj C σ) := C.linear
    letI : FiniteDimensional ℂ (X ⟶ Y) := C.fusion.hom_finite X Y
    exact finite_twist (X ⟶ Y) σ
  unit_simple := C.fusion.unit_simple
  finite_semisimple := C.fusion.finite_semisimple

/-- The scalar twist is itself a genuine braided fusion category. -/
def category : BraidedFusionCategory.{v,u} where
  Obj := Obj C σ

end PropertyF.Ground.ScalarTwist
end
end

/-! # Twisted traces and rigidity

Scalar-twist transport supplies the overlap rigidity used in the target proof. -/

section
/-! Pivotal traces and finite braid images under scalar twisting. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.ScalarTwist
universe v u
variable (C : BraidedFusionCategory.{v,u}) (σ : ℂ ≃+* ℂ)

/-- The original pivotal maps satisfy the same categorical equations. -/
def pivotal (p : Dimensions.PivotalStructure (C := C.Obj)) :
    Dimensions.PivotalStructure (C := (category C σ).Obj) := p

variable (p : Dimensions.PivotalStructure (C := C.Obj))
local notation "Cσ" => category C σ
local notation "pσ" => pivotal C σ p

/-- The twisted inverse unit-scalar map applies σ to the original scalar. -/
theorem unitScalar_twist (f : End (𝟙_ C.Obj)) :
    unitScalar Cσ f = σ (unitScalar C f) := by
  apply (unit_algebraMap_bijective Cσ).1
  simp only [algebraMap_unitScalar Cσ f]
  exact (algebraMap_unitScalar C f).symm.trans
    (congrArg (fun z : ℂ ↦ z • (1 : End (𝟙_ C.Obj))) (σ.symm_apply_apply _).symm)

/-- Pivotal dimensions transform by the specified field automorphism. -/
theorem pivotalDimension_twist (X : C.Obj) :
    Dimensions.pivotalDimension Cσ pσ X =
    σ (Dimensions.pivotalDimension C p X) :=
  unitScalar_twist C σ _

variable {p}

/-- Match chosen simple representatives and transport pivotal dimensions. -/
theorem labels (hdim : Modular.HasFPSimpleDimensions C p) :
    ∃ e : Fin (rank C) ≃ Fin (rank Cσ),
      ∀ i, Dimensions.pivotalDimension Cσ pσ (simples Cσ (e i)) = σ (fpSimple C i : ℂ) :=
  let ⟨e, he⟩ := Modular.simpleLabels_equiv C Cσ (CategoryTheory.Equivalence.refl)
  ⟨e, fun i ↦ (Dimensions.pivotalDimension_iso Cσ pσ (he i).some).symm.trans <| by
    change Dimensions.pivotalDimension Cσ pσ (simples C i) = _
    simp only [pivotalDimension_twist]
    simpa [Dimensions.pivotalDimension, unitScalar_eq_equiv, Modular.simpleDimension] using
      congrArg σ (hdim i)⟩

/-- Simple FP dimensions and their real conjugates give the twisted pivotal dimensions. -/
theorem exists_galois_fp_dimensions (hdim : Modular.HasFPSimpleDimensions C p) :
    ∃ original transformed : Fin (rank Cσ) → ℝ,
      (∀ i, 0 < original i) ∧ (∀ i, σ (original i : ℂ) = (transformed i : ℂ)) ∧
      ∀ i, Dimensions.pivotalDimension Cσ pσ (simples Cσ i) = (transformed i : ℂ) := by
  obtain ⟨e, he⟩ := labels C σ hdim
  refine ⟨fun i ↦ fpSimple C (e.symm i), fun i ↦ (σ (fpSimple C (e.symm i) : ℂ)).re,
    fun i ↦ fpSimple_pos C _, fun i ↦ (fp_simple_galois_real C σ (e.symm i)).symm, fun i ↦ ?_⟩
  simpa only [e.apply_symm_apply, fp_simple_galois_real] using he (e.symm i)

end PropertyF.Ground.ScalarTwist
end
end

section
/-! FP dimensions, pivotal traces, and categorical S matrices under scalar twist. -/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.ScalarTwist
universe v u
variable (C : BraidedFusionCategory.{v,u}) (σ : ℂ ≃+* ℂ)

/-- FP dimension is unchanged on every object. -/
theorem fpDimension_twist (X : C.Obj) :
    fpDimension (category C σ) X = fpDimension C X :=
  let E : C.Obj ≌ (category C σ).Obj := CategoryTheory.Equivalence.refl
  let F := E.functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  letI : F.Monoidal := by
    change (𝟭 C.Obj).Monoidal
    infer_instance
  fpDimension_functor C (category C σ) F X

variable (p : Dimensions.PivotalStructure (C := C.Obj))
local notation "Cσ" => category C σ
local notation "pσ" => pivotal C σ p

/-- A pivotal trace scalar is carried through σ. -/
theorem rightTrace_twist {X : C.Obj} (f : X ⟶ X) :
    Ground.unitScalarEquiv Cσ ((pσ).rightTrace f) = σ (Ground.unitScalarEquiv C (p.rightTrace f)) :=
  ((unitScalar_eq_equiv Cσ _).symm.trans (unitScalar_twist C σ _)).trans
    (congrArg σ (unitScalar_eq_equiv C _))

end PropertyF.Ground.ScalarTwist
end
end

section
/-! Reduce the Galois-column rigidity assertion to categorical overlap coherence. -/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
open scoped BigOperators
namespace PropertyF.Ground
universe v u

variable (Z : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := Z.Obj))
local notation "𝒇" => fpSimple Z
local notation "𝒮" => Modular.categoricalS Z p

set_option backward.isDefEq.respectTransparency false in
/-- For a positive pivotal category, all the dimension and scalar-twist
premises of categorical rigidity follow from actual fusion data and the
proved overlap trace recurrence. -/
theorem galois_rigidity_of_propertyF (hdim : Modular.HasFPSimpleDimensions Z p)
    {σ : ℂ ≃+* ℂ} {y : Fin (rank Z)} (hF : ObjectPropertyF (simples Z y)) {d : ℝ}
    (hσ : σ (𝒇 y : ℂ) = (d : ℂ)) (hS : σ (𝒮 y y) = (d : ℂ) * 𝒇 y) : 𝒇 y = |d| :=
  let D := ScalarTwist.category Z σ
  let q := ScalarTwist.pivotal Z σ p
  let X : D.Obj := simples Z y
  letI : Simple X := simples_simple Z y
  let ⟨original, transformed, hpos, htrans, hqdim⟩ :=
    ScalarTwist.exists_galois_fp_dimensions Z σ hdim
  have hd : d ≠ 0 := fun hz ↦ (map_ne_zero σ).2
    (show (𝒇 y : ℂ) ≠ 0 by exact_mod_cast (ne_of_gt (fpSimple_pos Z y)))
    (by simpa [hz] using hσ)
  have hXdim : Dimensions.pivotalDimension D q X = (d : ℂ) := by
    rw [ScalarTwist.pivotalDimension_twist, Dimensions.pivotalDimension, unitScalar_eq_equiv]
    change σ (Modular.simpleDimension Z p y) = _
    rw [hdim, hσ]
  have hXfp : fpDimension D X = 𝒇 y :=
    (ScalarTwist.fpDimension_twist Z σ _).trans (fpDimension_simple Z y)
  have hXS : Ground.unitScalarEquiv D (q.rightTrace (selfMonodromy X).asHom) =
      (d : ℂ) * 𝒇 y := by
    rw [ScalarTwist.rightTrace_twist Z σ p]
    exact hS
  actual_rigidity_of_overlap_and_galois_dimensions D q original transformed σ
    hpos htrans hqdim X d (𝒇 y) hd (fpSimple_pos Z y) hXdim hXfp hXS hF
    (Calculus.overlap_trace_power D q)

end PropertyF.Ground
end
end
