module
public import PropertyF.Ground.Target
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Modular.FusionTransport
public import PropertyF.Ground.Fusion.FunctorDimension
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Calculus.PositiveWeights
public import PropertyF.Ground.Calculus.TensorPowerCoherence
public import PropertyF.Ground.Fusion.Agreement

section
/-! Scalar twisting along an arbitrary complex-field automorphism. The underlying
category, monoidal structure, braiding and duality are unchanged; only the
complex action on morphisms is precomposed with the inverse automorphism. The
identity functor is consequently semilinear in the stated direction. -/

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
theorem finite_twist (M : Type*) [AddCommGroup M] [m : Module ℂ M]
    [FiniteDimensional ℂ M] (σ : ℂ ≃+* ℂ) :
    @FiniteDimensional ℂ M _ _ (Module.compHom M σ.symm.toRingHom) := by
  let b := Module.finBasis ℂ M
  let m' := Module.compHom M σ.symm.toRingHom
  let b' := @Module.Basis.mapCoeffs _ ℂ M _ _ m b ℂ _ m' σ (by
    intro a x
    conv_rhs => rw [← σ.symm_apply_apply a]
    rfl)
  exact @Module.Basis.finiteDimensional_of_finite ℂ M _ _ m' _ _ b'

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

/-- The identity-on-morphisms braided equivalence is σ-semilinear. -/
def conjugate : GaloisConjugate C (category C σ) σ where
  equivalence := CategoryTheory.Equivalence.refl
  monoidal := inferInstanceAs ((𝟭 C.Obj).Monoidal)
  braided := inferInstanceAs ((𝟭 C.Obj).Braided)
  map_smul := by
    intro X Y z f
    change z • f = σ.symm (σ z) • f
    rw [σ.symm_apply_apply]

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

/-- The twisted inverse unit-scalar map applies σ to the original scalar. -/
theorem unitScalar_twist (f : End (𝟙_ C.Obj)) :
    unitScalar (category C σ) f = σ (unitScalar C f) := by
  let f' : End (𝟙_ (category C σ).Obj) := f
  change unitScalar (category C σ) f' = σ (unitScalar C f)
  apply (unit_algebraMap_bijective (category C σ)).1
  rw [algebraMap_unitScalar (category C σ) f']
  change f = _
  conv_lhs => rw [← algebraMap_unitScalar C f]
  simp only [Algebra.algebraMap_eq_smul_one]
  change (unitScalar C f) • (1 : End (𝟙_ C.Obj)) = σ.symm (σ (unitScalar C f)) • (1 : End (𝟙_ C.Obj))
  rw [σ.symm_apply_apply]

/-- Pivotal dimensions transform by the specified field automorphism. -/
theorem pivotalDimension_twist (p : Dimensions.PivotalStructure (C := C.Obj)) (X : C.Obj) :
    Dimensions.pivotalDimension (category C σ) (pivotal C σ p) X =
    σ (Dimensions.pivotalDimension C p X) := by
  exact unitScalar_twist C σ _

/-- Match chosen simple representatives and transport both dimensions. -/
theorem labels (p : Dimensions.PivotalStructure (C := C.Obj)) :
    ∃ e : Fin (rank C) ≃ Fin (rank (category C σ)),
      ∀ i, fpSimple C i = fpSimple (category C σ) (e i) ∧
        Dimensions.pivotalDimension (category C σ) (pivotal C σ p)
          (simples (category C σ) (e i)) =
        σ (Dimensions.pivotalDimension C p (simples C i)) := by
  obtain ⟨e, he⟩ := Modular.simpleLabels_equiv C (category C σ) (conjugate C σ).equivalence
  refine ⟨e, fun i => ⟨Modular.conjugate_fpSimple (conjugate C σ) he i, ?_⟩⟩
  rw [← pivotalDimension_twist C σ p (simples C i)]
  exact (Dimensions.pivotalDimension_iso (category C σ) (pivotal C σ p) (he i).some).symm

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
    fpDimension (category C σ) X = fpDimension C X := by
  let E := conjugate C σ
  let F := E.equivalence.functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  letI : F.Faithful := inferInstanceAs E.equivalence.functor.Faithful
  letI : F.Monoidal := E.monoidal
  exact fpDimension_functor C (category C σ) F X

/-- A pivotal trace scalar is carried through σ. -/
theorem rightTrace_twist (p : Dimensions.PivotalStructure (C := C.Obj))
    {X : C.Obj} (f : X ⟶ X) :
    Dimensions.groundUnitScalarEquiv (category C σ) ((pivotal C σ p).rightTrace f) =
      σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace f)) := by
  simp only [Dimensions.groundUnitScalarEquiv_apply]
  exact unitScalar_twist C σ _


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

set_option backward.isDefEq.respectTransparency false in
/-- For a positive pivotal category, all the dimension and scalar-twist
premises of categorical rigidity follow from actual fusion data and the
proved overlap trace recurrence. -/
theorem galois_rigidity_of_propertyF (Z : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := Z.Obj))
    (hdim : Modular.HasFPSimpleDimensions Z p)
    (σ : ℂ ≃+* ℂ) (y : Fin (rank Z))
    (hF : ObjectPropertyF (simples Z y)) (d : ℝ)
    (hσ : σ (fpSimple Z y : ℂ) = (d : ℂ))
    (hS : σ (Modular.categoricalS Z p y y) = (d : ℂ) * fpSimple Z y) :
    fpSimple Z y = |d| := by
  let D := ScalarTwist.category Z σ
  let q := ScalarTwist.pivotal Z σ p
  let X : D.Obj := simples Z y
  letI : Simple X := simples_simple Z y
  obtain ⟨e, he⟩ := ScalarTwist.labels Z σ p
  let original : Fin (rank D) → ℝ := fun i => fpSimple Z (e.symm i)
  let transformed : Fin (rank D) → ℝ := fun i => (σ (original i : ℂ)).re
  have hreal := fp_simple_galois_real Z σ
  have hpos : ∀ i, 0 < original i := fun i => fpSimple_pos Z _
  have htrans : ∀ i, σ (original i : ℂ) = (transformed i : ℂ) := by
    intro i
    exact (hreal (e.symm i)).symm
  have hqdim : ∀ i, Dimensions.groundUnitScalarEquiv D (q.rightTrace (𝟙 (simples D i))) =
      (transformed i : ℂ) := by
    intro i
    rw [Dimensions.groundUnitScalarEquiv_apply]
    change Dimensions.pivotalDimension D q (simples D i) = _
    have h := (he (e.symm i)).2
    rw [e.apply_symm_apply] at h
    rw [h]
    unfold transformed original
    rw [hreal]
    congr 1
    unfold Modular.HasFPSimpleDimensions at hdim
    unfold Dimensions.pivotalDimension Modular.simpleDimension at *
    rw [unitScalar_eq_equiv]
    exact hdim _
  have hd : d ≠ 0 := by
    intro hz
    have hn : σ (fpSimple Z y : ℂ) ≠ 0 := (map_ne_zero σ).2 (by exact_mod_cast (ne_of_gt (fpSimple_pos Z y)))
    apply hn
    rw [hσ, hz]
    simp
  have hXdim : Dimensions.groundUnitScalarEquiv D (q.rightTrace (𝟙 X)) = (d : ℂ) := by
    change Dimensions.groundUnitScalarEquiv (ScalarTwist.category Z σ)
      ((ScalarTwist.pivotal Z σ p).rightTrace (𝟙 (show (ScalarTwist.category Z σ).Obj from simples Z y))) = _
    rw [ScalarTwist.rightTrace_twist Z σ p]
    rw [Dimensions.groundUnitScalarEquiv_apply, unitScalar_eq_equiv]
    change σ (Modular.simpleDimension Z p y) = _
    rw [hdim, hσ]
  have hXfp : fpDimension D X = fpSimple Z y := by
    rw [ScalarTwist.fpDimension_twist, fpDimension_simple]
  have hXS : Dimensions.groundUnitScalarEquiv D (q.rightTrace (selfMonodromy X).asHom) =
      (d : ℂ) * fpSimple Z y := by
    change Dimensions.groundUnitScalarEquiv (ScalarTwist.category Z σ)
      ((ScalarTwist.pivotal Z σ p).rightTrace (selfMonodromy (show (ScalarTwist.category Z σ).Obj from simples Z y)).asHom) = _
    rw [ScalarTwist.rightTrace_twist Z σ p]
    rw [Dimensions.groundUnitScalarEquiv_apply, unitScalar_eq_equiv]
    change σ (Modular.categoricalS Z p y y) = _
    exact hS
  apply actual_rigidity_of_overlap_and_galois_dimensions D X q original transformed σ
    hpos htrans
    (by simpa only [Dimensions.pivotalDimension, ← Dimensions.groundUnitScalarEquiv_apply] using hqdim)
    d (fpSimple Z y) hd (fpSimple_pos Z y)
    (by simpa only [Dimensions.pivotalDimension, ← Dimensions.groundUnitScalarEquiv_apply] using hXdim)
    hXfp hXS hF
  intro u k
  exact Calculus.overlap_trace_power D q u k

end PropertyF.Ground
end
end
