module
public import PropertyF.Ground.Target

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
