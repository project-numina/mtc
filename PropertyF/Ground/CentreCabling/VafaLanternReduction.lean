module
public import PropertyF.Ground.CentreCabling.VafaDeterminant
public import PropertyF.Ground.CentreCabling.TwistDual

/-!
# Lantern identities and Vafa relations

Determinants of the lantern identity yield Vafa relations and finite-order
monodromy. In spherical categories the dual twist equality supplies the
individual-twist factor in the general lantern identity.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u

/-- The simple scalar of a natural endomorphism. -/
def naturalSimpleScalar (C : Ground.BraidedFusionCategory.{v,u})
    (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj) (i : Fin (rank C)) : ℂ :=
  Calculus.groundSimpleScalar C i (End.of (α.app (simples C i)))

/-- The three-strand object used in Vafa's determinant calculation. -/
def vafaObject (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (rank C)) : C.Obj :=
  (simples C i ⊗ simples C (dualIndex C i)) ⊗ simples C i

/-- Pair twist on the first and second tensor factors. -/
def vafaPair12 (C : Ground.BraidedFusionCategory.{v,u})
    (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj) (i : Fin (rank C)) : vafaObject C i ⟶ vafaObject C i :=
  α.app (simples C i ⊗ simples C (dualIndex C i)) ▷ simples C i

/-- The crossed first/third pair, transported through a chosen crossing. -/
def vafaPair13 (C : Ground.BraidedFusionCategory.{v,u})
    (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj) (i : Fin (rank C))
    (e : vafaObject C i ≅ (simples C i ⊗ simples C i) ⊗ simples C (dualIndex C i)) :
    vafaObject C i ⟶ vafaObject C i :=
  e.hom ≫ (α.app (simples C i ⊗ simples C i) ▷ simples C (dualIndex C i)) ≫ e.inv

/-- The second/third pair, transported through a chosen crossing. -/
def vafaPair23 (C : Ground.BraidedFusionCategory.{v,u})
    (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj) (i : Fin (rank C))
    (e : vafaObject C i ≅ (simples C (dualIndex C i) ⊗ simples C i) ⊗ simples C i) :
    vafaObject C i ⟶ vafaObject C i :=
  e.hom ≫ (α.app (simples C (dualIndex C i) ⊗ simples C i) ▷ simples C i) ≫ e.inv

set_option backward.isDefEq.respectTransparency false in
/-- The lantern identity on actual endomorphisms implies the scalar Vafa
relations. The choice of crossing and the identity itself are explicit. -/
theorem vafa_relations_of_lantern
    {C : Ground.BraidedFusionCategory.{v,u}} {α : 𝟭 C.Obj ⟶ 𝟭 C.Obj}
    {e13 : ∀ i, vafaObject C i ≅
      (simples C i ⊗ simples C i) ⊗ simples C (dualIndex C i)}
    {e23 : ∀ i, vafaObject C i ≅
      (simples C (dualIndex C i) ⊗ simples C i) ⊗ simples C i}
    (h : ∀ i, vafaPair12 C α i ≫ vafaPair13 C α i (e13 i) ≫
      vafaPair23 C α i (e23 i) = naturalSimpleScalar C α i ^ 3 • α.app (vafaObject C i))
    (i : Fin (rank C)) :
    naturalSimpleScalar C α i ^ (4 * vafaMultiplicity C i) =
      ∏ j, naturalSimpleScalar C α j ^ vafaWeight C i j := by
  classical
  have hh := congrArg (fun f => LinearMap.det
    (CategoryTheory.Linear.rightComp ℂ (simples C i) f)) (h i)
  rw [determinant_postcomp_comp, determinant_postcomp_comp,
    determinant_postcomp_smul] at hh
  erw [determinant_natural_postcomp_simple C α i (vafaObject C i)] at hh
  have h12 := determinant_vafa_first_pair C α i
  have h13 := determinant_vafa_pair_conjugate C α i i i (dualIndex C i) (vafaObject C i) (e13 i)
  have h23 := determinant_vafa_pair_conjugate C α i (dualIndex C i) i i (vafaObject C i) (e23 i)
  change LinearMap.det (CategoryTheory.Linear.rightComp ℂ (simples C i) (vafaPair12 C α i)) = _ at h12
  change LinearMap.det (CategoryTheory.Linear.rightComp ℂ (simples C i) (vafaPair13 C α i (e13 i))) = _ at h13
  change LinearMap.det (CategoryTheory.Linear.rightComp ℂ (simples C i) (vafaPair23 C α i (e23 i))) = _ at h23
  rw [h12, h13, h23] at hh
  have hdim : Module.finrank ℂ (simples C i ⟶ vafaObject C i) = vafaMultiplicity C i := by
    simpa [vafaObject] using (vafaMultiplicity_eq_finrank C i).symm
  rw [hdim] at hh
  change _ = (naturalSimpleScalar C α i ^ 3) ^ vafaMultiplicity C i *
    naturalSimpleScalar C α i ^ vafaMultiplicity C i at hh
  simp_rw [fusionCoeff_comm C (dualIndex C i) i] at hh
  have hprod : (∏ j, naturalSimpleScalar C α j ^ vafaWeight C i j) =
      (∏ j, naturalSimpleScalar C α j ^
        (fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i)) *
      (∏ j, naturalSimpleScalar C α j ^
        (fusionCoeff C i i j * fusionCoeff C j (dualIndex C i) i)) *
      (∏ j, naturalSimpleScalar C α j ^
        (fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i)) := by
    simp only [vafaWeight, two_mul, add_mul, pow_add, Finset.prod_mul_distrib]
    ring
  rw [hprod]
  have hr : (naturalSimpleScalar C α i ^ 3) ^ vafaMultiplicity C i * naturalSimpleScalar C α i ^ vafaMultiplicity C i =
      naturalSimpleScalar C α i ^ (4 * vafaMultiplicity C i) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hr] at hh
  simpa only [mul_assoc, naturalSimpleScalar] using hh.symm

/-- The natural simple scalar agrees with the actual pivotal twist unit. -/
theorem natural_pivotal_twist_scalar
    (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (i : Fin (rank C)) :
    naturalSimpleScalar C (Dimensions.pivotalBraidedTwistNaturalIso C p).hom i =
      (pivotalTwistUnit C p i : ℂ) := by
  letI : Simple (simples C i) := simples_simple C i
  change Calculus.groundSimpleScalar C i (End.of
    (Dimensions.pivotalBraidedTwist C p (simples C i)).hom) = _
  rw [Dimensions.pivotalBraidedTwist_simple]
  change Calculus.groundSimpleScalar C i
    (Dimensions.pivotalBraidedTwistScalar C p (simples C i) • (1 : End (simples C i))) = _
  simp [pivotalTwistUnit]

/-- Crossing the middle and last strands brings the first/third pair together. -/
def vafaCross13 (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    vafaObject C i ≅ (simples C i ⊗ simples C i) ⊗ simples C (dualIndex C i) :=
  (α_ (simples C i) (simples C (dualIndex C i)) (simples C i)) ≪≫
    (Iso.refl (simples C i) ⊗ᵢ β_ (simples C (dualIndex C i)) (simples C i)) ≪≫
    (α_ (simples C i) (simples C i) (simples C (dualIndex C i))).symm

/-- Rotate the first strand around the second and third to expose their pair. -/
def vafaCross23 (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    vafaObject C i ≅ (simples C (dualIndex C i) ⊗ simples C i) ⊗ simples C i :=
  (α_ (simples C i) (simples C (dualIndex C i)) (simples C i)) ≪≫
    β_ (simples C i) (simples C (dualIndex C i) ⊗ simples C i)

/-- The actual pivotal lantern equation implies the required unit-valued
Vafa relations. The lantern equation remains an explicit hypothesis. -/
theorem pivotal_vafa_relations_of_lantern
    (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (h : ∀ i, let α := (Dimensions.pivotalBraidedTwistNaturalIso C p).hom
      vafaPair12 C α i ≫ vafaPair13 C α i (vafaCross13 C i) ≫
        vafaPair23 C α i (vafaCross23 C i) =
          naturalSimpleScalar C α i ^ 3 • α.app (vafaObject C i)) :
    ∀ i, pivotalTwistUnit C p i ^ (4 * vafaMultiplicity C i) =
      ∏ j, pivotalTwistUnit C p j ^ vafaWeight C i j := by
  intro i
  have hh := vafa_relations_of_lantern h i
  simp_rw [natural_pivotal_twist_scalar] at hh
  apply Units.ext
  simpa using hh

end PropertyF.Ground.CentreCabling

open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCabling
universe v u

/-- The three individual pivotal twists on the Vafa triple tensor object. -/
def vafaSingles (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (i : Fin (rank C)) :
    vafaObject C i ⟶ vafaObject C i :=
  (((Dimensions.pivotalBraidedTwist C p (simples C i)).hom ⊗ₘ
    (Dimensions.pivotalBraidedTwist C p (simples C (dualIndex C i))).hom) ⊗ₘ
      (Dimensions.pivotalBraidedTwist C p (simples C i)).hom)

set_option backward.isDefEq.respectTransparency false in
/-- In a spherical category the product of the three individual twists on
the Vafa triple is the cube of the twist scalar. -/
theorem vafaSingles_eq_scalar (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (i : Fin (rank C)) :
    vafaSingles C p i =
      naturalSimpleScalar C (Dimensions.pivotalBraidedTwistNaturalIso C p).hom i ^ 3 •
        𝟙 (vafaObject C i) := by
  letI : Simple (simples C i) := simples_simple C i
  letI : Simple (simples C (dualIndex C i)) := simples_simple C _
  have hdual := spherical_twistScalar_dual_label C p hp i
  have hscalar := natural_pivotal_twist_scalar C p i
  have hs : naturalSimpleScalar C (Dimensions.pivotalBraidedTwistNaturalIso C p).hom i =
      Dimensions.pivotalBraidedTwistScalar C p (simples C i) := by
    simpa [pivotalTwistUnit] using hscalar
  unfold vafaSingles
  simp only [Dimensions.pivotalBraidedTwist_simple, hdual, hs]
  simp [tensorHom_def, MonoidalLinear.smul_whiskerRight,
    MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul, smul_smul, pow_succ, mul_assoc, vafaObject]

/-- In a spherical category, the general lantern identity gives the Vafa
relations without any separate dual-scalar hypothesis. -/
theorem pivotal_vafa_relations_of_general_lantern
    (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (h : ∀ i, let α := (Dimensions.pivotalBraidedTwistNaturalIso C p).hom
      vafaPair12 C α i ≫ vafaPair13 C α i (vafaCross13 C i) ≫
        vafaPair23 C α i (vafaCross23 C i) = α.app (vafaObject C i) ≫ vafaSingles C p i) :
    ∀ i, pivotalTwistUnit C p i ^ (4 * vafaMultiplicity C i) =
      ∏ j, pivotalTwistUnit C p j ^ vafaWeight C i j := by
  apply pivotal_vafa_relations_of_lantern C p
  intro i
  dsimp only
  rw [h i, vafaSingles_eq_scalar C p hp i]
  simp

end PropertyF.Ground.CentreCabling
