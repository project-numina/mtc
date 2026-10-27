module
public import PropertyF.Ground.Dimensions.SimpleScalars
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Dimensions.SphericalCriterion
public import PropertyF.Ground.Dimensions.SphericalArithmetic

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

set_option backward.isDefEq.respectTransparency false in
/-- Twist a pivotal structure by a fusion-compatible family of nonzero simple scalars. -/
def pivotalScalarTwist (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (c : Fin (Ground.rank C) → ℂ)
    (hc : ∀ i, c i ≠ 0) (hunit : c (Ground.unitIndex C) = 1)
    (hmul : ∀ i j k, Ground.fusionCoeff C i j k ≠ 0 → c k = c i * c j) :
    PivotalStructure (C := C.Obj) where
  iso X := (simpleScalarNaturalIso C c hc).app X ≪≫ p.iso X
  naturality {X Y} f := by
    simp only [Iso.trans_hom, ← Category.assoc]
    have hn := (simpleScalarNaturalIso C c hc).hom.naturality f
    simp only [Functor.id_map] at hn
    change f ≫ ((simpleScalarNaturalIso C c hc).app Y).hom =
      ((simpleScalarNaturalIso C c hc).app X).hom ≫ f at hn
    rw [hn]
    simpa only [Category.assoc] using congrArg
      (fun h => ((simpleScalarNaturalIso C c hc).app X).hom ≫ h) (p.naturality f)
  tensor X Y := by
    simp only [Iso.trans_hom, p.tensor]
    change (simpleScalarNatural C c).app (X ⊗ Y) ≫
      ((p.iso X).hom ⊗ₘ (p.iso Y).hom) ≫ (doubleDualTensorIso X Y).hom = _
    rw [simpleScalarNatural_tensor C c hmul, ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rfl
  unit := by
    simp only [Iso.trans_hom, p.unit]
    change (simpleScalarNatural C c).app (𝟙_ C.Obj) ≫ _ = _
    simp only [simpleScalarNatural_unit C c hunit, Category.id_comp]

/-- Twisting rescales each simple pivotal dimension by the chosen scalar. -/
theorem pivotalDimension_scalarTwist_simple (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (c : Fin (Ground.rank C) → ℂ)
    (hc : ∀ i, c i ≠ 0) (hunit : c (Ground.unitIndex C) = 1)
    (hmul : ∀ i j k, Ground.fusionCoeff C i j k ≠ 0 → c k = c i * c j)
    (i : Fin (Ground.rank C)) :
    pivotalDimension C (pivotalScalarTwist C p c hc hunit hmul) (Ground.simples C i) =
      c i * pivotalDimension C p (Ground.simples C i) := by
  unfold pivotalDimension
  have ht : (pivotalScalarTwist C p c hc hunit hmul).rightTrace
      (𝟙 (Ground.simples C i)) = c i • p.rightTrace (𝟙 (Ground.simples C i)) := by
    apply End.homEquiv.injective
    have hs : (simpleScalarNaturalIso C c hc).hom.app (Ground.simples C i) =
        c i • 𝟙 (Ground.simples C i) := simpleScalarNaturalIso_app_simple C c hc i
    simp [PivotalStructure.rightTrace, pivotalScalarTwist, hs, tensorHom_def]
  rw [ht]
  simp only [← groundUnitScalarEquiv_apply, map_smul, smul_eq_mul]

/-- A sign-valued scalar twist of a spherical structure is spherical. -/
theorem pivotalScalarTwist_spherical (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0)
    (hunit : c (Ground.unitIndex C) = 1)
    (hmul : ∀ i j k, Ground.fusionCoeff C i j k ≠ 0 → c k = c i * c j)
    (hsign : ∀ i, c i * c i = 1) :
    (pivotalScalarTwist C p c hc hunit hmul).IsSpherical := by
  apply (isSpherical_iff_simple_dimensions C _).2
  intro i
  let X := Ground.simples C i
  let a := (simpleScalarNaturalIso C c hc).app X
  have ha : a.hom = c i • 𝟙 X := simpleScalarNaturalIso_app_simple C c hc i
  have hainv : a.inv = c i • 𝟙 X := by
    symm
    apply (Iso.comp_hom_eq_id a).1
    rw [ha]
    simp [← mul_smul, hsign i]
  dsimp [a] at ha hainv
  have hleft : (pivotalScalarTwist C p c hc hunit hmul).leftTrace (𝟙 X) =
      c i • p.leftTrace (𝟙 X) := by
    apply End.homEquiv.injective
    simp [PivotalStructure.leftTrace, pivotalScalarTwist, hainv, tensorHom_def]
  have hright : (pivotalScalarTwist C p c hc hunit hmul).rightTrace (𝟙 X) =
      c i • p.rightTrace (𝟙 X) := by
    apply End.homEquiv.injective
    simp [PivotalStructure.rightTrace, pivotalScalarTwist, ha, tensorHom_def]
  rw [hleft, hright, hp X (𝟙 X)]

/-- Among scalar twists of a spherical structure, sphericality is exactly
sign-valuedness on the simple objects. -/
theorem pivotalScalarTwist_spherical_iff (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0)
    (hunit : c (Ground.unitIndex C) = 1)
    (hmul : ∀ i j k, Ground.fusionCoeff C i j k ≠ 0 → c k = c i * c j) :
    (pivotalScalarTwist C p c hc hunit hmul).IsSpherical ↔ ∀ i, c i * c i = 1 := by
  constructor
  · intro hq i
    letI : Simple (Ground.simples C i) := Ground.simples_simple C i
    have hnorm := (target_squaredNorm_eq_dimension_sq C p hp (Ground.simples C i)).symm.trans
      (target_squaredNorm_eq_dimension_sq C (pivotalScalarTwist C p c hc hunit hmul)
        hq (Ground.simples C i))
    have hd : pivotalDimension C p (Ground.simples C i) ≠ 0 :=
      pivotalDimension_simple_ne_zero C p i
    have hsq : pivotalDimension C p (Ground.simples C i) ^ 2 =
        (c i * pivotalDimension C p (Ground.simples C i)) ^ 2 := by
      simp only [← rightTrace_id] at hnorm
      change pivotalDimension C p (Ground.simples C i) ^ 2 =
        pivotalDimension C (pivotalScalarTwist C p c hc hunit hmul) (Ground.simples C i) ^ 2 at hnorm
      rw [pivotalDimension_scalarTwist_simple] at hnorm
      exact hnorm
    apply mul_right_cancel₀ (pow_ne_zero 2 hd)
    calc
      (c i * c i) * pivotalDimension C p (Ground.simples C i) ^ 2 =
          (c i * pivotalDimension C p (Ground.simples C i)) ^ 2 := by ring
      _ = pivotalDimension C p (Ground.simples C i) ^ 2 := hsq.symm
      _ = 1 * pivotalDimension C p (Ground.simples C i) ^ 2 := by ring
  · exact pivotalScalarTwist_spherical C p hp c hc hunit hmul

end PropertyF.Ground.Dimensions
