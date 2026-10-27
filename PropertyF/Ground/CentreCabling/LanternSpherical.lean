module
public import PropertyF.Ground.CentreCabling.VafaLanternReduction
public import PropertyF.Ground.CentreCabling.TwistDual

/-! Reduction from the general three-strand lantern identity to Vafa. -/
@[expose] public noncomputable section
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
