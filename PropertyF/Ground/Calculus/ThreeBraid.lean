module
public import PropertyF.Ground.Calculus.FiniteOrder
public import Mathlib.CategoryTheory.Conj
public import Mathlib.Tactic

/-! The actual three-strand braid relation, including tensor-power unitors. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Remove the trailing tensor unit from the three-fold tensor power. -/
def threePowerIso (X : C) : tensorPower X 3 ≅ X ⊗ (X ⊗ X) :=
  Iso.refl X ⊗ᵢ (Iso.refl X ⊗ᵢ (ρ_ X))

set_option backward.isDefEq.respectTransparency false in
theorem threeGeneratorLeft_transport (X : C) :
  ((threePowerIso X).conjAut (braidGenerator X 1 0)).asIso.hom =
    (α_ X X X).inv ≫ (β_ X X).hom ▷ X ≫ (α_ X X X).hom := by
  change (threePowerIso X).inv ≫ (braidGenerator X 1 _).asIso.hom ≫ (threePowerIso X).hom = _
  dsimp only [threePowerIso, braidGenerator, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv]
  simp only [id_tensorHom, tensorHom_id, Category.assoc]
  monoidal

set_option backward.isDefEq.respectTransparency false in
theorem threeGeneratorRight_transport (X : C) :
  ((threePowerIso X).conjAut (braidGenerator X 1 1)).asIso.hom = X ◁ (β_ X X).hom := by
  change (threePowerIso X).inv ≫ (braidGenerator X 1 _).asIso.hom ≫ (threePowerIso X).hom = _
  dsimp only [threePowerIso, braidGenerator, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv]
  simp only [id_tensorHom, tensorHom_id]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The categorical adjacent braidings satisfy Yang–Baxter. -/
theorem three_braid_relation (X : C) :
    braidGenerator X 1 0 * braidGenerator X 1 1 * braidGenerator X 1 0 =
    braidGenerator X 1 1 * braidGenerator X 1 0 * braidGenerator X 1 1 := by
  apply (threePowerIso X).conjAut.injective
  apply Aut.ext
  apply Iso.ext
  simp only [map_mul, Aut.mul_asIso, Iso.trans_hom, threeGeneratorLeft_transport, threeGeneratorRight_transport, Category.assoc]
  exact BraidedCategory.yang_baxter X X X

/-- The two adjacent generators in the actual three-strand image. -/
def threeGeneratorLeft (X : C) : braidImage X 1 := imageGenerator X 1 0

def threeGeneratorRight (X : C) : braidImage X 1 := imageGenerator X 1 1

/-- The Yang–Baxter relation holds inside the actual categorical braid image. -/
theorem three_braid_image_relation (X : C) :
    threeGeneratorLeft X * threeGeneratorRight X * threeGeneratorLeft X =
    threeGeneratorRight X * threeGeneratorLeft X * threeGeneratorRight X := by
  apply Subtype.ext
  exact three_braid_relation X

/-- Every representation of the actual three-strand image satisfies the braid relation. -/
theorem three_braid_relation_map {H : Type*} [Monoid H] (X : C)
    (ρ : braidImage X 1 →* H) :
    ρ (threeGeneratorLeft X) * ρ (threeGeneratorRight X) * ρ (threeGeneratorLeft X) =
    ρ (threeGeneratorRight X) * ρ (threeGeneratorLeft X) * ρ (threeGeneratorRight X) := by
  simpa only [map_mul] using congrArg ρ (three_braid_image_relation X)

end PropertyF.Ground.Calculus
