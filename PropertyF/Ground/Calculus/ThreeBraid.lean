module
public import PropertyF.Definitions
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.CategoryTheory.Conj
public import Mathlib.Tactic

/-! Finiteness of categorical braid images supplies the finite-order condition
for the squared braiding and for every representation of the braid image. -/

@[expose] public section
open CategoryTheory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- An adjacent generator as an element of the actual categorical braid image. -/
def imageGenerator (X : C) (n : ℕ) (i : Fin (n + 1)) : braidImage X n :=
  ⟨braidGenerator X n i, Subgroup.subset_closure (Set.mem_range_self _)⟩

/-- Every represented braid image element has finite order when the categorical
image is finite. No faithfulness of the representation is required. -/
theorem represented_braid_finite_order {H : Type*} [Monoid H]
    (X : C) (n : ℕ) (h : Finite (braidImage X n))
    (ρ : braidImage X n →* H) (g : braidImage X n) :
    ∃ k : ℕ, k ≠ 0 ∧ (ρ g) ^ k = 1 := by
  let _ : Finite (braidImage X n) := h
  obtain ⟨k, hk, hpow⟩ := (ρ.isOfFinOrder (isOfFinOrder_of_finite g)).exists_pow_eq_one
  exact ⟨k, hk.ne', hpow⟩

/-- In particular, the represented square of the two-strand self-braiding
satisfies the `finite_order` condition needed for three-strand rigidity. -/
theorem represented_square_finite_order {H : Type*} [Monoid H]
    (X : C) (h : ObjectPropertyF X) (ρ : braidImage X 0 →* H) :
    ∃ k : ℕ, k ≠ 0 ∧ (ρ ((imageGenerator X 0 0) ^ 2)) ^ k = 1 :=
  represented_braid_finite_order X 0 (h 0) ρ _

/-- The categorical square itself has finite order. -/
theorem braid_square_finite_order (X : C) (h : ObjectPropertyF X) :
    ∃ k : ℕ, k ≠ 0 ∧ (braidGenerator X 0 0 ^ 2) ^ k = 1 := by
  obtain ⟨k, hk, hpow⟩ := represented_square_finite_order X h (braidImage X 0).subtype
  exact ⟨k, hk, hpow⟩

end PropertyF.Ground.Calculus

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
    ρ (threeGeneratorRight X) * ρ (threeGeneratorLeft X) * ρ (threeGeneratorRight X) := by simpa only [map_mul] using congrArg ρ (three_braid_image_relation X)

end PropertyF.Ground.Calculus
