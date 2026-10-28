module
public import PropertyF.Definitions
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.CategoryTheory.Conj
public import Mathlib.Tactic
public import PropertyF.Ground.Calculus.RightStrand
public import PropertyF.Ground.Dimensions.TensorMultiplicativity
public import PropertyF.Ground.Modular.SMatrix

/-! Finiteness of categorical braid images supplies the finite-order condition
for the squared braiding and for every representation of the braid image. -/

open PropertyF.Ground.Dimensions

@[expose] public section
open CategoryTheory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- An adjacent generator as an element of the actual categorical braid image. -/
def imageGenerator (X : C) (n : ℕ) (i : Fin (n + 1)) : braidImage X n :=
  ⟨braidGenerator X n i, Subgroup.subset_closure (Set.mem_range_self _)⟩

/-- The categorical square has finite order when its braid image is finite. -/
theorem braid_square_finite_order {X : C} (h : ObjectPropertyF X) :
    ∃ k : ℕ, k ≠ 0 ∧ (braidGenerator X 0 0 ^ 2) ^ k = 1 :=
  let _ : Finite (braidImage X 0) := h 0
  ((braidImage X 0).subtype.isOfFinOrder
    (isOfFinOrder_of_finite ((imageGenerator X 0 0) ^ 2))).exists_pow_eq_one.imp
      fun _ ⟨hk, hpow⟩ ↦ ⟨hk.ne', hpow⟩

end PropertyF.Ground.Calculus

/-! The actual three-strand braid relation, including tensor-power unitors. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

section
variable (X : C)

/-- Remove the trailing tensor unit from the three-fold tensor power. -/
def threePowerIso : tensorPower X 3 ≅ X ⊗ (X ⊗ X) :=
  Iso.refl X ⊗ᵢ (Iso.refl X ⊗ᵢ (ρ_ X))

set_option backward.isDefEq.respectTransparency false in
/-- The left generator becomes the crossing of the first two factors. -/
theorem threeGeneratorLeft_transport :
  ((threePowerIso X).conjAut (braidGenerator X 1 0)).asIso.hom =
    (α_ X X X).inv ≫ (β_ X X).hom ▷ X ≫ (α_ X X X).hom := by
  change (threePowerIso X).inv ≫ (braidGenerator X 1 _).asIso.hom ≫ (threePowerIso X).hom = _
  dsimp only [threePowerIso, braidGenerator, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv]
  simp only [id_tensorHom, tensorHom_id, Category.assoc]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The right generator becomes the crossing of the last two factors. -/
theorem threeGeneratorRight_transport :
  ((threePowerIso X).conjAut (braidGenerator X 1 1)).asIso.hom = X ◁ (β_ X X).hom := by
  change (threePowerIso X).inv ≫ (braidGenerator X 1 _).asIso.hom ≫ (threePowerIso X).hom = _
  dsimp only [threePowerIso, braidGenerator, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv]
  simp only [id_tensorHom, tensorHom_id]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The categorical adjacent braidings satisfy Yang–Baxter. -/
theorem three_braid_relation :
    braidGenerator X 1 0 * braidGenerator X 1 1 * braidGenerator X 1 0 =
    braidGenerator X 1 1 * braidGenerator X 1 0 * braidGenerator X 1 1 :=
  (threePowerIso X).conjAut.injective (Aut.ext (Iso.ext (by
    simpa only [map_mul, Aut.mul_asIso, Iso.trans_hom, threeGeneratorLeft_transport,
      threeGeneratorRight_transport, Category.assoc] using BraidedCategory.yang_baxter X X X)))

/-- The two adjacent generators in the actual three-strand image. -/
def threeGeneratorLeft : braidImage X 1 := imageGenerator X 1 0

/-- The right adjacent generator in the three-strand braid image. -/
def threeGeneratorRight : braidImage X 1 := imageGenerator X 1 1

/-- The Yang–Baxter relation holds inside the actual categorical braid image. -/
theorem three_braid_image_relation :
    threeGeneratorLeft X * threeGeneratorRight X * threeGeneratorLeft X =
    threeGeneratorRight X * threeGeneratorLeft X * threeGeneratorRight X :=
  Subtype.ext (three_braid_relation X)

end

/-- Every representation of the actual three-strand image satisfies the braid relation. -/
theorem three_braid_relation_map {H : Type*} [Monoid H] {X : C}
    (ρ : braidImage X 1 →* H) :
    ρ (threeGeneratorLeft X) * ρ (threeGeneratorRight X) * ρ (threeGeneratorLeft X) =
    ρ (threeGeneratorRight X) * ρ (threeGeneratorLeft X) * ρ (threeGeneratorRight X) := by
  simpa only [map_mul] using congrArg ρ (three_braid_image_relation X)

end PropertyF.Ground.Calculus

/-! Two- and three-strand categorical braid embeddings. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]


omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The left adjacent generator after removing the trailing tensor unit. -/
theorem threeGeneratorLeft_end_transport (X : C) :
    (isoEndAlgEquiv (threePowerIso X)) (Aut.toEnd (braidGenerator X 1 0)) =
      End.of ((α_ X X X).inv ≫ (β_ X X).hom ▷ X ≫ (α_ X X X).hom) :=
  End.ext (threeGeneratorLeft_transport X)

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The right adjacent generator after removing the trailing tensor unit. -/
theorem threeGeneratorRight_end_transport (X : C) :
    (isoEndAlgEquiv (threePowerIso X)) (Aut.toEnd (braidGenerator X 1 1)) =
      End.of (X ◁ (β_ X X).hom) :=
  End.ext (threeGeneratorRight_transport X)

/-- The left three-strand generator in a chosen block presentation. -/
def tripleBlockLeft (X : C) {r : ℕ} {d : Fin r → ℕ}
    (b : braidAlgebra X 1 ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩) :=
  b (braidInImage X 1 (threeGeneratorLeft X))

/-- The right three-strand generator in a chosen block presentation. -/
def tripleBlockRight (X : C) {r : ℕ} {d : Fin r → ℕ}
    (b : braidAlgebra X 1 ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩) :=
  b (braidInImage X 1 (threeGeneratorRight X))

end PropertyF.Ground.Calculus

/-! Simple-strand partial trace from the constructed iterated trace law. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u

/-- In a genuine braided fusion category, the partial trace onto a simple
surviving object is the total trace divided by its nonzero pivotal dimension. -/
theorem rightPartialTrace_simple_ground (C : BraidedFusionCategory.{v,u})
    {X Y : C.Obj} [Simple X] (p : PivotalStructure (C := C.Obj))
    (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ) (f : End (X ⊗ Y)) :
    rightPartialTrace p X Y f =
      (scalarTrace p scalar f / scalar (p.rightTrace (𝟙 X))) • (1 : End X) :=
  let _ : FiniteDimensional ℂ (X ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
  rightPartialTrace_simple_of_trace_compatibility (X := X) (Y := Y) p scalar f
    (by simpa only [map_zero] using scalar.injective.ne (Modular.pivotalTrace_simple_ne_zero C p X))
    (Dimensions.rightTrace_partialTrace p f)

end PropertyF.Ground.Calculus

/-! The graphical recurrence for two overlapping endomorphisms. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [Linear ℂ C]

/-- Embed a fresh endomorphism after a left spectator, with the associator
explicit. -/
def overlapFresh (A X Y : C) (u : End (X ⊗ Y)) : End ((A ⊗ X) ⊗ Y) :=
  End.of ((α_ A X Y).hom ≫ (A ◁ u.asHom) ≫ (α_ A X Y).inv)

/-- Multiply an old endomorphism by a new one sharing the middle factor. -/
def overlapEndProduct (A X Y : C) (v : End (A ⊗ X)) (u : End (X ⊗ Y)) :
    End ((A ⊗ X) ⊗ Y) := insertRightIdentity (A ⊗ X) Y v * overlapFresh A X Y u

variable (D : BraidedFusionCategory.{v,u})

variable {A X Y : D.Obj} [Simple X] (p : PivotalStructure (C := D.Obj))
  (scalar : End (𝟙_ D.Obj) ≃ₐ[ℂ] ℂ) (v : End (A ⊗ X)) (u : End (X ⊗ Y))

/-- Tracing the new strands of the overlap gives the old operator times the
normalized trace of the fresh operator. -/
theorem rightPartialTrace_overlap :
    rightPartialTrace p (A ⊗ X) Y (overlapEndProduct A X Y v u) =
      (scalarTrace p scalar u / scalar (p.rightTrace (𝟙 X))) • v := by
  rw [overlapEndProduct, rightPartialTrace_left, overlapFresh, rightPartialTrace_whiskerLeft,
    rightPartialTrace_simple_ground D (X := X) (Y := Y) p scalar u]
  exact End.ext (by simp)

/-- The categorical trace obeys the overlap recurrence with no braid-span
closure assumption on arbitrary partial traces. -/
theorem pivotalTrace_overlap :
    scalar (p.rightTrace (overlapEndProduct A X Y v u).asHom) =
      scalar (p.rightTrace v.asHom) *
        (scalar (p.rightTrace u.asHom) / scalar (p.rightTrace (𝟙 X))) := by
  rw [← Dimensions.rightTrace_partialTrace p (overlapEndProduct A X Y v u),
    rightPartialTrace_overlap D p scalar v u]
  simp [scalarTrace, PivotalStructure.rightTrace_smul, mul_comm]

end PropertyF.Ground.Calculus

/-! The trace of the actual three-strand double-monodromy braid. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Double self-braiding on the ordinary two-fold tensor product. -/
def selfMonodromy (X : C) : End (X ⊗ X) :=
  End.of ((β_ X X).hom ≫ (β_ X X).hom)

omit [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- Pivotal trace is unchanged by categorical conjugation. -/
theorem rightTrace_iso_conj [RightRigidCategory C]
    (p : PivotalStructure (C := C)) {X Y : C} (e : X ≅ Y) (a : End X) :
    p.rightTrace ((isoEndAlgEquiv e) a).asHom = p.rightTrace a.asHom := by
  simpa [isoEndAlgEquiv, Iso.conj_apply_asHom, Category.assoc] using
    p.rightTrace_cyclic e.inv (a.asHom ≫ e.hom)

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The actual braid `a²b²` becomes the graphical overlap of two copies of
double self-braiding after the standard tensor-power and associator isomorphisms. -/
theorem three_braid_double_overlap (X : C) :
    (isoEndAlgEquiv (threePowerIso X))
      (Aut.toEnd ((braidGenerator X 1 0) ^ 2 * (braidGenerator X 1 1) ^ 2)) =
    (isoEndAlgEquiv (α_ X X X))
      (overlapEndProduct X X X (selfMonodromy X) (selfMonodromy X)) := by
  rw [map_mul, map_pow, map_pow, map_mul, map_pow, map_pow, threeGeneratorLeft_end_transport, threeGeneratorRight_end_transport]
  apply End.ext
  simp [overlapEndProduct, insertRightIdentity, overlapFresh, selfMonodromy,
    isoEndAlgEquiv, Iso.conj_apply_asHom, pow_two, End.mul_asHom,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]

/-- The three-strand trace is the square of the double-braiding trace,
normalized by the pivotal dimension of the shared simple strand. -/
theorem three_braid_trace (D : BraidedFusionCategory.{v,u})
    (X : D.Obj) [Simple X] (p : PivotalStructure (C := D.Obj))
    (scalar : End (𝟙_ D.Obj) ≃ₐ[ℂ] ℂ) :
    scalar (p.rightTrace (Aut.toEnd ((braidGenerator X 1 0) ^ 2 *
      (braidGenerator X 1 1) ^ 2)).asHom) =
    scalar (p.rightTrace (selfMonodromy X).asHom) ^ 2 /
      scalar (p.rightTrace (𝟙 X)) := by
  rw [← rightTrace_iso_conj p (threePowerIso X), three_braid_double_overlap,
    rightTrace_iso_conj, pivotalTrace_overlap D (X := X) p scalar]
  ring

/-- Remove the trailing tensor unit from the two-fold tensor power. -/
def twoPowerIso (X : C) : tensorPower X 2 ≅ X ⊗ X :=
  Iso.refl X ⊗ᵢ (ρ_ X)

omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
set_option backward.isDefEq.respectTransparency false in
/-- The two-strand generator is the categorical self-braiding. -/
theorem twoGenerator_transport (X : C) :
    ((twoPowerIso X).conjAut (braidGenerator X 0 0)).asIso.hom = (β_ X X).hom := by
  change (twoPowerIso X).inv ≫ (braidGenerator X 0 0).asIso.hom ≫ (twoPowerIso X).hom = _
  dsimp only [twoPowerIso, braidGenerator, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv]
  simp only [id_tensorHom, tensorHom_id, Category.assoc]
  monoidal

end PropertyF.Ground.Calculus
