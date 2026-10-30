module
public import MTC.Braided.Definitions
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.CategoryTheory.Conj
public import Mathlib.Tactic
public import MTC.Braided.Trace.RightStrand
public import MTC.CategoryTheory.Dimensions.DimensionCharacter
public import MTC.Modular.SMatrix

/-!
# Traces of three-strand braids

The categorical three-strand generators obey the braid relation and have finite
order when the object has property F. Partial traces compute their overlap trace.
-/

open MTC.Dimensions

@[expose] public section
open CategoryTheory
namespace MTC.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- An adjacent generator as an element of the actual categorical braid image. -/
def imageGenerator (X : C) (n : ℕ) (i : Fin (n + 1)) : braidImage X n :=
  ⟨braidGenerator X n i, Subgroup.subset_closure (Set.mem_range_self _)⟩

end MTC.Calculus

/-! The actual three-strand braid relation, including tensor-power unitors. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Calculus
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
  simp [threePowerIso, braidGenerator, tensorPower]

set_option backward.isDefEq.respectTransparency false in
/-- The right generator becomes the crossing of the last two factors. -/
theorem threeGeneratorRight_transport :
  ((threePowerIso X).conjAut (braidGenerator X 1 1)).asIso.hom = X ◁ (β_ X X).hom := by
  change (threePowerIso X).inv ≫ (braidGenerator X 1 _).asIso.hom ≫ (threePowerIso X).hom = _
  simp [threePowerIso, braidGenerator, tensorPower]

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

end MTC.Calculus

/-! Two- and three-strand categorical braid embeddings. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

section GeneratorTransport

variable (X : C)

/-- The left adjacent generator after removing the trailing tensor unit. -/
theorem threeGeneratorLeft_end_transport :
    (threePowerIso X).conj (Aut.toEnd (braidGenerator X 1 0)) =
      End.of ((α_ X X X).inv ≫ (β_ X X).hom ▷ X ≫ (α_ X X X).hom) :=
  End.ext (threeGeneratorLeft_transport X)

/-- The right adjacent generator after removing the trailing tensor unit. -/
theorem threeGeneratorRight_end_transport :
    (threePowerIso X).conj (Aut.toEnd (braidGenerator X 1 1)) =
      End.of (X ◁ (β_ X X).hom) :=
  End.ext (threeGeneratorRight_transport X)

end GeneratorTransport

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
variable {X : C} {r : ℕ} {d : Fin r → ℕ} (b : BraidBlockPresentation X 1 d)

/-- The left three-strand generator in a chosen block presentation. -/
def tripleBlockLeft :=
  b (braidInImage (threeGeneratorLeft X))

/-- The right three-strand generator in a chosen block presentation. -/
def tripleBlockRight :=
  b (braidInImage (threeGeneratorRight X))

end MTC.Calculus

/-! Simple-strand partial trace from the constructed iterated trace law. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Calculus
universe v u

/-- In a genuine braided fusion category, the partial trace onto a simple
surviving object is the total trace divided by its nonzero pivotal dimension. -/
theorem rightPartialTrace_simple_ground (C : BraidedFusionCategory.{v,u})
    {X Y : C.Obj} [Simple X] (p : PivotalStructure (C := C.Obj))
    (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ) (f : End (X ⊗ Y)) :
    rightPartialTrace p f = (scalarTrace p scalar f / scalar (p.rightTrace (𝟙 X))) • (1 : End X) :=
  let _ : FiniteDimensional ℂ (X ⟶ X) := MTC.IsFusionCategory.hom_finite _ _
  rightPartialTrace_simple (X := X) (Y := Y) p scalar f
    (by simpa only [map_zero] using scalar.injective.ne (Modular.pivotalTrace_simple_ne_zero C p X))

end MTC.Calculus

/-! The graphical recurrence for two overlapping endomorphisms. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [Linear ℂ C]

/-- Embed a fresh endomorphism after a left spectator, with the associator
explicit. -/
def overlapFresh (A : C) {X Y : C} (u : End (X ⊗ Y)) : End ((A ⊗ X) ⊗ Y) :=
  End.of ((α_ A X Y).hom ≫ (A ◁ u.asHom) ≫ (α_ A X Y).inv)

/-- Multiply an old endomorphism by a new one sharing the middle factor. -/
def overlapEndProduct {A X Y : C} (v : End (A ⊗ X)) (u : End (X ⊗ Y)) :
    End ((A ⊗ X) ⊗ Y) := insertRightIdentity Y v * overlapFresh A u

variable (D : BraidedFusionCategory.{v,u})

variable {A X Y : D.Obj} [Simple X] (p : PivotalStructure (C := D.Obj))
  (scalar : End (𝟙_ D.Obj) ≃ₐ[ℂ] ℂ) (v : End (A ⊗ X)) (u : End (X ⊗ Y))

/-- Tracing the new strands of the overlap gives the old operator times the
normalized trace of the fresh operator. -/
theorem rightPartialTrace_overlap :
    rightPartialTrace p (overlapEndProduct v u) =
      (scalarTrace p scalar u / scalar (p.rightTrace (𝟙 X))) • v :=
  End.ext (by simp [overlapEndProduct, overlapFresh, rightPartialTrace_left,
    rightPartialTrace_whiskerLeft, rightPartialTrace_simple_ground D p scalar])

/-- The categorical trace obeys the overlap recurrence with no braid-span
closure assumption on arbitrary partial traces. -/
theorem pivotalTrace_overlap :
    scalar (p.rightTrace (overlapEndProduct v u).asHom) =
      scalar (p.rightTrace v.asHom) *
        (scalar (p.rightTrace u.asHom) / scalar (p.rightTrace (𝟙 X))) := by
  rw [← Dimensions.rightTrace_partialTrace p, rightPartialTrace_overlap D p scalar]
  simp [scalarTrace, PivotalStructure.rightTrace_smul, mul_comm]

end MTC.Calculus

/-! The trace of the actual three-strand double-monodromy braid. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Double self-braiding on the ordinary two-fold tensor product. -/
def selfMonodromy (X : C) : End (X ⊗ X) :=
  End.of ((β_ X X).hom ≫ (β_ X X).hom)

omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The actual braid `a²b²` becomes the graphical overlap of two copies of
double self-braiding after the standard tensor-power and associator isomorphisms. -/
theorem three_braid_double_overlap (X : C) :
    (threePowerIso X).conj
      (Aut.toEnd ((braidGenerator X 1 0) ^ 2 * (braidGenerator X 1 1) ^ 2)) =
    (α_ X X X).conj (overlapEndProduct (selfMonodromy X) (selfMonodromy X)) := by
  apply End.ext
  simp [map_mul, threeGeneratorLeft_end_transport, threeGeneratorRight_end_transport,
    overlapEndProduct, insertRightIdentity, overlapFresh, selfMonodromy,
    Iso.conj_apply_asHom, pow_two, End.mul_asHom, comp_whiskerRight, whiskerLeft_comp,
    Category.assoc]

/-- Pivotal trace of an element of an actual categorical braid algebra. -/
def actualBraidTrace (D : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := D.Obj))
    {X : D.Obj} {n : ℕ} (a : braidAlgebra X n) : ℂ :=
  MTC.unitScalarEquiv D (p.rightTrace (a : End (braidTensorPower X n)).asHom)

set_option backward.isDefEq.respectTransparency false in
/-- The trace of the three-strand overlap is the squared monodromy trace,
normalized by the pivotal dimension. -/
theorem actual_three_braid_trace (D : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (X : D.Obj) [Simple X] :
    actualBraidTrace D p (braidInImage (threeGeneratorLeft X ^ 2 * threeGeneratorRight X ^ 2)) =
      scalarTrace p (MTC.unitScalarEquiv D) (selfMonodromy X) ^ 2 / pivotalDimension D p X := by
  simp only [actualBraidTrace, threeGeneratorLeft, threeGeneratorRight, imageGenerator,
    SubmonoidClass.mk_pow, MulMemClass.mk_mul_mk, braidInImage_val, braidEndRepresentation,
    MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, pivotalDimension,
    unitScalar_eq_equiv, scalarTrace]
  rw [← rightTrace_iso_conj (threePowerIso X) p, three_braid_double_overlap,
    rightTrace_iso_conj, pivotalTrace_overlap, pow_two, mul_div_assoc]

/-- Remove the trailing tensor unit from the two-fold tensor power. -/
def twoPowerIso (X : C) : tensorPower X 2 ≅ X ⊗ X :=
  Iso.refl X ⊗ᵢ (ρ_ X)

end MTC.Calculus
