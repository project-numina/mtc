module
public import PropertyF.Ground.Calculus.RightStrand
public import PropertyF.Ground.Calculus.ThreeBraid
public import PropertyF.Ground.Dimensions.IteratedTrace
public import PropertyF.Ground.Modular.DimensionNonzero
public import PropertyF.Ground.Modular.SMatrix

/-! Two- and three-strand categorical braid embeddings. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]


/-- The left three-strand generator in a chosen block presentation. -/
def tripleBlockLeft (X : C) {r : ℕ} {d : Fin r → ℕ}
    (b : braidAlgebra X 1 ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  b (groupInImage (braidEndRepresentation X 1) (threeGeneratorLeft X))

/-- The right three-strand generator in a chosen block presentation. -/
def tripleBlockRight (X : C) {r : ℕ} {d : Fin r → ℕ}
    (b : braidAlgebra X 1 ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  b (groupInImage (braidEndRepresentation X 1) (threeGeneratorRight X))

end PropertyF.Ground.Calculus

/-! Simple-strand partial trace from the constructed iterated trace law. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u

/-- In a genuine braided fusion category, the partial trace onto a simple
surviving object is the total trace divided by its nonzero pivotal dimension. -/
theorem rightPartialTrace_simple_ground (C : Ground.BraidedFusionCategory.{v,u})
    (X Y : C.Obj) [Simple X] (p : Dimensions.PivotalStructure (C := C.Obj))
    (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ) (f : End (X ⊗ Y)) :
    rightPartialTrace p X Y f =
      (scalar (p.rightTrace f.asHom) / scalar (p.rightTrace (𝟙 X))) • (1 : End X) := by
  let _ : FiniteDimensional ℂ (X ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
  apply rightPartialTrace_simple_of_trace_compatibility X Y p scalar f
  · intro h
    apply Modular.pivotalTrace_simple_ne_zero C p X
    apply scalar.injective
    simpa using h
  · exact Dimensions.rightTrace_partialTrace p X Y f

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

/-- Tracing the new strands of the overlap gives the old operator times the
normalized trace of the fresh operator. -/
theorem rightPartialTrace_overlap (C : Ground.BraidedFusionCategory.{v,u})
    (A X Y : C.Obj) [Simple X] (p : Dimensions.PivotalStructure (C := C.Obj))
    (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ) (v : End (A ⊗ X)) (u : End (X ⊗ Y)) :
    rightPartialTrace p (A ⊗ X) Y (overlapEndProduct A X Y v u) =
      (scalar (p.rightTrace u.asHom) / scalar (p.rightTrace (𝟙 X))) • v := by
  rw [overlapEndProduct, rightPartialTrace_left, overlapFresh, rightPartialTrace_whiskerLeft,
    rightPartialTrace_simple_ground C X Y p scalar u]
  apply End.ext
  simp

/-- The categorical trace obeys the overlap recurrence with no braid-span
closure assumption on arbitrary partial traces. -/
theorem pivotalTrace_overlap (C : Ground.BraidedFusionCategory.{v,u})
    (A X Y : C.Obj) [Simple X] (p : Dimensions.PivotalStructure (C := C.Obj))
    (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ) (v : End (A ⊗ X)) (u : End (X ⊗ Y)) :
    scalar (p.rightTrace (overlapEndProduct A X Y v u).asHom) =
      scalar (p.rightTrace v.asHom) *
        (scalar (p.rightTrace u.asHom) / scalar (p.rightTrace (𝟙 X))) := by
  rw [← Dimensions.rightTrace_partialTrace p (A ⊗ X) Y (overlapEndProduct A X Y v u)]
  rw [rightPartialTrace_overlap C A X Y p scalar v u]
  simp [Dimensions.PivotalStructure.rightTrace_smul, mul_comm]

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
    (p : Dimensions.PivotalStructure (C := C)) {X Y : C} (e : X ≅ Y) (a : End X) :
    p.rightTrace ((isoEndAlgEquiv e) a).asHom = p.rightTrace a.asHom := by
  have h := p.rightTrace_cyclic e.inv (a.asHom ≫ e.hom)
  simpa [isoEndAlgEquiv, Iso.conj_apply_asHom, Category.assoc] using h

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The actual braid `a²b²` becomes the graphical overlap of two copies of
double self-braiding after the standard tensor-power and associator isomorphisms. -/
theorem three_braid_double_overlap (X : C) :
    (isoEndAlgEquiv (threePowerIso X))
      (Aut.toEnd ((braidGenerator X 1 0) ^ 2 * (braidGenerator X 1 1) ^ 2)) =
    (isoEndAlgEquiv (α_ X X X))
      (overlapEndProduct X X X (selfMonodromy X) (selfMonodromy X)) := by
  have ha : (isoEndAlgEquiv (threePowerIso X)) (Aut.toEnd (braidGenerator X 1 0)) =
      End.of ((α_ X X X).inv ≫ (β_ X X).hom ▷ X ≫ (α_ X X X).hom) := by
    apply End.ext
    exact threeGeneratorLeft_transport X
  have hb : (isoEndAlgEquiv (threePowerIso X)) (Aut.toEnd (braidGenerator X 1 1)) =
      End.of (X ◁ (β_ X X).hom) := by
    apply End.ext
    exact threeGeneratorRight_transport X
  rw [map_mul, map_pow, map_pow, map_mul, map_pow, map_pow, ha, hb]
  apply End.ext
  simp [overlapEndProduct, insertRightIdentity, overlapFresh, selfMonodromy,
    isoEndAlgEquiv, Iso.conj_apply_asHom, pow_two, End.mul_asHom,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]

/-- The three-strand trace is the square of the double-braiding trace,
normalized by the pivotal dimension of the shared simple strand. -/
theorem three_braid_trace (D : Ground.BraidedFusionCategory.{v,u})
    (X : D.Obj) [Simple X] (p : Dimensions.PivotalStructure (C := D.Obj))
    (scalar : End (𝟙_ D.Obj) ≃ₐ[ℂ] ℂ) :
    scalar (p.rightTrace (Aut.toEnd ((braidGenerator X 1 0) ^ 2 *
      (braidGenerator X 1 1) ^ 2)).asHom) =
    scalar (p.rightTrace (selfMonodromy X).asHom) ^ 2 /
      scalar (p.rightTrace (𝟙 X)) := by
  have h := congrArg (fun z : End (X ⊗ (X ⊗ X)) => scalar (p.rightTrace z.asHom))
    (three_braid_double_overlap X)
  simp only [rightTrace_iso_conj] at h
  rw [h, pivotalTrace_overlap D X X X p scalar]
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
