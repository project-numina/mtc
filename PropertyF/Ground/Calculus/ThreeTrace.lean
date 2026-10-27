module
public import PropertyF.Ground.Calculus.ThreeEmbedding
public import PropertyF.Ground.Calculus.OverlapTrace

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

end PropertyF.Ground.Calculus
