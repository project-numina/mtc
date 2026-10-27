module
public import PropertyF.Ground.Calculus.ThreeEmbedding
public import PropertyF.Ground.Calculus.OverlapTrace
public import PropertyF.Ground.Modular.SMatrix

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

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The two-strand square has the trace of double self-braiding. -/
theorem two_braid_square_trace [RightRigidCategory C]
    (X : C) (p : Dimensions.PivotalStructure (C := C)) :
    p.rightTrace (Aut.toEnd (braidGenerator X 0 0 ^ 2)).asHom =
      p.rightTrace (selfMonodromy X).asHom := by
  have h : (isoEndAlgEquiv (twoPowerIso X)) (Aut.toEnd (braidGenerator X 0 0)) =
      End.of ((β_ X X).hom) := by
    apply End.ext
    exact twoGenerator_transport X
  have hh := rightTrace_iso_conj p (twoPowerIso X) (Aut.toEnd (braidGenerator X 0 0 ^ 2))
  simp only [map_pow, h] at hh
  simpa [selfMonodromy, pow_two, End.mul_asHom] using hh.symm

/-- The two-strand double braid realizes the diagonal categorical S entry. -/
theorem two_braid_square_trace_categoricalS (D : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := D.Obj)) (i : Fin (Ground.rank D)) :
    Ground.unitScalarEquiv D (p.rightTrace
      (Aut.toEnd (braidGenerator (Ground.simples D i) 0 0 ^ 2)).asHom) =
      Ground.Modular.categoricalS D p i i := by
  simpa [Ground.Modular.categoricalS, Ground.Modular.SEntry,
    Ground.Modular.doubleBraiding, selfMonodromy] using
    congrArg (Ground.unitScalarEquiv D) (two_braid_square_trace (Ground.simples D i) p)

/-- The three-strand formula in terms of the actual categorical S-matrix. -/
theorem three_braid_trace_categoricalS (D : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := D.Obj)) (i : Fin (Ground.rank D)) :
    Ground.unitScalarEquiv D (p.rightTrace
      (Aut.toEnd ((braidGenerator (Ground.simples D i) 1 0) ^ 2 *
        (braidGenerator (Ground.simples D i) 1 1) ^ 2)).asHom) =
      Ground.Modular.categoricalS D p i i ^ 2 / Ground.Modular.simpleDimension D p i := by
  let _ : Simple (Ground.simples D i) := Ground.simples_simple D i
  simpa [Ground.Modular.categoricalS, Ground.Modular.SEntry,
    Ground.Modular.doubleBraiding, Ground.Modular.simpleDimension, selfMonodromy] using
    (three_braid_trace D (Ground.simples D i) p (Ground.unitScalarEquiv D))

/-- Applying a field automorphism transports the actual two-strand trace to
its Galois-conjugate S entry. -/
theorem two_braid_square_galois_trace (D : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := D.Obj)) (i : Fin (Ground.rank D))
    (σ : ℂ ≃+* ℂ) :
    σ (Ground.unitScalarEquiv D (p.rightTrace
      (Aut.toEnd (braidGenerator (Ground.simples D i) 0 0 ^ 2)).asHom)) =
      σ (Ground.Modular.categoricalS D p i i) :=
  congrArg σ (two_braid_square_trace_categoricalS D p i)

end PropertyF.Ground.Calculus
