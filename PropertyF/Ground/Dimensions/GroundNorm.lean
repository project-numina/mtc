module
public import PropertyF.Definitions
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import PropertyF.Ground.Dimensions.Trace
public import PropertyF.Ground.Fusion.Simples
public import PropertyF.Ground.Integrate.UnitScalar

/-! # Intrinsic squared norms

Squared norms are independent of duality choices and are invariant under object isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions

universe v u
section SimpleIsomorphisms
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasKernels C] [Linear ℂ C]

/-- Two isomorphisms from a simple object differ by a nonzero scalar and their inverses
by its inverse. -/
theorem isomorphisms_scalar {X Y : C} [Simple X] [FiniteDimensional ℂ (X ⟶ X)]
    (j k : X ≅ Y) : ∃ c : ℂ, c ≠ 0 ∧ k.hom = c • j.hom ∧
    k.inv = c⁻¹ • j.inv := by
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ (k.hom ≫ j.inv)
  have hhom : k.hom = c • j.hom := by
    calc
      k.hom = (k.hom ≫ j.inv) ≫ j.hom := by simp
      _ = c • j.hom := by rw [← hc]; simp
  have hc0 : c ≠ 0 := by
    intro h
    have : k.hom = 0 := by simp [h, hhom]
    have : 𝟙 X = 0 := by simpa using congrArg (fun f => f ≫ k.inv) this
    exact id_nonzero X this
  have hinv : k.inv = c⁻¹ • j.inv := by
    apply (cancel_mono k.hom).1
    simp only [Linear.smul_comp, ← Linear.comp_smul, Iso.inv_hom_id]
    rw [hhom]
    simp [hc0, smul_smul]
  exact ⟨c, hc0, hhom, hinv⟩
end SimpleIsomorphisms

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Abelian C] [Linear ℂ C] [RigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The product of the two quantum traces on a simple object does not depend
on the chosen double-dual isomorphism. -/
theorem squaredNorm_independent {X : C} [Simple X] [FiniteDimensional ℂ (X ⟶ X)]
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (j k : X ≅ (Xᘁ)ᘁ) :
    scalar (rightQuantumTrace j) * scalar (leftQuantumTrace j) =
      scalar (rightQuantumTrace k) * scalar (leftQuantumTrace k) := by
  obtain ⟨c, hc, hhom, hinv⟩ := isomorphisms_scalar j k
  have hr : rightQuantumTrace k = c • rightQuantumTrace j :=
    rightQuantumTrace_smul_hom k j c hhom
  have hl : leftQuantumTrace k = c⁻¹ • leftQuantumTrace j := by
    apply End.homEquiv.injective
    simp [leftQuantumTrace, hinv, tensorHom_def]
  rw [hr, hl, map_smul, map_smul]
  simp only [smul_eq_mul]
  field_simp

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions

universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- For every simple object of a genuine braided fusion category, the
intrinsic squared norm in the target is independent of the chosen double-dual
isomorphism. -/
theorem target_squaredNorm_choice_independent
    {X : C.Obj} [Simple X] (j : X ≅ ((Xᘁ)ᘁ)) :
    squaredNorm C X =
      unitScalar C (rightQuantumTrace j) * unitScalar C (leftQuantumTrace j) := by
  let : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  unfold squaredNorm
  simp only [Ground.unitScalar_eq_equiv]
  exact squaredNorm_independent (Ground.unitScalarEquiv C) (doubleDualIso C X) j

/-- With any spherical structure the target norm of a simple object is its
categorical dimension squared. -/
theorem target_squaredNorm_eq_dimension_sq
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (X : C.Obj) [Simple X] :
    squaredNorm C X =
      (unitScalar C (rightQuantumTrace (p.iso X))) ^ 2 := by
  rw [target_squaredNorm_choice_independent C (p.iso X),
    ← spherical_quantumTraces_eq p hp X, pow_two]

/-- The target's intrinsic global dimension is the sum of squared spherical
simple dimensions, for any spherical structure. -/
theorem target_globalDimension_eq_sum_squares
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical) :
    globalDimension C = ∑ i : Fin (rank C),
      (unitScalar C (rightQuantumTrace (p.iso (simples C i)))) ^ 2 := by
  unfold globalDimension
  apply Finset.sum_congr rfl
  intro i _
  let : Simple (simples C i) := simples_simple C i
  exact target_squaredNorm_eq_dimension_sq C p hp (simples C i)

/-- Intrinsic squared norms are invariant under simple-object isomorphism,
without assuming a pivotal or spherical structure. -/
theorem target_squaredNorm_iso
    {X Y : C.Obj} [Simple X] [Simple Y] (e : X ≅ Y) :
    squaredNorm C X = squaredNorm C Y := by
  let j := doubleDualIso C X
  let k : Y ≅ (Yᘁ)ᘁ := e.symm ≪≫ j ≪≫ rightDualIsoMap (rightDualIsoMap e)
  have hnat : e.hom ≫ k.hom = j.hom ≫ (e.homᘁ)ᘁ := by
    simp [k, rightDualIsoMap]
  have h := quantumTraces_iso j k e hnat
  rw [target_squaredNorm_choice_independent C j,
      target_squaredNorm_choice_independent C k, h.1, h.2]

end PropertyF.Ground.Dimensions

end
