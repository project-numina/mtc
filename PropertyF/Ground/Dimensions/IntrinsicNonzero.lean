module
public import PropertyF.Ground.Dimensions.SphericalArithmetic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

/-- A simple object has nonzero right quantum trace for any double-dual isomorphism. -/
theorem rightQuantumTrace_simple_ne_zero (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) [Simple X] (j : X ≅ (Xᘁ)ᘁ) :
    rightQuantumTrace j ≠ 0 := by
  let _ : Simple (𝟙_ C.Obj) := Ground.IsFusionCategory.unit_simple
  let _ : FiniteDimensional ℂ (X ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
  let s : 𝟙_ C.Obj ⟶ X ⊗ (Xᘁ) := ExactPairing.coevaluation X (Xᘁ)
  have hs : s ≠ 0 := by
    intro hz
    have ht := ExactPairing.evaluation_coevaluation X (Xᘁ)
    change ExactPairing.coevaluation X (Xᘁ) = 0 at hz
    rw [hz] at ht
    simp at ht
    have ht' := congrArg (fun t => (λ_ X).inv ≫ t ≫ (ρ_ X).hom) ht
    have hid : 𝟙 X = 0 := by simpa [Category.assoc] using ht'.symm
    exact id_nonzero X hid
  obtain ⟨r₀, hr₀⟩ := Ground.split_from_simple s hs
  have hr₀ne : r₀ ≠ 0 := by
    intro h
    rw [h] at hr₀
    simp at hr₀
    exact id_nonzero (𝟙_ C.Obj) hr₀.symm
  let t : X ⊗ (Xᘁ) ≅ ((Xᘁ)ᘁ) ⊗ (Xᘁ) := j ⊗ᵢ Iso.refl _
  let ev : ((Xᘁ)ᘁ) ⊗ (Xᘁ) ⟶ 𝟙_ C.Obj := ExactPairing.evaluation (Xᘁ) ((Xᘁ)ᘁ)
  have hev : ev ≠ 0 := by
    let _ : Simple ((Xᘁ)ᘁ) := Simple.of_iso (j).symm
    intro hz
    have ht := ExactPairing.coevaluation_evaluation (Xᘁ) ((Xᘁ)ᘁ)
    change ExactPairing.evaluation (Xᘁ) ((Xᘁ)ᘁ) = 0 at hz
    rw [hz] at ht
    simp at ht
    have ht' := congrArg (fun q => (ρ_ ((Xᘁ)ᘁ)).inv ≫ q ≫ (λ_ ((Xᘁ)ᘁ)).hom) ht
    have hid : 𝟙 ((Xᘁ)ᘁ) = 0 := by simpa [Category.assoc] using ht'.symm
    exact id_nonzero ((Xᘁ)ᘁ) hid
  let r : X ⊗ (Xᘁ) ⟶ 𝟙_ C.Obj := t.hom ≫ ev
  have hr : r ≠ 0 := by
    intro hz
    have h := congrArg (fun f => t.inv ≫ f) hz
    have : ev = 0 := by simpa [r, Category.assoc] using h
    exact hev this
  let e₁ := Ground.tensorRightHomLinearEquiv X (Xᘁ) ((Xᘁ)ᘁ) (𝟙_ C.Obj)
  let e₂ := CategoryTheory.Linear.homCongr ℂ (Iso.refl X) (λ_ ((Xᘁ)ᘁ))
  let e₃ := CategoryTheory.Linear.homCongr ℂ (Iso.refl X) (j).symm
  have hfin : Module.finrank ℂ (X ⊗ (Xᘁ) ⟶ 𝟙_ C.Obj) = 1 := by
    calc
      _ = Module.finrank ℂ (X ⟶ X) := (e₁.trans (e₂.trans e₃)).finrank_eq
      _ = 1 := CategoryTheory.finrank_endomorphism_simple_eq_one ℂ X
  obtain ⟨z, hz⟩ := exists_smul_eq_of_finrank_eq_one hfin hr₀ne r
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_smul] at hz
    exact hr hz.symm
  intro hzero
  have hhom : s ≫ r = 0 := by
    have h := congrArg End.asHom hzero
    simpa [rightQuantumTrace, s, r, t, ev, tensorIso_hom] using h
  rw [← hz, Linear.comp_smul, hr₀] at hhom
  have : z • (𝟙 (𝟙_ C.Obj)) ≠ 0 := smul_ne_zero hz0 (id_nonzero _)
  exact this hhom


/-- In a braided fusion category the right dual of a simple object is simple. -/
theorem simple_rightDual (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X] :
    Simple (Xᘁ) := by
  let : Simple (ᘁX) := Ground.simple_leftDual C X
  let e : (ᘁX) ≅ (Xᘁ) :=
    leftDualIso HasLeftDual.exact (BraidedCategory.exactPairing_swap X (Xᘁ))
  exact Simple.of_iso e.symm

/-- A simple object has nonzero left quantum trace for any double-dual
isomorphism, by applying the right-trace result to its simple dual. -/
theorem leftQuantumTrace_simple_ne_zero (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) [Simple X] (j : X ≅ (Xᘁ)ᘁ) : leftQuantumTrace j ≠ 0 := by
  let : Simple (Xᘁ) := simple_rightDual C X
  rw [leftQuantumTrace_eq_rightDual]
  exact rightQuantumTrace_simple_ne_zero C (Xᘁ) (rightDualIsoMap j).symm

/-- The intrinsic squared norm of every simple is nonzero, without assuming
any pivotal or spherical structure. -/
theorem target_squaredNorm_ne_zero (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) [Simple X] : Ground.squaredNorm C X ≠ 0 := by
  unfold Ground.squaredNorm
  have hr := rightQuantumTrace_simple_ne_zero C X (Ground.doubleDualIso C X)
  have hl := leftQuantumTrace_simple_ne_zero C X (Ground.doubleDualIso C X)
  have hsr : Ground.unitScalar C (rightQuantumTrace (Ground.doubleDualIso C X)) ≠ 0 := by
    rw [Ground.unitScalar_eq_equiv]
    simpa using (Ground.unitScalarEquiv C).injective.ne hr
  have hsl : Ground.unitScalar C (leftQuantumTrace (Ground.doubleDualIso C X)) ≠ 0 := by
    rw [Ground.unitScalar_eq_equiv]
    simpa using (Ground.unitScalarEquiv C).injective.ne hl
  exact mul_ne_zero hsr hsl

/-- Dualizing a double-dual component twice exchanges its left and right
quantum traces. -/
theorem leftQuantumTrace_dual_component {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] {X : C} (j : X ≅ (Xᘁ)ᘁ) :
    leftQuantumTrace (rightDualIsoMap j).symm = rightQuantumTrace j := by
  rw [leftQuantumTrace_eq_rightDual]
  have hdual : (rightDualIsoMap (rightDualIsoMap j).symm).symm =
      rightDualIsoMap (rightDualIsoMap j) := by
    apply Iso.ext
    rfl
  rw [hdual]
  exact (rightQuantumTrace_iso j (rightDualIsoMap (rightDualIsoMap j)) j (by rfl)).symm

/-- The intrinsic squared norm is invariant under right duality, without any
pivotal or spherical structure. -/
theorem target_squaredNorm_rightDual (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) [Simple X] : Ground.squaredNorm C (Xᘁ) = Ground.squaredNorm C X := by
  let : Simple (Xᘁ) := simple_rightDual C X
  let j := Ground.doubleDualIso C X
  rw [target_squaredNorm_choice_independent C (Xᘁ) (rightDualIsoMap j).symm,
    target_squaredNorm_choice_independent C X j]
  rw [← leftQuantumTrace_eq_rightDual j, leftQuantumTrace_dual_component]
  exact mul_comm _ _

/-- In a spherical fusion category, a simple and its dual have the same
squared pivotal dimension. -/
theorem spherical_pivotalDimension_rightDual_sq (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical) (X : C.Obj) [Simple X] :
    pivotalDimension C p (Xᘁ) ^ 2 = pivotalDimension C p X ^ 2 := by
  let : Simple (Xᘁ) := simple_rightDual C X
  have h := target_squaredNorm_rightDual C X
  rw [target_squaredNorm_eq_dimension_sq C p hp (Xᘁ),
    target_squaredNorm_eq_dimension_sq C p hp X] at h
  simpa [pivotalDimension, rightTrace_id] using h

end PropertyF.Ground.Dimensions
