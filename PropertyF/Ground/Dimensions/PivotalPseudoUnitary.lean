module
public import PropertyF.Ground.Dimensions.DoubleDualPairing
public import PropertyF.Ground.Dimensions.RootDualPairing
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
public import PropertyF.Ground.Dimensions.PivotalTwist
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Dimensions.PositiveCanonical
public import PropertyF.Ground.Dimensions.ComplexSaturation

/-! # Pivotal structures and pseudo-unitarity

Duality and reality properties of pivotal dimensions lead to a positive spherical structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- Every pivotal structure preserves evaluation. -/
theorem pivotal_evaluation {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (p : PivotalStructure (C := C)) (X : C) :
    ((p.iso (Xᘁ)).hom ⊗ₘ (p.iso X).hom) ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) = ε_ X (Xᘁ) := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let W := (Xᘁ) ⊗ X
  let : HasRightDual W := RightRigidCategory.rightDual W
  have h := p.naturality (ε_ X (Xᘁ))
  change ε_ X (Xᘁ) ≫ (p.iso I).hom = (p.iso W).hom ≫ (((ε_ X (Xᘁ))ᘁ)ᘁ) at h
  rw [p.tensor, p.unit] at h
  have he := doubleDual_evaluation X
  calc
    _ = ((p.iso (Xᘁ)).hom ⊗ₘ (p.iso X).hom) ≫
      ((doubleDualTensorIso (Xᘁ) X).hom ≫ (((ε_ X (Xᘁ))ᘁ)ᘁ) ≫
        (doubleDualUnitIso (C := C)).inv) := by rw [he]
    _ = ε_ X (Xᘁ) := by
      rw [← Category.assoc, ← Category.assoc, ← h]
      simp
set_option backward.isDefEq.respectTransparency false in
/-- A pivotal component on a dual is the inverse dual of the original component. -/
theorem pivotal_dual {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (p : PivotalStructure (C := C)) (X : C) :
    p.iso (Xᘁ) = (rightDualIsoMap (p.iso X)).symm := by
  apply Iso.ext
  change (p.iso (Xᘁ)).hom = ((p.iso X).inv)ᘁ
  have h := pivotal_evaluation p X
  simp only [tensorHom_def, Category.assoc] at h
  rw [← (rightAdjointMate_comp_evaluation (p.iso X).hom)] at h
  rw [← comp_whiskerRight_assoc] at h
  have hk : (p.iso (Xᘁ)).hom ≫ ((p.iso X).hom)ᘁ = 𝟙 (Xᘁ) := by
    apply evaluation_ext (X := X)
    simpa only [id_whiskerRight, Category.id_comp] using h
  calc
    _ = (p.iso (Xᘁ)).hom ≫ (((p.iso X).hom)ᘁ ≫ ((p.iso X).inv)ᘁ) := by
      rw [← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id, Category.comp_id]
    _ = _ := by rw [← Category.assoc, hk, Category.id_comp]
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The left dimension is the right dimension of the dual object. -/
theorem pivotal_leftTrace_id_eq_rightTrace_dual {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RigidCategory C] (p : PivotalStructure (C := C)) (X : C) :
    p.leftTrace (𝟙 X) = p.rightTrace (𝟙 (Xᘁ)) :=
  by rw [leftTrace_id, rightTrace_id, pivotal_dual, leftQuantumTrace_eq_rightDual]

/-- A pivotal fusion category is spherical exactly when all simple dimensions are real. -/
theorem pivotal_spherical_iff_simple_dimensions_real
    (p : PivotalStructure (C := C.Obj)) :
    p.IsSpherical ↔ ∀ i, star (pivotalDimension C p (Ground.simples C i)) =
      pivotalDimension C p (Ground.simples C i) := by
  have hdual (i : Fin (Ground.rank C)) :
      Ground.unitScalar C (p.leftTrace (𝟙 (Ground.simples C i))) =
        star (pivotalDimension C p (Ground.simples C i)) := by
    rw [pivotal_leftTrace_id_eq_rightTrace_dual]
    change pivotalDimension C p ((Ground.simples C i)ᘁ) = _
    rw [pivotalDimension_iso C p (rightDualLabelIso C i), pivotalDimension_dual_eq_conj]
  rw [isSpherical_iff_simple_dimensions]
  constructor
  · intro h i
    rw [← hdual, h i]
    rfl
  · intro h i
    apply (Ground.unitScalarEquiv C).injective
    simpa only [← Ground.unitScalar_eq_equiv, pivotalDimension] using
      (hdual i).trans (h i)
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic norm is the product of the pivotal dimensions of a simple and its dual. -/
theorem squaredNorm_eq_pivotal_dimension_product
    (p : PivotalStructure (C := C.Obj)) (i : Fin (Ground.rank C)) :
    Ground.squaredNorm C (Ground.simples C i) = pivotalDimension C p (Ground.simples C i) *
      pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) := by
  let X := Ground.simples C i
  let : Simple X := Ground.simples_simple C i
  rw [target_squaredNorm_choice_independent C X (p.iso X), leftQuantumTrace_eq_rightDual]
  rw [← pivotal_dual p X, ← rightTrace_id, ← rightTrace_id]
  change pivotalDimension C p X * pivotalDimension C p (Xᘁ) = _
  rw [pivotalDimension_iso C p (rightDualLabelIso C i)]

/-- Each Galois-conjugate intrinsic norm is the squared norm of the corresponding conjugate pivotal dimension. -/
theorem galois_squaredNorm_eq_pivotalDimension_norm_sq
    (p : PivotalStructure (C := C.Obj)) (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    σ (Ground.squaredNorm C (Ground.simples C i)) =
      ((‖σ (pivotalDimension C p (Ground.simples C i))‖ ^ 2 : ℝ) : ℂ) := by
  rw [squaredNorm_eq_pivotal_dimension_product C p i, map_mul, galois_pivotalDimension_dual_eq_conj]
  simpa using Complex.mul_conj' (σ (pivotalDimension C p (Ground.simples C i)))

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- Pseudo-unitarity saturates every pivotal simple-dimension FP bound. -/
theorem pseudoUnitary_saturation_of_pivotal
    (p : PivotalStructure (C := C.Obj)) (hpu : Ground.PseudoUnitary C) :
    ∀ i, ‖pivotalDimension C p (Ground.simples C i)‖ = Ground.fpSimple C i := by
  let d : Fin (Ground.rank C) → ℝ := fun i => ‖pivotalDimension C p (Ground.simples C i)‖
  have hb : ∀ i, |d i| ≤ Ground.fpSimple C i := by
    intro i
    rw [abs_of_nonneg (norm_nonneg _)]
    exact galois_pivotalDimension_norm_le_fpSimple C p (RingEquiv.refl ℂ) i
  have hg : Ground.globalDimension C = ((∑ i, d i ^ 2 : ℝ) : ℂ) := by
    unfold Ground.globalDimension
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact galois_squaredNorm_eq_pivotalDimension_norm_sq C p (RingEquiv.refl ℂ) i
  have heq : ∑ i, d i ^ 2 = Ground.globalFPDimension C := by
    apply Complex.ofReal_injective
    rw [← hg]
    exact hpu
  intro i
  simpa [d, abs_of_nonneg (norm_nonneg _)] using ((global_sum_squares_eq_iff C d hb).mp heq) i

set_option backward.isDefEq.respectTransparency false in
/-- Twisting any pivotal structure by its saturated phases constructs the canonical positive spherical structure. -/
theorem positive_spherical_of_pivotal_pseudoUnitary
    (p : PivotalStructure (C := C.Obj)) (hpu : Ground.PseudoUnitary C) :
    ∃ q : PivotalStructure (C := C.Obj), q.IsSpherical ∧ ∀ i,
      pivotalDimension C q (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  let z : Fin (Ground.rank C) → ℂ := fun i => pivotalDimension C p (Ground.simples C i)
  let f := Ground.fpSimple C
  let q : Fin (Ground.rank C) → ℂ := fun i => z i / (f i : ℂ)
  let c : Fin (Ground.rank C) → ℂ := fun i => (q i)⁻¹
  have hf (i) : (f i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Ground.fpSimple_pos C i))
  have hz (i) : z i ≠ 0 := pivotalDimension_simple_ne_zero C p i
  have hq (i) : q i ≠ 0 := div_ne_zero (hz i) (hf i)
  have hc (i) : c i ≠ 0 := inv_ne_zero (hq i)
  have hunit : c (Ground.unitIndex C) = 1 := by
    obtain ⟨e⟩ := Ground.unitIndex_iso C
    dsimp [c, q, z, f]
    rw [pivotalDimension_iso C p e, pivotalDimension_unit, Ground.fpSimple_unit]
    norm_num
  have hsat : ∀ i, ‖z i‖ = f i := pseudoUnitary_saturation_of_pivotal C p hpu
  have hphase := fusion_complex_eigenvalue_saturation C
    (fun i j k => (Ground.fusionCoeff C i j k : ℂ)) z hsat
    (by intro i j k; simp)
    (by intro i j; simpa [z] using (pivotalDimension_character C p i j).symm)
  have hmul : ∀ i j k, Ground.fusionCoeff C i j k ≠ 0 → c k = c i * c j := by
    intro i j k hN
    have hn : (Ground.fusionCoeff C i j k : ℂ) ≠ 0 := by exact_mod_cast hN
    have h := hphase i j k
    change (Ground.fusionCoeff C i j k : ℂ) * q k / (q i * q j) = _ at h
    have hqmul : q k = q i * q j := by
      have h' : (Ground.fusionCoeff C i j k : ℂ) * q k =
          (Ground.fusionCoeff C i j k : ℂ) * (q i * q j) := by
        exact (div_eq_iff (mul_ne_zero (hq i) (hq j))).mp h
      exact mul_left_cancel₀ hn h'
    dsimp [c]
    rw [hqmul, mul_inv_rev]
    ring
  let P := pivotalScalarTwist C p c hc hunit hmul
  have hvalue (i) : pivotalDimension C P (Ground.simples C i) = (f i : ℂ) := by
    rw [pivotalDimension_scalarTwist_simple]
    change (q i)⁻¹ * z i = (f i : ℂ)
    dsimp [q]
    field_simp [hz i, hf i]
  refine ⟨P, ?_, hvalue⟩
  apply (pivotal_spherical_iff_simple_dimensions_real C P).2
  intro i
  rw [hvalue]
  simp
end PropertyF.Ground.Dimensions

end
