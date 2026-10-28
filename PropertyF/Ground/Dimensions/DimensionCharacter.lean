module
public import PropertyF.Ground.Dimensions.BiproductTrace
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Dimensions.TensorMultiplicativity
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Dimensions.GroundNorm

/-! # Pivotal dimension characters

Pivotal dimension is additive on decompositions and multiplicative on tensor products.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Complex pivotal dimension obtained using the canonical unit scalar map. -/
def pivotalDimension (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) : ℂ :=
  Ground.unitScalar C (p.rightTrace (𝟙 X))

/-- A spherical structure whose simple dimensions are the FP dimensions. -/
abbrev HasFPSphericalStructure (C : BraidedFusionCategory.{v,u}) : Prop :=
  ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
    pivotalDimension C p (simples C i) = (fpSimple C i : ℂ)

/-- Pivotal dimension is a sum of simple dimensions with the actual Hom-space
multiplicities, for any pivotal structure. -/
theorem pivotalDimension_decomposition
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) :
    pivotalDimension C p X = ∑ i, (Module.finrank ℂ (simples C i ⟶ X) : ℂ) *
      pivotalDimension C p (simples C i) := by
  classical
  let m (i : Fin (rank C)) := Module.finrank ℂ (simples C i ⟶ X)
  let V : (Σ i, Fin (m i)) → C.Obj := fun a => simples C a.1
  obtain ⟨e⟩ := Ground.exists_canonical_decomposition C X
  have ht : p.rightTrace (𝟙 X) = ∑ i, (m i : ℂ) • p.rightTrace (𝟙 (simples C i)) := by
    calc
      _ = p.rightTrace (𝟙 (⨁ V)) := p.rightTrace_id_iso e
      _ = ∑ a, p.rightTrace (𝟙 (V a)) := rightDimension_biproduct V p
      _ = _ := by rw [Fintype.sum_sigma]; simp [V, Algebra.smul_def]
  unfold pivotalDimension
  simp only [← groundUnitScalarEquiv_apply, ht, map_sum, map_smul, smul_eq_mul]
  rfl

/-- The pivotal dimension of the tensor unit is normalized to one. -/
theorem pivotalDimension_unit
    (p : PivotalStructure (C := C.Obj)) : pivotalDimension C p (𝟙_ C.Obj) = 1 := by
  unfold pivotalDimension
  rw [rightTrace_unit]
  simpa using Ground.unitScalar_algebraMap C 1

/-- Pivotal dimensions multiply under tensor products. -/
theorem pivotalDimension_tensor
    (p : PivotalStructure (C := C.Obj)) (X Y : C.Obj) :
    pivotalDimension C p (X ⊗ Y) = pivotalDimension C p X * pivotalDimension C p Y := by
  simpa [pivotalDimension, ← groundUnitScalarEquiv_apply] using
    pivotalTrace_tensor p (groundUnitScalarEquiv C) (𝟙 X) (𝟙 Y)

/-- Pivotal simple dimensions form a fusion character. -/
theorem pivotalDimension_character
    (p : PivotalStructure (C := C.Obj)) :
    ∀ i j, pivotalDimension C p (simples C i) * pivotalDimension C p (simples C j) =
      ∑ k, (Ground.fusionCoeff C i j k : ℂ) * pivotalDimension C p (simples C k) := by
  intro i j
  rw [← pivotalDimension_tensor, pivotalDimension_decomposition]
  rfl

/-- Pivotal dimension is invariant under object isomorphism. -/
theorem pivotalDimension_iso
    (p : PivotalStructure (C := C.Obj)) {X Y : C.Obj} (e : X ≅ Y) :
    pivotalDimension C p X = pivotalDimension C p Y := by
  unfold pivotalDimension
  rw [p.rightTrace_id_iso e]

/-- Every Galois conjugate of each pivotal simple dimension is bounded by
its Frobenius–Perron dimension. -/
theorem galois_pivotalDimension_norm_le_fpSimple (C : BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj))
    (σ : ℂ ≃+* ℂ) (i : Fin (rank C)) :
    ‖σ (pivotalDimension C p (simples C i))‖ ≤ fpSimple C i := by
  apply galois_character_norm_le_fpSimple C
    (fun j => pivotalDimension C p (simples C j)) (unitIndex C)
  · obtain ⟨e⟩ := Ground.unitIndex_iso C
    rw [pivotalDimension_iso C p e, pivotalDimension_unit]
    exact one_ne_zero
  · exact pivotalDimension_character C p

end PropertyF.Ground.Dimensions
