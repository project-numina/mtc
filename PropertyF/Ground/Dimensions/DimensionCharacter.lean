module
public import PropertyF.Ground.Dimensions.BiproductTrace
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Dimensions.CharacterBound
public import PropertyF.Ground.Dimensions.GroundNorm

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Complex pivotal dimension obtained using the canonical unit scalar map. -/
def pivotalDimension (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) : ℂ :=
  Ground.unitScalar C (p.rightTrace (𝟙 X))

/-- Pivotal dimension is a sum of simple dimensions with the actual Hom-space
multiplicities, for any pivotal structure. -/
theorem pivotalDimension_decomposition (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) :
    pivotalDimension C p X = ∑ i, (Module.finrank ℂ (Ground.simples C i ⟶ X) : ℂ) *
      pivotalDimension C p (Ground.simples C i) := by
  classical
  let m (i : Fin (Ground.rank C)) := Module.finrank ℂ (Ground.simples C i ⟶ X)
  let V : (Σ i, Fin (m i)) → C.Obj := fun a => Ground.simples C a.1
  obtain ⟨e⟩ := Ground.exists_canonical_decomposition C X
  have ht : p.rightTrace (𝟙 X) = ∑ i, (m i : ℂ) • p.rightTrace (𝟙 (Ground.simples C i)) := by
    calc
      _ = p.rightTrace (𝟙 (⨁ V)) := p.rightTrace_id_iso e
      _ = ∑ a, p.rightTrace (𝟙 (V a)) := rightDimension_biproduct V p
      _ = _ := by rw [Fintype.sum_sigma]; simp [V, Algebra.smul_def]
  unfold pivotalDimension
  simp only [← groundUnitScalarEquiv_apply, ht, map_sum, map_smul, smul_eq_mul]
  rfl

/-- The pivotal dimension of the tensor unit is normalized to one. -/
theorem pivotalDimension_unit (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) : pivotalDimension C p (𝟙_ C.Obj) = 1 := by
  unfold pivotalDimension
  rw [rightTrace_unit]
  simpa using Ground.unitScalar_algebraMap C 1

/-- The remaining categorical ingredient for pivotal dimensions to
form a fusion character is tensor multiplicativity. Additivity and the simple multiplicities are proved above. -/
theorem pivotalDimension_character (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj))
    (hmul : ∀ X Y, pivotalDimension C p (X ⊗ Y) =
      pivotalDimension C p X * pivotalDimension C p Y) :
    ∀ i j, pivotalDimension C p (Ground.simples C i) * pivotalDimension C p (Ground.simples C j) =
      ∑ k, (Ground.fusionCoeff C i j k : ℂ) * pivotalDimension C p (Ground.simples C k) := by
  intro i j
  rw [← hmul, pivotalDimension_decomposition]
  rfl

/-- Pivotal dimension is invariant under object isomorphism. -/
theorem pivotalDimension_iso (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) {X Y : C.Obj} (e : X ≅ Y) :
    pivotalDimension C p X = pivotalDimension C p Y := by
  unfold pivotalDimension
  rw [p.rightTrace_id_iso e]

/-- Once tensor multiplicativity is proved, every Galois conjugate of
each pivotal simple dimension is bounded by its FP dimension. -/
theorem galois_pivotalDimension_norm_le_fpSimple (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj))
    (hmul : ∀ X Y, pivotalDimension C p (X ⊗ Y) =
      pivotalDimension C p X * pivotalDimension C p Y)
    (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    ‖σ (pivotalDimension C p (Ground.simples C i))‖ ≤ Ground.fpSimple C i := by
  apply galois_character_norm_le_fpSimple C
    (fun j => pivotalDimension C p (Ground.simples C j)) (Ground.unitIndex C)
  · obtain ⟨e⟩ := Ground.unitIndex_iso C
    rw [pivotalDimension_iso C p e, pivotalDimension_unit]
    exact one_ne_zero
  · exact pivotalDimension_character C p hmul

end PropertyF.Ground.Dimensions
