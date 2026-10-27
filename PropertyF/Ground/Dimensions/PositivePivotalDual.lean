module
public import PropertyF.Ground.Dimensions.RootDualPairing
public import PropertyF.Ground.Dimensions.PositiveSpherical

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
set_option backward.isDefEq.respectTransparency false in
/-- A spherical pivotal structure is dual-coherent on a simple when the
pivotal dimensions of the simple and its dual agree. -/
theorem spherical_pivotal_dual_simple_of_dimension (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical) (i : Fin (Ground.rank C))
    (hd : pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
      pivotalDimension C p (Ground.simples C i)) :
    p.iso ((Ground.simples C i)ᘁ) = (rightDualIsoMap (p.iso (Ground.simples C i))).symm := by
  let X := Ground.simples C i
  let : Simple X := Ground.simples_simple C i
  let : Simple (Xᘁ) := simple_rightDual C X
  let : FiniteDimensional ℂ ((Xᘁ) ⟶ (Xᘁ)) := Ground.IsFusionCategory.hom_finite _ _
  let j := (rightDualIsoMap (p.iso X)).symm
  let k := p.iso (Xᘁ)
  obtain ⟨c, _, hc, _⟩ := doubleDualIso_scalar j k
  have hdim : pivotalDimension C p (Xᘁ) = pivotalDimension C p X := by
    have ht := p.rightTrace_id_iso (rightDualLabelIso C i)
    change pivotalDimension C p (Xᘁ) = pivotalDimension C p X
    unfold pivotalDimension
    rw [ht]
    exact hd
  have ht : rightQuantumTrace k = c • rightQuantumTrace j := by
    apply End.homEquiv.injective
    simp [rightQuantumTrace, hc, tensorHom_def]
  have hq : rightQuantumTrace j = rightQuantumTrace (p.iso X) := by
    change rightQuantumTrace (rightDualIsoMap (p.iso X)).symm = _
    rw [← leftQuantumTrace_eq_rightDual, ← spherical_quantumTraces_eq p hp]
  have hcval : c = 1 := by
    have hv : c * pivotalDimension C p X = pivotalDimension C p X := by
      have ht' : p.rightTrace (𝟙 (Xᘁ)) = c • p.rightTrace (𝟙 X) := by
        rw [rightTrace_id, rightTrace_id, ← hq]
        exact ht
      have h := congrArg (groundUnitScalarEquiv C) ht'
      have h' : pivotalDimension C p (Xᘁ) = c * pivotalDimension C p X := by
        simpa [pivotalDimension, groundUnitScalarEquiv_apply] using h
      rw [hdim] at h'
      exact h'.symm
    have hn : pivotalDimension C p X ≠ 0 := pivotalDimension_simple_ne_zero C p i
    apply mul_right_cancel₀ hn
    simpa using hv
  apply Iso.ext
  change k.hom = j.hom
  simpa [hcval] using hc

/-- Positive spherical structures are dual-coherent on the simple labels. -/
theorem positive_spherical_pivotal_dual_simple (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) (i : Fin (Ground.rank C)) :
    p.iso ((Ground.simples C i)ᘁ) = (rightDualIsoMap (p.iso (Ground.simples C i))).symm :=
  spherical_pivotal_dual_simple_of_dimension C p hp i
    (spherical_dimension_dual_of_positive C p hp d hreal hpos i)
set_option backward.isDefEq.respectTransparency false in
/-- Dual coherence on simple representatives extends to all objects. -/
theorem pivotal_dual_of_simple_dual (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj))
    (hsimple : ∀ i, p.iso ((Ground.simples C i)ᘁ) =
      (rightDualIsoMap (p.iso (Ground.simples C i))).symm)
    (X : C.Obj) : p.iso (Xᘁ) = (rightDualIsoMap (p.iso X)).symm := by
  classical
  let V := simplePiecesObject C X
  let E := simpleDecomposition C X
  let inc (a : _) : V a ⟶ X := biproduct.ι V a ≫ E.inv
  let proj (a : _) : X ⟶ V a := E.hom ≫ biproduct.π V a
  have hsplit : ∑ a, proj a ≫ inc a = 𝟙 X := by
    change (∑ a, (E.hom ≫ biproduct.π V a) ≫ (biproduct.ι V a ≫ E.inv)) = 𝟙 X
    simp only [Category.assoc, ← Preadditive.comp_sum]
    simp only [← Category.assoc, ← Preadditive.sum_comp]
    rw [biproduct.total]
    rw [Category.comp_id, Iso.hom_inv_id]
  have hdual : (∑ a, (inc a)ᘁ ≫ (proj a)ᘁ) = 𝟙 (Xᘁ) := by
    have hm : (∑ a, proj a ≫ inc a)ᘁ = ∑ a, ((proj a ≫ inc a)ᘁ) := by
      simp [rightAdjointMate, sum_whiskerRight, whiskerLeft_sum,
        Preadditive.comp_sum, Preadditive.sum_comp]
    calc
      _ = (∑ a, proj a ≫ inc a)ᘁ := by
        simp only [hm, comp_rightAdjointMate]
      _ = _ := by rw [hsplit, rightAdjointMate_id]
  have hpiece (a : _) : ((proj a)ᘁ) ≫ (p.iso (Xᘁ)).hom =
      ((proj a)ᘁ) ≫ (rightDualIsoMap (p.iso X)).symm.hom := by
    have hnat := p.naturality ((proj a)ᘁ)
    have hnat' := dual_pivotal_naturality p (proj a)
    have he := congrArg Iso.hom (hsimple a.1)
    change (p.iso ((V a)ᘁ)).hom = (rightDualIsoMap (p.iso (V a))).symm.hom at he
    rw [hnat, hnat', he]
  apply Iso.ext
  calc
    _ = (∑ a, (inc a)ᘁ ≫ (proj a)ᘁ) ≫ (p.iso (Xᘁ)).hom := by rw [hdual, Category.id_comp]
    _ = ∑ a, (inc a)ᘁ ≫ ((proj a)ᘁ ≫ (p.iso (Xᘁ)).hom) := by simp [Preadditive.sum_comp, Category.assoc]
    _ = ∑ a, (inc a)ᘁ ≫ ((proj a)ᘁ ≫ (rightDualIsoMap (p.iso X)).symm.hom) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hpiece a]
    _ = _ := by simp [← Category.assoc, ← Preadditive.sum_comp, hdual]

/-- Positive spherical structures respect right duals on every object. -/
theorem positive_spherical_pivotal_dual (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) (X : C.Obj) :
    p.iso (Xᘁ) = (rightDualIsoMap (p.iso X)).symm :=
  pivotal_dual_of_simple_dual C p (positive_spherical_pivotal_dual_simple C p hp d hreal hpos) X

end PropertyF.Ground.Dimensions
