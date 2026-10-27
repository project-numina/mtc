module
public import PropertyF.Ground.CentreModular.VafaFPBalance

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u

/-- A natural automorphism acts on each simple Hom space by its scalar on the
simple source, including in the presence of repeated simple summands. -/
theorem simpleHomAction_natural_scalar (C : BraidedFusionCategory.{v,u})
    (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (t : Fin (rank C) → ℂˣ)
    (ht : ∀ i, (η.app (simples C i)).hom = (t i : ℂ) • 𝟙 (simples C i))
    (X : C.Obj) (i : Fin (rank C)) :
    (simpleHomAction C X i (η.app X)).toLinearMap = (t i : ℂ) • LinearMap.id := by
  ext f
  have hn := η.hom.naturality f
  change f ≫ (η.app X).hom = (η.app (simples C i)).hom ≫ f at hn
  rw [ht i] at hn
  simpa [simpleHomAction, CategoryTheory.Linear.homCongr_apply] using hn

/-- The actual FP determinant of a natural automorphism is the sum of its
simple scalar classes, weighted by FP dimensions and Hom multiplicities. -/
theorem fpDeterminant_natural (C : BraidedFusionCategory.{v,u})
    (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (t : Fin (rank C) → ℂˣ)
    (ht : ∀ i, (η.app (simples C i)).hom = (t i : ℂ) • 𝟙 (simples C i))
    (X : C.Obj) :
    fpDeterminant C X (η.app X) = ∑ i,
      (Module.finrank ℂ (simples C i ⟶ X) : ℝ) • (fpSimple C i • vafaUnitClass (t i)) := by
  unfold fpDeterminant
  apply Finset.sum_congr rfl
  intro i _
  have hd : (simpleHomAction C X i (η.app X)).det =
      (t i) ^ Module.finrank ℂ (simples C i ⟶ X) := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    change LinearMap.det _ = (t i : ℂ) ^ _
    rw [simpleHomAction_natural_scalar C η t ht X i, LinearMap.det_smul,
      LinearMap.det_id, mul_one]
  rw [hd, vafaUnitClass_pow, ← Nat.cast_smul_eq_nsmul ℝ]
  simp only [smul_smul, mul_comm]

/-- A natural automorphism whose actual FP determinant satisfies the
multiplicative balance on simple tensor products has finite-order simple
scalars. The displayed determinant identity remains an explicit premise. -/
theorem natural_scalars_finite_of_fpDeterminant_balance
    (C : BraidedFusionCategory.{v,u}) (η : 𝟭 C.Obj ≅ 𝟭 C.Obj)
    (t : Fin (rank C) → ℂˣ)
    (ht : ∀ i, (η.app (simples C i)).hom = (t i : ℂ) • 𝟙 (simples C i))
    (hdet : ∀ i j, fpDeterminant C (simples C i ⊗ simples C j)
      (η.app (simples C i ⊗ simples C j)) =
        fpDimension C (simples C i ⊗ simples C j) •
          (vafaUnitClass (t i) + vafaUnitClass (t j))) :
    ∀ i, IsOfFinOrder (t i) := by
  apply finite_order_of_fp_twist_balance C t
  intro i j
  have h := hdet i j
  rw [fpDeterminant_natural C η t ht, fpDimension_tensor, fpDimension_simple,
    fpDimension_simple] at h
  exact h

/-- The actual double braiding as an automorphism. -/
def monodromyIso (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) : X ⊗ Y ≅ X ⊗ Y :=
  (β_ X Y) ≪≫ (β_ Y X)

/-- Vanishing FP determinants of simple double braidings and an actual
balancing equation force finite order of every simple twist scalar. Both
categorical premises are explicit. -/
theorem natural_scalars_finite_of_monodromy_determinant
    (C : BraidedFusionCategory.{v,u}) (η : 𝟭 C.Obj ≅ 𝟭 C.Obj)
    (t : Fin (rank C) → ℂˣ)
    (ht : ∀ i, (η.app (simples C i)).hom = (t i : ℂ) • 𝟙 (simples C i))
    (hbalance : ∀ i j, η.app (simples C i ⊗ simples C j) =
      scalarIso C (simples C i ⊗ simples C j) (t i * t j) ≪≫
        monodromyIso C (simples C i) (simples C j))
    (hmon : ∀ i j, fpDeterminant C (simples C i ⊗ simples C j)
      (monodromyIso C (simples C i) (simples C j)) = 0) :
    ∀ i, IsOfFinOrder (t i) := by
  apply natural_scalars_finite_of_fpDeterminant_balance C η t ht
  intro i j
  rw [hbalance, fpDeterminant_trans, hmon, add_zero, fpDeterminant_scalar,
    vafaUnitClass_mul]

end PropertyF.Ground.CentreModular
