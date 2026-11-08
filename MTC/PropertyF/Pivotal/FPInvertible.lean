module
public import MTC.Fusion.ObjectDimension
public import MTC.CategoryTheory.Dimensions.DoubleDualPairing

/-! # Simple objects of FP dimension one -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits MTC.Fusion MTC.CategoryTheory.Dimensions
open scoped BigOperators
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- A simple label of FP dimension one tensored with its dual has only the
unit constituent, with multiplicity one. -/
theorem fusionCoeff_dual_of_fp_one (i k : Fin (rank C)) (hfp : fpSimple C i = 1) :
    fusionCoeff C i (dualIndex C i) k = if k = unitIndex C then 1 else 0 := by
  classical
  let u := unitIndex C
  let a : Fin (rank C) → ℝ := fun j ↦ (fusionCoeff C i (dualIndex C i) j : ℝ) * fpSimple C j
  have ha : ∀ j, 0 ≤ a j := fun j ↦ mul_nonneg (Nat.cast_nonneg _) (fpSimple_pos C j).le
  have hu : a u = 1 := by simp [a, u, fusionCoeff_dual_unit, fpSimple_unit]
  have hsum : ∑ j, a j = 1 := by
    have h := (fpSimple_mul C i (dualIndex C i)).symm
    simpa [a, fpSimple_dual, hfp] using h
  have herase : ∑ j ∈ Finset.univ.erase u, a j = 0 := by
    have h := Finset.add_sum_erase Finset.univ a (Finset.mem_univ u)
    rw [hsum, hu] at h
    linarith
  by_cases hk : k = u
  · subst k
    simp [u, fusionCoeff_dual_unit]
  · have hz : a k = 0 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ ha j)).mp herase k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
    have hz' : (fusionCoeff C i (dualIndex C i) k : ℝ) = 0 :=
      (mul_eq_zero.mp hz).resolve_right (ne_of_gt (fpSimple_pos C k))
    have hn : fusionCoeff C i (dualIndex C i) k = 0 := by exact_mod_cast hz'
    simp [hk, u, hn]

/-- A simple representative of FP dimension one is tensor-invertible: its
right dual is an actual inverse. -/
theorem simple_fp_one_tensor_rightDual_iso_unit (i : Fin (rank C))
    (hfp : fpSimple C i = 1) :
    Nonempty (simples C i ⊗ (simples C i)ᘁ ≅ 𝟙_ C.Obj) := by
  let W := simples C i ⊗ simples C (dualIndex C i)
  have hm (k : Fin (rank C)) : simpleMultiplicity C k W =
      simpleMultiplicity C k (simples C (unitIndex C)) := by
    simpa [W, simpleMultiplicity, fusionCoeff, finrank_simples_hom] using
      fusionCoeff_dual_of_fp_one C i k hfp
  let V (m : Fin (rank C) → ℕ) := ⨁ (fun p : Σ k, Fin (m k) ↦ simples C p.1)
  have hfun : (fun k ↦ simpleMultiplicity C k W) =
      (fun k ↦ simpleMultiplicity C k (simples C (unitIndex C))) := funext hm
  have eW : W ≅ V (fun k ↦ simpleMultiplicity C k W) :=
    (exists_canonical_decomposition C W).some
  have eU : simples C (unitIndex C) ≅
      V (fun k ↦ simpleMultiplicity C k (simples C (unitIndex C))) :=
    (exists_canonical_decomposition C (simples C (unitIndex C))).some
  rw [hfun] at eW
  have e : W ≅ 𝟙_ C.Obj := eW ≪≫ eU.symm ≪≫ (unitIndex_iso C).some
  exact ⟨(Iso.refl (simples C i) ⊗ᵢ rightDualLabelIso C i) ≪≫ e⟩

end MTC.PropertyF.Pivotal
