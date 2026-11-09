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

/-- Objects are isomorphic exactly when their simple multiplicities agree. -/
theorem nonempty_iso_iff_simpleMultiplicity_eq (X Y : C.Obj) :
    Nonempty (X ≅ Y) ↔ ∀ i, simpleMultiplicity C i X = simpleMultiplicity C i Y := by
  constructor
  · rintro ⟨e⟩ i
    exact (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e).finrank_eq
  · intro h
    let V (m : Fin (rank C) → ℕ) := ⨁ (fun p : Σ k, Fin (m k) ↦ simples C p.1)
    have eX : X ≅ V (fun i ↦ simpleMultiplicity C i X) :=
      (exists_canonical_decomposition C X).some
    have eY : Y ≅ V (fun i ↦ simpleMultiplicity C i Y) :=
      (exists_canonical_decomposition C Y).some
    have hm : (fun i ↦ simpleMultiplicity C i X) = fun i ↦ simpleMultiplicity C i Y := funext h
    rw [hm] at eX
    exact ⟨eX ≪≫ eY.symm⟩


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
  obtain ⟨e⟩ := (nonempty_iso_iff_simpleMultiplicity_eq C W (simples C (unitIndex C))).2 hm
  exact ⟨(Iso.refl (simples C i) ⊗ᵢ rightDualLabelIso C i) ≪≫ e ≪≫ (unitIndex_iso C).some⟩

end MTC.PropertyF.Pivotal
