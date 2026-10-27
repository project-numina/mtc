module
public import PropertyF.Ground.Fusion.Reciprocity
public import PropertyF.Ground.Cabling.Strands

/-! The symmetric total fusion matrix. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace PropertyF.Ground
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Sum of all simple fusion matrices, over the real numbers. -/
def totalFusionMatrix (D : BraidedFusionCategory) :
    Matrix (Fin (rank D)) (Fin (rank D)) ℝ :=
  fun j k => ∑ i, (fusionCoeff D i k j : ℝ)

/-- Duality and Frobenius reciprocity make the total fusion matrix symmetric. -/
theorem totalFusionMatrix_symmetric (D : BraidedFusionCategory) (j k : Fin (rank D)) :
    totalFusionMatrix D j k = totalFusionMatrix D k j := by
  classical
  unfold totalFusionMatrix
  calc
    _ = ∑ i, (fusionCoeff D (dualIndex D i) j k : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [fusionCoeff_comm D i k, fusionCoeff_reciprocity_labels,
        fusionCoeff_comm D j (dualIndex D i)]
    _ = _ := by
      have h := Equiv.sum_comp (dualEquiv D) (fun i => (fusionCoeff D i j k : ℝ))
      change (∑ i, (fusionCoeff D (dualIndex D i) j k : ℝ)) = _ at h
      exact h

/-- The total fusion matrix is strictly positive in every entry. -/
theorem totalFusionMatrix_pos (D : BraidedFusionCategory) (j k : Fin (rank D)) :
    0 < totalFusionMatrix D j k := by
  classical
  letI : Simple (simples D j) := simples_simple D j
  letI : Simple (simples D k) := simples_simple D k
  letI : Simple (ᘁ(simples D k)) := simple_leftDual D (simples D k)
  obtain ⟨s, r, hsr⟩ := unit_retract_leftDual_tensor (simples D j)
  letI : (tensorLeft (simples D j)).Faithful :=
    PropertyF.tensorLeft_faithful_of_unit_retract _ _ s r hsr
  let Y : D.Obj := simples D j ⊗ (ᘁ(simples D k))
  have hid : (𝟙 Y : Y ⟶ Y) ≠ 0 := by
    intro h
    have hh : (tensorLeft (simples D j)).map (𝟙 (ᘁ(simples D k))) =
        (tensorLeft (simples D j)).map 0 := by simpa [Y] using h
    exact id_nonzero (ᘁ(simples D k)) ((tensorLeft (simples D j)).map_injective hh)
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D Y
  let V : (Σ i, Fin (m i)) → D.Obj := fun p => simples D p.1
  have he : e.hom ≠ 0 := by
    intro h
    apply hid
    have hh := congrArg (fun t => t ≫ e.inv) h
    simpa using hh
  have hp : ∃ p, e.hom ≫ biproduct.π V p ≠ 0 := by
    by_contra h
    push Not at h
    apply he
    apply biproduct.hom_ext
    intro p
    simpa using h p
  obtain ⟨p, hp⟩ := hp
  letI : ∀ A B : D.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  have hm : 0 < Module.finrank ℂ (simples D p.1 ⟶ Y) := by
    rw [← finrank_to_simple_eq_from_simple D Y p.1]
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hp⟩
  have hc : 0 < fusionCoeff D p.1 k j := by
    rw [fusionCoeff_reciprocity_labels]
    obtain ⟨e'⟩ := dualIndex_iso D k
    change 0 < Module.finrank ℂ (simples D p.1 ⟶ simples D j ⊗ simples D (dualIndex D k))
    rw [(CategoryTheory.Linear.homCongr ℂ (Iso.refl _)
      (Iso.refl (simples D j) ⊗ᵢ e'.symm)).finrank_eq]
    exact hm
  unfold totalFusionMatrix
  exact Finset.sum_pos' (fun _ _ => Nat.cast_nonneg _)
    ⟨p.1, Finset.mem_univ _, Nat.cast_pos.mpr hc⟩

end PropertyF.Ground
