module
public import PropertyF.Ground.Fusion.Multiplicity

/-! Frobenius reciprocity for actual categorical Hom spaces. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Limits

namespace PropertyF.Ground
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
section
variable {k : Type*} [CommSemiring k] {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]

/-- Rigidity's Hom equivalence is linear. -/
def tensorRightHomLinearEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (X ⊗ Y ⟶ Z) ≃ₗ[k] (X ⟶ Z ⊗ Y') where
  toEquiv := tensorRightHomEquiv X Y Y' Z
  map_add' f g := by simp [tensorRightHomEquiv]
  map_smul' c f := by simp [tensorRightHomEquiv]

/-- Rigidity's left Hom equivalence is linear. -/
def tensorLeftHomLinearEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (Y' ⊗ X ⟶ Z) ≃ₗ[k] (X ⟶ Y ⊗ Z) where
  toEquiv := tensorLeftHomEquiv X Y Y' Z
  map_add' f g := by simp [tensorLeftHomEquiv]
  map_smul' c f := by simp [tensorLeftHomEquiv]

end

section
variable {k : Type*} [Field k] {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]

/-- Frobenius reciprocity for Hom dimensions. -/
theorem finrank_frobenius_reciprocity (X Y Z : C) [HasLeftDual Y] :
    Module.finrank k (Z ⟶ X ⊗ Y) = Module.finrank k (Z ⊗ (ᘁY) ⟶ X) :=
  (tensorRightHomLinearEquiv (k := k) Z (ᘁY) Y X).finrank_eq.symm

/-- An object and its left dual have endomorphism spaces of the same
dimension, obtained using both rigidity adjunctions. -/
theorem finrank_end_leftDual (X : C) [HasLeftDual X] :
    Module.finrank k ((ᘁX) ⟶ (ᘁX)) = Module.finrank k (X ⟶ X) :=
  (CategoryTheory.Linear.homCongr k (λ_ (ᘁX)).symm (Iso.refl _)).trans
    (tensorRightHomLinearEquiv (k := k) (𝟙_ C) (ᘁX) X (ᘁX)) |>.trans
    (tensorLeftHomLinearEquiv (k := k) (𝟙_ C) (ᘁX) X X).symm |>.trans
    (CategoryTheory.Linear.homCongr k (ρ_ X) (Iso.refl _)) |>.finrank_eq

end

section
variable {E : Type u} [Category.{v} E] [MonoidalCategory E] [BraidedCategory E]
  [Abelian E] [Linear ℂ E] [RigidCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [IsFusionCategory E]

/-- In a finite semisimple category an object with a one-dimensional
endomorphism space is simple. -/
theorem simple_of_finrank_end_eq_one {X : E}
    (hdim : Module.finrank ℂ (X ⟶ X) = 1) : Simple X := by
  classical
  let D : BraidedFusionCategory.{v,u} := { Obj := E }
  let : ∀ A B : E, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  have hid : (𝟙 X : X ⟶ X) ≠ 0 := by
    obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hdim]; decide)
    exact fun h ↦ hf (((IsZero.iff_id_eq_zero X).mpr h).eq_of_src f 0)
  obtain ⟨i, s, t, _, hts⟩ := exists_retract_of_biproduct_decomposition
    (simples D) (simples_decompose D X) hid
  let : Simple (simples D i) := simples_simple D i
  obtain ⟨z, hz⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℂ) (𝟙 X) hid).mp hdim (s ≫ t)
  have hz1 : z = 1 := smul_left_injective ℂ (id_nonzero (simples D i)) (by
    simpa [Category.assoc, hts] using congrArg (fun f => t ≫ f ≫ s) hz)
  exact Simple.of_iso ⟨s, t, by simpa [hz1] using hz.symm, hts⟩

/-- Duals of simple objects remain simple. -/
theorem simple_leftDual (X : E) [Simple X] :
    Simple (ᘁX) :=
  letI : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  simple_of_finrank_end_eq_one ((finrank_end_leftDual (k := ℂ) X).trans
    (CategoryTheory.finrank_endomorphism_simple_eq_one ℂ X))

/-- The right dual of a simple object in a braided fusion category is simple. -/
theorem simple_rightDual (X : E) [Simple X] :
    Simple (Xᘁ) :=
  letI : Simple (ᘁX) := simple_leftDual X
  Simple.of_iso (leftDualIso HasLeftDual.exact (BraidedCategory.exactPairing_swap X (Xᘁ))).symm

end

variable (D : BraidedFusionCategory.{v,u})
local instance (i : Fin (rank D)) : Simple (simples D i) := simples_simple D i

/-- The label of the left dual of a simple representative. -/
def dualIndex (j : Fin (rank D)) : Fin (rank D) := by
  letI : Simple (ᘁ(simples D j)) := simple_leftDual (simples D j)
  exact Classical.choose (exists_simple_iso D (ᘁ(simples D j)))

variable {D} in
theorem dualIndex_iso (j : Fin (rank D)) :
    Nonempty ((ᘁ(simples D j)) ≅ simples D (dualIndex D j)) :=
  letI : Simple (ᘁ(simples D j)) := simple_leftDual (simples D j)
  Classical.choose_spec (exists_simple_iso D (ᘁ(simples D j)))

variable {D} in
/-- Fusion reciprocity with the dual kept as an actual object. -/
theorem fusionCoeff_reciprocity (i j k : Fin (rank D)) :
    fusionCoeff D i j k =
      simpleMultiplicity D i (simples D k ⊗ (ᘁ(simples D j))) :=
  (finrank_frobenius_reciprocity (k := ℂ) (simples D i) (simples D j) (simples D k)).trans
    (finrank_to_simple_eq_from_simple _ (simples D i))

variable {D} in
/-- The usual fusion-coefficient Frobenius reciprocity identity. -/
theorem fusionCoeff_reciprocity_labels (i j k : Fin (rank D)) :
    fusionCoeff D i j k = fusionCoeff D k (dualIndex D j) i :=
  (dualIndex_iso j).elim fun e ↦
    (fusionCoeff_reciprocity i j k).trans
      (CategoryTheory.Linear.homCongr ℂ (Iso.refl _)
        (Iso.refl (simples D k) ⊗ᵢ e)).finrank_eq

/-- Frobenius reciprocity and braiding exchange a tensor factor with its dual. -/
theorem fusionCoeff_dual_symmetry (i j k : Fin (rank D)) :
    fusionCoeff D i k j = fusionCoeff D (dualIndex D i) j k :=
  (fusionCoeff_comm D i k j).trans
    ((fusionCoeff_reciprocity_labels k i j).trans (fusionCoeff_comm D j (dualIndex D i) k))

variable {D} in
/-- A simple object and its dual contain the tensor unit with multiplicity one. -/
theorem fusionCoeff_dual_unit (i : Fin (rank D)) :
    fusionCoeff D i (dualIndex D i) (unitIndex D) = 1 := by
  rw [fusionCoeff_comm D i (dualIndex D i), fusionCoeff_reciprocity_labels,
    fusionCoeff_unit, ite_eq_left rfl]

/-- The label of the tensor unit is fixed by duality. -/
theorem dualIndex_unit :
    dualIndex D (unitIndex D) = unitIndex D := by
  simpa [fusionCoeff_unit, eq_comm] using
    (fusionCoeff_reciprocity_labels (unitIndex D) (unitIndex D) (unitIndex D))

/-- Duality is involutive on simple labels. -/
theorem dualIndex_involutive :
    Function.Involutive (dualIndex D) :=
  fun i ↦ by simpa [fusionCoeff_unit, eq_comm] using
    ((fusionCoeff_reciprocity_labels i (dualIndex D i) (unitIndex D)).symm.trans
      (fusionCoeff_dual_unit i))

/-- Duality permutes the simple labels. -/
def dualEquiv : Equiv.Perm (Fin (rank D)) :=
  ⟨dualIndex D, dualIndex D, dualIndex_involutive D, dualIndex_involutive D⟩

end PropertyF.Ground

namespace PropertyF.Ground.Dimensions

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [RigidCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [IsFusionCategory C]

/-- A simple object has nonzero right quantum trace for any double-dual isomorphism. -/
theorem rightQuantumTrace_simple_ne_zero
    {X : C} [Simple X] (j : X ≅ (Xᘁ)ᘁ) :
    rightQuantumTrace j ≠ 0 := by
  let _ : Simple (𝟙_ C) := IsFusionCategory.unit_simple
  let _ : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  let s : 𝟙_ C ⟶ X ⊗ (Xᘁ) := ExactPairing.coevaluation X (Xᘁ)
  let _ : Simple (Xᘁ) := simple_rightDual X
  obtain ⟨r₀, hr₀⟩ := split_from_simple s
    ((exactPairing_ne_zero X (id_nonzero (Xᘁ))).1)
  have hr₀ne : r₀ ≠ 0 := fun h ↦
    id_nonzero (𝟙_ C) (by simpa [h] using hr₀.symm)
  let t : X ⊗ (Xᘁ) ≅ ((Xᘁ)ᘁ) ⊗ (Xᘁ) := j ⊗ᵢ Iso.refl _
  let ev : ((Xᘁ)ᘁ) ⊗ (Xᘁ) ⟶ 𝟙_ C := ExactPairing.evaluation (Xᘁ) ((Xᘁ)ᘁ)
  have hev : ev ≠ 0 := by
    let _ : Simple ((Xᘁ)ᘁ) := Simple.of_iso j.symm
    exact (exactPairing_ne_zero (Xᘁ) (id_nonzero ((Xᘁ)ᘁ))).2
  let r : X ⊗ (Xᘁ) ⟶ 𝟙_ C := t.hom ≫ ev
  have hr : r ≠ 0 := fun h ↦ hev ((cancel_epi t.hom).1 (by simpa [r] using h))
  have hfin : Module.finrank ℂ (X ⊗ (Xᘁ) ⟶ 𝟙_ C) = 1 :=
    ((tensorRightHomLinearEquiv (k := ℂ) X (Xᘁ) ((Xᘁ)ᘁ) (𝟙_ C)).trans
      ((CategoryTheory.Linear.homCongr ℂ (Iso.refl X) (λ_ ((Xᘁ)ᘁ))).trans
        (CategoryTheory.Linear.homCongr ℂ (Iso.refl X) j.symm))).finrank_eq.trans
          (CategoryTheory.finrank_endomorphism_simple_eq_one ℂ X)
  obtain ⟨z, hz⟩ := exists_smul_eq_of_finrank_eq_one hfin hr₀ne r
  intro hzero
  apply (smul_ne_zero (fun h : z = 0 ↦ hr (by simpa [h] using hz.symm)) (id_nonzero (𝟙_ C)))
  simpa only [← hz, Linear.comp_smul, hr₀] using
    (show s ≫ r = 0 from by
      simpa [rightQuantumTrace, s, r, t, ev, tensorIso_hom] using congrArg End.asHom hzero)


end PropertyF.Ground.Dimensions
