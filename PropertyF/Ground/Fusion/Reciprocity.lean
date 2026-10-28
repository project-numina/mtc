module
public import PropertyF.Ground.Fusion.Multiplicity

/-! Frobenius reciprocity for actual categorical Hom spaces. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Limits

namespace PropertyF.Ground
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Rigidity's Hom equivalence is complex-linear. -/
def tensorRightHomLinearEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (X ⊗ Y ⟶ Z) ≃ₗ[ℂ] (X ⟶ Z ⊗ Y') where
  toEquiv := tensorRightHomEquiv X Y Y' Z
  map_add' f g := by simp [tensorRightHomEquiv]
  map_smul' c f := by simp [tensorRightHomEquiv]

/-- Rigidity's left Hom equivalence is complex-linear. -/
def tensorLeftHomLinearEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (Y' ⊗ X ⟶ Z) ≃ₗ[ℂ] (X ⟶ Y ⊗ Z) where
  toEquiv := tensorLeftHomEquiv X Y Y' Z
  map_add' f g := by simp [tensorLeftHomEquiv]
  map_smul' c f := by simp [tensorLeftHomEquiv]

/-- Frobenius reciprocity for Hom dimensions. -/
theorem finrank_frobenius_reciprocity [RigidCategory C] (X Y Z : C) :
    Module.finrank ℂ (Z ⟶ X ⊗ Y) = Module.finrank ℂ (Z ⊗ (ᘁY) ⟶ X) :=
  (tensorRightHomLinearEquiv Z (ᘁY) Y X).finrank_eq.symm

/-- An object and its left dual have endomorphism spaces of the same
dimension, obtained using both rigidity adjunctions. -/
theorem finrank_end_leftDual [RigidCategory C] (X : C) :
    Module.finrank ℂ ((ᘁX) ⟶ (ᘁX)) = Module.finrank ℂ (X ⟶ X) :=
  calc
    _ = Module.finrank ℂ ((𝟙_ C) ⊗ (ᘁX) ⟶ (ᘁX)) :=
      (CategoryTheory.Linear.homCongr ℂ (λ_ (ᘁX)).symm (Iso.refl _)).finrank_eq
    _ = Module.finrank ℂ ((𝟙_ C) ⟶ (ᘁX) ⊗ X) :=
      (tensorRightHomLinearEquiv (𝟙_ C) (ᘁX) X (ᘁX)).finrank_eq
    _ = Module.finrank ℂ (X ⊗ (𝟙_ C) ⟶ X) :=
      (tensorLeftHomLinearEquiv (𝟙_ C) (ᘁX) X X).finrank_eq.symm
    _ = Module.finrank ℂ (X ⟶ X) :=
      (CategoryTheory.Linear.homCongr ℂ (ρ_ X) (Iso.refl _)).finrank_eq

variable (D : BraidedFusionCategory.{v,u})

/-- In a finite semisimple category an object with a one-dimensional
endomorphism space is simple. -/
theorem simple_of_finrank_end_eq_one {X : D.Obj}
    (hdim : Module.finrank ℂ (X ⟶ X) = 1) : Simple X := by
  classical
  let : ∀ A B : D.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  have hid : (𝟙 X : X ⟶ X) ≠ 0 := by
    obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hdim]; decide)
    exact fun h ↦ hf (((IsZero.iff_id_eq_zero X).mpr h).eq_of_src f 0)
  obtain ⟨i, s, t, _, hts⟩ := exists_simple_retract D hid
  let : Simple (simples D i) := simples_simple D i
  obtain ⟨z, hz⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℂ) (𝟙 X) hid).mp hdim (s ≫ t)
  have hz' : z • 𝟙 (simples D i) = 𝟙 (simples D i) := by
    simpa [Category.assoc, hts] using (congrArg (fun f => t ≫ f ≫ s) hz)
  have hz1 : z = 1 := by
    apply smul_left_injective ℂ (id_nonzero (simples D i))
    simpa using hz'
  have hst : s ≫ t = 𝟙 X := by simpa [hz1] using hz.symm
  exact Simple.of_iso ⟨s, t, hst, hts⟩

/-- Duals of simple objects remain simple. -/
theorem simple_leftDual (X : D.Obj) [Simple X] :
    Simple (ᘁX) :=
  letI : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  simple_of_finrank_end_eq_one D ((finrank_end_leftDual X).trans
    (CategoryTheory.finrank_endomorphism_simple_eq_one ℂ X))

/-- The right dual of a simple object in a braided fusion category is simple. -/
theorem simple_rightDual (X : D.Obj) [Simple X] :
    Simple (Xᘁ) :=
  letI : Simple (ᘁX) := simple_leftDual D X
  Simple.of_iso (leftDualIso HasLeftDual.exact (BraidedCategory.exactPairing_swap X (Xᘁ))).symm

/-- The label of the left dual of a simple representative. -/
def dualIndex (j : Fin (rank D)) : Fin (rank D) := by
  letI : Simple (simples D j) := simples_simple D j
  letI : Simple (ᘁ(simples D j)) := simple_leftDual D (simples D j)
  exact Classical.choose (exists_simple_iso D (ᘁ(simples D j)))

theorem dualIndex_iso (j : Fin (rank D)) :
    Nonempty ((ᘁ(simples D j)) ≅ simples D (dualIndex D j)) :=
  letI : Simple (simples D j) := simples_simple D j
  letI : Simple (ᘁ(simples D j)) := simple_leftDual D (simples D j)
  Classical.choose_spec (exists_simple_iso D (ᘁ(simples D j)))

/-- Fusion reciprocity with the dual kept as an actual object. -/
theorem fusionCoeff_reciprocity
    (i j k : Fin (rank D)) :
    fusionCoeff D i j k =
      Module.finrank ℂ (simples D i ⟶ simples D k ⊗ (ᘁ(simples D j))) :=
  calc
    _ = Module.finrank ℂ (simples D k ⊗ (ᘁ(simples D j)) ⟶ simples D i) :=
      finrank_frobenius_reciprocity (simples D i) (simples D j) (simples D k)
    _ = _ := finrank_to_simple_eq_from_simple D _ i

/-- The usual fusion-coefficient Frobenius reciprocity identity. -/
theorem fusionCoeff_reciprocity_labels
    (i j k : Fin (rank D)) :
    fusionCoeff D i j k = fusionCoeff D k (dualIndex D j) i :=
  (dualIndex_iso D j).elim fun e ↦
    (fusionCoeff_reciprocity D i j k).trans
      (CategoryTheory.Linear.homCongr ℂ (Iso.refl _)
        (Iso.refl (simples D k) ⊗ᵢ e)).finrank_eq

/-- Frobenius reciprocity and braiding exchange a tensor factor with its dual. -/
theorem fusionCoeff_dual_symmetry
    (i j k : Fin (rank D)) :
    fusionCoeff D i k j = fusionCoeff D (dualIndex D i) j k := by
  rw [fusionCoeff_comm D i k, fusionCoeff_reciprocity_labels D k i j,
    fusionCoeff_comm D j (dualIndex D i)]

/-- A simple object and its dual contain the tensor unit with multiplicity one. -/
theorem fusionCoeff_dual_unit (i : Fin (rank D)) :
    fusionCoeff D i (dualIndex D i) (unitIndex D) = 1 := by
  rw [fusionCoeff_comm D i (dualIndex D i), fusionCoeff_reciprocity_labels,
    fusionCoeff_unit]
  simp

/-- The label of the tensor unit is fixed by duality. -/
theorem dualIndex_unit :
    dualIndex D (unitIndex D) = unitIndex D := by
  simpa [fusionCoeff_unit, eq_comm] using
    (fusionCoeff_reciprocity_labels D (unitIndex D) (unitIndex D) (unitIndex D))

/-- Duality is involutive on simple labels. -/
theorem dualIndex_involutive :
    Function.Involutive (dualIndex D) := by
  intro i
  have hunit := fusionCoeff_dual_unit D i
  rw [fusionCoeff_reciprocity_labels, fusionCoeff_unit] at hunit
  simpa [eq_comm] using hunit

/-- Duality permutes the simple labels. -/
def dualEquiv : Equiv.Perm (Fin (rank D)) :=
  ⟨dualIndex D, dualIndex D, dualIndex_involutive D, dualIndex_involutive D⟩

end PropertyF.Ground

namespace PropertyF.Ground.Dimensions

/-- A simple object has nonzero right quantum trace for any double-dual isomorphism. -/
theorem rightQuantumTrace_simple_ne_zero (C : BraidedFusionCategory.{v,u})
    {X : C.Obj} [Simple X] (j : X ≅ (Xᘁ)ᘁ) :
    rightQuantumTrace j ≠ 0 := by
  let _ : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  let _ : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  let s : 𝟙_ C.Obj ⟶ X ⊗ (Xᘁ) := ExactPairing.coevaluation X (Xᘁ)
  let _ : Simple (Xᘁ) := simple_rightDual C X
  have hs : s ≠ 0 := (exactPairing_ne_zero X (Xᘁ) (id_nonzero (Xᘁ))).1
  obtain ⟨r₀, hr₀⟩ := split_from_simple s hs
  have hr₀ne : r₀ ≠ 0 := fun h ↦
    id_nonzero (𝟙_ C.Obj) (by simpa [h] using hr₀.symm)
  let t : X ⊗ (Xᘁ) ≅ ((Xᘁ)ᘁ) ⊗ (Xᘁ) := j ⊗ᵢ Iso.refl _
  let ev : ((Xᘁ)ᘁ) ⊗ (Xᘁ) ⟶ 𝟙_ C.Obj := ExactPairing.evaluation (Xᘁ) ((Xᘁ)ᘁ)
  have hev : ev ≠ 0 := by
    let _ : Simple ((Xᘁ)ᘁ) := Simple.of_iso j.symm
    exact (exactPairing_ne_zero (Xᘁ) ((Xᘁ)ᘁ) (id_nonzero ((Xᘁ)ᘁ))).2
  let r : X ⊗ (Xᘁ) ⟶ 𝟙_ C.Obj := t.hom ≫ ev
  have hr : r ≠ 0 := fun h ↦ hev ((cancel_epi t.hom).1 (by simpa [r] using h))
  have hfin : Module.finrank ℂ (X ⊗ (Xᘁ) ⟶ 𝟙_ C.Obj) = 1 :=
    ((tensorRightHomLinearEquiv X (Xᘁ) ((Xᘁ)ᘁ) (𝟙_ C.Obj)).trans
      ((CategoryTheory.Linear.homCongr ℂ (Iso.refl X) (λ_ ((Xᘁ)ᘁ))).trans
        (CategoryTheory.Linear.homCongr ℂ (Iso.refl X) j.symm))).finrank_eq.trans
          (CategoryTheory.finrank_endomorphism_simple_eq_one ℂ X)
  obtain ⟨z, hz⟩ := exists_smul_eq_of_finrank_eq_one hfin hr₀ne r
  have hz0 : z ≠ 0 := fun h ↦ hr (by simpa [h] using hz.symm)
  intro hzero
  have hhom : s ≫ r = 0 := by
    simpa [rightQuantumTrace, s, r, t, ev, tensorIso_hom] using (congrArg End.asHom hzero)
  exact (smul_ne_zero hz0 (id_nonzero _)) (by
    simpa only [← hz, Linear.comp_smul, hr₀] using hhom)


end PropertyF.Ground.Dimensions
