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
    Module.finrank ℂ ((ᘁX) ⟶ (ᘁX)) = Module.finrank ℂ (X ⟶ X) := by
  calc
    _ = Module.finrank ℂ ((𝟙_ C) ⊗ (ᘁX) ⟶ (ᘁX)) :=
      (CategoryTheory.Linear.homCongr ℂ (λ_ (ᘁX)).symm (Iso.refl _)).finrank_eq
    _ = Module.finrank ℂ ((𝟙_ C) ⟶ (ᘁX) ⊗ X) :=
      (tensorRightHomLinearEquiv (𝟙_ C) (ᘁX) X (ᘁX)).finrank_eq
    _ = Module.finrank ℂ (X ⊗ (𝟙_ C) ⟶ X) :=
      (tensorLeftHomLinearEquiv (𝟙_ C) (ᘁX) X X).finrank_eq.symm
    _ = Module.finrank ℂ (X ⟶ X) :=
      (CategoryTheory.Linear.homCongr ℂ (ρ_ X) (Iso.refl _)).finrank_eq

/-- In a finite semisimple category an object with a one-dimensional
endomorphism space is simple. -/
theorem simple_of_finrank_end_eq_one (D : BraidedFusionCategory.{v,u}) (X : D.Obj)
    (hdim : Module.finrank ℂ (X ⟶ X) = 1) : Simple X := by
  classical
  letI : ∀ A B : D.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  have hid : (𝟙 X : X ⟶ X) ≠ 0 := by
    obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hdim]; decide)
    intro h
    apply hf
    calc
      f = 𝟙 X ≫ f := (Category.id_comp f).symm
      _ = 0 := by rw [h]; simp
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D X
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
  obtain ⟨p, _⟩ := hp
  letI : Simple (V p) := simples_simple D p.1
  let s : X ⟶ V p := e.hom ≫ biproduct.π V p
  let t : V p ⟶ X := biproduct.ι V p ≫ e.inv
  have hts : t ≫ s = 𝟙 (V p) := by simp [s, t, Category.assoc]
  obtain ⟨z, hz⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℂ) (𝟙 X) hid).mp hdim (s ≫ t)
  have hz' : z • 𝟙 (V p) = 𝟙 (V p) := by
    have h := congrArg (fun f => t ≫ f ≫ s) hz
    simpa [Category.assoc, hts] using h
  have hz1 : z = 1 := by
    apply smul_left_injective ℂ (id_nonzero (V p))
    simpa using hz'
  have hst : s ≫ t = 𝟙 X := by simpa [hz1] using hz.symm
  exact Simple.of_iso ⟨s, t, hst, hts⟩

/-- Duals of simple objects remain simple. -/
theorem simple_leftDual (D : BraidedFusionCategory.{v,u}) (X : D.Obj) [Simple X] :
    Simple (ᘁX) := by
  apply simple_of_finrank_end_eq_one D
  rw [finrank_end_leftDual]
  letI : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ X

/-- The label of the left dual of a simple representative. -/
def dualIndex (D : BraidedFusionCategory.{v,u}) (j : Fin (rank D)) : Fin (rank D) := by
  letI : Simple (simples D j) := simples_simple D j
  letI : Simple (ᘁ(simples D j)) := simple_leftDual D (simples D j)
  exact Classical.choose (exists_simple_iso D (ᘁ(simples D j)))

theorem dualIndex_iso (D : BraidedFusionCategory.{v,u}) (j : Fin (rank D)) :
    Nonempty ((ᘁ(simples D j)) ≅ simples D (dualIndex D j)) := by
  letI : Simple (simples D j) := simples_simple D j
  letI : Simple (ᘁ(simples D j)) := simple_leftDual D (simples D j)
  exact Classical.choose_spec (exists_simple_iso D (ᘁ(simples D j)))

/-- Fusion reciprocity with the dual kept as an actual object. -/
theorem fusionCoeff_reciprocity (D : BraidedFusionCategory.{v,u})
    (i j k : Fin (rank D)) :
    fusionCoeff D i j k =
      Module.finrank ℂ (simples D i ⟶ simples D k ⊗ (ᘁ(simples D j))) := by
  calc
    _ = Module.finrank ℂ (simples D k ⊗ (ᘁ(simples D j)) ⟶ simples D i) :=
      finrank_frobenius_reciprocity (simples D i) (simples D j) (simples D k)
    _ = _ := finrank_to_simple_eq_from_simple D _ i

/-- The usual fusion-coefficient Frobenius reciprocity identity. -/
theorem fusionCoeff_reciprocity_labels (D : BraidedFusionCategory.{v,u})
    (i j k : Fin (rank D)) :
    fusionCoeff D i j k = fusionCoeff D k (dualIndex D j) i := by
  obtain ⟨e⟩ := dualIndex_iso D j
  rw [fusionCoeff_reciprocity]
  exact (CategoryTheory.Linear.homCongr ℂ (Iso.refl _)
    (Iso.refl (simples D k) ⊗ᵢ e)).finrank_eq

/-- Duality is involutive on simple labels. -/
theorem dualIndex_involutive (D : BraidedFusionCategory.{v,u}) :
    Function.Involutive (dualIndex D) := by
  intro i
  have hunit : fusionCoeff D i (dualIndex D i) (unitIndex D) = 1 := by
    rw [fusionCoeff_comm D i (dualIndex D i), fusionCoeff_reciprocity_labels,
      fusionCoeff_unit]
    simp
  have hdual : fusionCoeff D i (dualIndex D i) (unitIndex D) =
      if i = dualIndex D (dualIndex D i) then 1 else 0 := by
    rw [fusionCoeff_reciprocity_labels, fusionCoeff_unit]
  by_contra h
  have h' : i ≠ dualIndex D (dualIndex D i) := Ne.symm h
  simp [h'] at hdual
  omega

/-- Duality permutes the simple labels. -/
def dualEquiv (D : BraidedFusionCategory.{v,u}) : Equiv.Perm (Fin (rank D)) :=
  ⟨dualIndex D, dualIndex D, dualIndex_involutive D, dualIndex_involutive D⟩

end PropertyF.Ground
