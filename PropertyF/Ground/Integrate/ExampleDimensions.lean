module
public import PropertyF.Ground.Integrate.Example
public import PropertyF.Ground.Integrate.FPRepresentatives
public import PropertyF.Ground.Integrate.Conjugacy
public import PropertyF.Ground.Dimensions.UnitNorm

/-! Dimensions of the finite-dimensional complex vector-space example. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Example

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Every vector space in the example is a finite direct sum of units. -/
theorem vector_decomposition (X : V) : ∃ (m : ℕ),
    Nonempty (X ≅ ⨁ (fun _ : Fin m => 𝟙_ V)) := by
  classical
  let n := Module.finrank ℂ X
  let f : Fin n → V := fun _ => 𝟙_ V
  let b := (Module.finBasis ℂ X).repr.trans (Finsupp.linearEquivFunOnFinite ℂ ℂ _)
  let v : F.obj X ≅ ModuleCat.of ℂ (Fin n → ℂ) := b.toModuleIso
  have h : F.obj (⨁ f) ≅ ModuleCat.of ℂ (Fin n → ℂ) :=
    F.mapBiproduct f ≪≫ ModuleCat.biproductIsoPi _
  exact ⟨n, ⟨F.preimageIso (v ≪≫ h.symm)⟩⟩

/-- The only simple isomorphism class in finite-dimensional vector spaces is
the tensor unit. -/
theorem simple_iso_unit (X : V) [Simple X] : Nonempty (X ≅ 𝟙_ V) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := vector_decomposition X
  let f : Fin n → V := fun _ => 𝟙_ V
  have he : e.hom ≠ 0 := by
    intro h
    apply id_nonzero X
    have hh := congrArg (fun t => t ≫ e.inv) h
    simpa using hh
  have hp : ∃ i, e.hom ≫ biproduct.π f i ≠ 0 := by
    by_contra h
    push Not at h
    apply he
    apply biproduct.hom_ext
    intro i
    simpa using h i
  obtain ⟨i, hi⟩ := hp
  let : Simple (𝟙_ V) := unitSimple
  let : IsIso (e.hom ≫ biproduct.π f i) := CategoryTheory.isIso_of_hom_simple hi
  exact ⟨asIso (e.hom ≫ biproduct.π f i)⟩

/-- The intrinsic global dimension of complex finite-dimensional vector spaces
is one. -/
theorem globalDimension_eq_one : globalDimension complexVectorSpaces = 1 := by
  let C := complexVectorSpaces
  let S : Fin 1 → C.Obj := fun _ => 𝟙_ C.Obj
  have hs : ∀ i, Simple (S i) := fun _ => unitSimple
  have hinj : ∀ i j, Nonempty (S i ≅ S j) → i = j := fun i j _ => Subsingleton.elim i j
  have hcover : ∀ X : C.Obj, Simple X → ∃ i, Nonempty (X ≅ S i) := by
    intro X hX
    exact ⟨0, @simple_iso_unit X hX⟩
  rw [Dimensions.target_globalDimension_independent_simples C S hs hinj hcover]
  simp [S, Dimensions.target_squaredNorm_unit]

/-- The spectral FP global dimension of the same example is one. -/
theorem globalFPDimension_eq_one : globalFPDimension complexVectorSpaces = 1 := by
  classical
  let C := complexVectorSpaces
  let S : Fin 1 → C.Obj := fun _ => 𝟙_ C.Obj
  have hs : ∀ i, Simple (S i) := fun _ => unitSimple
  have hinj : ∀ i j, Nonempty (S i ≅ S j) → i = j := fun i j _ => Subsingleton.elim i j
  have hcover : ∀ j, ∃ i, Nonempty (S i ≅ simples C j) := by
    intro j
    obtain ⟨e⟩ := @simple_iso_unit (simples C j) (simples_simple C j)
    exact ⟨0, ⟨e.symm⟩⟩
  have hmatrix (i : Fin 1) : presentationMatrix C S i = 1 := by
    ext k j
    let : Simple (𝟙_ V) := unitSimple
    let : FiniteDimensional ℂ ((𝟙_ V) ⟶ (𝟙_ V)) := by infer_instance
    have hdim : Module.finrank ℂ ((𝟙_ V) ⟶ (𝟙_ V) ⊗ (𝟙_ V)) = 1 := by
      rw [(CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (λ_ (𝟙_ V))).finrank_eq]
      exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ _
    simp [presentationMatrix, S, Matrix.one_apply, Subsingleton.elim k j]
    exact hdim
  have h := globalFPDimension_presentation C S hs hinj hcover
  simp [hmatrix, spectrum.spectralRadius_one] at h
  exact h.symm

/-- Finite-dimensional complex vector spaces are pseudo-unitary. -/
theorem pseudoUnitary : PseudoUnitary complexVectorSpaces := by
  unfold PseudoUnitary
  rw [globalDimension_eq_one, globalFPDimension_eq_one]
  norm_num

/-- The target's pseudo-unitary-conjugate hypothesis is inhabited by this
concrete category. -/
theorem hasPseudoUnitaryGaloisConjugate :
    Ground.HasPseudoUnitaryGaloisConjugate complexVectorSpaces :=
  Ground.hasPseudoUnitaryGaloisConjugate_of_pseudoUnitary complexVectorSpaces pseudoUnitary

end PropertyF.Ground.Example
