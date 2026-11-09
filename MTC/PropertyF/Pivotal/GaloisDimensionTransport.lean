module
public import MTC.PropertyF.Pivotal.MonoidalQuantumTrace
public import MTC.PropertyF.Pivotal.GaloisUnitScalar
public import MTC.PropertyF.Pivotal.SScalarTwist

/-! # Intrinsic global dimension under semilinear braided equivalence -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.Monoidal CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Functor.OplaxMonoidal
open MTC.Fusion MTC.CategoryTheory.Dimensions MTC.Braided
open scoped BigOperators
namespace MTC.PropertyF.Pivotal
universe v u
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
variable {C D : BraidedFusionCategory.{v,u}} {σ : ℂ ≃+* ℂ}

/-- Both actual quantum-trace scalars transform semilinearly under the
functor's canonical double-dual comparison. -/
theorem quantumTrace_scalars_galois (h : GaloisConjugate C D σ)
    {X : C.Obj} (j : X ≅ (Xᘁ)ᘁ) :
    letI := h.monoidal
    let J := transformedDoubleDual h.equivalence.functor j
    unitScalar D (rightQuantumTrace J) = σ (unitScalar C (rightQuantumTrace j)) ∧
      unitScalar D (leftQuantumTrace J) = σ (unitScalar C (leftQuantumTrace j)) := by
  let F := h.equivalence.functor
  letI := h.monoidal
  let J := transformedDoubleDual F j
  have hr := unitScalar_galois_transport h (rightQuantumTrace j)
  have hl := unitScalar_galois_transport h (leftQuantumTrace j)
  change unitScalar D (End.of (ε F ≫ F.map (rightQuantumTrace j).asHom ≫ η F)) = _ at hr
  change unitScalar D (End.of (ε F ≫ F.map (leftQuantumTrace j).asHom ≫ η F)) = _ at hl
  rw [show End.of (ε F ≫ F.map (rightQuantumTrace j).asHom ≫ η F) = rightQuantumTrace J from
    End.ext (monoidalFunctor_rightQuantumTrace F j)] at hr
  rw [show End.of (ε F ≫ F.map (leftQuantumTrace j).asHom ≫ η F) = leftQuantumTrace J from
    End.ext (monoidalFunctor_leftQuantumTrace F j)] at hl
  exact ⟨hr, hl⟩

/-- Intrinsic squared norms of actual simple objects transform by the field
automorphism, independently of the chosen double-dual isomorphisms. -/
theorem squaredNorm_galois (h : GaloisConjugate C D σ)
    (X : C.Obj) [Simple X] :
    squaredNorm D (h.equivalence.functor.obj X) = σ (squaredNorm C X) := by
  let F := h.equivalence.functor
  letI := h.monoidal
  letI : Simple (F.obj X) := simple_obj F X
  let j := doubleDualIso C X
  let J := transformedDoubleDual F j
  rw [target_squaredNorm_choice_independent J, target_squaredNorm_choice_independent j]
  obtain ⟨hr, hl⟩ := quantumTrace_scalars_galois h j
  change unitScalar D (rightQuantumTrace J) = _ at hr
  change unitScalar D (leftQuantumTrace J) = _ at hl
  rw [hr, hl, map_mul]

/-- Actual intrinsic global dimension is carried through an arbitrary
semilinear braided equivalence by the specified automorphism of ℂ. -/
theorem globalDimension_galois (h : GaloisConjugate C D σ) :
    globalDimension D = σ (globalDimension C) := by
  obtain ⟨e, he⟩ := MTC.Modular.simpleLabels_equiv C D h.equivalence
  rw [globalDimension, globalDimension, map_sum]
  symm
  apply Fintype.sum_equiv e
  intro i
  letI : Simple (simples C i) := simples_simple C i
  rw [← squaredNorm_galois h (simples C i)]
  exact target_squaredNorm_iso D (he i).some

/-- Pseudo-unitarity of the canonical scalar twist implies pseudo-unitarity
of every semilinearly equivalent presentation of that conjugate. -/
theorem pseudoUnitary_of_scalarTwist_of_galois (h : GaloisConjugate C D σ)
    (hσ : PseudoUnitary (MTC.PropertyF.Reduction.ScalarTwist.category C σ)) : PseudoUnitary D := by
  change globalDimension D = (globalFPDimension D : ℂ)
  rw [globalDimension_galois h, ← globalDimension_scalarTwist C σ]
  change globalDimension (MTC.PropertyF.Reduction.ScalarTwist.category C σ) = _ at hσ
  rw [hσ, ← MTC.Modular.conjugate_globalFPDimension h,
    MTC.Modular.conjugate_globalFPDimension (scalarTwistGaloisConjugate C σ)]

/-- In the actual S-invertible pivotal case, property F makes every
semilinearly represented Galois conjugate pseudo-unitary. -/
theorem allGaloisConjugatesPseudoUnitary_of_invertibleS_of_propertyF
    (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    (hdet : (MTC.Modular.categoricalS C p).det ≠ 0) (hF : HasPropertyF C.Obj) :
    AllGaloisConjugatesPseudoUnitary C := by
  intro D σ h
  obtain ⟨h⟩ := h
  exact pseudoUnitary_of_scalarTwist_of_galois h
    (scalarTwists_pseudoUnitary_of_invertibleS_of_propertyF C p hdet hF σ)

/-- The full nondegenerate-manuscript conclusion under the explicitly
stronger hypothesis of invertibility of the actual pivotal S matrix. -/
theorem main_of_invertibleS_of_propertyF
    (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    (hdet : (MTC.Modular.categoricalS C p).det ≠ 0) (hF : HasPropertyF C.Obj) :
    PseudoUnitary C ∧ AllGaloisConjugatesPseudoUnitary C ∧
      WeaklyIntegral (globalFPDimension C) :=
  ⟨pseudoUnitary_of_invertibleS_of_propertyF C p hdet hF,
    allGaloisConjugatesPseudoUnitary_of_invertibleS_of_propertyF C p hdet hF,
    weaklyIntegral_of_invertibleS_of_propertyF C p hdet hF⟩

end MTC.PropertyF.Pivotal
end
