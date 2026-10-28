module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import PropertyF.Ground.Fusion.Multiplicity
public import PropertyF.Ground.Integrate.Representatives
public import PropertyF.Ground.Modular.BraidFunctor

/-!
# Simple labels and transport of fusion data across equivalences.
-/

@[expose] public noncomputable section

section
/-! Simple labels under equivalences of genuine fusion categories. -/


open CategoryTheory
namespace PropertyF.Ground.Modular
universe v u

/-- An equivalence transports the chosen simple labels bijectively, with an
actual isomorphism between each transported representative and its new label. -/
theorem simpleLabels_equiv (C D : Ground.BraidedFusionCategory.{v,u})
    (E : C.Obj ≌ D.Obj) : ∃ e : Fin (rank C) ≃ Fin (rank D),
    ∀ i, Nonempty (E.functor.obj (simples C i) ≅ simples D (e i)) := by
  classical
  let F := E.functor
  let S : Fin (rank C) → D.Obj := fun i => F.obj (simples C i)
  apply simple_presentation_equiv D S
  · intro i
    let _ : Simple (simples C i) := simples_simple C i
    exact simple_obj F (simples C i)
  · intro i j ⟨e⟩
    apply simples_injective C
    exact ⟨F.preimageIso e⟩
  · intro j
    let Y := simples D j
    let X := F.objPreimage Y
    have e := F.objObjPreimageIso Y
    let _ : Simple Y := simples_simple D j
    let _ : Simple (F.obj X) := Simple.of_iso e
    let _ : Simple X := Functor.simple_of_simple_obj F X
    obtain ⟨i, ⟨ei⟩⟩ := exists_simple_iso C X
    exact ⟨i, ⟨F.mapIso ei.symm ≪≫ e⟩⟩

end PropertyF.Ground.Modular
end

section
/-!
# Galois invariance of fusion rules and property F

A semilinear equivalence induces additive Hom equivalences, preserves Hom
finranks, and therefore carries the fusion matrices to their reindexings.
Spectrum invariance under algebra equivalence proves the ground target's
spectral-radius FP dimensions are preserved without a Perron–Frobenius theorem.
-/
open scoped BigOperators
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.Monoidal

namespace PropertyF.Ground.Modular
universe v u

variable {C D : Ground.BraidedFusionCategory.{v,u}}
variable {σ : ℂ ≃+* ℂ} (h : Ground.GaloisConjugate C D σ)
include h

/-- Semilinear equivalences preserve the dimensions of Hom spaces. -/
theorem conjugate_hom_finrank (X Y : C.Obj) :
    Module.finrank ℂ (X ⟶ Y) =
      Module.finrank ℂ (h.equivalence.functor.obj X ⟶ h.equivalence.functor.obj Y) :=
  let F := h.equivalence.functor
  let : F.Additive := F.additive_of_preserves_binary_products
  let eqv : (X ⟶ Y) ≃+ (F.obj X ⟶ F.obj Y) :=
    AddEquiv.ofBijective F.mapAddHom ⟨F.map_injective, F.map_surjective⟩
  by simpa only [Cardinal.toNat_lift, Module.finrank] using
    congrArg Cardinal.toNat (lift_rank_eq_of_equiv_equiv σ eqv σ.bijective (fun z f => h.map_smul z f))

section
variable {e : Fin (rank C) ≃ Fin (rank D)}
variable (he : ∀ i, Nonempty (h.equivalence.functor.obj (simples C i) ≅ simples D (e i)))
include he

/-- The semilinear equivalence preserves the categorical fusion coefficients. -/
theorem conjugate_fusionCoeff (i j k : Fin (rank C)) : fusionCoeff C i j k = fusionCoeff D (e i) (e j) (e k) := by
  let F := h.equivalence.functor
  let _ := h.monoidal
  let a := (he i).some
  let b := (he j).some
  let c := (he k).some
  let t : F.obj (simples C i ⊗ simples C j) ≅ simples D (e i) ⊗ simples D (e j) :=
    (μIso F (simples C i) (simples C j)).symm ≪≫ (a ⊗ᵢ b)
  change Module.finrank ℂ (simples C k ⟶ simples C i ⊗ simples C j) = _
  rw [conjugate_hom_finrank h]
  exact (CategoryTheory.Linear.homCongr ℂ c t).finrank_eq


/-- Conjugation transports the target's fusion matrix by reindexing. -/
theorem conjugate_fusionMatrix (i : Fin (rank C)) :
    Matrix.reindexAlgEquiv ℂ ℂ e (fusionMatrix C i) = fusionMatrix D (e i) :=
  Matrix.ext fun k j ↦ by
    have hc := conjugate_fusionCoeff h he i (e.symm j) (e.symm k)
    simp only [e.apply_symm_apply] at hc
    simpa only [fusionCoeff, fusionMatrix, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      Matrix.submatrix_apply] using congrArg (fun n : ℕ => (n : ℂ)) hc

/-- The spectral-radius FP dimensions are invariant under Galois conjugation. -/
theorem conjugate_fpSimple (i : Fin (rank C)) : fpSimple C i = fpSimple D (e i) := by
  rw [fpSimple, fpSimple, ← conjugate_fusionMatrix h he i, spectralRadius_eq_of_unital,
    spectralRadius_eq_of_unital, AlgEquiv.spectrum_eq]


end

/-- Galois conjugacy gives the label bijection and preserves each FP dimension. -/
theorem conjugate_labels :
    ∃ e : Fin (rank C) ≃ Fin (rank D), ∀ i, fpSimple C i = fpSimple D (e i) :=
  (simpleLabels_equiv C D h.equivalence).imp fun _ he ↦ conjugate_fpSimple h he

/-- The target's global FP dimension is invariant under Galois conjugacy. -/
theorem conjugate_globalFPDimension :
    globalFPDimension C = globalFPDimension D :=
  (conjugate_labels h).elim fun e he ↦ by
    simpa only [globalFPDimension, he] using e.sum_comp (fun j => fpSimple D j ^ 2)


/-- Ground version of braid-image invariance for a conjugate category. -/
theorem ground_conjugate_images (Y : D.Obj) (n : ℕ) :
    ∃ X : C.Obj, Nonempty (braidImage Y n ≃* braidImage X n) :=
  letI := h.monoidal
  letI := h.braided
  braidImages_of_essentiallySurjective h.equivalence.functor Y n

/-- Property F is invariant in the forward direction under Galois conjugacy. -/
theorem conjugate_propertyF
    (hF : HasPropertyF C.Obj) : HasPropertyF D.Obj := fun Y n ↦
  (ground_conjugate_images h Y n).elim fun X ⟨e⟩ ↦
    Finite.of_equiv (braidImage X n) (h := hF X n) e.symm.toEquiv

end PropertyF.Ground.Modular
end
