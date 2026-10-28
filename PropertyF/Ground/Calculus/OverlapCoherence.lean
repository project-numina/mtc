module
public import PropertyF.Ground.Calculus.OverlapBound
public import PropertyF.Ground.Calculus.ThreeTrace

/-! Tensor-power coherence for the concrete strand insertions. -/

open PropertyF.Ground.Dimensions

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

section SingleInsertion

variable {X : C} {n : ℕ} (a : braidAlgebra X n)

/-- At the level of endomorphisms, left insertion is left whiskering. -/
theorem addLeftBraidAlgebra_asHom :
    ((addLeftBraidAlgebra X n a : braidAlgebra X (n + 1)) :
      End (tensorPower X ((n + 1) + 2))).asHom =
      X ◁ (a : End (tensorPower X (n + 2))).asHom := rfl

/-- At the level of endomorphisms, right insertion is right whiskering,
transported across the append isomorphism. -/
theorem addRightBraidAlgebra_asHom :
    ((addRightBraidAlgebra X n a : braidAlgebra X (n + 1)) :
      End (tensorPower X ((n + 1) + 2))).asHom =
      (appendIso X (n + 2)).inv ≫ ((a : End (tensorPower X (n + 2))).asHom ▷ X) ≫
        (appendIso X (n + 2)).hom := rfl

end SingleInsertion

/-- Canonical left insertion isomorphism, indexed by the braid-algebra
convention that index `n` has `n+2` strands. -/
def insertLeftPowerIso (X : C) (n : ℕ) : ∀ k, tensorPower X k ⊗ tensorPower X (n + 2) ≅
    tensorPower X ((n + k) + 2)
  | 0 => λ_ (tensorPower X (n + 2))
  | k + 1 => (α_ X (tensorPower X k) (tensorPower X (n + 2))) ≪≫
      (Iso.refl X ⊗ᵢ insertLeftPowerIso X n k)

/-- Canonical right insertion isomorphism, built by appending one strand at
a time on the right. -/
def insertRightPowerIso (X : C) (n : ℕ) : ∀ k, tensorPower X (n + 2) ⊗ tensorPower X k ≅
    tensorPower X ((n + k) + 2)
  | 0 => ρ_ (tensorPower X (n + 2))
  | k + 1 => (Iso.refl (tensorPower X (n + 2)) ⊗ᵢ (appendIso X k).symm) ≪≫
      (α_ (tensorPower X (n + 2)) (tensorPower X k) X).symm ≪≫
      (insertRightPowerIso X n k ⊗ᵢ Iso.refl X) ≪≫ appendIso X ((n + k) + 2)

section IteratedInsertion

variable {X : C} {n : ℕ} (k : ℕ) (a : braidAlgebra X n)

set_option backward.isDefEq.respectTransparency false in
/-- Repeated left insertion is one identity tensor factor, transported along
the canonical tensor-power isomorphism. -/
theorem addLeftBraidAlgebraIter_asHom :
    ((addLeftBraidAlgebraIter X n k a : braidAlgebra X (n + k)) :
      End (tensorPower X ((n + k) + 2))).asHom =
      (insertLeftPowerIso X n k).inv ≫
        (tensorPower X k ◁ (a : End (tensorPower X (n + 2))).asHom) ≫
          (insertLeftPowerIso X n k).hom := by
  induction k with
  | zero =>
    dsimp only [addLeftBraidAlgebraIter, insertLeftPowerIso, tensorPower]
    monoidal
  | succ k ih =>
    change ((addLeftBraidAlgebra X (n + k) (addLeftBraidAlgebraIter X n k a) :
      braidAlgebra X (n + k + 1)) : End (tensorPower X ((n + k + 1) + 2))).asHom = _
    rw [addLeftBraidAlgebra_asHom, ih]
    simp only [insertLeftPowerIso, Iso.trans_hom, Iso.trans_inv, tensorIso_hom,
      tensorIso_inv, Iso.refl_hom, Iso.refl_inv, id_tensorHom, whiskerLeft_comp,
      Category.assoc, tensorPower]
    monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Repeated right insertion is one identity tensor factor, transported along
the canonical tensor-power isomorphism. -/
theorem addRightBraidAlgebraIter_asHom :
    ((addRightBraidAlgebraIter X n k a : braidAlgebra X (n + k)) :
      End (tensorPower X ((n + k) + 2))).asHom =
      (insertRightPowerIso X n k).inv ≫
        ((a : End (tensorPower X (n + 2))).asHom ▷ tensorPower X k) ≫
          (insertRightPowerIso X n k).hom := by
  induction k with
  | zero =>
    dsimp only [addRightBraidAlgebraIter, insertRightPowerIso, tensorPower]
    monoidal
  | succ k ih =>
    change ((addRightBraidAlgebra X (n + k) (addRightBraidAlgebraIter X n k a) :
      braidAlgebra X (n + k + 1)) : End (tensorPower X ((n + k + 1) + 2))).asHom = _
    rw [addRightBraidAlgebra_asHom, ih]
    simp only [insertRightPowerIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv,
      tensorHom_id, comp_whiskerRight, Category.assoc, id_tensorHom, whisker_exchange_assoc]
    rw [← associator_naturality_left_assoc]
    simp

end IteratedInsertion

end PropertyF.Ground.Calculus

/-! The exact tensor-power coherence needed for the overlap trace step. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Identify the previous tensor power as a prefix followed by its final
strand, then append the new tail. -/
def overlapPowerIso (X : C) (t k : ℕ) :
    (tensorPower X (overlapIndex t k + 1) ⊗ X) ⊗ tensorPower X (t + 1) ≅
      tensorPower X (overlapIndex t (k + 1) + 2) :=
  (appendIso X (overlapIndex t k + 1) ⊗ᵢ Iso.refl (tensorPower X (t + 1))) ≪≫
    insertRightPowerIso X (overlapIndex t k) (t + 1)

/-- The number of strands before the fresh operator is exactly the prefix of
the old operator after its final shared strand is removed. -/
theorem overlap_prefix_count (t k : ℕ) :
    overlapIndex t k + 1 = (k + 1) * (t + 1) := by
  rw [overlapIndex_formula]
  ring

/-- The canonical left-insertion isomorphism for the fresh overlap factor. -/
def freshOverlapIso (X : C) (t k : ℕ) :
    tensorPower X (overlapIndex t k + 1) ⊗ tensorPower X (t + 2) ≅
      tensorPower X (overlapIndex t (k + 1) + 2) :=
  (eqToIso (congrArg (tensorPower X) (overlap_prefix_count t k)) ⊗ᵢ
      Iso.refl (tensorPower X (t + 2))) ≪≫
    insertLeftPowerIso X t ((k + 1) * (t + 1)) ≪≫
    eqToIso (congrArg (fun n => tensorPower X (n + 2)) (overlapIndex_formula t (k + 1)).symm)

/-- The left- and right-insertion isomorphisms agree on an overlap. -/
abbrev HasOverlapCoherence (X : C) (t k : ℕ) : Prop :=
  freshOverlapIso X t k =
    (α_ (tensorPower X (overlapIndex t k + 1)) X (tensorPower X (t + 1))).symm ≪≫
      overlapPowerIso X t k

/-- The previous overlap operator expressed with its last strand explicit. -/
def previousOverlapLocal {X : C} {t : ℕ} (k : ℕ) (u : braidAlgebra X t) :
    End (tensorPower X (overlapIndex t k + 1) ⊗ X) :=
  (isoEndAlgEquiv (appendIso X (overlapIndex t k + 1)).symm)
    (overlapProduct u k : End (tensorPower X (overlapIndex t k + 2)))

/-- The actual overlapping product agrees with the local endomorphism product. -/
abbrev IsLocalOverlapProduct {X : C} {t : ℕ} (k : ℕ) (u : braidAlgebra X t) : Prop :=
  (isoEndAlgEquiv (overlapPowerIso X t k).symm)
      (overlapProduct u (k + 1) : End (tensorPower X (overlapIndex t (k + 1) + 2))) =
    overlapEndProduct (previousOverlapLocal k u) (u : End (tensorPower X (t + 2)))

set_option backward.isDefEq.respectTransparency false in
/-- Under the overlap isomorphism the previous braid is exactly the local
endomorphism with identity on the new tail. -/
theorem overlapLeft_local {X : C} (t k : ℕ) (v : braidAlgebra X (overlapIndex t k)) :
    (isoEndAlgEquiv (overlapPowerIso X t k).symm)
      (overlapLeft X t k v : End (tensorPower X (overlapIndex t (k + 1) + 2))) =
    insertRightIdentity (tensorPower X (t + 1))
      ((isoEndAlgEquiv (appendIso X (overlapIndex t k + 1)).symm)
        (v : End (tensorPower X (overlapIndex t k + 2)))) := by
  apply End.ext
  change (overlapPowerIso X t k).hom ≫
    ((addRightBraidAlgebraIter X (overlapIndex t k) (t + 1) v :
      braidAlgebra X (overlapIndex t k + (t + 1))) :
      End (tensorPower X ((overlapIndex t k + (t + 1)) + 2))).asHom ≫
    (overlapPowerIso X t k).inv = _
  rw [addRightBraidAlgebraIter_asHom]
  simp [insertRightIdentity, isoEndAlgEquiv, Iso.conj_apply_asHom, overlapPowerIso,
    tensorIso_hom, tensorIso_inv, tensorHom_id, comp_whiskerRight, Category.assoc]

section LocalOverlap

variable {X : C} {t : ℕ} (k : ℕ) (u : braidAlgebra X t)

set_option backward.isDefEq.respectTransparency false in
/-- The fresh algebra element is left whiskering along its canonical
left-insertion isomorphism. -/
theorem freshOverlapIso_action :
    (isoEndAlgEquiv (freshOverlapIso X t k))
      (End.of (tensorPower X (overlapIndex t k + 1) ◁
        (u : End (tensorPower X (t + 2))).asHom)) =
    (overlapRight X t k u : End (tensorPower X (overlapIndex t (k + 1) + 2))) := by
  have hcast : ∀ (a b : ℕ) (h : a = b)
      (F : braidAlgebra X t →ₐ[ℂ] braidAlgebra X b) (u : braidAlgebra X t),
      (((Eq.mpr (congrArg (fun n => braidAlgebra X t →ₐ[ℂ] braidAlgebra X n) h) F) u :
        braidAlgebra X a) : End (tensorPower X (a + 2))).asHom =
      (eqToIso (congrArg (fun n => tensorPower X (n + 2)) h)).hom ≫
        ((F u : braidAlgebra X b) : End (tensorPower X (b + 2))).asHom ≫
      (eqToIso (congrArg (fun n => tensorPower X (n + 2)) h)).inv := by
    intro a b h F u
    cases h
    simp
  apply End.ext
  change (freshOverlapIso X t k).inv ≫
      (tensorPower X (overlapIndex t k + 1) ◁ (u : End (tensorPower X (t + 2))).asHom) ≫
      (freshOverlapIso X t k).hom = _
  dsimp only [overlapRight]
  rw [hcast _ _ (overlapIndex_formula t (k + 1)), addLeftBraidAlgebraIter_asHom]
  simp only [freshOverlapIso, Iso.trans_hom, Iso.trans_inv, tensorIso_hom, tensorIso_inv,
    Iso.refl_hom, Iso.refl_inv, tensorHom_id, Category.assoc]
  rw [← whisker_exchange_assoc]
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Agreement of the two canonical tensor-power isomorphisms identifies the
fresh actual braid factor with the local overlap factor. -/
theorem overlapRight_local_of_iso (hiso : HasOverlapCoherence X t k) :
    (isoEndAlgEquiv (overlapPowerIso X t k).symm)
      (overlapRight X t k u : End (tensorPower X (overlapIndex t (k + 1) + 2))) =
    overlapFresh (tensorPower X (overlapIndex t k + 1))
      (u : End (tensorPower X (t + 2))) := by
  rw [← freshOverlapIso_action, hiso]
  apply End.ext
  simp [overlapFresh, isoEndAlgEquiv, Iso.conj_apply_asHom]

set_option backward.isDefEq.respectTransparency false in
/-- A single coherence equality between the left- and right-insertion
isomorphisms gives the entire actual overlap-product identification. -/
theorem overlapProduct_local_of_iso (hiso : HasOverlapCoherence X t k) :
    IsLocalOverlapProduct k u := by
  simp only [IsLocalOverlapProduct, overlapProduct, Subalgebra.coe_mul, map_mul, overlapEndProduct,
    overlapLeft_local, overlapRight_local_of_iso k u hiso, previousOverlapLocal]

end LocalOverlap

variable (D : BraidedFusionCategory.{v,u}) {X : D.Obj} [Simple X]
  (p : PivotalStructure (C := D.Obj)) {t : ℕ} (u : braidAlgebra X t)

set_option backward.isDefEq.respectTransparency false in
/-- Identifying the actual product with the local graphical overlap implies
the precise one-step trace recurrence. -/
theorem overlap_trace_step_of_coherence (k : ℕ)
    (hcoh : IsLocalOverlapProduct k u) :
    actualBraidTrace D p (overlapProduct u (k + 1)) *
        pivotalDimension D p X =
      actualBraidTrace D p (overlapProduct u k) *
        actualBraidTrace D p u := by
  have hh := congrArg
    (fun z => Ground.unitScalarEquiv D (p.rightTrace z.asHom)) hcoh
  rw [rightTrace_iso_conj, pivotalTrace_overlap D (X := X) p (Ground.unitScalarEquiv D)] at hh
  unfold previousOverlapLocal at hh
  rw [rightTrace_iso_conj] at hh
  change actualBraidTrace D p _ = actualBraidTrace D p _ *
    (actualBraidTrace D p u / _) at hh
  unfold pivotalDimension
  rw [unitScalar_eq_equiv, hh, mul_assoc,
    div_mul_cancel₀ _ (Modular.unitScalar_rightTrace_ne_zero D p X)]

/-- Canonical isomorphism coherence supplies the scaled trace identity for
every iterated actual overlapping braid-algebra product. -/
theorem overlap_trace_power_of_isos (hiso : ∀ k, HasOverlapCoherence X t k) :
    HasOverlapTracePower D p u :=
  overlap_trace_power_of_step D p u fun k ↦
    overlap_trace_step_of_coherence D p u k (overlapProduct_local_of_iso k u (hiso k))

end PropertyF.Ground.Calculus
