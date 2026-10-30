module
public import MTC.Braided.Trace.OverlapBound
public import MTC.Braided.Trace.ThreeTrace

/-!
# Coherence of overlapping braid products

Canonical tensor-power isomorphisms identify strand insertions with local operators.
Their coherence implies the recurrence for traces of overlapping products.
-/

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
      End (braidTensorPower X (n + 1))).asHom =
      X ◁ (a : End (braidTensorPower X n)).asHom := rfl

/-- At the level of endomorphisms, right insertion is right whiskering,
transported across the append isomorphism. -/
theorem addRightBraidAlgebra_asHom :
    ((addRightBraidAlgebra X n a : braidAlgebra X (n + 1)) : End _).asHom =
      (appendIso X (n + 2)).inv ≫ ((a : End _).asHom ▷ X) ≫ (appendIso X (n + 2)).hom := rfl

end SingleInsertion

/-- Canonical left insertion isomorphism, indexed by the braid-algebra
convention that index `n` has `n+2` strands. -/
def insertLeftPowerIso (X : C) (n : ℕ) : ∀ k, tensorPower X k ⊗ braidTensorPower X n ≅
    tensorPower X ((n + k) + 2)
  | 0 => λ_ (braidTensorPower X n)
  | k + 1 => (α_ X (tensorPower X k) (braidTensorPower X n)) ≪≫
      (Iso.refl X ⊗ᵢ insertLeftPowerIso X n k)

/-- Canonical right insertion isomorphism, built by appending one strand at
a time on the right. -/
def insertRightPowerIso (X : C) (n : ℕ) : ∀ k, braidTensorPower X n ⊗ tensorPower X k ≅
    tensorPower X ((n + k) + 2)
  | 0 => ρ_ (braidTensorPower X n)
  | k + 1 => (Iso.refl (braidTensorPower X n) ⊗ᵢ (appendIso X k).symm) ≪≫
      (α_ (braidTensorPower X n) (tensorPower X k) X).symm ≪≫
      (insertRightPowerIso X n k ⊗ᵢ Iso.refl X) ≪≫ appendIso X ((n + k) + 2)

section IteratedInsertion

variable {X : C} {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- Repeated left insertion is one identity tensor factor, transported along
the canonical tensor-power isomorphism. -/
theorem addLeftBraidAlgebraIter_asHom : ∀ (k : ℕ) (a : braidAlgebra X n),
    ((addLeftBraidAlgebraIter X n k a : braidAlgebra X (n + k)) : End _).asHom =
      ((insertLeftPowerIso X n k).conj (End.of (tensorPower X k ◁ (a : End _).asHom))).asHom
  | 0, a => by simp [addLeftBraidAlgebraIter, insertLeftPowerIso, tensorPower, Iso.conj_apply_asHom]
  | k + 1, a => by
    change ((addLeftBraidAlgebra X (n + k) (addLeftBraidAlgebraIter X n k a) :
      braidAlgebra X (n + k + 1)) : End (tensorPower X ((n + k + 1) + 2))).asHom = _
    rw [addLeftBraidAlgebra_asHom, addLeftBraidAlgebraIter_asHom k a]
    simp only [Iso.conj_apply_asHom, insertLeftPowerIso, Iso.trans_hom, Iso.trans_inv, tensorIso_hom,
      tensorIso_inv, Iso.refl_hom, Iso.refl_inv, id_tensorHom, whiskerLeft_comp,
      Category.assoc, tensorPower]
    monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Repeated right insertion is one identity tensor factor, transported along
the canonical tensor-power isomorphism. -/
theorem addRightBraidAlgebraIter_asHom : ∀ (k : ℕ) (a : braidAlgebra X n),
    ((addRightBraidAlgebraIter X n k a : braidAlgebra X (n + k)) : End _).asHom =
      ((insertRightPowerIso X n k).conj (End.of ((a : End _).asHom ▷ tensorPower X k))).asHom
  | 0, a => by simp [addRightBraidAlgebraIter, insertRightPowerIso, tensorPower, Iso.conj_apply_asHom]
  | k + 1, a => by
    change ((addRightBraidAlgebra X (n + k) (addRightBraidAlgebraIter X n k a) :
      braidAlgebra X (n + k + 1)) : End (tensorPower X ((n + k + 1) + 2))).asHom = _
    rw [addRightBraidAlgebra_asHom, addRightBraidAlgebraIter_asHom k a]
    simp only [Iso.conj_apply_asHom, insertRightPowerIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
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
    eqToIso (congrArg (fun n => braidTensorPower X n) (overlapIndex_formula t (k + 1)).symm)

/-- The left- and right-insertion isomorphisms agree on an overlap. -/
abbrev HasOverlapCoherence (X : C) (t k : ℕ) : Prop :=
  freshOverlapIso X t k =
    (α_ (tensorPower X (overlapIndex t k + 1)) X (tensorPower X (t + 1))).symm ≪≫
      overlapPowerIso X t k

/-- The previous overlap operator expressed with its last strand explicit. -/
def previousOverlapLocal {X : C} {t : ℕ} (k : ℕ) (u : braidAlgebra X t) :
    End (tensorPower X (overlapIndex t k + 1) ⊗ X) :=
  (appendIso X (overlapIndex t k + 1)).symm.conj
    (overlapProduct u k : End (tensorPower X (overlapIndex t k + 2)))

/-- The actual overlapping product agrees with the local endomorphism product. -/
abbrev IsLocalOverlapProduct {X : C} {t : ℕ} (k : ℕ) (u : braidAlgebra X t) : Prop :=
  (overlapPowerIso X t k).symm.conj
      (overlapProduct u (k + 1) : End (tensorPower X (overlapIndex t (k + 1) + 2))) =
    overlapEndProduct (previousOverlapLocal k u) (u : End (tensorPower X (t + 2)))

set_option backward.isDefEq.respectTransparency false in
/-- Under the overlap isomorphism the previous braid is exactly the local
endomorphism with identity on the new tail. -/
theorem overlapLeft_local {X : C} (t k : ℕ) (v : braidAlgebra X (overlapIndex t k)) :
    (overlapPowerIso X t k).symm.conj (overlapLeft X t k v : End _) =
    insertRightIdentity (tensorPower X (t + 1))
      ((appendIso X (overlapIndex t k + 1)).symm.conj (v : End _)) :=
  End.ext (by
    change (overlapPowerIso X t k).hom ≫
      ((addRightBraidAlgebraIter X (overlapIndex t k) (t + 1) v :
        braidAlgebra X (overlapIndex t k + (t + 1))) :
        End (tensorPower X ((overlapIndex t k + (t + 1)) + 2))).asHom ≫
      (overlapPowerIso X t k).inv = _
    rw [addRightBraidAlgebraIter_asHom]
    simp [insertRightIdentity, Iso.conj_apply_asHom, overlapPowerIso,
      tensorIso_hom, tensorIso_inv, tensorHom_id, comp_whiskerRight, Category.assoc])

section LocalOverlap

variable {X : C} {t : ℕ} (k : ℕ) (u : braidAlgebra X t)

set_option backward.isDefEq.respectTransparency false in
/-- The fresh algebra element is left whiskering along its canonical
left-insertion isomorphism. -/
theorem freshOverlapIso_action :
    (freshOverlapIso X t k).hom ≫ (overlapRight X t k u : End _).asHom =
      (tensorPower X (overlapIndex t k + 1) ◁ (u : End _).asHom) ≫
        (freshOverlapIso X t k).hom := by
  apply (cancel_epi (freshOverlapIso X t k).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  symm
  have hcast : ∀ (a b : ℕ) (h : a = b)
      (F : braidAlgebra X t →ₐ[ℂ] braidAlgebra X b) (u : braidAlgebra X t),
      (((Eq.mpr (congrArg (fun n => braidAlgebra X t →ₐ[ℂ] braidAlgebra X n) h) F) u :
        braidAlgebra X a) : End (tensorPower X (a + 2))).asHom =
      (eqToIso (congrArg (fun n => braidTensorPower X n) h)).hom ≫
        ((F u : braidAlgebra X b) : End (tensorPower X (b + 2))).asHom ≫
      (eqToIso (congrArg (fun n => braidTensorPower X n) h)).inv := by
    rintro a b rfl F u
    simp
  dsimp only [overlapRight]
  rw [hcast _ _ (overlapIndex_formula t (k + 1)), addLeftBraidAlgebraIter_asHom]
  simp only [Iso.conj_apply_asHom, freshOverlapIso, Iso.trans_hom, Iso.trans_inv, tensorIso_hom, tensorIso_inv,
    Iso.refl_hom, Iso.refl_inv, tensorHom_id, Category.assoc]
  rw [← whisker_exchange_assoc]
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  rfl

end LocalOverlap

variable (D : BraidedFusionCategory.{v,u}) {X : D.Obj} [Simple X]
  (p : PivotalStructure (C := D.Obj)) {t : ℕ} (u : braidAlgebra X t)

set_option backward.isDefEq.respectTransparency false in
/-- Identifying the actual product with the local graphical overlap implies
the precise one-step trace recurrence. -/
theorem overlap_trace_step_of_coherence (k : ℕ)
    (hcoh : IsLocalOverlapProduct k u) :
    actualBraidTrace D p (overlapProduct u (k + 1)) * pivotalDimension D p X =
      actualBraidTrace D p (overlapProduct u k) * actualBraidTrace D p u := by
  have hh := congrArg
    (fun z => Ground.unitScalarEquiv D (p.rightTrace z.asHom)) hcoh
  rw [rightTrace_iso_conj, pivotalTrace_overlap D (X := X) p (Ground.unitScalarEquiv D)] at hh
  unfold previousOverlapLocal at hh
  rw [rightTrace_iso_conj] at hh
  change actualBraidTrace D p _ = actualBraidTrace D p _ *
    (actualBraidTrace D p u / _) at hh
  unfold pivotalDimension
  rw [unitScalar_eq_equiv, hh, mul_assoc,
    div_mul_cancel₀ _ (by simpa only [← unitScalar_eq_equiv] using
      Modular.unitScalar_rightTrace_ne_zero D p X)]

end PropertyF.Ground.Calculus
