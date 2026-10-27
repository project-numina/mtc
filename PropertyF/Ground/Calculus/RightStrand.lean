module
public import PropertyF.Ground.Calculus.ImageMaps
public import PropertyF.Ground.Calculus.EndBlocks
public import Mathlib.Tactic

/-! Right identity-strand insertion on categorical braid algebras. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

def appendIso (X : C) : ∀ n : ℕ, tensorPower X n ⊗ X ≅ tensorPower X (n + 1)
  | 0 => (λ_ X) ≪≫ (ρ_ X).symm
  | n + 1 => by
    simpa only [tensorPower] using
      ((α_ X (tensorPower X n) X) ≪≫ (Iso.refl X ⊗ᵢ appendIso X n))

def addRightAut (X : C) (n : ℕ) : Aut (tensorPower X (n+2)) →* Aut (tensorPower X ((n+1)+2)) :=
  (appendIso X (n+2)).conjAut.toMonoidHom.comp ((tensorRight X).mapAut (tensorPower X (n+2)))

omit [BraidedCategory C] in
theorem append_step (X A B : C) (e : A ⊗ X ≅ B) (f : A ⟶ A) :
  ((α_ X A X) ≪≫ (Iso.refl X ⊗ᵢ e)).inv ≫ ((X ◁ f) ▷ X) ≫
    ((α_ X A X) ≪≫ (Iso.refl X ⊗ᵢ e)).hom = X ◁ (e.inv ≫ (f ▷ X) ≫ e.hom) := by
  dsimp only [Iso.trans_hom, Iso.trans_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv]
  simp only [id_tensorHom, whiskerLeft_comp, Category.assoc]
  monoidal

@[reassoc]
theorem crossing_natural (X A B : C) (g : A ⟶ B) :
    ((α_ X X A).inv ≫ (β_ X X).hom ▷ A ≫ (α_ X X A).hom) ≫ X ◁ X ◁ g =
      X ◁ X ◁ g ≫ ((α_ X X B).inv ≫ (β_ X X).hom ▷ B ≫ (α_ X X B).hom) := by
  simp only [Category.assoc]
  rw [← associator_naturality_right X X g]
  rw [← whisker_exchange_assoc, ← associator_inv_naturality_right_assoc]

theorem append_first_two (X A B : C) (e : A ⊗ X ≅ B) :
  let E := (α_ X (X ⊗ A) X) ≪≫
    (Iso.refl X ⊗ᵢ ((α_ X A X) ≪≫ (Iso.refl X ⊗ᵢ e)))
  E.inv ≫ (((α_ X X A).inv ≫ (β_ X X).hom ▷ A ≫ (α_ X X A).hom) ▷ X) ≫ E.hom =
    (α_ X X B).inv ≫ (β_ X X).hom ▷ B ≫ (α_ X X B).hom := by
  dsimp only
  calc
    _ = (X ◁ X ◁ e.inv) ≫
        ((α_ X X (A ⊗ X)).inv ≫ (β_ X X).hom ▷ (A ⊗ X) ≫ (α_ X X (A ⊗ X)).hom) ≫
        (X ◁ X ◁ e.hom) := by
          dsimp only [Iso.trans_hom, Iso.trans_inv, tensorIso_hom, tensorIso_inv,
            Iso.refl_hom, Iso.refl_inv]
          simp only [id_tensorHom, Category.assoc]
          monoidal
    _ = _ := by
      simp only [Category.assoc]
      rw [← crossing_natural_assoc X B (A ⊗ X) e.inv]
      simp [← whiskerLeft_comp]


omit [BraidedCategory C] in
theorem appendIso_succ (X : C) (n : ℕ) : appendIso X (n+1) =
  (α_ X (tensorPower X n) X) ≪≫ (Iso.refl X ⊗ᵢ appendIso X n) := by rfl

set_option backward.isDefEq.respectTransparency false in
theorem addRightAut_generator (X : C) (n : ℕ) (i : Fin (n+1)) :
    addRightAut X n (braidGenerator X n i) = braidGenerator X (n+1) i.castSucc := by
  induction n with
  | zero =>
    have : i = 0 := Fin.eq_zero i
    subst i
    apply Aut.ext
    apply Iso.ext
    change (appendIso X 2).inv ≫ ((braidGenerator X 0 0).asIso.hom ▷ X) ≫
      (appendIso X 2).hom = (braidGenerator X 1 0).asIso.hom
    dsimp only [appendIso, braidGenerator, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv]
    dsimp only [id, tensorPower, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv]
    simp only [id_tensorHom, tensorHom_id]
    monoidal
  | succ n ih =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero =>
      apply Aut.ext
      apply Iso.ext
      change (appendIso X (n+3)).inv ≫ ((braidGenerator X (n+1) ⟨0, hi⟩).asIso.hom ▷ X) ≫
        (appendIso X (n+3)).hom = (braidGenerator X (n+2) ⟨0, by omega⟩).asIso.hom
      simp only [braidGenerator, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
        tensorHom_id]
      change (appendIso X (n+3)).inv ≫
        (((α_ X X (tensorPower X (n+1))).inv ≫
          (β_ X X).hom ▷ tensorPower X (n+1) ≫
          (α_ X X (tensorPower X (n+1))).hom) ▷ X) ≫ (appendIso X (n+3)).hom =
        (α_ X X (tensorPower X (n+2))).inv ≫ (β_ X X).hom ▷ tensorPower X (n+2) ≫
          (α_ X X (tensorPower X (n+2))).hom
      rw [appendIso_succ X (n+2), appendIso_succ X (n+1)]
      exact append_first_two X _ _ (appendIso X (n+1))
    | succ i =>
      apply Aut.ext
      apply Iso.ext
      let j : Fin (n+1) := ⟨i, by omega⟩
      have h := congrArg (fun a : Aut (tensorPower X (n+3)) => a.asIso.hom) (ih j)
      change (appendIso X (n+2)).inv ≫ ((braidGenerator X n j).asIso.hom ▷ X) ≫
        (appendIso X (n+2)).hom = (braidGenerator X (n+1) j.castSucc).asIso.hom at h
      change (appendIso X (n+3)).inv ≫ ((braidGenerator X (n+1) ⟨i+1, hi⟩).asIso.hom ▷ X) ≫
        (appendIso X (n+3)).hom = (braidGenerator X (n+2) ⟨i+1, by omega⟩).asIso.hom
      simp only [braidGenerator, tensorIso_hom, Iso.refl_hom, id_tensorHom]
      change (appendIso X (n+3)).inv ≫ ((X ◁ (braidGenerator X n j).asIso.hom) ▷ X) ≫
        (appendIso X (n+3)).hom = X ◁ (braidGenerator X (n+1) j.castSucc).asIso.hom
      rw [appendIso_succ X (n+2), append_step, h]

/-- Appending one identity strand on the right maps the actual braid image to
the larger actual braid image. -/
def addRightStrand (X : C) (n : ℕ) : braidImage X n →* braidImage X (n + 1) := by
  let f := addRightAut X n
  have hf : ∀ a ∈ braidImage X n, f a ∈ braidImage X (n + 1) := by
    change braidImage X n ≤ (braidImage X (n + 1)).comap f
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change addRightAut X n (braidGenerator X n i) ∈ braidImage X (n + 1)
    rw [addRightAut_generator]
    exact Subgroup.subset_closure (Set.mem_range_self _)
  exact (f.comp (braidImage X n).subtype).codRestrict _ (fun a => hf a a.property)

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Append a right identity strand as an algebra map on all endomorphisms. -/
def appendRightEndAlgHom (X : C) (n : ℕ) :
    End (tensorPower X (n + 2)) →ₐ[ℂ] End (tensorPower X ((n + 1) + 2)) :=
  (isoEndAlgEquiv (appendIso X (n + 2))).toAlgHom.comp
    (functorEndAlgHom (tensorRight X) (tensorPower X (n + 2)))

/-- The endomorphism map carries the categorical braid representation to
the appended braid representation. -/
theorem appendRightEndAlgHom_group (X : C) (n : ℕ) (g : braidImage X n) :
    appendRightEndAlgHom X n (braidEndRepresentation X n g) =
      braidEndRepresentation X (n + 1) (addRightStrand X n g) := by
  apply End.ext
  rfl

/-- Appending one right identity strand gives a map of actual braid algebras. -/
def addRightBraidAlgebra (X : C) (n : ℕ) : braidAlgebra X n →ₐ[ℂ] braidAlgebra X (n + 1) :=
  imageAlgebraMap (braidEndRepresentation X n) (braidEndRepresentation X (n + 1))
    (addRightStrand X n) (appendRightEndAlgHom X n) (appendRightEndAlgHom_group X n)

/-- The induced algebra map carries every braid to the right-inserted braid. -/
theorem addRightBraidAlgebra_group (X : C) (n : ℕ) (g : braidImage X n) :
    addRightBraidAlgebra X n (groupInImage (braidEndRepresentation X n) g) =
      groupInImage (braidEndRepresentation X (n + 1)) (addRightStrand X n g) := by
  apply imageAlgebraMap_group

/-- Right insertion expressed in independently chosen matrix blocks. -/
def addRightBlockMap (X : C) (n : ℕ) {r s : ℕ} {d : Fin r → ℕ} {k : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + 1) ≃ₐ[ℂ] ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ) :
    (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ]
      (∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ) :=
  f.toAlgHom.comp ((addRightBraidAlgebra X n).comp e.symm.toAlgHom)

set_option backward.isDefEq.respectTransparency false in
/-- Right insertion preserves the adjoint for any unitary presentations. -/
theorem addRightBlockMap_star (X : C) (n : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {k : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + 1) ≃ₐ[ℂ] ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ)
    (he : ∀ g i, e (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hf : ∀ g i, f (groupInImage (braidEndRepresentation X (n + 1)) g) i ∈
      Matrix.unitaryGroup (Fin (k i)) ℂ)
    (x : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    addRightBlockMap X n e f (star x) = star (addRightBlockMap X n e f x) := by
  apply presented_intertwiner_map_star (braidEndRepresentation X n)
    (braidEndRepresentation X (n + 1)) (addRightStrand X n) e f he hf
    (addRightBlockMap X n e f)
  intro g
  change f (addRightBraidAlgebra X n (e.symm (e (groupInImage (braidEndRepresentation X n) g)))) = _
  rw [e.symm_apply_apply, addRightBraidAlgebra_group]
  rfl

/-- Bundled star algebra map for one right identity strand. -/
def addRightBlockStarMap (X : C) (n : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {k : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + 1) ≃ₐ[ℂ] ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ)
    (he : ∀ g i, e (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hf : ∀ g i, f (groupInImage (braidEndRepresentation X (n + 1)) g) i ∈
      Matrix.unitaryGroup (Fin (k i)) ℂ) :
    (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →⋆ₐ[ℂ]
      (∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ) where
  toAlgHom := addRightBlockMap X n e f
  map_star' := addRightBlockMap_star X n e f he hf

/-- Repeated right identity-strand insertion on the actual image groups. -/
def addRightStrands (X : C) (n : ℕ) : ∀ k, braidImage X n →* braidImage X (n + k)
  | 0 => MonoidHom.id _
  | k + 1 => (addRightStrand X (n + k)).comp (addRightStrands X n k)

/-- Repeated right identity-strand insertion on the actual braid algebras. -/
def addRightBraidAlgebraIter (X : C) (n : ℕ) :
    ∀ k, braidAlgebra X n →ₐ[ℂ] braidAlgebra X (n + k)
  | 0 => AlgHom.id ℂ _
  | k + 1 => (addRightBraidAlgebra X (n + k)).comp (addRightBraidAlgebraIter X n k)

/-- Repeated insertion acts as expected on every actual braid. -/
theorem addRightBraidAlgebraIter_group (X : C) (n : ℕ) :
    ∀ (k : ℕ) (g : braidImage X n),
      addRightBraidAlgebraIter X n k (groupInImage (braidEndRepresentation X n) g) =
        groupInImage (braidEndRepresentation X (n + k)) (addRightStrands X n k g)
  | 0, g => rfl
  | k + 1, g => by
    change addRightBraidAlgebra X (n + k)
      (addRightBraidAlgebraIter X n k (groupInImage (braidEndRepresentation X n) g)) = _
    rw [addRightBraidAlgebraIter_group X n k g, addRightBraidAlgebra_group]
    rfl

/-- Repeated right insertion expressed in unitary matrix blocks. -/
def addRightBlocksIter (X : C) (n k : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + k) ≃ₐ[ℂ] ∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ) :
    (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ]
      (∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ) :=
  f.toAlgHom.comp ((addRightBraidAlgebraIter X n k).comp e.symm.toAlgHom)

set_option backward.isDefEq.respectTransparency false in
/-- Repeated right identity-strand insertion is star-preserving in independently
chosen unitary block presentations. -/
theorem addRightBlocksIter_star (X : C) (n k : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + k) ≃ₐ[ℂ] ∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ)
    (he : ∀ g i, e (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hf : ∀ g i, f (groupInImage (braidEndRepresentation X (n + k)) g) i ∈
      Matrix.unitaryGroup (Fin (q i)) ℂ)
    (x : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    addRightBlocksIter X n k e f (star x) = star (addRightBlocksIter X n k e f x) := by
  apply presented_intertwiner_map_star (braidEndRepresentation X n)
    (braidEndRepresentation X (n + k)) (addRightStrands X n k) e f he hf
    (addRightBlocksIter X n k e f)
  intro g
  change f (addRightBraidAlgebraIter X n k (e.symm (e (groupInImage (braidEndRepresentation X n) g)))) = _
  rw [e.symm_apply_apply, addRightBraidAlgebraIter_group]
  rfl

/-- The repeated identity-strand insertion as a star algebra map. -/
def addRightBlocksIterStarMap (X : C) (n k : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + k) ≃ₐ[ℂ] ∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ)
    (he : ∀ g i, e (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hf : ∀ g i, f (groupInImage (braidEndRepresentation X (n + k)) g) i ∈
      Matrix.unitaryGroup (Fin (q i)) ℂ) :
    (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →⋆ₐ[ℂ]
      (∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ) where
  toAlgHom := addRightBlocksIter X n k e f
  map_star' := addRightBlocksIter_star X n k e f he hf


end PropertyF.Ground.Calculus
