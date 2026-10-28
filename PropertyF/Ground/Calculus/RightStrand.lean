module
public import PropertyF.Ground.Calculus.UnitaryBlocks
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import PropertyF.Ground.Cabling.Strands
public import PropertyF.Ground.Calculus.EndBlocks
public import Mathlib.Tactic

/-! Compatibility of adjoints on algebras spanned by braid images. -/

@[expose] public section
namespace PropertyF.Ground.Calculus

variable {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
  [StarRing A] [StarRing B] [StarModule ℂ A] [StarModule ℂ B]

/-- A complex algebra map that preserves the adjoint of each generator preserves
it on their entire linear span. In particular this applies to identity-strand
embeddings once the braids are represented by unitary matrices. -/
theorem map_star_of_mem_span (φ : A →ₐ[ℂ] B) (S : Set A)
    (hS : ∀ x ∈ S, φ (star x) = star (φ x))
    {x : A} (hx : x ∈ Submodule.span ℂ S) : φ (star x) = star (φ x) :=
  Submodule.span_induction hS (by simp)
    (fun _ _ _ _ hx hy => by simp [hx, hy])
    (fun _ _ _ hx => by simp [star_smul, hx]) hx

/-- A unitary matrix's adjoint is the inverse of the corresponding unit. -/
theorem star_eq_coe_inv_of_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : (Matrix ι ι ℂ)ˣ) (hu : (u : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ) :
    star (u : Matrix ι ι ℂ) = (↑u⁻¹ : Matrix ι ι ℂ) :=
  u.eq_inv_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff'.mp hu)

/-- If a group spans an algebra and two representations have adjoint equal to
inverse on group elements, every intertwining algebra map preserves adjoints.
This captures identity-strand maps without assuming injectivity or surjectivity. -/
theorem map_star_of_group_span {G H : Type*} [Group G] [Group H]
    (ρ : G →* A) (σ : H →* B) (τ : G →* H) (φ : A →ₐ[ℂ] B)
    (hspan : Submodule.span ℂ (Set.range ρ) = ⊤)
    (hρ : ∀ g, star (ρ g) = ρ g⁻¹)
    (hσ : ∀ h, star (σ h) = σ h⁻¹)
    (hφ : ∀ g, φ (ρ g) = σ (τ g)) (x : A) :
    φ (star x) = star (φ x) :=
  map_star_of_mem_span φ (Set.range ρ)
    (fun _ h => by
      obtain ⟨g, rfl⟩ := h
      rw [hρ, hφ, hφ, hσ, map_inv])
    (hspan.symm ▸ Submodule.mem_top)

end PropertyF.Ground.Calculus

/-! Compatibility of unitary block realizations under maps of group images. -/

@[expose] public noncomputable section
namespace PropertyF.Ground.Calculus

variable {G H A B : Type*} [Group G] [Group H]
  [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

/-- The group image spans any algebra-equivalent block presentation. -/
theorem presented_group_span (ρ : G →* A) {n : ℕ} {d : Fin n → ℕ}
    (e : groupImageAlgebra ρ ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩) :
    Submodule.span ℂ (Set.range (e.toMonoidHom.comp (groupInImage ρ))) = ⊤ := by
  classical
  change Submodule.span ℂ (Set.range (fun g => e (groupInImage ρ g))) = ⊤
  rw [Set.range_comp']
  change Submodule.span ℂ (e.toLinearEquiv.toLinearMap '' Set.range (groupInImage ρ)) = ⊤
  rw [← Submodule.map_span, groupInImage_span, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.surjective

/-- A unitary block representation sends group inversion to conjugate transpose. -/
theorem unitary_block_star_inv {n : ℕ} {d : Fin n → ℕ}
    (ρ : G →* Blocks.Algebra ⟨_, d⟩)
    (hu : ∀ g, Blocks.IsUnitary ⟨_, d⟩ (ρ g)) (g : G) :
    star (ρ g) = ρ g⁻¹ :=
  funext fun i => star_eq_coe_inv_of_unitary (((Pi.evalMonoidHom _ i).comp ρ).toHomUnits g) (hu g i)

/-- Any algebra map intertwining two unitary block presentations is a star map.
This gives the analytic part of identity-strand compatibility; the categorical
strand map and its intertwining property must still be supplied separately. -/
theorem presented_intertwiner_map_star
    (ρ : G →* A) (σ : H →* B) (τ : G →* H)
    {n m : ℕ} {d : Fin n → ℕ} {k : Fin m → ℕ}
    (e : groupImageAlgebra ρ ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩)
    (f : groupImageAlgebra σ ≃ₐ[ℂ] Blocks.Algebra ⟨_, k⟩)
    (he : IsUnitaryPresentation ρ e)
    (hf : IsUnitaryPresentation σ f)
    (φ : (Blocks.Algebra ⟨_, d⟩) →ₐ[ℂ]
      (Blocks.Algebra ⟨_, k⟩))
    (hφ : ∀ g, φ (e (groupInImage ρ g)) = f (groupInImage σ (τ g)))
    (x : Blocks.Algebra ⟨_, d⟩) : φ (star x) = star (φ x) :=
  let ρ' := e.toMonoidHom.comp (groupInImage ρ)
  let σ' := f.toMonoidHom.comp (groupInImage σ)
  map_star_of_group_span ρ' σ' τ φ (presented_group_span ρ e)
    (unitary_block_star_inv ρ' he) (unitary_block_star_inv σ' hf) hφ x

end PropertyF.Ground.Calculus

/-! Algebra maps induced by intertwiners of categorical group images. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus

variable {G H A B : Type*} [Group G] [Group H]
  [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

/-- An algebra map intertwining group representations carries the image
algebra into the target image algebra. -/
def imageAlgebraMap (ρ : G →* A) (σ : H →* B) (τ : G →* H)
    (F : A →ₐ[ℂ] B) (hF : ∀ g, F (ρ g) = σ (τ g)) :
    groupImageAlgebra ρ →ₐ[ℂ] groupImageAlgebra σ := by
  let f := F.comp (groupImageAlgebra ρ).val
  refine f.codRestrict _ ?_
  intro x
  have hx : (x : A) ∈ Submodule.span ℂ (Set.range ρ) := by
    rw [← groupImageAlgebra_toSubmodule]
    exact x.property
  have hspan : Submodule.span ℂ (Set.range ρ) ≤
      ((groupImageAlgebra σ).toSubmodule.comap F.toLinearMap) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    change F (ρ g) ∈ groupImageAlgebra σ
    rw [hF]
    simpa using (groupInImage σ (τ g)).property
  exact hspan hx

/-- The induced algebra map intertwines the image-group representations. -/
theorem imageAlgebraMap_group (ρ : G →* A) (σ : H →* B) (τ : G →* H)
    (F : A →ₐ[ℂ] B) (hF : ∀ g, F (ρ g) = σ (τ g)) (g : G) :
    imageAlgebraMap ρ σ τ F hF (groupInImage ρ g) = groupInImage σ (τ g) :=
  Subtype.ext (by
    change F (groupInImage ρ g : A) = (groupInImage σ (τ g) : B)
    simpa using hF g)

universe v u v' u'
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [Linear ℂ C] [Linear ℂ D]

/-- A complex-linear additive functor acts by algebra homomorphisms on
endomorphisms. -/
def functorEndAlgHom (F : C ⥤ D) [F.Additive] [F.Linear ℂ] (X : C) :
    End X →ₐ[ℂ] End (F.obj X) where
  toFun := F.mapEnd X
  map_one' := (F.mapEnd X).map_one
  map_mul' := (F.mapEnd X).map_mul
  map_zero' := by
    apply End.ext
    simp
  map_add' x y := by
    apply End.ext
    simp
  commutes' z := by
    apply End.ext
    simp [Algebra.algebraMap_eq_smul_one]

variable [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
  [MonoidalLinear ℂ C]

/-- Adding an identity strand on the left induces an algebra map on the
actual braid-image spans. -/
def addLeftBraidAlgebra (X : C) (n : ℕ) : braidAlgebra X n →ₐ[ℂ] braidAlgebra X (n + 1) :=
  imageAlgebraMap (braidEndRepresentation X n) (braidEndRepresentation X (n + 1))
    (addLeftStrand X n) (functorEndAlgHom (tensorLeft X) (tensorPower X (n + 2))) (by
      intro g
      rfl)

/-- The identity-strand algebra map carries each actual braid to its inserted
copy. -/
theorem addLeftBraidAlgebra_group {X : C} {n : ℕ} (g : braidImage X n) :
    addLeftBraidAlgebra X n (braidInImage X n g) =
      braidInImage X (n + 1) (addLeftStrand X n g) := imageAlgebraMap_group _ _ _ _ _ g

/-- Repeated left identity-strand insertion on the actual image groups. -/
def addLeftStrands (X : C) (n : ℕ) : ∀ k, braidImage X n →* braidImage X (n + k)
  | 0 => MonoidHom.id _
  | k + 1 => (addLeftStrand X (n + k)).comp (addLeftStrands X n k)

/-- Repeated left identity-strand insertion on the actual braid algebras. -/
def addLeftBraidAlgebraIter (X : C) (n : ℕ) :
    ∀ k, braidAlgebra X n →ₐ[ℂ] braidAlgebra X (n + k)
  | 0 => AlgHom.id ℂ _
  | k + 1 => (addLeftBraidAlgebra X (n + k)).comp (addLeftBraidAlgebraIter X n k)

/-- Repeated insertion acts as expected on every actual braid. -/
theorem addLeftBraidAlgebraIter_group {X : C} {n : ℕ} :
    ∀ (k : ℕ) (g : braidImage X n),
      addLeftBraidAlgebraIter X n k (braidInImage X n g) =
        braidInImage X (n + k) (addLeftStrands X n k g)
  | 0, g => rfl
  | k + 1, g => by
    change addLeftBraidAlgebra X (n + k)
      (addLeftBraidAlgebraIter X n k (braidInImage X n g)) = _
    rw [addLeftBraidAlgebraIter_group k g, addLeftBraidAlgebra_group]
    rfl

/-- Repeated left insertion expressed in unitary matrix blocks. -/
def addLeftBlocksIter (X : C) (n k : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩)
    (f : braidAlgebra X (n + k) ≃ₐ[ℂ] Blocks.Algebra ⟨_, q⟩) :
    (Blocks.Algebra ⟨_, d⟩) →ₐ[ℂ]
      (Blocks.Algebra ⟨_, q⟩) :=
  f.toAlgHom.comp ((addLeftBraidAlgebraIter X n k).comp e.symm.toAlgHom)

set_option backward.isDefEq.respectTransparency false in
/-- Repeated left identity-strand insertion is star-preserving in independently
chosen unitary block presentations. -/
theorem addLeftBlocksIter_star {X : C} {n : ℕ} (k : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩)
    (f : braidAlgebra X (n + k) ≃ₐ[ℂ] Blocks.Algebra ⟨_, q⟩)
    (he : IsUnitaryBraidPresentation e)
    (hf : IsUnitaryBraidPresentation f)
    (x : Blocks.Algebra ⟨_, d⟩) :
    addLeftBlocksIter X n k e f (star x) = star (addLeftBlocksIter X n k e f x) := by
  apply presented_intertwiner_map_star (braidEndRepresentation X n)
    (braidEndRepresentation X (n + k)) (addLeftStrands X n k) e f he hf
    (addLeftBlocksIter X n k e f)
  intro g
  change f (addLeftBraidAlgebraIter X n k (e.symm (e (braidInImage X n g)))) = _
  rw [e.symm_apply_apply, addLeftBraidAlgebraIter_group]
  rfl

/-- The repeated identity-strand insertion as a star algebra map. -/
def addLeftBlocksIterStarMap (X : C) (n k : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩)
    (f : braidAlgebra X (n + k) ≃ₐ[ℂ] Blocks.Algebra ⟨_, q⟩)
    (he : IsUnitaryBraidPresentation e)
    (hf : IsUnitaryBraidPresentation f) :
    (Blocks.Algebra ⟨_, d⟩) →⋆ₐ[ℂ]
      (Blocks.Algebra ⟨_, q⟩) where
  toAlgHom := addLeftBlocksIter X n k e f
  map_star' := addLeftBlocksIter_star k e f he hf

end PropertyF.Ground.Calculus

/-! Right identity-strand insertion on categorical braid algebras. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Append one tensor factor to a right-associated tensor power. -/
def appendIso (X : C) : ∀ n : ℕ, tensorPower X n ⊗ X ≅ tensorPower X (n + 1)
  | 0 => (λ_ X) ≪≫ (ρ_ X).symm
  | n + 1 => by
    simpa only [tensorPower] using
      ((α_ X (tensorPower X n) X) ≪≫ (Iso.refl X ⊗ᵢ appendIso X n))

/-- Append an identity strand to an automorphism of a tensor power. -/
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
  (α_ X (tensorPower X n) X) ≪≫ (Iso.refl X ⊗ᵢ appendIso X n) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem addRightAut_generator (X : C) (n : ℕ) (i : Fin (n+1)) :
    addRightAut X n (braidGenerator X n i) = braidGenerator X (n+1) i.castSucc := by
  have first (n : ℕ) : addRightAut X n (braidGenerator X n 0) =
      braidGenerator X (n + 1) 0 := by
    apply Aut.ext
    apply Iso.ext
    change (appendIso X (n + 2)).inv ≫ ((braidGenerator X n 0).asIso.hom ▷ X) ≫
      (appendIso X (n + 2)).hom = (braidGenerator X (n + 1) 0).asIso.hom
    simp only [← Fin.zero_eta, braidGenerator.eq_1, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
      tensorHom_id]
    change (appendIso X (n + 2)).inv ≫
      (((α_ X X (tensorPower X n)).inv ≫ (β_ X X).hom ▷ tensorPower X n ≫
        (α_ X X (tensorPower X n)).hom) ▷ X) ≫ (appendIso X (n + 2)).hom =
      (α_ X X (tensorPower X (n + 1))).inv ≫ (β_ X X).hom ▷ tensorPower X (n + 1) ≫
        (α_ X X (tensorPower X (n + 1))).hom
    rw [appendIso_succ X (n + 1), appendIso_succ X n]
    exact append_first_two X _ _ (appendIso X n)
  induction n with
  | zero => exact (Fin.eq_zero i).symm ▸ first 0
  | succ n ih =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => exact first (n + 1)
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
    exact Subgroup.subset_closure ⟨i.castSucc, (addRightAut_generator X n i).symm⟩
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
theorem addRightBraidAlgebra_group {X : C} {n : ℕ} (g : braidImage X n) :
    addRightBraidAlgebra X n (braidInImage X n g) =
      braidInImage X (n + 1) (addRightStrand X n g) := imageAlgebraMap_group _ _ _ _ _ g

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
theorem addRightBraidAlgebraIter_group {X : C} {n : ℕ} :
    ∀ (k : ℕ) (g : braidImage X n),
      addRightBraidAlgebraIter X n k (braidInImage X n g) =
        braidInImage X (n + k) (addRightStrands X n k g)
  | 0, g => rfl
  | k + 1, g => by
    change addRightBraidAlgebra X (n + k)
      (addRightBraidAlgebraIter X n k (braidInImage X n g)) = _
    rw [addRightBraidAlgebraIter_group k g, addRightBraidAlgebra_group]
    rfl

/-- Repeated right insertion expressed in unitary matrix blocks. -/
def addRightBlocksIter (X : C) (n k : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩)
    (f : braidAlgebra X (n + k) ≃ₐ[ℂ] Blocks.Algebra ⟨_, q⟩) :
    (Blocks.Algebra ⟨_, d⟩) →ₐ[ℂ]
      (Blocks.Algebra ⟨_, q⟩) :=
  f.toAlgHom.comp ((addRightBraidAlgebraIter X n k).comp e.symm.toAlgHom)

set_option backward.isDefEq.respectTransparency false in
/-- Repeated right identity-strand insertion is star-preserving in independently
chosen unitary block presentations. -/
theorem addRightBlocksIter_star {X : C} {n : ℕ} (k : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩)
    (f : braidAlgebra X (n + k) ≃ₐ[ℂ] Blocks.Algebra ⟨_, q⟩)
    (he : IsUnitaryBraidPresentation e)
    (hf : IsUnitaryBraidPresentation f)
    (x : Blocks.Algebra ⟨_, d⟩) :
    addRightBlocksIter X n k e f (star x) = star (addRightBlocksIter X n k e f x) := by
  apply presented_intertwiner_map_star (braidEndRepresentation X n)
    (braidEndRepresentation X (n + k)) (addRightStrands X n k) e f he hf
    (addRightBlocksIter X n k e f)
  intro g
  change f (addRightBraidAlgebraIter X n k (e.symm (e (braidInImage X n g)))) = _
  rw [e.symm_apply_apply, addRightBraidAlgebraIter_group]
  rfl

/-- The repeated identity-strand insertion as a star algebra map. -/
def addRightBlocksIterStarMap (X : C) (n k : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩)
    (f : braidAlgebra X (n + k) ≃ₐ[ℂ] Blocks.Algebra ⟨_, q⟩)
    (he : IsUnitaryBraidPresentation e)
    (hf : IsUnitaryBraidPresentation f) :
    (Blocks.Algebra ⟨_, d⟩) →⋆ₐ[ℂ]
      (Blocks.Algebra ⟨_, q⟩) where
  toAlgHom := addRightBlocksIter X n k e f
  map_star' := addRightBlocksIter_star k e f he hf

end PropertyF.Ground.Calculus
