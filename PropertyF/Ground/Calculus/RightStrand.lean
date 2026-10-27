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

end PropertyF.Ground.Calculus
