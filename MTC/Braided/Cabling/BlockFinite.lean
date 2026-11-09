module
public import MTC.Braided.Cabling.PureSum
public import Mathlib.Data.Fintype.Pi

/-! # Finiteness from finitely many preserved categorical blocks -/

@[expose] public noncomputable section
open CategoryTheory
open scoped BigOperators
namespace MTC.Braided.Cabling
universe v u w

/-- Endomorphisms preserving an identity resolution are determined by their diagonal blocks. -/
theorem preserved_block_hom_ext
    {C : Type u} [Category.{v} C] [Preadditive C]
    {I : Type w} [Fintype I] {B : I → C} {T : C}
    (ι : ∀ i, B i ⟶ T) (π : ∀ i, T ⟶ B i)
    (hresolution : (∑ i, π i ≫ ι i) = 𝟙 T)
    {f g : T ⟶ T}
    (hf : ∀ i, ι i ≫ f = (ι i ≫ f ≫ π i) ≫ ι i)
    (hg : ∀ i, ι i ≫ g = (ι i ≫ g ≫ π i) ≫ ι i)
    (hdiag : ∀ i, ι i ≫ f ≫ π i = ι i ≫ g ≫ π i) : f = g := by
  calc
    f = (∑ i, π i ≫ ι i) ≫ f := by rw [hresolution, Category.id_comp]
    _ = ∑ i, π i ≫ ((ι i ≫ f ≫ π i) ≫ ι i) := by
      simp only [Preadditive.sum_comp, Category.assoc, hf]
    _ = ∑ i, π i ≫ ((ι i ≫ g ≫ π i) ≫ ι i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hdiag i]
    _ = (∑ i, π i ≫ ι i) ≫ g := by
      simp only [Preadditive.sum_comp, Category.assoc, hg]
    _ = g := by rw [hresolution, Category.id_comp]


/-- An injective family of automorphisms preserving finitely many blocks is
finite when the diagonal action on every block has finite range. -/
theorem finite_type_of_finite_preserved_blocks
    {C : Type u} [Category.{v} C] [Preadditive C]
    {I : Type w} [Fintype I] {B : I → C} {T : C}
    (ι : ∀ i, B i ⟶ T) (π : ∀ i, T ⟶ B i)
    (hresolution : (∑ i, π i ≫ ι i) = 𝟙 T)
    {A : Type*} (g : A → Aut T) (hg : Function.Injective g)
    (hpreserve : ∀ (h : A) i,
      ι i ≫ (g h).asIso.hom = (ι i ≫ (g h).asIso.hom ≫ π i) ≫ ι i)
    (hfinite : ∀ i, Set.Finite (Set.range fun h : A => ι i ≫ (g h).asIso.hom ≫ π i)) :
    Finite A := by
  classical
  let diag (i : I) (h : A) := ι i ≫ (g h).asIso.hom ≫ π i
  letI (i : I) : Finite {f : B i ⟶ B i // f ∈ Set.range (diag i)} :=
    (hfinite i).to_subtype
  letI (i : I) : Fintype {f : B i ⟶ B i // f ∈ Set.range (diag i)} := Fintype.ofFinite _
  let F : A → ∀ i, {f : B i ⟶ B i // f ∈ Set.range (diag i)} :=
    fun h i => ⟨diag i h, ⟨h, rfl⟩⟩
  apply Finite.of_injective F
  intro h k hk
  have hd (i : I) : diag i h = diag i k := congrArg (fun f => (f i).val) hk
  apply hg
  apply Aut.ext
  apply Iso.ext
  exact preserved_block_hom_ext ι π hresolution (hpreserve h) (hpreserve k) hd


/-- The subgroup version of the finite preserved-block criterion. -/
theorem finite_subgroup_of_finite_preserved_blocks
    {C : Type u} [Category.{v} C] [Preadditive C]
    {I : Type w} [Fintype I] (B : I → C) (T : C)
    (ι : ∀ i, B i ⟶ T) (π : ∀ i, T ⟶ B i)
    (hresolution : (∑ i, π i ≫ ι i) = 𝟙 T)
    (H : Subgroup (Aut T))
    (hpreserve : ∀ (h : H) i,
      ι i ≫ (h : Aut T).asIso.hom = (ι i ≫ (h : Aut T).asIso.hom ≫ π i) ≫ ι i)
    (hfinite : ∀ i, Set.Finite (Set.range fun h : H => ι i ≫ (h : Aut T).asIso.hom ≫ π i)) :
    Finite H :=
  finite_type_of_finite_preserved_blocks ι π hresolution (fun h : H => h)
    Subtype.val_injective hpreserve hfinite

end MTC.Braided.Cabling
end

/-! # From finite blockwise pure-word actions to finite braid images -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace MTC.Braided.Cabling
universe v u w

/-- A finite family of preserved blocks with finite diagonal ranges makes
an actual braid image finite. The ranges are taken over the pure braid image,
not over a chosen set of word representatives. -/
theorem finite_braidImage_of_finite_actual_pure_blocks
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]
    {I : Type w} [Fintype I] (Y : C) (n : ℕ) {B : I → C}
    (ι : ∀ i, B i ⟶ tensorPower Y (n+2))
    (π : ∀ i, tensorPower Y (n+2) ⟶ B i)
    (hresolution : (∑ i, π i ≫ ι i) = 𝟙 (tensorPower Y (n+2)))
    (hpreserve : ∀ (h : pureBraidImage Y n) i,
      ι i ≫ h.val.val.asIso.hom = (ι i ≫ h.val.val.asIso.hom ≫ π i) ≫ ι i)
    (hfinite : ∀ i, Set.Finite (Set.range fun h : pureBraidImage Y n =>
      ι i ≫ h.val.val.asIso.hom ≫ π i)) :
    Finite (braidImage Y n) := by
  apply braidImage_finite_of_pureBraidImage_finite Y n
  exact finite_type_of_finite_preserved_blocks ι π hresolution
    (fun h : pureBraidImage Y n => h.val.val)
    (fun _ _ h => Subtype.ext (Subtype.ext h)) hpreserve hfinite

/-- A braid image is finite if its pure words preserve a finite family of
blocks resolving the identity and have finite diagonal range on each block. -/
theorem finite_braidImage_of_finite_pure_block_ranges
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]
    {I : Type w} [Fintype I] (Y : C) (n : ℕ)
    (B : I → C) (ι : ∀ i, B i ⟶ tensorPower Y (n+2))
    (π : ∀ i, tensorPower Y (n+2) ⟶ B i)
    (hresolution : (∑ i, π i ≫ ι i) = 𝟙 (tensorPower Y (n+2)))
    (hpreserve : ∀ (w : (strandPermutation n).ker) i,
      ι i ≫ ((braidWordAction Y n w.val).val).asIso.hom =
        (ι i ≫ ((braidWordAction Y n w.val).val).asIso.hom ≫ π i) ≫ ι i)
    (hfinite : ∀ i, Set.Finite (Set.range fun w : (strandPermutation n).ker =>
      ι i ≫ ((braidWordAction Y n w.val).val).asIso.hom ≫ π i)) :
    Finite (braidImage Y n) := by
  let f := (braidWordAction Y n).subgroupMap ((strandPermutation n).ker)
  have hf : Function.Surjective f := MonoidHom.subgroupMap_surjective _ _
  apply finite_braidImage_of_finite_actual_pure_blocks Y n ι π hresolution
  · intro h i
    obtain ⟨w, rfl⟩ := hf h
    exact hpreserve w i
  · intro i
    have heq := hf.range_comp (fun h : pureBraidImage Y n => ι i ≫ h.val.val.asIso.hom ≫ π i)
    exact heq ▸ hfinite i

end MTC.Braided.Cabling
end
