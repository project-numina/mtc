module
public import MTC.Braided.Cabling.PureSum
public import Mathlib.Data.Fintype.Pi

/-! # Finiteness from finitely many preserved categorical blocks -/

@[expose] public noncomputable section
open CategoryTheory
open scoped BigOperators
namespace MTC.Braided.Cabling
universe v u w

/-- An injective family of automorphisms preserving finitely many blocks is
finite when the diagonal action on every block has finite range. -/
theorem finite_type_of_finite_preserved_blocks
    {C : Type u} [Category.{v} C] [Preadditive C]
    {I : Type w} [Fintype I] (B : I → C) (T : C)
    (ι : ∀ i, B i ⟶ T) (π : ∀ i, T ⟶ B i)
    (hresolution : (∑ i, π i ≫ ι i) = 𝟙 T)
    (A : Type*) (g : A → Aut T) (hg : Function.Injective g)
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
  have he : (g h).asIso.hom = (g k).asIso.hom := by
    calc
      (g h).asIso.hom = (∑ i, π i ≫ ι i) ≫ (g h).asIso.hom := by rw [hresolution, Category.id_comp]
      _ = ∑ i, π i ≫ ((ι i ≫ (g h).asIso.hom ≫ π i) ≫ ι i) := by
        simp only [Preadditive.sum_comp, Category.assoc, hpreserve]
      _ = ∑ i, π i ≫ ((ι i ≫ (g k).asIso.hom ≫ π i) ≫ ι i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show ι i ≫ (g h).asIso.hom ≫ π i = ι i ≫ (g k).asIso.hom ≫ π i from hd i]
      _ = (∑ i, π i ≫ ι i) ≫ (g k).asIso.hom := by
        simp only [Preadditive.sum_comp, Category.assoc, hpreserve]
      _ = (g k).asIso.hom := by rw [hresolution, Category.id_comp]
  exact hg (Aut.ext (Iso.ext he))

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
  finite_type_of_finite_preserved_blocks B T ι π hresolution H (fun h => h)
    Subtype.val_injective hpreserve hfinite

end MTC.Braided.Cabling
end
