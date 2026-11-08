module
public import MTC.Braided.Cabling.PureSum
public import Mathlib.Data.Fintype.Pi

/-! # Finiteness from finitely many preserved categorical blocks -/

@[expose] public noncomputable section
open CategoryTheory
open scoped BigOperators
namespace MTC.Braided.Cabling
universe v u w

/-- If a subgroup preserves finitely many blocks that resolve the identity,
and every diagonal block has only finitely many possible actions, then the
subgroup itself is finite. No orthogonality of the blocks is needed. -/
theorem finite_subgroup_of_finite_preserved_blocks
    {C : Type u} [Category.{v} C] [Preadditive C]
    {I : Type w} [Fintype I] (B : I → C) (T : C)
    (ι : ∀ i, B i ⟶ T) (π : ∀ i, T ⟶ B i)
    (hresolution : (∑ i, π i ≫ ι i) = 𝟙 T)
    (H : Subgroup (Aut T))
    (hpreserve : ∀ (h : H) i,
      ι i ≫ (h : Aut T).asIso.hom = (ι i ≫ (h : Aut T).asIso.hom ≫ π i) ≫ ι i)
    (hfinite : ∀ i, Set.Finite (Set.range fun h : H => ι i ≫ (h : Aut T).asIso.hom ≫ π i)) :
    Finite H := by
  classical
  let diag (i : I) (h : H) := ι i ≫ (h : Aut T).asIso.hom ≫ π i
  letI (i : I) : Finite {f : B i ⟶ B i // f ∈ Set.range (diag i)} :=
    (hfinite i).to_subtype
  letI (i : I) : Fintype {f : B i ⟶ B i // f ∈ Set.range (diag i)} := Fintype.ofFinite _
  let F : H → ∀ i, {f : B i ⟶ B i // f ∈ Set.range (diag i)} :=
    fun h i => ⟨diag i h, ⟨h, rfl⟩⟩
  apply Finite.of_injective F
  intro h k hk
  have hd (i : I) : diag i h = diag i k := congrArg (fun f => (f i).val) hk
  have he : (h : Aut T).asIso.hom = (k : Aut T).asIso.hom := by
    calc
      (h : Aut T).asIso.hom = (∑ i, π i ≫ ι i) ≫ (h : Aut T).asIso.hom := by rw [hresolution, Category.id_comp]
      _ = ∑ i, π i ≫ ((ι i ≫ (h : Aut T).asIso.hom ≫ π i) ≫ ι i) := by
        simp only [Preadditive.sum_comp, Category.assoc, hpreserve]
      _ = ∑ i, π i ≫ ((ι i ≫ (k : Aut T).asIso.hom ≫ π i) ≫ ι i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show ι i ≫ (h : Aut T).asIso.hom ≫ π i = ι i ≫ (k : Aut T).asIso.hom ≫ π i from hd i]
      _ = (∑ i, π i ≫ ι i) ≫ (k : Aut T).asIso.hom := by
        simp only [Preadditive.sum_comp, Category.assoc, hpreserve]
      _ = (k : Aut T).asIso.hom := by rw [hresolution, Category.id_comp]
  exact Subtype.ext (Aut.ext (Iso.ext he))

end MTC.Braided.Cabling
end
