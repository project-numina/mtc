module
public import PropertyF.Ground.Cabling.BlockGroupoid
open CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- A property of block morphisms that contains identities and is closed under
composition and inversion of isomorphisms. -/
structure BlockMorphismClass {I : Type} (f : I → C) where
  holds : ∀ i j, (f i ⟶ f j) → Prop
  id_mem : ∀ i, holds i i (𝟙 _)
  comp_mem : ∀ {i j k} {g : f i ⟶ f j} {h : f j ⟶ f k},
    holds i j g → holds j k h → holds i k (g ≫ h)
  inv_mem : ∀ {i j} (e : f i ≅ f j), holds i j e.hom → holds j i e.inv

/-- If all generator block maps belong to a class stable under composition
and inversion, then all braid-word block maps belong to that class. -/
theorem braidWords_blockMaps_mem {I : Type} [Fintype I] (f : I → C)
    (n : ℕ) (ρ : BraidWords n →* Aut (⨁ f)) (π : BraidWords n →* Equiv.Perm I)
    (hperm : ∀ i, permutesBlocks f (ρ (FreeGroup.of i)) (π (FreeGroup.of i)))
    (P : BlockMorphismClass f)
    (hgen : ∀ j i, P.holds i (π (FreeGroup.of j) i)
      (permutedBlockMap f (ρ (FreeGroup.of j)) (π (FreeGroup.of j)) i)) :
    ∀ w i, P.holds i (π w i) (permutedBlockMap f (ρ w) (π w) i) := by
  intro w
  induction w using FreeGroup.induction_on with
  | one =>
    intro i
    rw [map_one, map_one]
    simpa [permutedBlockMap] using P.id_mem i
  | of j => exact hgen j
  | inv_of j ih =>
    intro i
    let p := π (FreeGroup.of j)
    let a := ρ (FreeGroup.of j)
    let k := p⁻¹ i
    have hp : p k = i := Equiv.apply_symm_apply p i
    let e := permutedBlockIso f a p (hperm j) k
    have he : P.holds k (p k) e.hom := hgen j k
    have hi := P.inv_mem e he
    change P.holds (p k) k (biproduct.ι f (p k) ≫ a.asIso.inv ≫ biproduct.π f k) at hi
    rw [hp] at hi
    rw [map_inv, map_inv]
    change P.holds i (p⁻¹ i) (permutedBlockMap f a⁻¹ p⁻¹ i)
    simpa [permutedBlockMap, k] using hi
  | mul x y ihx ihy =>
    intro i
    have hb := braidWords_permuteBlocks f n ρ π hperm y
    have hm := P.comp_mem (ihy i) (ihx (π y i))
    rw [← permutedBlockMap_mul f (ρ x) (ρ y) (π x) (π y) hb i] at hm
    rw [map_mul, map_mul]
    exact hm
end PropertyF
