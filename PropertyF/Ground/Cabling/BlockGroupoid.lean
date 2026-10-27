module
public import PropertyF.Ground.Cabling.PureBlocks
open CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- The component of a block-permuting automorphism from a block to its
permuted block. -/
def permutedBlockMap {I : Type} [Fintype I] (f : I → C) (a : Aut (⨁ f))
    (p : Equiv.Perm I) (i : I) : f i ⟶ f (p i) :=
  biproduct.ι f i ≫ a.asIso.hom ≫ biproduct.π f (p i)

/-- The corresponding block component reconstructs the restriction of the
automorphism to its original block. -/
theorem permutedBlockMap_inclusion {I : Type} [Fintype I] (f : I → C)
    (a : Aut (⨁ f)) (p : Equiv.Perm I) (h : permutesBlocks f a p) (i : I) :
    biproduct.ι f i ≫ a.asIso.hom = permutedBlockMap f a p i ≫ biproduct.ι f (p i) := by
  have hi := h i
  have hh := congrArg (fun z => biproduct.ι f i ≫ z) hi
  simpa [permutedBlockMap, Category.assoc] using hh

/-- Components of a product are composites of the matching block maps.
The reversed order matches the automorphism group's multiplication. -/
theorem permutedBlockMap_mul {I : Type} [Fintype I] (f : I → C)
    (a b : Aut (⨁ f)) (p q : Equiv.Perm I)
    (hb : permutesBlocks f b q) (i : I) :
    permutedBlockMap f (a*b) (p*q) i =
      permutedBlockMap f b q i ≫ permutedBlockMap f a p (q i) := by
  have hh := congrArg (fun z => z ≫ a.asIso.hom ≫ biproduct.π f (p (q i)))
    (permutedBlockMap_inclusion f b q hb i)
  simpa [permutedBlockMap, Aut.mul_asIso, Equiv.Perm.mul_apply, Category.assoc] using hh

/-- The inverse automorphism induces the inverse block map. -/
def permutedBlockIso {I : Type} [Fintype I] (f : I → C)
    (a : Aut (⨁ f)) (p : Equiv.Perm I) (h : permutesBlocks f a p) (i : I) :
    f i ≅ f (p i) where
  hom := permutedBlockMap f a p i
  inv := biproduct.ι f (p i) ≫ a.asIso.inv ≫ biproduct.π f i
  hom_inv_id := by
    have hi := permutedBlockMap_inclusion f a p h i
    have hh := congrArg (fun z => z ≫ a.asIso.inv ≫ biproduct.π f i) hi
    simpa [Category.assoc] using hh.symm
  inv_hom_id := by
    have hi := permutedBlockMap_inclusion f a⁻¹ p⁻¹ (permutesBlocks_inv f h) (p i)
    have hp : p⁻¹ (p i) = i := Equiv.symm_apply_apply p i
    unfold permutedBlockMap at hi
    rw [hp] at hi
    have hi' : biproduct.ι f (p i) ≫ a.asIso.inv =
        (biproduct.ι f (p i) ≫ a.asIso.inv ≫ biproduct.π f i) ≫ biproduct.ι f i := by
      simpa [Category.assoc] using hi
    have hh := congrArg (fun z => z ≫ a.asIso.hom ≫ biproduct.π f (p i)) hi'
    simpa [permutedBlockMap, Category.assoc] using hh.symm
end PropertyF
