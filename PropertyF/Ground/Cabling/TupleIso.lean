module
public import PropertyF.Ground.Cabling.TupleCrossing
public import PropertyF.Ground.Cabling.GeneratorBlock
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- A categorical generator acts on every tuple block by a canonical mixed
braiding isomorphism. -/
theorem tuple_cross_iso {I : Type} [Fintype I] (f : I → C) :
    ∀ (n : ℕ) (i : Fin (n + 1)) (t : Fin (n + 2) → I),
      ∃ e : tupleTensor f (n + 2) t ≅ tupleTensor f (n + 2) (swapTuple i t),
        tupleTensorInclusion f (n + 2) t ≫ (braidGenerator (⨁ f) n i).asIso.hom =
          e.hom ≫ tupleTensorInclusion f (n + 2) (swapTuple i t) := by
  intro n
  induction n with
  | zero =>
    intro i t
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rw [swapTuple_zero]
    exact ⟨firstMixedBraid (f (t 0)) (f (t 1)) (tupleTensor f 0 (Fin.tail (Fin.tail t))),
      firstBraid_components f (t 0) (t 1) 0 (Fin.tail (Fin.tail t))⟩
  | succ n ih =>
    intro i t
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [swapTuple_zero]
      exact ⟨firstMixedBraid (f (t 0)) (f (t 1)) (tupleTensor f (n+1) (Fin.tail (Fin.tail t))),
        firstBraid_components f (t 0) (t 1) (n+1) (Fin.tail (Fin.tail t))⟩
    · obtain ⟨e, he⟩ := ih j (Fin.tail t)
      rw [swapTuple_succ]
      refine ⟨Iso.refl (f (t 0)) ⊗ᵢ e, ?_⟩
      exact tailBraid_components f (t 0) n j _ _ _ _ e.hom he
/-- Projection from a tensor power of a biproduct to a tuple block. -/
def tupleTensorProjection {I : Type} [Fintype I] (f : I → C) :
    ∀ (n : ℕ) (t : Fin n → I), tensorPower (⨁ f) n ⟶ tupleTensor f n t
  | 0, _ => 𝟙 _
  | n+1, t => biproduct.π f (t 0) ⊗ₘ tupleTensorProjection f n (Fin.tail t)

set_option backward.isDefEq.respectTransparency false in
/-- Tuple inclusions have explicit retractions. -/
theorem tupleTensorInclusion_split {I : Type} [Fintype I] (f : I → C) :
    ∀ (n : ℕ) (t : Fin n → I),
      tupleTensorInclusion f n t ≫ tupleTensorProjection f n t = 𝟙 _
  | 0, _ => by
    change (𝟙 (𝟙_ C)) ≫ 𝟙 (𝟙_ C) = 𝟙 (𝟙_ C)
    simp
  | n+1, t => by
    change (biproduct.ι f (t 0) ⊗ₘ tupleTensorInclusion f n (Fin.tail t)) ≫
      (biproduct.π f (t 0) ⊗ₘ tupleTensorProjection f n (Fin.tail t)) = 𝟙 _
    rw [tensorHom_comp_tensorHom, biproduct.ι_π_self, tupleTensorInclusion_split f n (Fin.tail t)]
    exact id_tensorHom_id _ _

/-- The map induced on a tuple is uniquely determined by its inclusion into
the tensor power. -/
theorem tupleTensorInclusion_cancel {I : Type} [Fintype I] (f : I → C)
    (n : ℕ) (t : Fin n → I) {A : C} (g h : A ⟶ tupleTensor f n t)
    (eq : g ≫ tupleTensorInclusion f n t = h ≫ tupleTensorInclusion f n t) : g = h := by
  have hh := congrArg (fun z => z ≫ tupleTensorProjection f n t) eq
  simpa [Category.assoc, tupleTensorInclusion_split] using hh
/-- The local generator-block condition follows from the cabled membership
of the mixed tuple crossing itself. -/
theorem powerSum_generator_cableHom_of_tuple_crossings (X : C) (k : Fin count → ℕ)
    (n : ℕ)
    (hlocal : ∀ (j : Fin (n+1)) (t : Fin (n+2) → Fin count),
      ∃ e : tupleTensor (fun a => tensorPower X (k a)) (n+2) t ≅
          tupleTensor (fun a => tensorPower X (k a)) (n+2) (swapTuple j t),
        tupleTensorInclusion (fun a => tensorPower X (k a)) (n+2) t ≫
          (braidGenerator (⨁ fun a => tensorPower X (k a)) n j).asIso.hom =
            e.hom ≫ tupleTensorInclusion (fun a => tensorPower X (k a)) (n+2) (swapTuple j t) ∧
        cableHom X (∑ i, k (t i)) (∑ i, k (swapTuple j t i))
          ((tupleTensorPowersIso X k (n+2) t).inv ≫ e.hom ≫
            (tupleTensorPowersIso X k (n+2) (swapTuple j t)).hom)) :
    ∀ (j : Fin (n+1)) (t : Fin (n+2) → Fin count),
      cableHom X (∑ i, k (t i))
        (∑ i, k ((((tuplePermutation (Fin count) (n+2)).comp (strandPermutation n)) (FreeGroup.of j)) t i))
        (permutedBlockMap (powerSumBlock X k n) (sumPowerWordAction X k n (FreeGroup.of j))
          (((tuplePermutation (Fin count) (n+2)).comp (strandPermutation n)) (FreeGroup.of j)) t) := by
  intro j t
  obtain ⟨g, hg, hgmap⟩ := powerSum_generator_blockMap X k n j t
  obtain ⟨e, he, hmem⟩ := hlocal j t
  have hge : g = e.hom := tupleTensorInclusion_cancel
    (fun a => tensorPower X (k a)) (n+2) (swapTuple j t) g e.hom (hg.symm.trans he)
  rw [hgmap, hge]
  exact hmem
end PropertyF
