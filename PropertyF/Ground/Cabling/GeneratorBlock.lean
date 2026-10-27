module
public import PropertyF.Ground.Cabling.TupleCrossing
public import PropertyF.Ground.Cabling.CableClass
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C]
attribute [local instance] Abelian.hasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
/-- The component of a cabled crossing is its mixed tuple crossing conjugated
by the canonical tuple-to-power comparisons. -/
theorem powerSum_generator_blockMap (X : C) (k : Fin count → ℕ)
    (n : ℕ) (j : Fin (n+1)) (t : Fin (n+2) → Fin count) :
    ∃ g : tupleTensor (fun a => tensorPower X (k a)) (n+2) t ⟶
        tupleTensor (fun a => tensorPower X (k a)) (n+2) (swapTuple j t),
      tupleTensorInclusion (fun a => tensorPower X (k a)) (n+2) t ≫
        (braidGenerator (⨁ fun a => tensorPower X (k a)) n j).asIso.hom =
          g ≫ tupleTensorInclusion (fun a => tensorPower X (k a)) (n+2) (swapTuple j t) ∧
      permutedBlockMap (powerSumBlock X k n) (sumPowerWordAction X k n (FreeGroup.of j))
        (((tuplePermutation (Fin count) (n+2)).comp (strandPermutation n)) (FreeGroup.of j)) t =
        (tupleTensorPowersIso X k (n+2) t).inv ≫ g ≫
          (tupleTensorPowersIso X k (n+2) (swapTuple j t)).hom := by
  classical
  let f := fun a : Fin count => tensorPower X (k a)
  let E := sumPowersTensorPowerIso X k (n+2)
  let p := ((tuplePermutation (Fin count) (n+2)).comp (strandPermutation n)) (FreeGroup.of j)
  have hp : p t = swapTuple j t := by
    rfl
  obtain ⟨g, hg⟩ := tuple_cross f n j t
  refine ⟨g, hg, ?_⟩
  have hι := sumPowersTensorPowerIso_ι_inv X k (n+2) t
  have hι' := sumPowersTensorPowerIso_ι_inv X k (n+2) (swapTuple j t)
  change biproduct.ι (powerSumBlock X k n) t ≫ E.inv = _ at hι
  change biproduct.ι (powerSumBlock X k n) (swapTuple j t) ≫ E.inv = _ at hι'
  have hproj : tupleTensorInclusion f (n+2) (swapTuple j t) ≫ E.hom ≫
      biproduct.π (powerSumBlock X k n) (swapTuple j t) =
        (tupleTensorPowersIso X k (n+2) (swapTuple j t)).hom := by
    have h := congrArg (fun z => (tupleTensorPowersIso X k (n+2) (swapTuple j t)).hom ≫ z ≫
      E.hom ≫ biproduct.π (powerSumBlock X k n) (swapTuple j t)) hι'
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
      biproduct.ι_π_self, Category.comp_id, Category.id_comp] at h
    change (tupleTensorPowersIso X k (n+2) (swapTuple j t)).hom ≫
      𝟙 (tensorPower X (∑ i, k (swapTuple j t i))) =
      tupleTensorInclusion f (n+2) (swapTuple j t) ≫ E.hom ≫
        biproduct.π (powerSumBlock X k n) (swapTuple j t) at h
    rw [Category.comp_id] at h
    exact h.symm
  dsimp only [permutedBlockMap]
  have heval : sumPowerWordAction X k n (FreeGroup.of j) =
      E.conjAut (braidGenerator (⨁ f) n j) := by
    change E.conjAut ((FreeGroup.lift (braidGenerator (⨁ f) n)) (FreeGroup.of j)) = _
    rw [FreeGroup.lift_apply_of]
  rw [heval]
  change biproduct.ι (powerSumBlock X k n) t ≫
    (E.conjAut (braidGenerator (⨁ f) n j)).asIso.hom ≫
      biproduct.π (powerSumBlock X k n) (swapTuple j t) = _
  simp only [Iso.conjAut_apply, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, hι]
  simp only [Category.assoc]
  rw [← Category.assoc (tupleTensorInclusion f (n+2) t), hg]
  simp only [Category.assoc]
  rw [hproj]
end PropertyF
