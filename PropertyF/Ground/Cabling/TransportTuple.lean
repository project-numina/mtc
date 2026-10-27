module
public import PropertyF.Ground.Cabling.CablingDiagram
public import PropertyF.Ground.Cabling.TensorComponents
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C] [MonoidalPreadditive C]
attribute [local instance] Abelian.hasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
/-- A crossing's action on tuple inclusions implies its action on cabled
block projectors. -/
theorem powerSum_permutesBlocks_of_tupleInclusions (X : C) (k : Fin count → ℕ)
    (n : ℕ) (i : Fin (n + 1)) (p : Equiv.Perm (Fin (n + 2) → Fin count))
    (h : ∀ t, ∃ g : tupleTensor (fun a => tensorPower X (k a)) (n + 2) t ⟶
          tupleTensor (fun a => tensorPower X (k a)) (n + 2) (p t),
      tupleTensorInclusion (fun a => tensorPower X (k a)) (n + 2) t ≫
          (braidGenerator (⨁ fun a => tensorPower X (k a)) n i).asIso.hom =
        g ≫ tupleTensorInclusion (fun a => tensorPower X (k a)) (n + 2) (p t)) :
    permutesBlocks (powerSumBlock X k n)
      ((sumPowersTensorPowerIso X k (n + 2)).conjAut
        (braidGenerator (⨁ fun a => tensorPower X (k a)) n i)) p := by
  classical
  apply transport_permutesBlocks_of_inclusions (powerSumBlock X k n)
    (sumPowersTensorPowerIso X k (n + 2)) _ p
  intro t
  obtain ⟨g, hg⟩ := h t
  refine ⟨(tupleTensorPowersIso X k (n + 2) t).inv ≫ g ≫
    (tupleTensorPowersIso X k (n + 2) (p t)).hom, ?_⟩
  change (biproduct.ι (fun t : Fin (n + 2) → Fin count => tensorPower X (∑ i, k (t i))) t ≫
    (sumPowersTensorPowerIso X k (n + 2)).inv) ≫ _ = _
  rw [sumPowersTensorPowerIso_ι_inv]
  simp only [Category.assoc]
  rw [hg]
  have ht := sumPowersTensorPowerIso_ι_inv X k (n + 2) (p t)
  have ht' := congrArg (fun z => (tupleTensorPowersIso X k (n + 2) t).inv ≫
    g ≫ (tupleTensorPowersIso X k (n + 2) (p t)).hom ≫ z) ht
  change _ = (tupleTensorPowersIso X k (n + 2) t).inv ≫ g ≫
    (tupleTensorPowersIso X k (n + 2) (p t)).hom ≫
      biproduct.ι (fun t : Fin (n + 2) → Fin count => tensorPower X (∑ i, k (t i))) (p t) ≫
        (sumPowersTensorPowerIso X k (n + 2)).inv
  simpa [Category.assoc] using ht'.symm
end PropertyF
