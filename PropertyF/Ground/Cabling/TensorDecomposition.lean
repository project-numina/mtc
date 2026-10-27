module
public import PropertyF.Ground.Cabling.Generated
public import Mathlib.Data.Fin.Tuple.Basic
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Flatten a double finite biproduct into a biproduct indexed by pairs. -/
def flattenFiniteBiproduct {I J : Type} [Fintype I] [Fintype J] (f : I → J → C) :
    (⨁ fun i => ⨁ fun j => f i j) ≅ ⨁ fun p : I × J => f p.1 p.2 :=
  biproduct.isoProduct _ ≪≫ Pi.mapIso (fun i => biproduct.isoProduct (f i)) ≪≫
    piPiIso (fun _ : I => J) f ≪≫
    Pi.whiskerEquiv (f := fun p : Σ _ : I, J => f p.1 p.2)
      (g := fun p : I × J => f p.1 p.2)
      (Equiv.sigmaEquivProd I J) (fun _ => Iso.refl _) ≪≫
    (biproduct.isoProduct _).symm

/-- Tensor products distribute over finite biproducts on both sides. -/
def tensorFiniteBiproduct {I J : Type} [Fintype I] [Fintype J] (f : I → C) (g : J → C) :
    (⨁ f) ⊗ (⨁ g) ≅ ⨁ fun p : I × J => f p.1 ⊗ g p.2 :=
  rightDistributor f (⨁ g) ≪≫
    biproduct.mapIso (fun i => leftDistributor (f i) g) ≪≫
    flattenFiniteBiproduct (fun i j => f i ⊗ g j)

/-- Tensor the objects indexed by a tuple, right-associated. -/
def tupleTensor {I : Type} (f : I → C) : ∀ n, (Fin n → I) → C
  | 0, _ => 𝟙_ C
  | n + 1, t => f (t 0) ⊗ tupleTensor f n (Fin.tail t)

/-- Tensor powers of a biproduct decompose into tuple-indexed blocks. -/
def tensorPowerBiproductIso {I : Type} [Fintype I] (f : I → C) : ∀ n,
    tensorPower (⨁ f) n ≅ ⨁ (tupleTensor f n)
  | 0 => by
      let _ : Unique (Fin 0 → I) := ⟨⟨fun i => Fin.elim0 i⟩, fun t => by funext i; exact Fin.elim0 i⟩
      exact (biproductUniqueIso (tupleTensor f 0)).symm
  | n + 1 => by
      let e := Fin.consEquiv (fun _ : Fin (n + 1) => I)
      exact (Iso.refl (⨁ f) ⊗ᵢ tensorPowerBiproductIso f n) ≪≫
        tensorFiniteBiproduct f (tupleTensor f n) ≪≫
        biproduct.whiskerEquiv e (fun p => by
          change tupleTensor f (n + 1) (Fin.cons p.1 p.2) ≅ f p.1 ⊗ tupleTensor f n p.2
          simpa [tupleTensor] using Iso.refl (f p.1 ⊗ tupleTensor f n p.2))
/-- A block indexed by powers is itself a tensor power of the generator. -/
def tupleTensorPowersIso {I : Type} (X : C) (k : I → ℕ) : ∀ (n : ℕ) (t : Fin n → I),
    tupleTensor (fun i => tensorPower X (k i)) n t ≅
      tensorPower X (∑ i, k (t i))
  | 0, t => by simpa [tupleTensor, tensorPower] using Iso.refl (𝟙_ C)
  | n + 1, t => by
      simpa [tupleTensor, Fin.sum_univ_succ, Fin.tail] using
        ((Iso.refl (tensorPower X (k (t 0))) ⊗ᵢ tupleTensorPowersIso X k n (Fin.tail t)) ≪≫
          tensorPowerTensorIso X (k (t 0)) (∑ i : Fin n, k (t i.succ)))

/-- Tensor powers of a sum of powers split into blocks indexed by tuples. -/
def sumPowersTensorPowerIso {I : Type} [Fintype I] (X : C) (k : I → ℕ) (n : ℕ) :
    tensorPower (⨁ fun i => tensorPower X (k i)) n ≅
      ⨁ fun t : Fin n → I => tensorPower X (∑ i, k (t i)) :=
  tensorPowerBiproductIso (fun i => tensorPower X (k i)) n ≪≫
    biproduct.mapIso (tupleTensorPowersIso X k n)
end PropertyF
