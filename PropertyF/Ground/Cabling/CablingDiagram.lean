module
public import PropertyF.Ground.Cabling.PureBlocks
public import PropertyF.Ground.Cabling.TensorDecomposition
public import PropertyF.Ground.Cabling.Witness
public import Mathlib.CategoryTheory.Conj
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The subgroup version of the uniform zero/one/positive-strand image. -/
def braidImageAllSubgroup (X : C) : ∀ m : ℕ, Subgroup (Aut (tensorPower X m))
  | 0 => ⊥
  | 1 => ⊥
  | m + 2 => braidImage X m

/-- Identify the uniform braid-image type with the corresponding subgroup. -/
def braidImageAllSubgroupEquiv (X : C) (m : ℕ) :
    (braidImageAllSubgroup X m) ≃* braidImageAll X m := by
  cases m with
  | zero => exact MulEquiv.refl _
  | succ m => cases m with
    | zero => exact MulEquiv.refl _
    | succ m => exact MulEquiv.refl _

/-- The block of the tensor-power decomposition indexed by a tuple. -/
def powerSumBlock (X : C) (k : Fin count → ℕ) (n : ℕ) (t : Fin (n + 2) → Fin count) : C :=
  tensorPower X (∑ i, k (t i))

/-- The actual braid-word action transported across the block decomposition. -/
def sumPowerWordAction (X : C) (k : Fin count → ℕ) (n : ℕ) :
    BraidWords n →* Aut (⨁ powerSumBlock X k n) :=
  (sumPowersTensorPowerIso X k (n + 2)).conjAut.toMonoidHom.comp
    ((braidImage (⨁ fun i => tensorPower X (k i)) n).subtype.comp
      (braidWordAction (⨁ fun i => tensorPower X (k i)) n))

/-- The actual pure tuple action, subject only to the crossing permutation law. -/
def powerSumPureBlockAction (X : C) (k : Fin count → ℕ) (n : ℕ)
    (hgen : ∀ i, permutesBlocks (powerSumBlock X k n)
      (sumPowerWordAction X k n (FreeGroup.of i))
      (((tuplePermutation (Fin count) (n + 2)).comp (strandPermutation n)) (FreeGroup.of i))) :
    pureWords n →* ∀ t, Aut (powerSumBlock X k n t) :=
  pureTupleBlockAction (powerSumBlock X k n) (sumPowerWordAction X k n) hgen

/-- If the block restrictions are cabled X-braids, they form a product-valued
homomorphism. -/
def powerSumCableAction (X : C) (k : Fin count → ℕ) (n : ℕ)
    (hgen : ∀ i, permutesBlocks (powerSumBlock X k n)
      (sumPowerWordAction X k n (FreeGroup.of i))
      (((tuplePermutation (Fin count) (n + 2)).comp (strandPermutation n)) (FreeGroup.of i)))
    (hcable : ∀ (w : pureWords n) (t : Fin (n + 2) → Fin count),
      powerSumPureBlockAction X k n hgen w t ∈ braidImageAllSubgroup X (∑ i, k (t i))) :
    pureWords n →* ∀ t : Fin (n + 2) → Fin count, braidImageAll X (∑ i, k (t i)) where
  toFun w t := braidImageAllSubgroupEquiv X _
    ⟨powerSumPureBlockAction X k n hgen w t, hcable w t⟩
  map_one' := by
    funext t
    change braidImageAllSubgroupEquiv X _ ⟨_, _⟩ = 1
    rw [← map_one (braidImageAllSubgroupEquiv X _)]
    congr 1
    apply Subtype.ext
    exact congrFun (map_one (powerSumPureBlockAction X k n hgen)) t
  map_mul' x y := by
    funext t
    change braidImageAllSubgroupEquiv X _ ⟨_, _⟩ =
      braidImageAllSubgroupEquiv X _ ⟨_, _⟩ * braidImageAllSubgroupEquiv X _ ⟨_, _⟩
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    exact congrFun (map_mul (powerSumPureBlockAction X k n hgen) x y) t
/-- The cabled block action detects the pure action on the sum of powers. -/
theorem powerSumCableAction_ker_le (X : C) (k : Fin count → ℕ) (n : ℕ)
    (hgen : ∀ i, permutesBlocks (powerSumBlock X k n)
      (sumPowerWordAction X k n (FreeGroup.of i))
      (((tuplePermutation (Fin count) (n + 2)).comp (strandPermutation n)) (FreeGroup.of i)))
    (hcable : ∀ (w : pureWords n) (t : Fin (n + 2) → Fin count),
      powerSumPureBlockAction X k n hgen w t ∈ braidImageAllSubgroup X (∑ i, k (t i))) :
    (powerSumCableAction X k n hgen hcable).ker ≤
      (pureWordAction (⨁ fun i => tensorPower X (k i)) n).ker := by
  intro w hw
  have hb : powerSumPureBlockAction X k n hgen w = 1 := by
    funext t
    have ht := congrFun (MonoidHom.mem_ker.mp hw) t
    change braidImageAllSubgroupEquiv X _ ⟨powerSumPureBlockAction X k n hgen w t, _⟩ = 1 at ht
    rw [← map_one (braidImageAllSubgroupEquiv X _)] at ht
    have ht' := (braidImageAllSubgroupEquiv X _).injective ht
    exact congrArg Subtype.val ht'
  have hρ := pureTupleBlockAction_ker_le (powerSumBlock X k n) (sumPowerWordAction X k n) hgen hb
  change pureWordAction (⨁ fun i => tensorPower X (k i)) n w = 1
  apply Subtype.ext
  apply Subtype.ext
  change sumPowerWordAction X k n w.val = 1 at hρ
  change (sumPowersTensorPowerIso X k (n + 2)).conjAut
    ((braidWordAction (⨁ fun i => tensorPower X (k i)) n w.val).val) = 1 at hρ
  apply (sumPowersTensorPowerIso X k (n + 2)).conjAut.injective
  exact hρ.trans (map_one _).symm
/-- A concrete cabling witness for a sum of powers, from the crossing
permutation law and the statement that each pure block action is an X-braid. -/
def sumPowersCablingWitness (D : BraidedFusionCategory.{v,u}) (X : D.Obj)
    (k : Fin count → ℕ) (n : ℕ)
    (hgen : ∀ i, permutesBlocks (powerSumBlock X k n)
      (sumPowerWordAction X k n (FreeGroup.of i))
      (((tuplePermutation (Fin count) (n + 2)).comp (strandPermutation n)) (FreeGroup.of i)))
    (hcable : ∀ (w : pureWords n) (t : Fin (n + 2) → Fin count),
      powerSumPureBlockAction X k n hgen w t ∈ braidImageAllSubgroup X (∑ i, k (t i))) :
    CablingWitness D X (⨁ fun i => tensorPower X (k i)) n := by
  classical
  let e := Fintype.equivFin (Fin (n + 2) → Fin count)
  let N := Fintype.card (Fin (n + 2) → Fin count)
  let lengths : Fin N → Fin (n + 2) → ℕ := fun r i => k (e.symm r i)
  let cable : pureWords n →* ∀ r : Fin N, braidImageAll X (∑ i, lengths r i) := {
    toFun := fun w r => powerSumCableAction X k n hgen hcable w (e.symm r)
    map_one' := by ext r; exact congrFun (map_one (powerSumCableAction X k n hgen hcable)) _
    map_mul' := by intro a b; ext r; exact congrFun (map_mul (powerSumCableAction X k n hgen hcable) a b) _
  }
  have hker : cable.ker ≤ (pureWordAction (⨁ fun i => tensorPower X (k i)) n).ker := by
    intro w hw
    apply powerSumCableAction_ker_le X k n hgen hcable
    change powerSumCableAction X k n hgen hcable w = 1
    funext t
    have ht := congrFun (MonoidHom.mem_ker.mp hw) (e t)
    change powerSumCableAction X k n hgen hcable w (e.symm (e t)) = 1 at ht
    rw [e.symm_apply_apply] at ht
    exact ht
  exact cablingWitnessOfPureAction D X (⨁ fun i => tensorPower X (k i)) n N lengths cable hker
end PropertyF
