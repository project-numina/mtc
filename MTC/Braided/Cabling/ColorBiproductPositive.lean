module
public import MTC.Braided.Cabling.PureSumColored
public import MTC.Braided.Cabling.ColorBiproductFinite
public import MTC.Braided.Cabling.BlockFiniteSum

/-! # Finite sums of positive powers from explicit colored cabling

The flattening and actual per-word cabling realization are explicit inputs;
this module does not assert the cabling theorem. -/

/-! Elementary strand-count bounds for positive-width colored tuples. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace MTC.Braided.Cabling

/-- A tuple with at least two positive block widths has at least two original
strands, so its flattening lies in an ordinary braid image. -/
theorem two_le_sum_positive_widths (n : ℕ) (k : Fin (n + 2) → ℕ)
    (hk : ∀ i, 0 < k i) : 2 ≤ ∑ i, k i := by
  have h : n + 2 ≤ ∑ i, k i := by
    calc
      n + 2 = ∑ _ : Fin (n + 2), 1 := by simp
      _ ≤ ∑ i, k i := Finset.sum_le_sum fun i _ => hk i
  omega

end MTC.Braided.Cabling
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace MTC.Braided.Cabling
universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- Express a positive-width tuple flattening using the `r+2` strand count
of the existing braid-image API. -/
def positiveWidthFlatten (X : C) (n : ℕ) (q : Fin (n + 2) → ℕ)
    (hq : ∀ j, 0 < q j)
    (e : coloredTensor (n + 2) (fun j => tensorPower X (q j)) ≅
      tensorPower X (∑ j, q j)) :
    coloredTensor (n + 2) (fun j => tensorPower X (q j)) ≅
      tensorPower X (((∑ j, q j) - 2) + 2) :=
  e ≪≫ eqToIso (congrArg (tensorPower X) (Nat.sub_add_cancel (two_le_sum_positive_widths n q hq)).symm)

/-- Finite sums of positive powers have finite braid images when every
colored pure word is realized, under the supplied fixed flattening, by an
actual original-strand braid-image element. -/
theorem finite_positivePower_biproduct_of_cabling
    {I : Type} [Fintype I] [DecidableEq I] (X : C) (k : I → ℕ)
    (hk : ∀ i, 0 < k i) (hX : ObjectPropertyF X)
    (flatten : ∀ (n : ℕ) (q : Fin (n + 2) → ℕ),
      coloredTensor (n + 2) (fun j => tensorPower X (q j)) ≅ tensorPower X (∑ j, q j))
    (hcable : ∀ (n : ℕ) (q : Fin (n + 2) → ℕ) (hq : ∀ j, 0 < q j)
      (w : List (Fin (n + 1) × Bool)) (hw : strandPermutation n (FreeGroup.mk w) = 1),
      ∃ z : braidImage X ((∑ j, q j) - 2),
        coloredPureWordHom n w hw (fun j => tensorPower X (q j)) =
          (positiveWidthFlatten X n q hq (flatten n q)).hom ≫ z.val.asIso.hom ≫
            (positiveWidthFlatten X n q hq (flatten n q)).inv) :
    ObjectPropertyF (⨁ (fun i => tensorPower X (k i))) := by
  intro n
  apply finite_braidImage_biproduct_of_finite_pure_block_ranges (fun i => tensorPower X (k i)) n
  intro f
  let q : Fin (n + 2) → ℕ := fun j => k (f j)
  have hq : ∀ j, 0 < q j := fun j => hk (f j)
  exact finite_pureColor_range_of_cabling (fun i => tensorPower X (k i)) n
    ((∑ j, q j) - 2) f X (positiveWidthFlatten X n q hq (flatten n q)) hX (hcable n q hq)

end MTC.Braided.Cabling
end
