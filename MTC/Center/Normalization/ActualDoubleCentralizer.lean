module
public import MTC.Center.Normalization.RelativeCentralizer
public import MTC.Center.Braid.PivotalRegularSupport

open MTC.Fusion MTC.Braided MTC.Center.Braid MTC.CategoryTheory.Dimensions
open MTC.PropertyF.Reduction MTC.Modular

/-! # Actual-object double-centralizer reduction

The displayed orthogonality and relative centralizer containment are explicit
hypotheses; neither is proved here. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})
  [RigidCategory (Center C.Obj)] [IsFusionCategory (Center C.Obj)]
local notation "Z" => bundledCenter C
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Actual simple monodromy identity implies its numerical S test for an
arbitrary pivotal structure. -/
theorem sCentralizes_of_doubleBraiding_eq_id
    (D : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := D.Obj))
    (i j : Fin (rank D))
    (h : doubleBraiding (simples D i) (simples D j) = 𝟙 _) : sCentralizes D p i j := by
  rw [sCentralizes, categoricalS, SEntry, h, ← unitScalar_eq_equiv]
  change pivotalDimension D p (simples D i ⊗ simples D j) = _
  exact pivotalDimension_tensor p _ _

/-- Under the stated numerical orthogonality and relative-centralizer
containment, the actual centralizer of the transparent positive image is
exactly the class of actual product retracts, for every centre object. -/
theorem productRetract_iff_centralizes_transparentPositive_of_criteria
    (pZ : PivotalStructure (C := Center C.Obj))
    (horth : ∀ x k : Fin (rank Z),
      (∑ y, star (categoricalS Z pZ y x) * categoricalS Z pZ y k) =
        if x = k then globalDimension Z else 0)
    (hcore : sCentralizer Z pZ (↑(productLabels C) : Set _) ⊆ symmetricCore C)
    (W : Center C.Obj) :
    MTC.Center.ProductRetract W ↔
      ∀ E : Center C.Obj, (∃ X : C.Obj, MTC.Center.Transparent X ∧
        Nonempty (E ≅ (Center.ofBraided C.Obj).obj X)) → MTC.Center.Centralizes W E := by
  constructor
  · intro hW E hE
    exact MTC.Center.centralizes_symm ((productRetractCentralizer_iff E).mpr hE W hW)
  · intro hW
    obtain ⟨m, ⟨e⟩⟩ := simples_decompose Z W
    let V : (Σ i, Fin (m i)) → Center C.Obj := fun a => simples Z a.1
    apply MTC.Center.productRetract_of_retract (Retract.ofIso e)
    apply MTC.Center.productRetract_finiteBiproduct
    intro a
    apply (mem_productLabels C a.1).mp
    apply pivotal_doubleCentralizer_of_fusion_closed horth (productLabels_isFusionSubring C) hcore
    intro x hx
    have hE := (commonCanonicalCentralizer_iff (simples Z x)).mp hx
    have hcent := hW (simples Z x) hE
    let r : Retract (simples Z a.1) W :=
      (Retract.mk (biproduct.ι V a) (biproduct.π V a) (biproduct.ι_π_self V a)).trans
        (Retract.ofIso e.symm)
    have hm : doubleBraiding (simples Z a.1) (simples Z x) = 𝟙 _ :=
      doubleBraiding_eq_one_of_retract r hcent
    exact sCentralizes_symm (sCentralizes_of_doubleBraiding_eq_id Z pZ a.1 x hm)

/-- The actual objectwise centre double-centralizer identity follows from the
generic relative numerical-to-actual fusion-subring criterion. -/
theorem productRetract_iff_centralizes_transparentPositive_of_relative
    (pZ : PivotalStructure (C := Center C.Obj))
    (hrelative : ∀ (A : Finset (Fin (rank Z))), IsFusionSubring Z A →
      ∀ y : Fin (rank Z), (∀ a ∈ A, sCentralizes Z pZ a y) →
      ∀ a ∈ A, doubleBraiding (simples Z a) (simples Z y) = 𝟙 _)
    (W : Center C.Obj) :
    MTC.Center.ProductRetract W ↔
      ∀ E : Center C.Obj, (∃ X : C.Obj, MTC.Center.Transparent X ∧
        Nonempty (E ≅ (Center.ofBraided C.Obj).obj X)) → MTC.Center.Centralizes W E := by
  have hdet := center_categoricalS_det_ne_zero_of_relative C pZ hrelative
  have hglobal : globalDimension Z = ∑ i, star (simpleDimension Z pZ i) * simpleDimension Z pZ i := by
    rw [MTC.Center.Induction.globalDimension_eq_sum_pivotal_norm_sq pZ]
    simp only [Complex.ofReal_sum, Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [simpleDimension, Complex.star_def, mul_comm] using
      (Complex.mul_conj' (simpleDimension Z pZ i)).symm
  have horth (x k : Fin (rank Z)) :
      (∑ y, star (categoricalS Z pZ y x) * categoricalS Z pZ y k) =
        if x = k then globalDimension Z else 0 := by
    by_cases h : x = k
    · subst k
      simp only [ite_true]
      rw [hglobal]
      simpa only [starRingEnd_apply] using
        MTC.PropertyF.Pivotal.categoricalS_column_length Z pZ hdet x
    · simp only [h, ite_false]
      simpa only [starRingEnd_apply] using
        MTC.PropertyF.Pivotal.categoricalS_columns_orthogonal Z pZ hdet h
  have hcore := productNumericalCentralizer_subset_symmetricCore_of_fusionSubring_criterion
    C hrelative
  exact productRetract_iff_centralizes_transparentPositive_of_criteria C pZ horth hcore W

end MTC.Center.Normalization
end
