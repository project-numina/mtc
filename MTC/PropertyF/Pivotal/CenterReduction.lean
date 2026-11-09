module
public import MTC.PropertyF.Pivotal.Centralizer
public import MTC.PropertyF.Pivotal.Nondegenerate
public import MTC.Center.Normalization.FPPlacement
public import MTC.Center.Braid.ImageCore
public import MTC.Center.Induction.PivotalSquare

/-! # The pivotal centre reduction with explicit core interfaces

The general pivotal numerical double-centralizer and trace argument apply to
the actual Drinfeld centre. The core comparison and FP normalization are
explicit intermediate hypotheses; this is not the manuscript's degenerate
theorem until those hypotheses are established from its stated assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open MTC.Fusion MTC.Modular MTC.Braided MTC.CategoryTheory.Dimensions
open scoped BigOperators
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)]
variable [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "Z" => MTC.PropertyF.Reduction.bundledCenter C

/-- Once the numerical centralizer is contained in the actual symmetric core
and dimensions are normalized on that core, property F makes the actual centre
pseudo-unitary, without any sphericality assumption. -/
theorem center_pseudoUnitary_of_normalized_core
    (pZ : PivotalStructure (C := (MTC.PropertyF.Reduction.bundledCenter C).Obj))
    (hdet : (categoricalS Z pZ).det ≠ 0)
    (hF : HasPropertyF C.Obj)
    (hcore : sCentralizer Z pZ (↑(MTC.Center.Braid.productLabels C) : Set _) ⊆
      MTC.Center.Braid.symmetricCore C)
    (hfp : ∀ y ∈ MTC.Center.Braid.symmetricCore C,
      simpleDimension Z pZ y = (fpSimple Z y : ℂ)) :
    PseudoUnitary Z := by
  obtain ⟨j, hj, _⟩ := existsUnique_fp_column Z pZ hdet
  have hjcore : j ∈ sCentralizer Z pZ (MTC.Center.Braid.symmetricCore C) := by
    intro y hy
    change categoricalS Z pZ y j = simpleDimension Z pZ y * simpleDimension Z pZ j
    rw [hfp y hy, hj y, mul_comm]
  have hprod : MTC.Center.ProductRetract (simples Z j) :=
    (MTC.Center.Braid.mem_productLabels C j).mp <|
      pivotal_doubleCentralizer_of_invertibleS Z pZ hdet
        (MTC.Center.Braid.productLabels_isFusionSubring C) hcore hjcore
  exact (pseudoUnitary_of_fp_column_propertyF Z pZ hdet j hj
    (MTC.Center.productRetract_propertyF hprod hF)).1

/-- Pseudo-unitarity of the actual Drinfeld centre descends to a pivotal
base category using the general centre-square formulae. -/
theorem pseudoUnitary_of_center_pseudoUnitary
    (p : PivotalStructure (C := C.Obj)) (hZ : PseudoUnitary Z) : PseudoUnitary C := by
  let d : ℝ := ∑ i : Fin (rank C), ‖pivotalDimension C p (simples C i)‖ ^ 2
  have hd : globalDimension C = (d : ℂ) :=
    MTC.Center.Induction.globalDimension_eq_sum_pivotal_norm_sq p
  have hdpos : 0 < d := by
    have h : 1 ≤ d := by
      simpa only [d, pivotalDimension_unitIndex, norm_one, one_pow] using
        (Finset.single_le_sum (fun (i : Fin (rank C)) _ ↦
          sq_nonneg ‖pivotalDimension C p (simples C i)‖)
          (Finset.mem_univ (unitIndex C)))
    linarith
  have hfp : 0 < globalFPDimension C :=
    lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)
  change globalDimension Z = (globalFPDimension Z : ℂ) at hZ
  rw [MTC.Center.Induction.globalDimension_square_of_pivotal p,
    MTC.Center.Induction.globalFPDimension_square_of_actual_induction C, hd] at hZ
  have hsq : d ^ 2 = globalFPDimension C ^ 2 := by exact_mod_cast hZ
  have heq : d = globalFPDimension C := (sq_eq_sq₀ hdpos.le hfp.le).mp hsq
  change globalDimension C = (globalFPDimension C : ℂ)
  rw [hd, heq]

/-- The pivotal centre argument with its two remaining categorical
interfaces exposed: centre S invertibility and identification of the
numerical product centralizer with the actual symmetric core. -/
theorem pseudoUnitary_of_normalized_muger_and_center_criteria
    (p : PivotalStructure (C := C.Obj))
    (pZ : PivotalStructure (C := (MTC.PropertyF.Reduction.bundledCenter C).Obj))
    (hcompat : ∀ W, MTC.Center.Induction.PivotalCompatibleAt p pZ W)
    (hdet : (categoricalS Z pZ).det ≠ 0) (hF : HasPropertyF C.Obj)
    (hcore : sCentralizer Z pZ (↑(MTC.Center.Braid.productLabels C) : Set _) ⊆
      MTC.Center.Braid.symmetricCore C)
    (hbase : ∀ i, MTC.Center.Transparent (simples C i) →
      simpleDimension C p i = (fpSimple C i : ℂ)) : PseudoUnitary C :=
  pseudoUnitary_of_center_pseudoUnitary C p <|
    center_pseudoUnitary_of_normalized_core C pZ hdet hF hcore
      (fun _ hy ↦ MTC.Center.Normalization.symmetricCore_pivotalDimension_eq_fp C hcompat hbase hy)

/-- The centre reduction needs numerical S-centrality only for the simple
constituents of the two canonical images, not for arbitrary centre labels. -/
theorem pseudoUnitary_of_normalized_muger_and_simple_criterion
    (p : PivotalStructure (C := C.Obj))
    (pZ : PivotalStructure (C := (MTC.PropertyF.Reduction.bundledCenter C).Obj))
    (hcompat : ∀ W, MTC.Center.Induction.PivotalCompatibleAt p pZ W)
    (hdet : (categoricalS Z pZ).det ≠ 0) (hF : HasPropertyF C.Obj)
    (hcriterion : ∀ a ∈ MTC.Center.Braid.imageLabels C, ∀ y : Fin (rank Z),
      sCentralizes Z pZ a y →
      doubleBraiding (simples Z a) (simples Z y) = 𝟙 _)
    (hbase : ∀ i, MTC.Center.Transparent (simples C i) →
      simpleDimension C p i = (fpSimple C i : ℂ)) : PseudoUnitary C :=
  pseudoUnitary_of_normalized_muger_and_center_criteria C p pZ hcompat hdet hF
    (MTC.Center.Normalization.productNumericalCentralizer_subset_symmetricCore C hcriterion) hbase

end MTC.PropertyF.Pivotal
