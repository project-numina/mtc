module
public import MTC.Braided.Trace.UnitaryBlocks
public import MTC.CategoryTheory.BlockTrace
public import Mathlib.GroupTheory.OrderOfElement
public import MTC.Modular.SMatrix
public import MTC.CategoryTheory.Dimensions.DimensionCharacter
public import MTC.Center.Basic
public import MTC.Braided.Trace.BraidWeights
public import MTC.Fusion.Agreement

open MTC.PropertyF.Reduction

open MTC.Fusion

open MTC.Braided

/-!
# Centrality and finite-order trace saturation

Finite-order matrices admit unitary representatives. In a fusion category with
positive dimensions, trace saturation detects an identity, relating the
categorical double braiding to its numerical S-matrix centrality test.
-/
@[expose] public noncomputable section
open MTC.Modular (HasFPSimpleDimensions doubleBraiding sCentralizes)
open MTC.CategoryTheory.Dimensions
open scoped BigOperators
namespace MTC.Center.Braid

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Matrix ι ι ℂ} (hM : IsOfFinOrder M)

include hM in
/-- A finite-order complex matrix can be conjugated to a unitary matrix. -/
theorem finiteOrder_matrix_unitarizable :
    ∃ P : (Matrix ι ι ℂ)ˣ, ((P : Matrix ι ι ℂ) * M * (↑(P⁻¹) : Matrix ι ι ℂ)) ∈ Matrix.unitaryGroup ι ℂ :=
  let u : (Matrix ι ι ℂ)ˣ := hM.isUnit.unit
  have hufin : IsOfFinOrder u := Units.isOfFinOrder_val.mp (by simpa [u] using hM)
  let G := Subgroup.zpowers u
  let : Finite G := hufin.finite_zpowers
  let : Fintype G := Fintype.ofFinite G
  let ⟨P, hP⟩ := MTC.Braided.Trace.exists_unitarizing_basis ((Units.coeHom _).comp G.subtype)
  ⟨P, by simpa [u] using hP ⟨u, Subgroup.mem_zpowers u⟩⟩

include hM in
/-- A finite-order matrix has real trace at most its size, with equality
only for the identity. -/
theorem finiteOrder_matrix_trace_saturation :
    M.trace.re ≤ Fintype.card ι ∧
      (M.trace.re = Fintype.card ι → M = 1) :=
  let ⟨P, hP⟩ := finiteOrder_matrix_unitarizable hM
  let U : Matrix ι ι ℂ := (P : Matrix ι ι ℂ) * M * (↑(P⁻¹) : Matrix ι ι ℂ)
  have ht : U.trace = M.trace := Matrix.trace_units_conj P M
  ⟨ht ▸ (Complex.re_le_norm _).trans (MTC.norm_trace_le_card hP), fun heq ↦ by
    simpa [U, Matrix.mul_assoc, ← Units.val_mul] using
      congrArg (fun A : Matrix ι ι ℂ ↦ (↑(P⁻¹) : Matrix ι ι ℂ) * A * (P : Matrix ι ι ℂ))
        (MTC.eq_one_of_re_trace_eq_card hP (ht.symm ▸ heq))⟩

end MTC.Center.Braid

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace MTC.Center.Braid
universe v u
variable {D : MTC.Fusion.BraidedFusionCategory.{v,u}} {p : PivotalStructure (C := D.Obj)}
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Positive weighted sums preserve equality when the terms are pointwise ordered. -/
theorem eq_of_pos_weighted_sum_eq {ι R : Type*} [Fintype ι] [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    {w a b : ι → R}
    (hw : ∀ i, 0 < w i) (hle : ∀ i, a i ≤ b i)
    (hsum : (∑ i, w i * a i) = ∑ i, w i * b i) (i : ι) : a i = b i :=
  (strictMono_mul_left_of_pos (hw i)).injective <|
    (Finset.sum_eq_sum_iff_of_le (fun j _ ↦ mul_le_mul_of_nonneg_left (hle j) (hw j).le)).mp
      hsum i (Finset.mem_univ i)

variable {ι : Type*} [Fintype ι] {J : ι → Type*}
  [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]

/-- A positive weighted maximal trace forces a finite-order matrix family to be the identity. -/
theorem finiteOrder_matrices_eq_one_of_weighted_trace (M : ∀ i, Matrix (J i) (J i) ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hM : ∀ i, IsOfFinOrder (M i))
    (ht : (∑ i, w i * (M i).trace.re) = ∑ i, w i * (Fintype.card (J i) : ℝ)) : ∀ i, M i = 1 :=
  fun i ↦ (finiteOrder_matrix_trace_saturation (hM i)).2 <|
    eq_of_pos_weighted_sum_eq hw (fun j ↦ (finiteOrder_matrix_trace_saturation (hM j)).1) ht i

/-- In a fusion category with positive simple pivotal dimensions, a
finite-order endomorphism whose pivotal trace equals the object's dimension
is the identity. -/
theorem finiteOrder_eq_one_of_trace_eq_dimension
    (hdim : HasFPSimpleDimensions D p)
    {X : D.Obj} {a : End X} (ha : IsOfFinOrder a)
    (ht : p.rightTrace a.asHom = p.rightTrace (𝟙 X)) : a = 1 := by
  let m (i : Fin (rank D)) := Module.finrank ℂ (simples D i ⟶ X)
  obtain ⟨e⟩ := exists_canonical_decomposition D X
  let B := MTC.Braided.Trace.groundEndBlockEquiv D e
  have hsum : (∑ i, fpSimple D i * (B a i).trace.re) =
      ∑ i, fpSimple D i * (m i : ℝ) := by
    have h2 := MTC.Braided.Trace.pivotalTrace_groundEndBlocks D e 1 p (MTC.Fusion.unitScalarEquiv D)
    have hdim' : ∀ i, MTC.Fusion.unitScalarEquiv D (p.rightTrace (𝟙 (simples D i))) =
        (fpSimple D i : ℂ) := by
      simpa [HasFPSimpleDimensions, Modular.simpleDimension, pivotalDimension, MTC.Fusion.unitScalar_eq_equiv] using hdim
    simpa [hdim', B, End.one_asHom, Complex.re_sum, Complex.mul_re] using congrArg Complex.re
      ((MTC.Braided.Trace.pivotalTrace_groundEndBlocks D e a p (MTC.Fusion.unitScalarEquiv D)).symm.trans
        ((congrArg (MTC.Fusion.unitScalarEquiv D) ht).trans h2))
  exact B.injective <| funext fun i ↦ by
    simpa using finiteOrder_matrices_eq_one_of_weighted_trace (B a) (fpSimple D)
      (fpSimple_pos D) (fun j ↦ (Pi.evalMonoidHom _ j).isOfFinOrder (B.toMonoidHom.isOfFinOrder ha))
      (by simpa only [Fintype.card_fin] using hsum) i

/-- For a finite-order double braiding, the positive spherical S-test is
equivalent to categorical centrality. -/
theorem doubleBraiding_eq_one_of_sTest_of_finite_order
    (hdim : HasFPSimpleDimensions D p) {i j : Fin (rank D)}
    (hfinite : IsOfFinOrder (End.of (doubleBraiding (simples D i) (simples D j))))
    (hs : sCentralizes D p i j) : doubleBraiding (simples D i) (simples D j) = 𝟙 _ :=
  congrArg End.asHom <| finiteOrder_eq_one_of_trace_eq_dimension hdim hfinite <|
    (MTC.Fusion.unitScalarEquiv D).injective <| by
      change Modular.categoricalS D p i j = _
      rw [hs]
      simpa [Modular.simpleDimension, pivotalDimension, MTC.Fusion.unitScalar_eq_equiv] using
        (pivotalDimension_tensor p (simples D i) (simples D j)).symm

end MTC.Center.Braid
