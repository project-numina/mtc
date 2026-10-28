module
public import PropertyF.Ground.Calculus.UnitaryBlocks
public import PropertyF.BlockTrace
public import Mathlib.GroupTheory.OrderOfElement
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Centre.Basic
public import PropertyF.Ground.Calculus.BraidWeights
public import PropertyF.Ground.Fusion.Agreement

/-!
# Centrality and finite-order trace saturation

Finite-order matrices admit unitary representatives. In a fusion category with
positive dimensions, trace saturation detects an identity, relating the
categorical double braiding to its numerical S-matrix centrality test.
-/
@[expose] public noncomputable section
open PropertyF.Ground.Modular (HasFPSimpleDimensions doubleBraiding sCentralizes)
open PropertyF.Ground.Dimensions
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite-order complex matrix can be conjugated to a unitary matrix. -/
theorem finiteOrder_matrix_unitarizable {M : Matrix ι ι ℂ} (hM : IsOfFinOrder M) :
    ∃ P : (Matrix ι ι ℂ)ˣ, ((P : Matrix ι ι ℂ) * M * (↑(P⁻¹) : Matrix ι ι ℂ)) ∈ Matrix.unitaryGroup ι ℂ :=
  let u : (Matrix ι ι ℂ)ˣ := hM.isUnit.unit
  have hufin : IsOfFinOrder u := Units.isOfFinOrder_val.mp (by simpa [u] using hM)
  let G := Subgroup.zpowers u
  let : Finite G := hufin.finite_zpowers
  let : Fintype G := Fintype.ofFinite G
  let ⟨P, hP⟩ := Calculus.exists_unitarizing_basis G.subtype
  let g : G := ⟨u, Subgroup.mem_zpowers u⟩
  ⟨P, by simpa [g, u] using hP g⟩

/-- A finite-order matrix has real trace at most its size, with equality
only for the identity. -/
theorem finiteOrder_matrix_trace_saturation {M : Matrix ι ι ℂ} (hM : IsOfFinOrder M) :
    M.trace.re ≤ Fintype.card ι ∧
      (M.trace.re = Fintype.card ι → M = 1) := by
  obtain ⟨P, hP⟩ := finiteOrder_matrix_unitarizable hM
  let U : Matrix ι ι ℂ := (P : Matrix ι ι ℂ) * M * (↑(P⁻¹) : Matrix ι ι ℂ)
  have ht : U.trace = M.trace := Matrix.trace_units_conj P M
  constructor
  · rw [← ht]
    exact (Complex.re_le_norm _).trans (PropertyF.norm_trace_le_card hP)
  · intro heq
    simpa [U, Matrix.mul_assoc, ← Units.val_mul] using
      congrArg (fun A : Matrix ι ι ℂ ↦ (↑(P⁻¹) : Matrix ι ι ℂ) * A * (P : Matrix ι ι ℂ))
        (PropertyF.eq_one_of_re_trace_eq_card hP (by rwa [ht]))

end PropertyF.Ground.CentreCabling

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u
variable {D : Ground.BraidedFusionCategory.{v,u}} {p : PivotalStructure (C := D.Obj)}
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Positive weighted sums preserve equality when the terms are pointwise ordered. -/
theorem eq_of_pos_weighted_sum_eq {ι R : Type*} [Fintype ι] [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {w a b : ι → R}
    (hw : ∀ i, 0 < w i) (hle : ∀ i, a i ≤ b i)
    (hsum : (∑ i, w i * a i) = ∑ i, w i * b i) (i : ι) : a i = b i :=
  mul_left_cancel₀ (ne_of_gt (hw i)) <|
    (Finset.sum_eq_sum_iff_of_le (fun j _ ↦ mul_le_mul_of_nonneg_left (hle j) (hw j).le)).mp
      hsum i (Finset.mem_univ i)

variable {ι : Type*} [Fintype ι] {J : ι → Type*}
  [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]

/-- A positive weighted maximal trace forces a finite-order matrix family to be the identity. -/
theorem finiteOrder_matrices_eq_one_of_weighted_trace
    (M : ∀ i, Matrix (J i) (J i) ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hM : ∀ i, IsOfFinOrder (M i))
    (ht : (∑ i, w i * (M i).trace.re) = ∑ i, w i * (Fintype.card (J i) : ℝ)) :
    ∀ i, M i = 1 := fun i ↦
  (finiteOrder_matrix_trace_saturation (hM i)).2 <|
    eq_of_pos_weighted_sum_eq hw (fun j ↦ (finiteOrder_matrix_trace_saturation (hM j)).1) ht i

/-- In a fusion category with positive simple pivotal dimensions, a
finite-order endomorphism whose pivotal trace equals the object's dimension
is the identity. -/
theorem finiteOrder_eq_one_of_trace_eq_dimension
    (hdim : HasFPSimpleDimensions D p)
    {X : D.Obj} {a : End X} (ha : IsOfFinOrder a)
    (ht : p.rightTrace a.asHom = p.rightTrace (𝟙 X)) : a = 1 := by
  classical
  let m (i : Fin (rank D)) := Module.finrank ℂ (simples D i ⟶ X)
  obtain ⟨e⟩ := exists_canonical_decomposition D X
  let B := Calculus.groundEndBlockEquiv D e
  have hsum : (∑ i, fpSimple D i * (B a i).trace.re) =
      ∑ i, fpSimple D i * (m i : ℝ) := by
    have h2 := Calculus.pivotalTrace_groundEndBlocks D p (Ground.unitScalarEquiv D) e 1
    simp only [End.one_asHom] at h2
    change (∀ i, Ground.unitScalarEquiv D (p.rightTrace (𝟙 (simples D i))) =
      (fpSimple D i : ℂ)) at hdim
    simpa [hdim, B, Complex.re_sum, Complex.mul_re] using congrArg Complex.re
      ((Calculus.pivotalTrace_groundEndBlocks D p (Ground.unitScalarEquiv D) e a).symm.trans
        ((congrArg (Ground.unitScalarEquiv D) ht).trans h2))
  apply B.injective
  funext i
  simpa using finiteOrder_matrices_eq_one_of_weighted_trace (B a) (fpSimple D)
    (fpSimple_pos D) (fun j ↦ (Pi.evalMonoidHom _ j).isOfFinOrder (B.toMonoidHom.isOfFinOrder ha))
    (by simpa only [Fintype.card_fin] using hsum) i

/-- For a finite-order double braiding, the positive spherical S-test is
equivalent to categorical centrality. -/
theorem doubleBraiding_eq_one_of_sTest_of_finite_order
    (hdim : HasFPSimpleDimensions D p)
    {i j : Fin (rank D)}
    (hfinite : IsOfFinOrder (End.of (doubleBraiding (simples D i) (simples D j))))
    (hs : sCentralizes D p i j) :
    doubleBraiding (simples D i) (simples D j) = 𝟙 _ := by
  have ht : p.rightTrace (doubleBraiding (simples D i) (simples D j)) =
      p.rightTrace (𝟙 (simples D i ⊗ simples D j)) := by
    apply (Ground.unitScalarEquiv D).injective
    change Modular.categoricalS D p i j = _
    rw [hs]
    simpa [Modular.simpleDimension, pivotalDimension,
      Ground.unitScalar_eq_equiv] using
      (pivotalDimension_tensor D p (simples D i) (simples D j)).symm
  exact congrArg End.asHom (finiteOrder_eq_one_of_trace_eq_dimension hdim hfinite ht)

end PropertyF.Ground.CentreCabling
