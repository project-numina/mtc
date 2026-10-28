module
public import PropertyF.Ground.Calculus.UnitaryBlocks
public import PropertyF.UnitaryTrace
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
  have ht : U.trace = M.trace := by
    dsimp [U]
    rw [Matrix.trace_mul_cycle]
    simp
  have hu : PropertyF.ColumnUnitary U := PropertyF.columnUnitary_of_unitary hP
  constructor
  · rw [← ht]
    exact (Complex.re_le_norm _).trans (PropertyF.norm_trace_le_card hu)
  · intro heq
    have hU : U = 1 := PropertyF.eq_one_of_re_trace_eq_card hu (by rw [ht]; exact heq)
    have hh := congrArg (fun A : Matrix ι ι ℂ => (↑(P⁻¹) : Matrix ι ι ℂ) * A * (P : Matrix ι ι ℂ)) hU
    simpa [U, Matrix.mul_assoc, ← Units.val_mul] using hh

end PropertyF.Ground.CentreCabling

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u
variable (D : Ground.BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := D.Obj))
attribute [local instance] Abelian.hasFiniteBiproducts

/-- In a fusion category with positive simple pivotal dimensions, a
finite-order endomorphism whose pivotal trace equals the object's dimension
is the identity. -/
theorem finiteOrder_eq_one_of_trace_eq_dimension
    (hdim : ∀ i, Dimensions.groundUnitScalarEquiv D (p.rightTrace (𝟙 (simples D i))) =
      (fpSimple D i : ℂ))
    {X : D.Obj} {a : End X} (ha : IsOfFinOrder a)
    (ht : p.rightTrace a.asHom = p.rightTrace (𝟙 X)) : a = 1 := by
  classical
  let m (i : Fin (rank D)) := Module.finrank ℂ (simples D i ⟶ X)
  obtain ⟨e⟩ := exists_canonical_decomposition D X
  let B := Calculus.groundEndBlockEquiv D X m e
  have hf (i : Fin (rank D)) : IsOfFinOrder (B a i) :=
    (Pi.evalMonoidHom _ i).isOfFinOrder (B.toMonoidHom.isOfFinOrder ha)
  have hb (i : Fin (rank D)) := finiteOrder_matrix_trace_saturation (hf i)
  have hsum : (∑ i, fpSimple D i * (B a i).trace.re) =
      ∑ i, fpSimple D i * (m i : ℝ) := by
    have h1 := Calculus.pivotalTrace_groundEndBlocks D p (Dimensions.groundUnitScalarEquiv D) X m e a
    have h2 := Calculus.pivotalTrace_groundEndBlocks D p (Dimensions.groundUnitScalarEquiv D) X m e 1
    simp only [End.one_asHom] at h2
    have hh := congrArg Complex.re (h1.symm.trans ((congrArg (Dimensions.groundUnitScalarEquiv D) ht).trans h2))
    simpa [hdim, B, Complex.re_sum, Complex.mul_re] using hh
  have hle : ∀ i, fpSimple D i * (B a i).trace.re ≤ fpSimple D i * (m i : ℝ) :=
    fun i => mul_le_mul_of_nonneg_left (by simpa using (hb i).1) (fpSimple_pos D i).le
  have heq (i : Fin (rank D)) : (B a i).trace.re = (m i : ℝ) := by
    have hh := (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hsum i (Finset.mem_univ i)
    exact mul_left_cancel₀ (ne_of_gt (fpSimple_pos D i)) hh
  apply B.injective
  apply funext
  intro i
  have h := (hb i).2 (by simpa using heq i)
  simpa using h

/-- For a finite-order double braiding, the positive spherical S-test is
equivalent to categorical centrality. -/
theorem doubleBraiding_eq_one_of_sTest_of_finite_order
    (hdim : Modular.HasFPSimpleDimensions D p)
    {i j : Fin (rank D)}
    (hfinite : IsOfFinOrder (End.of (Modular.doubleBraiding (simples D i) (simples D j))))
    (hs : Modular.categoricalS D p i j =
      Modular.simpleDimension D p i * Modular.simpleDimension D p j) :
    Modular.doubleBraiding (simples D i) (simples D j) = 𝟙 _ := by
  have hdim' : ∀ k, Dimensions.groundUnitScalarEquiv D (p.rightTrace (𝟙 (simples D k))) =
      (fpSimple D k : ℂ) := by
    intro k
    simpa [Modular.simpleDimension, Dimensions.groundUnitScalarEquiv_apply,
      Ground.unitScalar_eq_equiv] using hdim k
  have ht : p.rightTrace (Modular.doubleBraiding (simples D i) (simples D j)) =
      p.rightTrace (𝟙 (simples D i ⊗ simples D j)) := by
    apply (Dimensions.groundUnitScalarEquiv D).injective
    have hd := Dimensions.pivotalDimension_tensor D p (simples D i) (simples D j)
    have hd' : Modular.simpleDimension D p i * Modular.simpleDimension D p j =
        Ground.unitScalarEquiv D (p.rightTrace (𝟙 (simples D i ⊗ simples D j))) := by
      simpa [Modular.simpleDimension, Dimensions.pivotalDimension,
        Ground.unitScalar_eq_equiv] using hd.symm
    have hs' := hs
    change Ground.unitScalarEquiv D (p.rightTrace (Modular.doubleBraiding _ _)) = _ at hs'
    simpa [Dimensions.groundUnitScalarEquiv_apply, Ground.unitScalar_eq_equiv] using hs'.trans hd' 
  have h := finiteOrder_eq_one_of_trace_eq_dimension D p hdim' hfinite ht
  exact congrArg End.asHom h

end PropertyF.Ground.CentreCabling
