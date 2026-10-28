module
public import PropertyF.Ground.Calculus.EndBlocks
public import PropertyF.Ground.Dimensions.BiproductTrace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Trace
public import PropertyF.Ground.Calculus.UnitaryBlocks

/-!
# Braid traces and multiplicities

The pivotal trace decomposes into traces on matrix blocks of simple constituents.
Representations of braid algebras give nonnegative integral multiplicities, yielding
`pivotalTrace_braid_multiplicities` and unitary trace presentations.
-/

open PropertyF.Ground.Dimensions

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Calculus
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable (C : BraidedFusionCategory.{v,u})

/-- Scalar identification for a chosen simple object. -/
def groundSimpleScalar (i : Fin (Ground.rank C)) :
    End (Ground.simples C i) ≃ₐ[ℂ] ℂ := by
  let _ : Simple (Ground.simples C i) := Ground.simples_simple C i
  let _ : FiniteDimensional ℂ (Ground.simples C i ⟶ Ground.simples C i) :=
    Ground.IsFusionCategory.hom_finite _ _
  exact simpleEndScalar _

variable {X : C.Obj} {m : Fin (Ground.rank C) → ℕ}
  (e : X ≅ ⨁ (simpleCopies C m)) (a : End X)

set_option backward.isDefEq.respectTransparency false in
/-- A diagonal biproduct component is its block coefficient times the identity. -/
theorem groundEndBlockEquiv_diagonal (i : Fin (Ground.rank C)) (j : Fin (m i)) :
    biproduct.ι (simpleCopies C m) ⟨i, j⟩ ≫ e.inv ≫ a.asHom ≫ e.hom ≫
        biproduct.π (simpleCopies C m) ⟨i, j⟩ =
      (groundEndBlockEquiv C e a i j j) • 𝟙 (Ground.simples C i) := by
  classical
  simpa [groundEndBlockEquiv, orthogonalEndBlocks, isoEndAlgEquiv,
    simpleFiberEquiv, groundSimpleScalar, HomOrthogonal.matrixDecompositionAddEquiv,
    HomOrthogonal.matrixDecomposition, Matrix.reindexAlgEquiv, Matrix.reindexRingEquiv,
    Matrix.reindexAddEquiv, Matrix.reindex, Category.assoc, biproduct.components] using
    congrArg End.asHom (eq_smul_one_of_algEquiv (groundSimpleScalar C i) (End.of
      (biproduct.ι (simpleCopies C m) ⟨i, j⟩ ≫ e.inv ≫ a.asHom ≫ e.hom ≫
        biproduct.π (simpleCopies C m) ⟨i, j⟩)))

set_option backward.isDefEq.respectTransparency false in
/-- The actual pivotal trace on a fusion-category endomorphism is the sum of
simple categorical dimensions times the ordinary traces of its constituent
multiplicity blocks. -/
theorem pivotalTrace_groundEndBlocks (p : PivotalStructure (C := C.Obj))
    (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ) :
    scalar (p.rightTrace a.asHom) = ∑ i,
      scalar (p.rightTrace (𝟙 (Ground.simples C i))) *
        (groundEndBlockEquiv C e a i).trace := by
  classical
  let F : (Σ i, Fin (m i)) → C.Obj := fun q => Ground.simples C q.1
  let z : (⨁ F) ⟶ (⨁ F) := e.inv ≫ a.asHom ≫ e.hom
  have hz : p.rightTrace z = p.rightTrace a.asHom := rightTrace_iso_conj e p a
  have h := cyclicTrace_biproduct_scalar_blocks
    (fun Y => scalar.toLinearMap.comp (rightTraceLinear p Y))
    (fun f g => congrArg scalar (p.rightTrace_cyclic f g)) z
    (c := fun q => groundEndBlockEquiv C e a q.1 q.2 q.2)
    (fun ⟨i, j⟩ => by simpa [F, z, Category.assoc] using groundEndBlockEquiv_diagonal C e a i j)
  simpa [rightTraceLinear, hz, F, Matrix.trace, Finset.mul_sum, mul_comm,
    Fintype.sum_sigma] using h

end PropertyF.Ground.Calculus

/-! Consequences of the categorical multiplicity weights. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Calculus

/-- Dimensions obtained by decomposing a family into matrix blocks. -/
abbrev HasMultiplicityDecomposition {ι κ : Type*} [Fintype κ]
    (m : ι → ℕ) (d : κ → ℕ) (mult : ι → κ → ℕ) : Prop :=
  ∀ i, m i = ∑ j, mult i j * d j

/-- The block trace mass is the constituent multiplicity mass whenever the
actual representation dimensions decompose into braid-block dimensions. -/
theorem multiplicity_mass_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : ι → ℕ) (d : κ → ℕ) (mult : ι → κ → ℕ) (fp : ι → ℝ)
    (hdim : HasMultiplicityDecomposition m d mult) :
    (∑ j, (∑ i, (mult i j : ℝ) * fp i) * (d j : ℝ)) =
      ∑ i, (m i : ℝ) * fp i := by
  simp only [hdim, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_comm, mul_left_comm]

/-- The paper's Galois-transported multiplicity weights cannot vanish when
all original constituent dimensions are positive and the block is retained. -/
theorem transported_weight_ne_zero {ι : Type*} [Fintype ι]
    (mult : ι → ℕ) (dim qdim : ι → ℝ) (σ : ℂ ≃+* ℂ)
    (hpos : ∀ i, 0 < dim i) (htransport : ∀ i, σ (dim i : ℂ) = (qdim i : ℂ))
    (hret : ∃ i, 0 < mult i) : (∑ i, (mult i : ℝ) * qdim i) ≠ 0 := by
  have hsum : 0 < ∑ i, (mult i : ℝ) * dim i := by
    obtain ⟨i, hi⟩ := hret
    exact Finset.sum_pos' (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hpos i).le)
      ⟨i, Finset.mem_univ _, mul_pos (by exact_mod_cast hi) (hpos i)⟩
  intro hz
  have hz' : (∑ i, (mult i : ℂ) * σ (dim i : ℂ)) = 0 := by
    simpa only [htransport, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum, Complex.ofReal_zero] using congrArg Complex.ofReal hz
  apply (ne_of_gt hsum)
  exact_mod_cast (σ.injective (by simpa [map_sum, map_mul] using hz') :
    (∑ i, (mult i : ℂ) * (dim i : ℂ)) = 0)

end PropertyF.Ground.Calculus

/-! Cyclic linear functionals on complex matrix algebras. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Calculus

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (T : Matrix ι ι ℂ →ₗ[ℂ] ℂ) (hT : ∀ X Y, T (X * Y) = T (Y * X))

include hT in
/-- A cyclic functional agrees with a multiple of the trace on matrix units. -/
private theorem cyclic_matrix_single (i₀ i j : ι) (a : ℂ) :
    T (Matrix.single i j a) = T (Matrix.single i₀ i₀ 1) * (Matrix.single i j a).trace := by
  by_cases hij : i = j
  · subst j
    have hdiag := hT (Matrix.single i i₀ a) (Matrix.single i₀ i (1 : ℂ))
    simp only [Matrix.single_mul_single_same, mul_one, one_mul] at hdiag
    rw [hdiag, Matrix.trace_single_eq_same, mul_comm]
    change T (Matrix.single i₀ i₀ a) = a • T (Matrix.single i₀ i₀ 1)
    rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  · rw [Matrix.trace_single_eq_of_ne _ _ _ hij, mul_zero]
    simpa only [Matrix.single_mul_single_same, one_mul,
      Matrix.single_mul_single_of_ne a i j i (Ne.symm hij) 1, map_zero] using
      hT (Matrix.single i i (1 : ℂ)) (Matrix.single i j a)

include hT in
/-- A cyclic linear functional on a complex matrix algebra is a scalar
multiple of ordinary matrix trace, including the zero-dimensional case. -/
theorem cyclic_matrix_trace : ∃ w : ℂ, ∀ X, T X = w * X.trace := by
  classical
  by_cases hn : Nonempty ι
  · let i₀ : ι := Classical.choice hn
    refine ⟨T (Matrix.single i₀ i₀ 1), fun X => ?_⟩
    induction X using Matrix.induction_on with
    | h_add X Y hX hY => rw [map_add, hX, hY, Matrix.trace_add, mul_add]
    | h_std_basis i j a => exact cyclic_matrix_single T hT i₀ i j a
  · let _ : IsEmpty ι := not_nonempty_iff.mp hn
    exact ⟨0, fun X => by simp [Subsingleton.elim X 0]⟩

end

/-- Every cyclic linear functional on a finite product of matrix algebras is
a weighted sum of ordinary block traces. The weights may be arbitrary complex
numbers; reality and categorical multiplicities require additional input. -/
theorem cyclic_block_trace {B : Blocks} (T : B.Algebra →ₗ[ℂ] ℂ)
    (hT : ∀ X Y, T (X * Y) = T (Y * X)) :
    ∃ w : Fin B.count → ℂ, ∀ X, T X = ∑ i, w i * (X i).trace := by
  classical
  let V : Fin B.count → Type := fun i => Matrix (Fin (B.size i)) (Fin (B.size i)) ℂ
  let Tblock (i : Fin B.count) : V i →ₗ[ℂ] ℂ := T.comp (LinearMap.single ℂ V i)
  have hc (i : Fin B.count) : ∀ X Y : V i, Tblock i (X * Y) = Tblock i (Y * X) := by
    intro X Y
    change T (Pi.single i (X * Y)) = T (Pi.single i (Y * X))
    simpa only [Pi.single_mul] using hT (Pi.single i X) (Pi.single i Y)
  choose w hw using fun i : Fin B.count => cyclic_matrix_trace (Tblock i) (hc i)
  refine ⟨w, fun X => ?_⟩
  conv_lhs => rw [← LinearMap.sum_single_apply V X]
  rw [map_sum]
  change (∑ i, Tblock i (X i)) = _
  simp only [hw]

end PropertyF.Ground.Calculus

/-! Multiplicities in traces of representations of matrix-block algebras. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Calculus

section IdempotentTrace

variable {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A * A = A)
include hA

/-- The trace of an idempotent complex matrix is a nonnegative integer. -/
theorem idempotent_matrix_trace_nat : ∃ n : ℕ, A.trace = n :=
  ⟨_, by simpa only [Matrix.trace_toLin'_eq] using
    ((LinearMap.isProj_range_iff_isIdempotentElem A.toLin').2
      ((show IsIdempotentElem A from hA).map Matrix.toLinAlgEquiv')).trace⟩

/-- A complex idempotent matrix with zero trace is zero. -/
theorem idempotent_matrix_eq_zero_of_trace_eq_zero (ht : A.trace = 0) : A = 0 :=
  Matrix.toLinAlgEquiv'.injective (by
    simpa only [map_zero] using LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero
      ((show IsIdempotentElem A from hA).map Matrix.toLinAlgEquiv')
      (by
        change (LinearMap.trace ℂ (Fin m → ℂ)) A.toLin' = 0
        simpa only [Matrix.trace_toLin'_eq] using ht))

end IdempotentTrace

/-- A weighted block trace of an element supported in one block. -/
theorem sum_trace_single {B : Blocks} (w : Fin B.count → ℂ)
    (i : Fin B.count) (A : Matrix (Fin (B.size i)) (Fin (B.size i)) ℂ) :
    (∑ j, w j * ((Pi.single i A : B.Algebra) j).trace) =
      w i * A.trace := by
  classical
  rw [Fintype.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j h
    rw [Pi.single_eq_of_ne h, Matrix.trace_zero, mul_zero]

variable {B : Blocks} (hd : ∀ i, 0 < B.size i)

include hd in
/-- For any representation of a finite product of nonzero complex matrix
algebras, its ordinary trace is a nonnegative integer-weighted sum of the
standard block traces. The integers are ranks of images of matrix units. -/
theorem representation_trace_multiplicities {m : ℕ}
    (φ : B.Algebra →ₐ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    ∃ mult : Fin B.count → ℕ, ∀ x, (φ x).trace = ∑ i, (mult i : ℂ) * (x i).trace := by
  classical
  let T := (Matrix.traceLinearMap (Fin m) ℂ ℂ).comp φ.toLinearMap
  obtain ⟨w, hw⟩ := cyclic_block_trace T (fun x y => by
    change (φ (x * y)).trace = (φ (y * x)).trace
    simpa only [map_mul] using Matrix.trace_mul_comm (φ x) (φ y))
  have hnat : ∀ i, ∃ k : ℕ, w i = k := by
    intro i
    let j : Fin (B.size i) := ⟨0, hd i⟩
    let e : B.Algebra := Pi.single i (Matrix.single j j 1)
    obtain ⟨k, hk⟩ := idempotent_matrix_trace_nat (A := φ e) (by
      rw [← map_mul]
      simp [e, ← Pi.single_mul, Matrix.single_mul_single_same])
    refine ⟨k, ?_⟩
    simpa [T, e, sum_trace_single] using (hw e).symm.trans hk
  choose mult hm using hnat
  exact ⟨mult, fun x => by simpa [T, hm] using hw x⟩

include hd in
/-- A faithful block-algebra representation has nonnegative integer
multiplicities, and every source block occurs in at least one target block. -/
theorem faithful_block_representation_multiplicities {B' : Blocks}
    (φ : B.Algebra →ₐ[ℂ] B'.Algebra) (hinj : Function.Injective φ) :
    ∃ mult : Fin B'.count → Fin B.count → ℕ,
      (∀ i x, (φ x i).trace = ∑ j, (mult i j : ℂ) * (x j).trace) ∧
      (∀ j, ∃ i, 0 < mult i j) := by
  classical
  choose mult hmult using fun i : Fin B'.count =>
    representation_trace_multiplicities hd ((Pi.evalAlgHom ℂ _ i).comp φ)
  change ∀ i x, (φ x i).trace = ∑ j, (mult i j : ℂ) * (x j).trace at hmult
  refine ⟨mult, hmult, fun j => ?_⟩
  by_contra hn
  push Not at hn
  let k : Fin (B.size j) := ⟨0, hd j⟩
  let e : B.Algebra := Pi.single j (Matrix.single k k 1)
  have hzero : φ e = 0 := by
    funext i
    apply idempotent_matrix_eq_zero_of_trace_eq_zero
    · simpa [e, ← Pi.single_mul, Matrix.single_mul_single_same] using
        (congrFun (map_mul φ e e) i).symm
    · simpa only [e, sum_trace_single, Matrix.trace_single_eq_same, mul_one,
        Nat.eq_zero_of_le_zero (hn i), Nat.cast_zero] using hmult i e
  simpa [e] using congrArg (fun x : B.Algebra => x j k k)
    (hinj (show φ e = φ 0 from by simpa using hzero))

end PropertyF.Ground.Calculus

/-! Multiplicity weights for the pivotal trace on finite braid-image blocks. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Calculus
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable (C : BraidedFusionCategory.{v,u})

/-- The faithful inclusion of the braid algebra in the full endomorphism
algebra, expressed in their respective matrix-block presentations. -/
def braidToEndBlocks {X : C.Obj} {n : ℕ}
    {m : Fin (Ground.rank C) → ℕ}
    (e : braidTensorPower X n ≅ ⨁ (simpleCopies C m))
    {r : ℕ} {d : Fin r → ℕ}
    (b : BraidBlockPresentation X n d) :
    (Blocks.Algebra ⟨_, d⟩) →ₐ[ℂ]
      (Blocks.Algebra ⟨_, m⟩) :=
  (groundEndBlockEquiv C e).toAlgHom.comp
    ((braidAlgebra X n).val.comp b.symm.toAlgHom)

variable (p : PivotalStructure (C := C.Obj)) (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ)

/-- The categorical braid trace has the weights supplied by block multiplicities. -/
abbrev HasMultiplicityTrace {X : C.Obj} {n r : ℕ}
    {d : Fin r → ℕ} (b : BraidBlockPresentation X n d)
    (mult : Fin (Ground.rank C) → Fin r → ℕ) : Prop :=
  ∀ a : braidAlgebra X n,
    scalar (p.rightTrace (a : End (braidTensorPower X n)).asHom) =
      ∑ j, (∑ i, (mult i j : ℂ) * scalar (p.rightTrace (𝟙 (Ground.simples C i)))) *
        (b a j).trace

/-- The actual categorical trace on the braid algebra has the paper's
multiplicity-weight formula. Every retained braid block occurs in a simple
constituent's multiplicity space. -/
theorem pivotalTrace_braid_multiplicities {X : C.Obj} {n : ℕ}
    {m : Fin (Ground.rank C) → ℕ}
    (e : braidTensorPower X n ≅ ⨁ (simpleCopies C m))
    {r : ℕ} {d : Fin r → ℕ} (hd : ∀ j, 0 < d j)
    (b : BraidBlockPresentation X n d) :
    ∃ mult : Fin (Ground.rank C) → Fin r → ℕ,
      (∀ j, ∃ i, 0 < mult i j) ∧
      HasMultiplicityDecomposition m d mult ∧ HasMultiplicityTrace C p scalar b mult := by
  let F := braidToEndBlocks C e b
  obtain ⟨mult, hmult, hretained⟩ := faithful_block_representation_multiplicities hd F
    ((groundEndBlockEquiv C e).injective.comp (Subtype.val_injective.comp b.symm.injective))
  have hdim : ∀ i, m i = ∑ j, mult i j * d j := by
    intro i
    exact_mod_cast (show (m i : ℂ) = ∑ j, (mult i j : ℂ) * d j from by
      simpa only [map_one, Pi.one_apply, Matrix.trace_one, Fintype.card_fin] using hmult i 1)
  refine ⟨mult, hretained, hdim, fun a => ?_⟩
  have hi : ∀ i, (groundEndBlockEquiv C e (a : End (braidTensorPower X n)) i).trace =
      ∑ j, (mult i j : ℂ) * (b a j).trace := by
    intro i
    simpa [F, braidToEndBlocks] using hmult i (b a)
  rw [pivotalTrace_groundEndBlocks C e _ p scalar]
  simp_rw [hi, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, mul_assoc, mul_left_comm]

/-- Finite categorical braid images admit unitary blocks and natural-number
multiplicities with the actual pivotal trace formula and retention. -/
theorem exists_unitary_braid_trace_blocks
    {X : C.Obj} {n : ℕ}
    (hfinite : Finite (braidImage X n)) :
    ∃ (r : ℕ) (d : Fin r → ℕ)
      (b : BraidBlockPresentation X n d)
      (mult : Fin (Ground.rank C) → Fin r → ℕ),
      (∀ j, 0 < d j) ∧
      IsUnitaryBraidPresentation b ∧
      (∀ j, ∃ i, 0 < mult i j) ∧
      HasMultiplicityDecomposition
        (fun i => Module.finrank ℂ (Ground.simples C i ⟶ braidTensorPower X n)) d mult ∧
      HasMultiplicityTrace C p scalar b mult := by
  let m : Fin (Ground.rank C) → ℕ := fun i =>
    Module.finrank ℂ (Ground.simples C i ⟶ braidTensorPower X n)
  obtain ⟨e⟩ := Ground.exists_canonical_decomposition C (braidTensorPower X n)
  obtain ⟨r, d, b, hnonzero, hunitary⟩ := braidAlgebra_unitary_blocks hfinite
  have hd : ∀ j, 0 < d j := fun j => Nat.pos_of_ne_zero (hnonzero j).ne
  obtain ⟨mult, hret, hdim, htrace⟩ :=
    pivotalTrace_braid_multiplicities C p scalar e hd b
  exact ⟨r, d, b, mult, hd, hunitary, hret, hdim, htrace⟩

end PropertyF.Ground.Calculus
