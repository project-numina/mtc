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

/-! The pivotal trace in the simple-constituent matrix decomposition. -/

open PropertyF.Ground.Dimensions

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Calculus
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Scalar identification for a chosen simple object. -/
def groundSimpleScalar (C : BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) :
    End (Ground.simples C i) ≃ₐ[ℂ] ℂ := by
  let _ : Simple (Ground.simples C i) := Ground.simples_simple C i
  let _ : FiniteDimensional ℂ (Ground.simples C i ⟶ Ground.simples C i) :=
    Ground.IsFusionCategory.hom_finite _ _
  exact simpleEndScalar _

/-- Evaluating a simple endomorphism at its Schur scalar recovers the morphism. -/
theorem groundSimpleScalar_smul_id (C : BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) (a : End (Ground.simples C i)) :
    (groundSimpleScalar C i a) • 𝟙 (Ground.simples C i) = a.asHom := by
  have h := (groundSimpleScalar C i).symm_apply_apply a
  change (algebraMap ℂ (End (Ground.simples C i))) (groundSimpleScalar C i a) = a at h
  have h' := congrArg End.asHom h
  simpa [Algebra.algebraMap_eq_smul_one] using h'

set_option backward.isDefEq.respectTransparency false in
/-- A diagonal matrix coefficient is the scalar of the corresponding simple
biproduct component of the transported endomorphism. -/
theorem groundEndBlockEquiv_diagonal (C : BraidedFusionCategory.{v,u})
    {X : C.Obj} {m : Fin (Ground.rank C) → ℕ}
    (e : X ≅ ⨁ (fun p : Σ i, Fin (m i) => Ground.simples C p.1))
    (a : End X) (i : Fin (Ground.rank C)) (j : Fin (m i)) :
    groundEndBlockEquiv C X m e a i j j =
      groundSimpleScalar C i (End.of
        (biproduct.ι (fun p : Σ i, Fin (m i) => Ground.simples C p.1) ⟨i, j⟩ ≫
          e.inv ≫ a.asHom ≫ e.hom ≫
          biproduct.π (fun p : Σ i, Fin (m i) => Ground.simples C p.1) ⟨i, j⟩)) := by
  classical
  simp [groundEndBlockEquiv, orthogonalEndBlocks, isoEndAlgEquiv,
    simpleFiberEquiv, groundSimpleScalar, HomOrthogonal.matrixDecompositionAddEquiv, HomOrthogonal.matrixDecomposition,
    Matrix.reindexAlgEquiv, Matrix.reindexRingEquiv, Matrix.reindexAddEquiv,
    Matrix.reindex, Category.assoc, biproduct.components]

set_option backward.isDefEq.respectTransparency false in
/-- The actual pivotal trace on a fusion-category endomorphism is the sum of
simple categorical dimensions times the ordinary traces of its constituent
multiplicity blocks. -/
theorem pivotalTrace_groundEndBlocks (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj))
    (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ) {X : C.Obj} {m : Fin (Ground.rank C) → ℕ}
    (e : X ≅ ⨁ (fun p : Σ i, Fin (m i) => Ground.simples C p.1)) (a : End X) :
    scalar (p.rightTrace a.asHom) = ∑ i,
      scalar (p.rightTrace (𝟙 (Ground.simples C i))) *
        (groundEndBlockEquiv C X m e a i).trace := by
  classical
  let F : (Σ i, Fin (m i)) → C.Obj := fun q => Ground.simples C q.1
  let z : (⨁ F) ⟶ (⨁ F) := e.inv ≫ a.asHom ≫ e.hom
  have hz : p.rightTrace z = p.rightTrace a.asHom := by
    have h := p.rightTrace_cyclic e.inv (a.asHom ≫ e.hom)
    simpa [z, Category.assoc] using h
  have hc (q : Σ i, Fin (m i)) : biproduct.ι F q ≫ z ≫ biproduct.π F q =
      (groundEndBlockEquiv C X m e a q.1 q.2 q.2) • 𝟙 (F q) := by
    rcases q with ⟨i, j⟩
    rw [groundEndBlockEquiv_diagonal]
    simpa [z, F, Category.assoc] using (groundSimpleScalar_smul_id C i _).symm
  have h := cyclicTrace_biproduct_scalar_blocks (rightTraceLinear p)
    (fun f g => p.rightTrace_cyclic f g) F z
    (fun q => groundEndBlockEquiv C X m e a q.1 q.2 q.2) hc
  have h' := congrArg scalar h
  simp only [map_sum, map_smul, smul_eq_mul, rightTraceLinear, LinearMap.coe_mk,
    AddHom.coe_mk] at h'
  rw [← hz, h', Fintype.sum_sigma]
  simp [F, Matrix.trace, Finset.mul_sum, mul_comm]

end PropertyF.Ground.Calculus

/-! Consequences of the categorical multiplicity weights. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Calculus

/-- The block trace mass is the constituent multiplicity mass whenever the
actual representation dimensions decompose into braid-block dimensions. -/
theorem multiplicity_mass_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : ι → ℕ) (d : κ → ℕ) (mult : ι → κ → ℕ) (fp : ι → ℝ)
    (hdim : ∀ i, m i = ∑ j, mult i j * d j) :
    (∑ j, (∑ i, (mult i j : ℝ) * fp i) * (d j : ℝ)) =
      ∑ i, (m i : ℝ) * fp i := by
  simp only [hdim, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_comm, mul_left_comm]

/-- The paper's Galois-transported multiplicity weights cannot vanish when
all original constituent dimensions are positive and the block is retained. -/
theorem transported_weight_ne_zero {ι : Type*} [Fintype ι]
    (mult : ι → ℕ) (dim : ι → ℝ) (σ : ℂ ≃+* ℂ)
    (hpos : ∀ i, 0 < dim i) (hret : ∃ i, 0 < mult i) :
    (∑ i, (mult i : ℂ) * σ (dim i : ℂ)) ≠ 0 := by
  have hsum : 0 < ∑ i, (mult i : ℝ) * dim i := by
    obtain ⟨i, hi⟩ := hret
    exact Finset.sum_pos' (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hpos i).le)
      ⟨i, Finset.mem_univ _, mul_pos (by exact_mod_cast hi) (hpos i)⟩
  intro hz
  have hzero : (∑ i, (mult i : ℂ) * (dim i : ℂ)) = 0 := by
    apply σ.injective
    simp [map_sum, map_mul, hz]
  exact (ne_of_gt hsum) (by exact_mod_cast hzero)

end PropertyF.Ground.Calculus

/-! Cyclic linear functionals on complex matrix algebras. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Calculus

/-- A cyclic linear functional on a complex matrix algebra is a scalar
multiple of ordinary matrix trace, including the zero-dimensional case. -/
theorem cyclic_matrix_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ →ₗ[ℂ] ℂ) (hT : ∀ X Y, T (X * Y) = T (Y * X)) :
    ∃ w : ℂ, ∀ X, T X = w * X.trace := by
  classical
  by_cases hn : Nonempty ι
  · let i₀ : ι := Classical.choice hn
    let w := T (Matrix.single i₀ i₀ 1)
    refine ⟨w, fun X => ?_⟩
    have hs : ∀ i j (a : ℂ), T (Matrix.single i j a) =
        w * (Matrix.single i j a).trace := by
      intro i j a
      by_cases hij : i = j
      · subst j
        have hdiag := hT (Matrix.single i i₀ a) (Matrix.single i₀ i (1 : ℂ))
        simp only [Matrix.single_mul_single_same, mul_one, one_mul] at hdiag
        have hscalar : Matrix.single i₀ i₀ a = a • Matrix.single i₀ i₀ (1 : ℂ) := by
          simp [Matrix.smul_single]
        rw [hdiag, hscalar, map_smul, Matrix.trace_single_eq_same]
        simp [w, mul_comm]
      · have hoff := hT (Matrix.single i i (1 : ℂ)) (Matrix.single i j a)
        have hz : Matrix.single i j a * Matrix.single i i (1 : ℂ) = 0 :=
          Matrix.single_mul_single_of_ne a i j i (Ne.symm hij) 1
        simp only [Matrix.single_mul_single_same, one_mul, hz, map_zero] at hoff
        rw [hoff, Matrix.trace_single_eq_of_ne _ _ _ hij, mul_zero]
    induction X using Matrix.induction_on with
    | h_add X Y hX hY => simp [hX, hY, Matrix.trace_add, mul_add]
    | h_std_basis i j a => exact hs i j a
  · have hempty : IsEmpty ι := not_nonempty_iff.mp hn
    let _ := hempty
    refine ⟨0, fun X => ?_⟩
    have hX : X = 0 := Subsingleton.elim _ _
    simp [hX]

/-- Every cyclic linear functional on a finite product of matrix algebras is
a weighted sum of ordinary block traces. The weights may be arbitrary complex
numbers; reality and categorical multiplicities require additional input. -/
theorem cyclic_block_trace {n : ℕ} {d : Fin n → ℕ}
    (T : (PropertyF.Blocks.Algebra ⟨_, d⟩) →ₗ[ℂ] ℂ)
    (hT : ∀ X Y, T (X * Y) = T (Y * X)) :
    ∃ w : Fin n → ℂ, ∀ X, T X = ∑ i, w i * (X i).trace := by
  classical
  let V : Fin n → Type := fun i => Matrix (Fin (d i)) (Fin (d i)) ℂ
  let Tblock (i : Fin n) : V i →ₗ[ℂ] ℂ := T.comp (LinearMap.single ℂ V i)
  have hc (i : Fin n) : ∀ X Y : V i, Tblock i (X * Y) = Tblock i (Y * X) := by
    intro X Y
    change T (Pi.single i (X * Y)) = T (Pi.single i (Y * X))
    rw [Pi.single_mul, Pi.single_mul]
    exact hT _ _
  have hw : ∀ i, ∃ w : ℂ, ∀ X : V i, Tblock i X = w * X.trace :=
    fun i => cyclic_matrix_trace (Tblock i) (hc i)
  choose w hw using hw
  refine ⟨w, fun X => ?_⟩
  calc
    T X = ∑ i, Tblock i (X i) := by
      conv_lhs => rw [← LinearMap.sum_single_apply V X]
      simp [Tblock]
    _ = ∑ i, w i * (X i).trace := by simp [hw]

end PropertyF.Ground.Calculus

/-! Multiplicities in traces of representations of matrix-block algebras. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Calculus

/-- The trace of an idempotent complex matrix is a nonnegative integer. -/
theorem idempotent_matrix_trace_nat {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : A * A = A) : ∃ n : ℕ, A.trace = n := by
  let p := A.toLin'
  have hp : IsIdempotentElem p := by
    change A.toLin' * A.toLin' = A.toLin'
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hA]
  refine ⟨Module.finrank ℂ (LinearMap.range p), ?_⟩
  simpa only [p, Matrix.trace_toLin'_eq] using ((LinearMap.isProj_range_iff_isIdempotentElem p).2 hp).trace

/-- For any representation of a finite product of nonzero complex matrix
algebras, its ordinary trace is a nonnegative integer-weighted sum of the
standard block traces. The integers are ranks of images of matrix units. -/
theorem representation_trace_multiplicities {n m : ℕ} {d : Fin n → ℕ}
    (hd : ∀ i, 0 < d i)
    (φ : (PropertyF.Blocks.Algebra ⟨_, d⟩) →ₐ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    ∃ mult : Fin n → ℕ, ∀ x, (φ x).trace = ∑ i, (mult i : ℂ) * (x i).trace := by
  classical
  let T := (Matrix.traceLinearMap (Fin m) ℂ ℂ).comp φ.toLinearMap
  have hT : ∀ x y, T (x * y) = T (y * x) := by
    intro x y
    change (φ (x * y)).trace = (φ (y * x)).trace
    simpa only [map_mul] using Matrix.trace_mul_comm (φ x) (φ y)
  obtain ⟨w, hw⟩ := cyclic_block_trace T hT
  have hnat : ∀ i, ∃ k : ℕ, w i = k := by
    intro i
    let j : Fin (d i) := ⟨0, hd i⟩
    let e : PropertyF.Blocks.Algebra ⟨_, d⟩ := Pi.single i (Matrix.single j j 1)
    have he : e * e = e := by
      simp [e, ← Pi.single_mul, Matrix.single_mul_single_same]
    have hφ : φ e * φ e = φ e := by rw [← map_mul, he]
    obtain ⟨k, hk⟩ := idempotent_matrix_trace_nat hφ
    refine ⟨k, ?_⟩
    have ht := hw e
    have ht' : (φ e).trace = w i := by
      change (φ e).trace = ∑ k, w k * (e k).trace at ht
      rw [Finset.sum_eq_single i] at ht
      · simpa [e] using ht
      · intro j _ hji
        simp [e, Pi.single_eq_of_ne hji]
      · simp
    exact ht'.symm.trans hk
  choose mult hm using hnat
  refine ⟨mult, fun x => ?_⟩
  have hx := hw x
  change (φ x).trace = ∑ i, w i * (x i).trace at hx
  simpa [hm] using hx

/-- A complex idempotent matrix with zero trace is zero. -/
theorem idempotent_matrix_eq_zero_of_trace_eq_zero {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℂ} (hA : A * A = A) (ht : A.trace = 0) : A = 0 := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_zero]
  change A.toLin' = 0
  apply (LinearMap.IsIdempotentElem.trace_eq_zero_iff ?_).mp
  · simpa using ht
  · change A.toLin' * A.toLin' = A.toLin'
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hA]

/-- A faithful block-algebra representation has nonnegative integer
multiplicities, and every source block occurs in at least one target block. -/
theorem faithful_block_representation_multiplicities {n m : ℕ}
    {d : Fin n → ℕ} {q : Fin m → ℕ} (hd : ∀ i, 0 < d i)
    (φ : (PropertyF.Blocks.Algebra ⟨_, d⟩) →ₐ[ℂ]
      (PropertyF.Blocks.Algebra ⟨_, q⟩)) (hinj : Function.Injective φ) :
    ∃ mult : Fin m → Fin n → ℕ,
      (∀ i x, (φ x i).trace = ∑ j, (mult i j : ℂ) * (x j).trace) ∧
      (∀ j, ∃ i, 0 < mult i j) := by
  classical
  have hm : ∀ i, ∃ k : Fin n → ℕ, ∀ x,
      (φ x i).trace = ∑ j, (k j : ℂ) * (x j).trace := by
    intro i
    exact representation_trace_multiplicities hd ((Pi.evalAlgHom ℂ _ i).comp φ)
  choose mult hmult using hm
  refine ⟨mult, hmult, fun j => ?_⟩
  by_contra hn
  push Not at hn
  let k : Fin (d j) := ⟨0, hd j⟩
  let e : PropertyF.Blocks.Algebra ⟨_, d⟩ := Pi.single j (Matrix.single k k 1)
  have he : e * e = e := by
    simp [e, ← Pi.single_mul, Matrix.single_mul_single_same]
  have hzero : φ e = 0 := by
    funext i
    have hidem : φ e i * φ e i = φ e i := by
      have h := congrFun (map_mul φ e e) i
      simpa [he] using h.symm
    have ht : (φ e i).trace = 0 := by
      rw [hmult]
      rw [Finset.sum_eq_single j]
      · simp [Nat.eq_zero_of_le_zero (hn i)]
      · intro r _ h
        simp [e, Pi.single_eq_of_ne h]
      · simp
    exact idempotent_matrix_eq_zero_of_trace_eq_zero hidem ht
  have hezero : e = 0 := hinj (by simpa using hzero)
  have hentry := congrArg (fun x : PropertyF.Blocks.Algebra ⟨_, d⟩ => x j k k) hezero
  simp [e] at hentry

end PropertyF.Ground.Calculus

/-! Multiplicity weights for the pivotal trace on finite braid-image blocks. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Calculus
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The faithful inclusion of the braid algebra in the full endomorphism
algebra, expressed in their respective matrix-block presentations. -/
def braidToEndBlocks (C : BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (m : Fin (Ground.rank C) → ℕ)
    (e : tensorPower X (n + 2) ≅ ⨁ (fun p : Σ i, Fin (m i) => Ground.simples C p.1))
    (r : ℕ) (d : Fin r → ℕ)
    (b : braidAlgebra X n ≃ₐ[ℂ] PropertyF.Blocks.Algebra ⟨_, d⟩) :
    (PropertyF.Blocks.Algebra ⟨_, d⟩) →ₐ[ℂ]
      (PropertyF.Blocks.Algebra ⟨_, m⟩) :=
  (groundEndBlockEquiv C _ m e).toAlgHom.comp
    ((braidAlgebra X n).val.comp b.symm.toAlgHom)

/-- The categorical inclusion is faithful, so no finite braid-image block is lost. -/
theorem braidToEndBlocks_injective (C : BraidedFusionCategory.{v,u}) {X : C.Obj}
    {n : ℕ} {m : Fin (Ground.rank C) → ℕ}
    (e : tensorPower X (n + 2) ≅ ⨁ (fun p : Σ i, Fin (m i) => Ground.simples C p.1))
    {r : ℕ} {d : Fin r → ℕ}
    (b : braidAlgebra X n ≃ₐ[ℂ] PropertyF.Blocks.Algebra ⟨_, d⟩) :
    Function.Injective (braidToEndBlocks C X n m e r d b) := by
  intro x y h
  apply b.symm.injective
  apply Subtype.ext
  apply (groundEndBlockEquiv C _ m e).injective
  exact h

/-- The actual categorical trace on the braid algebra has the paper's
multiplicity-weight formula. Every retained braid block occurs in a simple
constituent's multiplicity space. -/
theorem pivotalTrace_braid_multiplicities
    (C : BraidedFusionCategory.{v,u}) {X : C.Obj} {n : ℕ}
    (p : PivotalStructure (C := C.Obj)) (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ)
    {m : Fin (Ground.rank C) → ℕ}
    (e : tensorPower X (n + 2) ≅ ⨁ (fun q : Σ i, Fin (m i) => Ground.simples C q.1))
    {r : ℕ} {d : Fin r → ℕ} (hd : ∀ j, 0 < d j)
    (b : braidAlgebra X n ≃ₐ[ℂ] PropertyF.Blocks.Algebra ⟨_, d⟩) :
    ∃ mult : Fin (Ground.rank C) → Fin r → ℕ,
      (∀ j, ∃ i, 0 < mult i j) ∧
      (∀ i, m i = ∑ j, mult i j * d j) ∧
      ∀ a : braidAlgebra X n,
        scalar (p.rightTrace (a : End (tensorPower X (n + 2))).asHom) =
          ∑ j, (∑ i, (mult i j : ℂ) * scalar (p.rightTrace (𝟙 (Ground.simples C i)))) *
            (b a j).trace := by
  let F := braidToEndBlocks C X n m e r d b
  obtain ⟨mult, hmult, hretained⟩ := faithful_block_representation_multiplicities hd F
    (braidToEndBlocks_injective C e b)
  have hdim : ∀ i, m i = ∑ j, mult i j * d j := by
    intro i
    have h := hmult i 1
    simp only [map_one, Pi.one_apply, Matrix.trace_one, Fintype.card_fin] at h
    exact_mod_cast h
  refine ⟨mult, hretained, hdim, fun a => ?_⟩
  have hi : ∀ i, (groundEndBlockEquiv C _ m e (a : End (tensorPower X (n + 2))) i).trace =
      ∑ j, (mult i j : ℂ) * (b a j).trace := by
    intro i
    have h := hmult i (b a)
    change (groundEndBlockEquiv C _ m e ((b.symm (b a) : braidAlgebra X n) : End _) i).trace = _ at h
    rw [b.symm_apply_apply] at h
    exact h
  rw [pivotalTrace_groundEndBlocks C p scalar e]
  simp_rw [hi, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, mul_assoc, mul_left_comm]

/-- Finite categorical braid images admit unitary blocks and natural-number
multiplicities with the actual pivotal trace formula and retention. -/
theorem exists_unitary_braid_trace_blocks
    (C : BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (hfinite : Finite (braidImage X n))
    (p : PivotalStructure (C := C.Obj)) (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ) :
    ∃ (r : ℕ) (d : Fin r → ℕ)
      (b : braidAlgebra X n ≃ₐ[ℂ] PropertyF.Blocks.Algebra ⟨_, d⟩)
      (mult : Fin (Ground.rank C) → Fin r → ℕ),
      (∀ j, 0 < d j) ∧
      IsUnitaryPresentation (braidEndRepresentation X n) b ∧
      (∀ j, ∃ i, 0 < mult i j) ∧
      (∀ i, Module.finrank ℂ (Ground.simples C i ⟶ tensorPower X (n + 2)) =
        ∑ j, mult i j * d j) ∧
      ∀ a : braidAlgebra X n,
        scalar (p.rightTrace (a : End (tensorPower X (n + 2))).asHom) =
          ∑ j, (∑ i, (mult i j : ℂ) * scalar (p.rightTrace (𝟙 (Ground.simples C i)))) *
            (b a j).trace := by
  let m : Fin (Ground.rank C) → ℕ := fun i =>
    Module.finrank ℂ (Ground.simples C i ⟶ tensorPower X (n + 2))
  obtain ⟨e⟩ := Ground.exists_canonical_decomposition C (tensorPower X (n + 2))
  obtain ⟨r, d, b, hnonzero, hunitary⟩ := braidAlgebra_unitary_blocks X n hfinite
  have hd : ∀ j, 0 < d j := fun j => Nat.pos_of_ne_zero (hnonzero j).ne
  obtain ⟨mult, hret, hdim, htrace⟩ :=
    pivotalTrace_braid_multiplicities C p scalar e hd b
  exact ⟨r, d, b, mult, hd, hunitary, hret, hdim, htrace⟩

end PropertyF.Ground.Calculus
