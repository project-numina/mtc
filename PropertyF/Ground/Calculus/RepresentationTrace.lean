module
public import PropertyF.Ground.Calculus.CyclicTrace
public import Mathlib.LinearAlgebra.Trace

/-! Multiplicities in traces of representations of matrix-block algebras. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Calculus

/-- The trace of an idempotent complex matrix is a nonnegative integer. -/
theorem idempotent_matrix_trace_nat {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
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
theorem representation_trace_multiplicities {n m : ℕ} (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i)
    (φ : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    ∃ mult : Fin n → ℕ, ∀ x, (φ x).trace = ∑ i, (mult i : ℂ) * (x i).trace := by
  classical
  let T := (Matrix.traceLinearMap (Fin m) ℂ ℂ).comp φ.toLinearMap
  have hT : ∀ x y, T (x * y) = T (y * x) := by
    intro x y
    change (φ (x * y)).trace = (φ (y * x)).trace
    rw [map_mul, map_mul]
    exact Matrix.trace_mul_comm _ _
  obtain ⟨w, hw⟩ := cyclic_block_trace d T hT
  have hnat : ∀ i, ∃ k : ℕ, w i = k := by
    intro i
    let j : Fin (d i) := ⟨0, hd i⟩
    let e : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ := Pi.single i (Matrix.single j j 1)
    have he : e * e = e := by
      ext k a b
      by_cases h : k = i
      · subst k
        simp [e]
      · simp [e, h]
    have hφ : φ e * φ e = φ e := by rw [← map_mul, he]
    obtain ⟨k, hk⟩ := idempotent_matrix_trace_nat (φ e) hφ
    refine ⟨k, ?_⟩
    have ht := hw e
    have ht' : (φ e).trace = w i := by
      change (φ e).trace = ∑ k, w k * (e k).trace at ht
      rw [Finset.sum_eq_single i] at ht
      · simpa [e] using ht
      · intro j hj hji
        have hz : e j = 0 := Pi.single_eq_of_ne hji _
        simp [hz]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    exact ht'.symm.trans hk
  choose mult hm using hnat
  refine ⟨mult, fun x => ?_⟩
  have hx := hw x
  change (φ x).trace = ∑ i, w i * (x i).trace at hx
  simpa [hm] using hx

/-- A complex idempotent matrix with zero trace is zero. -/
theorem idempotent_matrix_eq_zero_of_trace_eq_zero {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (hA : A * A = A) (ht : A.trace = 0) : A = 0 := by
  let p := A.toLin'
  have hp : IsIdempotentElem p := by
    change A.toLin' * A.toLin' = A.toLin'
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hA]
  have ht' : LinearMap.trace ℂ (Fin m → ℂ) p = 0 := by simpa [p] using ht
  have hz : p = 0 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff hp).mp ht'
  apply Matrix.toLinAlgEquiv'.injective
  simpa [p] using hz

/-- A faithful block-algebra representation has nonnegative integer
multiplicities, and every source block occurs in at least one target block. -/
theorem faithful_block_representation_multiplicities {n m : ℕ}
    (d : Fin n → ℕ) (q : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (φ : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ]
      (∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ)) (hinj : Function.Injective φ) :
    ∃ mult : Fin m → Fin n → ℕ,
      (∀ i x, (φ x i).trace = ∑ j, (mult i j : ℂ) * (x j).trace) ∧
      (∀ j, ∃ i, 0 < mult i j) := by
  classical
  have hm : ∀ i, ∃ k : Fin n → ℕ, ∀ x,
      (φ x i).trace = ∑ j, (k j : ℂ) * (x j).trace := by
    intro i
    exact representation_trace_multiplicities d hd ((Pi.evalAlgHom ℂ _ i).comp φ)
  choose mult hmult using hm
  refine ⟨mult, hmult, fun j => ?_⟩
  by_contra hn
  push Not at hn
  let k : Fin (d j) := ⟨0, hd j⟩
  let e : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ := Pi.single j (Matrix.single k k 1)
  have he : e * e = e := by
    ext i a b
    by_cases h : i = j
    · subst i
      simp [e]
    · simp [e, h]
  have hzero : φ e = 0 := by
    funext i
    have hidem : φ e i * φ e i = φ e i := by
      have h := congrFun (map_mul φ e e) i
      simpa [he] using h.symm
    have ht : (φ e i).trace = 0 := by
      rw [hmult]
      apply Finset.sum_eq_zero
      intro r _
      by_cases h : r = j
      · subst r
        simp [Nat.eq_zero_of_le_zero (hn i)]
      · have hz : e r = 0 := Pi.single_eq_of_ne h _
        simp [hz]
    exact idempotent_matrix_eq_zero_of_trace_eq_zero _ hidem ht
  have hezero : e = 0 := hinj (by simpa using hzero)
  have hentry := congrArg (fun x : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ => x j k k) hezero
  simp [e] at hentry

end PropertyF.Ground.Calculus
