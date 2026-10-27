module
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic

@[expose] public noncomputable section
namespace PropertyF.Ground.Dimensions

/-- The trace of a complex involution is the difference of its positive and
negative eigenspace dimensions. This is the finite-dimensional ingredient in
ENO's trace matrices. -/
theorem involution_trace_formula {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hT : T * T = 1) :
    ∃ m : ℕ, m ≤ Module.finrank ℂ V ∧
      LinearMap.trace ℂ V T = 2 * (m : ℂ) - (Module.finrank ℂ V : ℂ) := by
  let P : V →ₗ[ℂ] V := (2 : ℂ)⁻¹ • (1 + T)
  have hinv (x : V) : T (T x) = x := by
    have h := congrArg (fun f : V →ₗ[ℂ] V => f x) hT
    simpa using h
  have hp : IsIdempotentElem P := by
    change P * P = P
    ext x
    change P (P x) = P x
    simp only [P, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
      map_smul, map_add, hinv, smul_add, smul_smul]
    module
  have htrace := (LinearMap.IsIdempotentElem.isProj_range P hp).trace
  have hP : (2 : ℂ) • P = 1 + T := by
    ext x
    simp [P]
  have htp := congrArg (LinearMap.trace ℂ V) hP
  simp only [map_smul, map_add, LinearMap.trace_id, smul_eq_mul] at htp
  refine ⟨Module.finrank ℂ (LinearMap.range P), (LinearMap.range P).finrank_le, ?_⟩
  rw [htrace] at htp
  have hid : LinearMap.trace ℂ V (1 : V →ₗ[ℂ] V) = (Module.finrank ℂ V : ℂ) :=
    LinearMap.trace_id ℂ V
  rw [hid] at htp
  linear_combination -htp

/-- The trace of an involution is an integer whose absolute value is at most
the dimension of its underlying vector space. -/
theorem involution_trace_integer_bound {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hT : T * T = 1) :
    ∃ n : ℤ, LinearMap.trace ℂ V T = (n : ℂ) ∧
      |n| ≤ (Module.finrank ℂ V : ℤ) := by
  obtain ⟨m, hm, htrace⟩ := involution_trace_formula T hT
  refine ⟨2 * (m : ℤ) - (Module.finrank ℂ V : ℤ), ?_, ?_⟩
  · simpa using htrace
  · have hm' : (m : ℤ) ≤ (Module.finrank ℂ V : ℤ) := by exact_mod_cast hm
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := by positivity
    rw [abs_le]
    constructor <;> omega

/-- An involution whose trace reaches the dimension is the identity. -/
theorem involution_eq_one_of_trace_eq_finrank {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hT : T * T = 1)
    (htrace : LinearMap.trace ℂ V T = (Module.finrank ℂ V : ℂ)) : T = 1 := by
  let Q : V →ₗ[ℂ] V := (2 : ℂ)⁻¹ • (1 - T)
  have hinv (x : V) : T (T x) = x := by
    have h := congrArg (fun f : V →ₗ[ℂ] V => f x) hT
    simpa using h
  have hq : IsIdempotentElem Q := by
    change Q * Q = Q
    ext x
    change Q (Q x) = Q x
    simp only [Q, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply,
      map_smul, map_sub, hinv, smul_sub, smul_smul]
    module
  have hqt : LinearMap.trace ℂ V Q = 0 := by
    have hid : LinearMap.trace ℂ V (1 : V →ₗ[ℂ] V) = (Module.finrank ℂ V : ℂ) :=
      LinearMap.trace_id ℂ V
    simp [Q, hid, htrace]
  have hzero : Q = 0 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff hq).mp hqt
  have hQ : (2 : ℂ) • Q = 1 - T := by
    ext x
    simp [Q]
  rw [hzero, smul_zero] at hQ
  exact (sub_eq_zero.mp hQ.symm).symm

/-- An involution whose trace has maximal magnitude is the corresponding
scalar sign times the identity. -/
theorem involution_eq_sign_of_trace_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hT : T * T = 1) (s : ℂ)
    (hs : s * s = 1) (htrace : LinearMap.trace ℂ V T = s * (Module.finrank ℂ V : ℂ)) :
    T = s • (1 : V →ₗ[ℂ] V) := by
  rcases mul_self_eq_one_iff.mp hs with h | h
  · subst s
    simpa using involution_eq_one_of_trace_eq_finrank T hT (by simpa using htrace)
  · subst s
    have hneg : (-T) * (-T) = 1 := by simpa using hT
    have ht : LinearMap.trace ℂ V (-T) = (Module.finrank ℂ V : ℂ) := by
      simp only [map_neg, neg_one_mul] at htrace ⊢
      rw [htrace, neg_neg]
    have h := involution_eq_one_of_trace_eq_finrank (-T) hneg ht
    simpa using congrArg Neg.neg h

end PropertyF.Ground.Dimensions
