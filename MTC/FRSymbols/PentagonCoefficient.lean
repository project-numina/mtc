module
public import MTC.FRSymbols.Cyclotomic
import Mathlib.Tactic.Ring

/-!
# Computable power-basis arithmetic for pentagon certificates

A list holds rational coefficients in increasing degree order. The executable
comparison uses the monic relation supplied with the table. Lean checks that
relation once at the primitive root specified by the conductor.
-/

@[expose] public section
namespace MTC.FRSymbols.PentagonCoefficient

abbrev Coeff := List ℚ

/-- Interpret a coefficient vector by Horner's rule at the chosen primitive root. -/
noncomputable def value (n : ℕ) : Coeff → ExactCyclotomic n
  | [] => 0
  | q :: p => AdjoinRoot.of (Polynomial.cyclotomic n ℚ) q + cyclotomicGenerator n * value n p

def add : Coeff → Coeff → Coeff
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => (x + y) :: add a b

def scale (q : ℚ) (p : Coeff) : Coeff := p.map (q * ·)

def mul : Coeff → Coeff → Coeff
  | [], _ => []
  | x :: a, b => add (scale x b) (0 :: mul a b)

@[simp] theorem value_nil (n : ℕ) : value n [] = 0 := rfl

@[simp] theorem value_one (n : ℕ) : value n [1] = 1 := by simp [value]

@[simp] theorem value_add (n : ℕ) (a b : Coeff) : value n (add a b) = value n a + value n b := by
  induction a generalizing b with
  | nil => simp [add]
  | cons x a ih =>
    cases b with
    | nil => simp [add]
    | cons y b => simp [add, value, ih]; ring

@[simp] theorem value_scale (n : ℕ) (q : ℚ) (p : Coeff) :
    value n (scale q p) = AdjoinRoot.of (Polynomial.cyclotomic n ℚ) q * value n p := by
  induction p with
  | nil => simp [scale]
  | cons x p ih =>
    change value n ((q * x) :: scale q p) = _
    simp only [value, map_mul, ih]
    ring

@[simp] theorem value_mul (n : ℕ) (a b : Coeff) : value n (mul a b) = value n a * value n b := by
  induction a with
  | nil => simp [mul]
  | cons x a ih =>
    simp only [mul, value_add, value_scale, value, map_zero, zero_add, ih]
    ring

private theorem value_append (n : ℕ) (p q : Coeff) :
    value n (p ++ q) = value n p + cyclotomicGenerator n ^ p.length * value n q := by
  induction p with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, value, ih, List.length_cons, pow_succ]
    ring

private theorem value_split (n d : ℕ) (p : Coeff) :
    value n p = value n (p.take d) + cyclotomicGenerator n ^ d * value n (p.drop d) := by
  induction d generalizing p with
  | zero => simp
  | succ d ih =>
    cases p with
    | nil => simp
    | cons x xs =>
      simp only [List.take_succ_cons, List.drop_succ_cons, value, pow_succ]
      rw [ih xs]
      ring

/-- Substituting the monic relation removes at least one degree on each pass.
The fuel is the length of the polynomial before the first substitution. -/
def reduce (low : Coeff) : ℕ → Coeff → Coeff
  | 0, p => p
  | fuel + 1, p =>
    if p.length ≤ low.length then p
    else reduce low fuel (add (p.take low.length) (mul (scale (-1) low) (p.drop low.length)))

private theorem value_reduce (n : ℕ) (low : Coeff) (h : value n (low ++ [1]) = 0)
    (fuel : ℕ) (p : Coeff) : value n (reduce low fuel p) = value n p := by
  have hrel : -value n low = cyclotomicGenerator n ^ low.length := by
    have hz : value n low + cyclotomicGenerator n ^ low.length = 0 := by
      simpa only [value_append, value_one, mul_one] using h
    calc
      -value n low = -value n low + (value n low + cyclotomicGenerator n ^ low.length) := by rw [hz, add_zero]
      _ = _ := by ring
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
    simp only [reduce]
    split
    · rfl
    · rw [ih, value_add, value_mul, value_scale, map_neg, map_one, neg_one_mul, hrel]
      exact (value_split n low.length p).symm

/-- Compare exact coefficients modulo the monic polynomial with lower terms
`low`. Empty and zero-padded encodings of the same polynomial compare equal. -/
def eqMod (low a b : Coeff) : Bool :=
  let diff := add a (scale (-1) b)
  (reduce low diff.length diff).all (· == 0)

private theorem value_all_zero (n : ℕ) (p : Coeff) (h : p.all (· == 0) = true) :
    value n p = 0 := by
  induction p with
  | nil => rfl
  | cons q p ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [value, h.1, ih h.2]

theorem eqMod_sound (n : ℕ) (low a b : Coeff) (hm : value n (low ++ [1]) = 0)
    (h : eqMod low a b = true) : value n a = value n b := by
  have hz := value_all_zero n _ h
  rw [value_reduce n low hm, value_add, value_scale, map_neg, map_one, neg_one_mul] at hz
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hz)

def unityTail : ℕ → Coeff
  | 0 => []
  | k + 1 => -1 :: List.replicate k 0

private theorem value_zeros (n k : ℕ) : value n (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, value, ih]

private theorem unity_relation (n : ℕ) [NeZero n] :
    value n (unityTail n ++ [1]) = 0 := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ k =>
    rw [value_append]
    simp [unityTail, value, value_zeros, cyclotomicGenerator_pow]

def factor (k : ℕ) : Coeff := add (List.replicate k 0 ++ [1]) [-1]

private theorem value_factor (n k : ℕ) :
    value n (factor k) = cyclotomicGenerator n ^ k - 1 := by
  simp [factor, value_append, value, value_zeros, sub_eq_add_neg]

/-- A factor for each proper positive divisor kills every nonprimitive root
of X^n-1. These same factors are nonzero at the primitive root. -/
def factors (n : ℕ) : Coeff :=
  ((List.range n).filter (fun k => 0 < k && n % k == 0)).foldr (fun k acc => mul (factor k) acc) [1]

private theorem factors_nonzero (n : ℕ) [NeZero n] : value n (factors n) ≠ 0 := by
  have aux (ks : List ℕ) (hk : ∀ k ∈ ks, 0 < k ∧ k < n) :
      value n (ks.foldr (fun k acc => mul (factor k) acc) [1]) ≠ 0 := by
    induction ks with
    | nil => simp
    | cons k ks ih =>
      have hp := hk k (by simp)
      simp only [List.foldr_cons, value_mul, value_factor]
      apply mul_ne_zero
      · exact sub_ne_zero.mpr ((cyclotomicGenerator_primitive n).pow_ne_one_of_pos_of_lt hp.1.ne' hp.2)
      · apply ih
        exact fun j hj => hk j (List.mem_cons_of_mem _ hj)
  apply aux
  intro k hk
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hk
  exact ⟨hk.2.1, hk.1⟩

/-- Independently certify that the claimed monic relation vanishes at ζ_n.
Multiply by the proper-divisor factors and test divisibility by X^n-1. -/
def checkModulus (n : ℕ) (low : Coeff) : Bool :=
  eqMod (unityTail n) (mul (low ++ [1]) (factors n)) []

theorem checkModulus_sound (n : ℕ) [NeZero n] (low : Coeff) (h : checkModulus n low = true) :
    value n (low ++ [1]) = 0 := by
  have hz := eqMod_sound n _ _ _ (unity_relation n) h
  rw [value_mul, value_nil, mul_eq_zero] at hz
  exact hz.resolve_right (factors_nonzero n)

end MTC.FRSymbols.PentagonCoefficient
