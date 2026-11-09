module

/-!
# Raw exact Atlas records

The downloadable S matrix is unnormalized, and the T matrix is stored as its
 diagonal. A term `(a / b) * exp(2πi * p / q)` is represented by integers;
this is syntax for an exact cyclotomic value, not a floating-point approximation.
These records are data, not proofs of modular-data axioms or categorifiability.
Fermionic records use the Atlas quotient convention, and are not modular data.
-/

@[expose] public section
namespace MTC.AnyonAtlas

/-- A rational coefficient times a root of unity. Denominators are positive in imported data. -/
structure CyclotomicTerm where
  coeffNum : Int
  coeffDen : Nat
  phaseNum : Int
  phaseDen : Nat
  deriving Repr, DecidableEq

/-- An exact sum of roots of unity. -/
abbrev CyclotomicExpression := List CyclotomicTerm

/-- Raw Atlas matrices, with metadata retained separately in the JSON index. -/
structure RawRecord where
  id : String
  kind : String
  rank : Nat
  s : List (List CyclotomicExpression)
  t : List CyclotomicExpression
  deriving Repr, DecidableEq

end MTC.AnyonAtlas
