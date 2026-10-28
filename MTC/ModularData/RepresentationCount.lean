module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

/-!
# Counting semisimple representation profiles

A finite group has finitely many irreducible complex representations. If `k`
is their number, each `n`-dimensional semisimple representation determines
`k` multiplicities, each at most `n`. This file proves the elementary count of
possible profiles, independently of the substantial representation-theoretic
work needed to connect the profiles to representations.

For the congruence application see arXiv:0806.2493, Theorem 6.8, and
arXiv:1201.6644, Theorem 2.3. These refer to projective representations and
the levels of their linear lifts respectively.
-/

@[expose] public section
namespace MTC.ModularData

/-- Bounded multiplicities of `k` possible irreducibles in dimension `n`. -/
abbrev MultiplicityProfile (k n : ℕ) := Fin k → Fin (n + 1)

/-- An explicit upper bound, before imposing the dimension equation. -/
theorem card_multiplicityProfile (k n : ℕ) :
    Fintype.card (MultiplicityProfile k n) = (n + 1) ^ k := by
  simp [MultiplicityProfile]

/-- Restricting to profiles with any additional property can only reduce the
count. In applications this property includes the dimension equation. -/
theorem card_profile_subset_le (k n : ℕ) (s : Finset (MultiplicityProfile k n)) :
    s.card ≤ (n + 1) ^ k := by
  calc
    s.card ≤ Fintype.card (MultiplicityProfile k n) := Finset.card_le_univ s
    _ = (n + 1) ^ k := card_multiplicityProfile k n

end MTC.ModularData
