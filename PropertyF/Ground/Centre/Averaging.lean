module
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.Perm.Sign

/-! Finite-group averaging in an arbitrary algebra. Applying this to a sign-twisted
symmetric-group action gives the categorical antisymmetrizer once that action is built. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Centre

variable (k G : Type*) [CommRing k] [Group G] [Fintype G] [Invertible (Fintype.card G : k)]

/-- The normalized group-algebra sum is an idempotent. -/
theorem groupAverage_idempotent : GroupAlgebra.average k G * GroupAlgebra.average k G =
    GroupAlgebra.average k G := by
  conv_lhs => lhs; rw [GroupAlgebra.average]
  simp only [Algebra.smul_mul_assoc, Finset.sum_mul, MonoidAlgebra.of_apply,
    GroupAlgebra.mul_average_left]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
    smul_smul, invOf_mul_self, one_smul]

variable {k G} {A : Type*} [Ring A] [Algebra k A]

/-- Twist an algebra-valued group action by a one-dimensional character. -/
def twistAction (χ : G →* kˣ) (ρ : G →* A) : G →* A where
  toFun g := (χ g : k) • ρ g
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, Units.val_mul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_comm]

/-- The average of a finite-group action in an algebra. A sign-twisted action
produces the alternating projector. -/
def algebraAverage (ρ : G →* A) : A :=
  MonoidAlgebra.lift k A G ρ (GroupAlgebra.average k G)

/-- The average is the normalized sum of the operators in the action. -/
theorem algebraAverage_eq_sum (ρ : G →* A) :
    algebraAverage (k := k) ρ = ⅟(Fintype.card G : k) • ∑ g : G, ρ g := by
  simp [algebraAverage, GroupAlgebra.average]

/-- Averaging an action gives an actual idempotent in its target algebra. -/
theorem algebraAverage_idempotent (ρ : G →* A) :
    algebraAverage (k := k) ρ * algebraAverage (k := k) ρ = algebraAverage (k := k) ρ := by
  rw [algebraAverage, ← map_mul, groupAverage_idempotent]

/-- The sign character of the symmetric group, with values in the scalar ring. -/
def permutationSign (k : Type*) [CommRing k] (n : ℕ) : Equiv.Perm (Fin n) →* kˣ :=
  (Units.map (Int.castRingHom k)).comp Equiv.Perm.sign

/-- The alternating projector associated with a symmetric-group action. -/
def alternatingProjector (n : ℕ) [Invertible (Fintype.card (Equiv.Perm (Fin n)) : k)]
    (ρ : Equiv.Perm (Fin n) →* A) : A :=
  algebraAverage (k := k) (twistAction (permutationSign k n) ρ)

/-- The alternating projector is idempotent before making any splitting assumption. -/
theorem alternatingProjector_idempotent (n : ℕ)
    [Invertible (Fintype.card (Equiv.Perm (Fin n)) : k)]
    (ρ : Equiv.Perm (Fin n) →* A) :
    alternatingProjector (k := k) n ρ * alternatingProjector (k := k) n ρ =
      alternatingProjector (k := k) n ρ :=
  algebraAverage_idempotent _

/-- The alternating projector is the normalized signed sum of permutation operators. -/
theorem alternatingProjector_eq_sum (n : ℕ)
    [Invertible (Fintype.card (Equiv.Perm (Fin n)) : k)]
    (ρ : Equiv.Perm (Fin n) →* A) :
    alternatingProjector (k := k) n ρ =
      ⅟(Fintype.card (Equiv.Perm (Fin n)) : k) •
        ∑ σ : Equiv.Perm (Fin n), ((permutationSign k n σ : k) • ρ σ) := by
  exact algebraAverage_eq_sum _

end PropertyF.Ground.Centre
