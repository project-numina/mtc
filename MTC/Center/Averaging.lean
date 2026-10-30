module
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import MTC.CategoryTheory.Dimensions.BiproductTrace
public import Mathlib.CategoryTheory.Idempotents.Basic

/-!
# Averaging and alternating projectors

Averaging a finite group action in an algebra gives an idempotent when the
group order is invertible. Twisting a symmetric-group action by its sign
character gives the alternating projector.

In an idempotent-complete linear category the projector splits, and its
pivotal trace is the trace of the identity on its split image.
-/
@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Centre

variable (k G : Type*) [CommRing k] [Group G] [Fintype G] [Invertible (Fintype.card G : k)]

/-- The normalized group-algebra sum is an idempotent. -/
theorem groupAverage_idempotent : GroupAlgebra.average k G * GroupAlgebra.average k G =
    GroupAlgebra.average k G := by
  conv_lhs => lhs; rw [GroupAlgebra.average]
  simp only [Algebra.smul_mul_assoc, Finset.sum_mul, MonoidAlgebra.of_apply,
    GroupAlgebra.mul_average_left, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul k, smul_smul, invOf_mul_self, one_smul]

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

/-- The sign character of the symmetric group, with values in the scalar ring. -/
def permutationSign (k : Type*) [CommRing k] (n : ℕ) : Equiv.Perm (Fin n) →* kˣ :=
  (Units.map (Int.castRingHom k)).comp Equiv.Perm.sign

variable {n : ℕ} [Invertible (Fintype.card (Equiv.Perm (Fin n)) : k)]

/-- The alternating projector associated with a symmetric-group action. -/
def alternatingProjector (ρ : Equiv.Perm (Fin n) →* A) : A :=
  algebraAverage (k := k) (twistAction (permutationSign k n) ρ)

/-- The alternating projector is idempotent before making any splitting assumption. -/
theorem alternatingProjector_idempotent (ρ : Equiv.Perm (Fin n) →* A) :
    IsIdempotentElem (alternatingProjector (k := k) ρ) := by
  rw [IsIdempotentElem, alternatingProjector, algebraAverage, ← map_mul, groupAverage_idempotent]

end PropertyF.Ground.Centre

/-! Splitting the alternating projector and identifying its pivotal trace. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Centre

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [IsIdempotentComplete C]
variable {X : C} {n : ℕ} [Invertible (Fintype.card (Equiv.Perm (Fin n)) : ℂ)]

/-- A symmetric-group action on an object has a split alternating projector. -/
theorem alternatingProjector_splits (ρ : Equiv.Perm (Fin n) →* End X) :
    ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y),
      i ≫ r = 𝟙 Y ∧ r ≫ i = (alternatingProjector (k := ℂ) ρ).asHom :=
  IsIdempotentComplete.idempotents_split X (alternatingProjector (k := ℂ) ρ).asHom
    (by simpa only [End.mul_asHom] using congrArg End.asHom (alternatingProjector_idempotent (k := ℂ) ρ))

variable [MonoidalCategory C] [RightRigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The trace of the alternating projector is the dimension of its split image. -/
theorem alternatingProjector_trace (ρ : Equiv.Perm (Fin n) →* End X)
    (p : PropertyF.Ground.Dimensions.PivotalStructure (C := C)) :
    ∃ Y : C, p.rightTrace ((alternatingProjector (k := ℂ) ρ).asHom) = p.rightTrace (𝟙 Y) :=
  match alternatingProjector_splits ρ with
  | ⟨Y, i, r, hir, hri⟩ => ⟨Y, by rw [← hri, p.rightTrace_cyclic, hir]⟩

end PropertyF.Ground.Centre
