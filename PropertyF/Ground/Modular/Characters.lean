module
public import PropertyF.BlockTrace
public import PropertyF.Definitions
public import PropertyF.CenterBasics
public import Mathlib.CategoryTheory.Monoidal.Center
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.GroupTheory.Index

/-!
# Galois action on fusion characters

The integral structure constants make postcomposition by every field automorphism
of ℂ an action on fusion characters. If the normalized S-columns classify those
characters, this action yields the permutation required by `ModularData`.
The classification itself (including the Verlinde formula) is not assumed to
follow from the definitions here.
-/

@[expose] public noncomputable section
open scoped BigOperators

namespace PropertyF.Ground.Modular

/-- The data needed to state the character equations. No fusion-ring axioms are
needed for the Galois action itself. -/
structure FusionRules (ι : Type*) where
  unit : ι
  coeff : ι → ι → ι → ℕ

/-- A normalized complex-valued character of integral fusion rules. -/
structure Character {ι : Type*} [Fintype ι] (N : FusionRules ι) where
  value : ι → ℂ
  unit_eq : value N.unit = 1
  mul_eq : ∀ i j, value i * value j = ∑ k, (N.coeff i j k : ℂ) * value k

namespace Character

variable {ι : Type*} [Fintype ι] {N : FusionRules ι}

@[ext] theorem ext {χ ψ : Character N} (h : χ.value = ψ.value) : χ = ψ := by
  cases χ; cases ψ; cases h; rfl

/-- Transport of a character along an arbitrary field automorphism. -/
def map (τ : ℂ ≃+* ℂ) (χ : Character N) : Character N where
  value i := τ (χ.value i)
  unit_eq := by rw [χ.unit_eq, map_one]
  mul_eq i j := by
    rw [← map_mul, χ.mul_eq, map_sum]
    simp only [map_mul, map_natCast]

/-- Complex automorphisms act by permutations of the character set. -/
def galoisPerm (τ : ℂ ≃+* ℂ) : Equiv.Perm (Character N) where
  toFun := map τ
  invFun := map τ.symm
  left_inv χ := by ext i; simp [map]
  right_inv χ := by ext i; simp [map]

/-- A labelling of all characters transports the Galois action to labels. -/
def galoisLabel (e : ι ≃ Character N) : (ℂ ≃+* ℂ) →* Equiv.Perm ι where
  toFun τ := e.symm.permCongr (galoisPerm τ)
  map_one' := by ext i; apply e.injective; ext j; simp [galoisPerm, map]
  map_mul' σ τ := by ext i; apply e.injective; ext j; simp [galoisPerm, map]

@[simp] theorem galoisLabel_character (e : ι ≃ Character N)
    (τ : ℂ ≃+* ℂ) (i j : ι) :
    (e (galoisLabel e τ i)).value j = τ ((e i).value j) := by
  simp [galoisLabel, galoisPerm, map]

end Character
end PropertyF.Ground.Modular

namespace PropertyF.Ground.Modular

end PropertyF.Ground.Modular
