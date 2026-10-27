module
public import PropertyF.Axioms

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

/-- Construct the old modular-data interface from its numerical identities and
classification of fusion characters by the normalized S columns. In particular,
neither the Galois label action nor its compatibility with columns is assumed. -/
def modularDataOfCharacters (rank : ℕ) (unit : Fin rank)
    (dual : Fin rank → Fin rank) (dimension : Fin rank → ℂ)
    (globalDimension : ℂ) (S : Matrix (Fin rank) (Fin rank) ℂ)
    (dimension_ne_zero : ∀ X, dimension X ≠ 0)
    (global_ne_zero : globalDimension ≠ 0)
    (global_eq : globalDimension = ∑ X, dimension X ^ 2)
    (S_symmetric : ∀ X Y, S X Y = S Y X)
    (S_unit : ∀ X, S X unit = dimension X)
    (unit_dimension : dimension unit = 1)
    (S_square : ∀ X Y, ∑ Z, S X Z * S Z Y =
      if X = dual Y then globalDimension else 0)
    (N : FusionRules (Fin rank))
    (columns : Fin rank → Character N)
    (column_eq : ∀ X Y, (columns Y).value X = S X Y / dimension Y)
    (columns_bijective : Function.Bijective columns) : PropertyF.ModularData := by
  let e : Fin rank ≃ Character N := Equiv.ofBijective columns columns_bijective
  exact {
    rank, unit, dual, dimension, globalDimension, S,
    dimension_ne_zero, global_ne_zero, global_eq, S_symmetric, S_unit,
    unit_dimension, S_square
    galoisLabel := Character.galoisLabel e
    galois_character := by
      intro τ X Y
      rw [← column_eq, ← column_eq]
      exact (Character.galoisLabel_character e τ Y X).symm }

end PropertyF.Ground.Modular
