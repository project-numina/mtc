module
public import PropertyF.Ground.Calculus.PartialTrace
public import PropertyF.Ground.Centre.Basic
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Dimensions.SimpleScalars
public import PropertyF.Ground.Centre.Basic
public import PropertyF.Ground.Fusion.SemisimpleSplit
public import PropertyF.Ground.Centre.Cokernel
public import PropertyF.Ground.Centre.Abelian
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.CategoryTheory.Abelian.Exact

/-! A finite-step semisimple decomposition from split subobjects. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [HasBinaryBiproducts D]

/-- The block-diagonal map embeds pairs of endomorphisms into endomorphisms
of a binary direct sum. -/
def diagonalEndMap (S K : D) : ((S ⟶ S) × (K ⟶ K)) →ₗ[ℂ] (S ⊞ K ⟶ S ⊞ K) where
  toFun x := biprod.map x.1 x.2
  map_add' x y := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp
  map_smul' r x := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

/-- A block-diagonal endomorphism determines both diagonal blocks. -/
theorem diagonalEndMap_injective {S K : D} : Function.Injective (diagonalEndMap S K) := by
  intro a b h
  apply Prod.ext
  · simpa [diagonalEndMap, Category.assoc] using
      congrArg (fun f => biprod.inl ≫ f ≫ biprod.fst) h
  · simpa [diagonalEndMap, Category.assoc] using
      congrArg (fun f => biprod.inr ≫ f ≫ biprod.snd) h

/-- Removing a nonzero direct summand strictly decreases the dimension of the
endomorphism space. -/
theorem finrank_end_complement_lt (S K : D)
    [FiniteDimensional ℂ (S ⟶ S)] [FiniteDimensional ℂ (K ⟶ K)]
    [FiniteDimensional ℂ (S ⊞ K ⟶ S ⊞ K)] (hS : ¬ IsZero S) :
    Module.finrank ℂ (K ⟶ K) < Module.finrank ℂ (S ⊞ K ⟶ S ⊞ K) := by
  have hpos : 0 < Module.finrank ℂ (S ⟶ S) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨𝟙 S, (IsZero.iff_id_eq_zero S).not.mp hS⟩
  have hle := LinearMap.finrank_le_finrank_of_injective (f := diagonalEndMap S K)
    (diagonalEndMap_injective (S := S) (K := K))
  rw [Module.finrank_prod] at hle
  omega

/-- Objects built from finitely many simple objects by binary direct sums,
up to isomorphism. -/
inductive FiniteSimpleSum (D : Type u) [Category.{v} D] [Preadditive D]
    [HasBinaryBiproducts D] : D → Prop
  | zero {X} : IsZero X → FiniteSimpleSum D X
  | cons {X S K} : Simple S → FiniteSimpleSum D K → Nonempty (X ≅ S ⊞ K) →
      FiniteSimpleSum D X


end PropertyF.Ground.CentreInduction
