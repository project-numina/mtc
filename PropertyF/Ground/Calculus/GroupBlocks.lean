module
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-! Wedderburn decomposition of the linear span of a finite group image. -/

@[expose] public noncomputable section
namespace PropertyF.Ground.Calculus

variable {G A : Type*} [Group G] [Finite G] [Ring A] [Algebra ℂ A]

/-- The group-algebra map associated to a representation in a complex algebra. -/
def groupAlgebraMap (ρ : G →* A) : MonoidAlgebra ℂ G →ₐ[ℂ] A :=
  MonoidAlgebra.lift ℂ A G ρ

/-- The complex algebra spanned by the group image. -/
def groupImageAlgebra (ρ : G →* A) : Subalgebra ℂ A := (groupAlgebraMap ρ).range

omit [Finite G] in
/-- The image algebra has precisely the underlying linear span of the group image. -/
theorem groupImageAlgebra_toSubmodule (ρ : G →* A) :
    (groupImageAlgebra ρ).toSubmodule = Submodule.span ℂ (Set.range ρ) := by
  classical
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    change MonoidAlgebra.lift ℂ A G ρ a ∈ Submodule.span ℂ (Set.range ρ)
    rw [MonoidAlgebra.lift_apply]
    apply Submodule.sum_mem
    intro g hg
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self g))
  · apply Submodule.span_le.mpr
    rintro x ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.of ℂ G g, MonoidAlgebra.lift_of ρ g⟩

/-- A finite group's image algebra is semisimple, by Maschke and passage to a quotient. -/
theorem groupImageAlgebra_semisimple (ρ : G →* A) :
    IsSemisimpleRing (groupImageAlgebra ρ) := by
  classical
  let _ : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩ : Nat.card G ≠ 0)⟩
  exact RingHom.isSemisimpleRing_of_surjective (groupAlgebraMap ρ).rangeRestrict.toRingHom
    (AlgHom.rangeRestrict_surjective (groupAlgebraMap ρ))

/-- The image algebra is finite-dimensional, even when the ambient algebra is not. -/
theorem groupImageAlgebra_finite (ρ : G →* A) :
    FiniteDimensional ℂ (groupImageAlgebra ρ) := by
  classical
  exact Module.Finite.of_surjective (groupAlgebraMap ρ).rangeRestrict.toLinearMap
    (AlgHom.rangeRestrict_surjective (groupAlgebraMap ρ))

/-- The finite group image algebra is a finite product of nonempty complex
matrix blocks. It is not assumed that the representation is faithful. -/
theorem groupImageAlgebra_blocks (ρ : G →* A) :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (groupImageAlgebra ρ ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  let _ := groupImageAlgebra_semisimple ρ
  let _ := groupImageAlgebra_finite ρ
  exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (groupImageAlgebra ρ)

end PropertyF.Ground.Calculus
