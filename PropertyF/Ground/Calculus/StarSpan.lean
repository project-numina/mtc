module
public import PropertyF.Ground.Calculus.Unitarization
public import Mathlib.LinearAlgebra.Span.Defs

/-! Compatibility of adjoints on algebras spanned by braid images. -/

@[expose] public section
namespace PropertyF.Ground.Calculus

variable {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
  [StarRing A] [StarRing B] [StarModule ℂ A] [StarModule ℂ B]

/-- A complex algebra map that preserves the adjoint of each generator preserves
it on their entire linear span. In particular this applies to identity-strand
embeddings once the braids are represented by unitary matrices. -/
theorem map_star_of_mem_span (φ : A →ₐ[ℂ] B) (S : Set A)
    (hS : ∀ x ∈ S, φ (star x) = star (φ x))
    {x : A} (hx : x ∈ Submodule.span ℂ S) : φ (star x) = star (φ x) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul c x hx ih => simp [star_smul, ih]

/-- A unitary matrix's adjoint is the inverse of the corresponding unit. -/
theorem star_eq_coe_inv_of_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : (Matrix ι ι ℂ)ˣ) (hu : (u : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ) :
    star (u : Matrix ι ι ℂ) = (↑u⁻¹ : Matrix ι ι ℂ) := by
  have h : star (u : Matrix ι ι ℂ) * (u : Matrix ι ι ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hu
  calc
    star (u : Matrix ι ι ℂ) = star (u : Matrix ι ι ℂ) * ((u : Matrix ι ι ℂ) * ↑u⁻¹) := by simp
    _ = (star (u : Matrix ι ι ℂ) * (u : Matrix ι ι ℂ)) * ↑u⁻¹ := by rw [mul_assoc]
    _ = (↑u⁻¹ : Matrix ι ι ℂ) := by rw [h, one_mul]

/-- An algebra map intertwining two unitary group representations preserves
adjoints on the span of the group image, independently of the chosen invariant
inner products. -/
theorem map_star_on_unitary_group_span {G ι κ : Type*} [Group G]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (ρ : G →* (Matrix ι ι ℂ)ˣ) (σ : G →* (Matrix κ κ ℂ)ˣ)
    (φ : Matrix ι ι ℂ →ₐ[ℂ] Matrix κ κ ℂ)
    (hφ : ∀ g, φ (ρ g : Matrix ι ι ℂ) = (σ g : Matrix κ κ ℂ))
    (hρ : ∀ g, (ρ g : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ)
    (hσ : ∀ g, (σ g : Matrix κ κ ℂ) ∈ Matrix.unitaryGroup κ ℂ)
    {x : Matrix ι ι ℂ}
    (hx : x ∈ Submodule.span ℂ (Set.range fun g => (ρ g : Matrix ι ι ℂ))) :
    φ (star x) = star (φ x) := by
  apply map_star_of_mem_span φ _ _ hx
  rintro _ ⟨g, rfl⟩
  rw [star_eq_coe_inv_of_unitary (ρ g) (hρ g), ← map_inv ρ, hφ,
    hφ, star_eq_coe_inv_of_unitary (σ g) (hσ g), map_inv]

end PropertyF.Ground.Calculus
