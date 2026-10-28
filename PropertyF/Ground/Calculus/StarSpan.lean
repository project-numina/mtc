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

/-- If a group spans an algebra and two representations have adjoint equal to
inverse on group elements, every intertwining algebra map preserves adjoints.
This captures identity-strand maps without assuming injectivity or surjectivity. -/
theorem map_star_of_group_span {G H : Type*} [Group G] [Group H]
    (ρ : G →* A) (σ : H →* B) (τ : G →* H) (φ : A →ₐ[ℂ] B)
    (hspan : Submodule.span ℂ (Set.range ρ) = ⊤)
    (hρ : ∀ g, star (ρ g) = ρ g⁻¹)
    (hσ : ∀ h, star (σ h) = σ h⁻¹)
    (hφ : ∀ g, φ (ρ g) = σ (τ g)) (x : A) :
    φ (star x) = star (φ x) := by
  apply map_star_of_mem_span φ (Set.range ρ)
  · rintro _ ⟨g, rfl⟩
    rw [hρ, hφ, hφ, hσ, map_inv]
  · rw [hspan]
    exact Submodule.mem_top

end PropertyF.Ground.Calculus
