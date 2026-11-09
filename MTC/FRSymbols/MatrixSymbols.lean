module
public import MTC.FRSymbols.FusionRules
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic

/-!
# Matrix-valued F and R symbols

Fusion multiplicities are retained as explicit trivalent-vertex indices. We
use F as the change of basis `((a b) c) → (a (b c))`, and R as the change
of basis for `a b → b a`. The two hexagon paths and the pentagon path are
expanded into finite sums, so they can be checked over an exact field.

These definitions describe coherence data. They do not yet include the
triangle, rigidity or pivotal/unitary conditions required to reconstruct a
fusion or modular category. See Etingof, Gelaki, Nikshych and Ostrik,
*Tensor Categories*, Sections 2.1, 8.1 and 9.4, and the Atlas,
arXiv:2610.25439, Section 2.2.
-/

@[expose] public section
open scoped BigOperators
namespace MTC.FRSymbols

variable {L K : Type*} [Fintype L] [DecidableEq L] [CommSemiring K]

/-- A basis of `((a ⊗ b) ⊗ c) → d`, grouped by the intermediate label. -/
abbrev LeftTree (n : FusionRules L) (a b c d : L) :=
  Σ x : L, Fin (n.N a b x) × Fin (n.N x c d)

/-- A basis of `(a ⊗ (b ⊗ c)) → d`. -/
abbrev RightTree (n : FusionRules L) (a b c d : L) :=
  Σ x : L, Fin (n.N b c x) × Fin (n.N a x d)

/-- Matrix-valued associator and braiding blocks, including their inverses.
The last index is the output basis index. No coherence is assumed here. -/
structure MatrixSymbols (n : FusionRules L) (K : Type*) [CommSemiring K] where
  F : ∀ a b c d, LeftTree n a b c d → RightTree n a b c d → K
  Finv : ∀ a b c d, RightTree n a b c d → LeftTree n a b c d → K
  R : ∀ a b c, Fin (n.N a b c) → Fin (n.N b a c) → K
  Rinv : ∀ a b c, Fin (n.N b a c) → Fin (n.N a b c) → K

namespace MatrixSymbols
variable {n : FusionRules L} (s : MatrixSymbols n K)

/-- Invertibility of every associator and braiding block in both directions. -/
def Invertible : Prop :=
  (∀ a b c d (i j : LeftTree n a b c d),
    (∑ k, s.F a b c d i k * s.Finv a b c d k j) = if i = j then 1 else 0) ∧
  (∀ a b c d (i j : RightTree n a b c d),
    (∑ k, s.Finv a b c d i k * s.F a b c d k j) = if i = j then 1 else 0) ∧
  (∀ a b c (i j : Fin (n.N a b c)),
    (∑ k, s.R a b c i k * s.Rinv a b c k j) = if i = j then 1 else 0) ∧
  (∀ a b c (i j : Fin (n.N b a c)),
    (∑ k, s.Rinv a b c i k * s.R a b c k j) = if i = j then 1 else 0)

/-- Pentagon for four simple objects and each pair of fusion-tree bases. -/
def Pentagon : Prop := ∀ a b c d u e f g h
    (α : Fin (n.N a b e)) (β : Fin (n.N e c f)) (γ : Fin (n.N f d u))
    (δ : Fin (n.N c d g)) (ζ : Fin (n.N b g h)) (η : Fin (n.N a h u)),
  (∑ ε : Fin (n.N e g u),
    s.F e c d u ⟨f, β, γ⟩ ⟨g, δ, ε⟩ *
    s.F a b g u ⟨e, α, ε⟩ ⟨h, ζ, η⟩) =
  ∑ j : L, ∑ μ : Fin (n.N b c j), ∑ ν : Fin (n.N a j f),
    ∑ ρ : Fin (n.N j d h),
      s.F a b c f ⟨e, α, β⟩ ⟨j, μ, ν⟩ *
      s.F a j d u ⟨f, ν, γ⟩ ⟨h, ρ, η⟩ *
      s.F b c d h ⟨j, μ, ρ⟩ ⟨g, δ, ζ⟩

/-- First hexagon: braid `a` past `b ⊗ c`, or past `b` and `c` in turn. -/
def Hexagon₁ : Prop := ∀ a b c d e g
    (μ : Fin (n.N a b e)) (ν : Fin (n.N e c d))
    (ell : Fin (n.N c a g)) (κ : Fin (n.N b g d)),
  (∑ x : L, ∑ α : Fin (n.N b c x), ∑ σ : Fin (n.N a x d),
    ∑ ρ : Fin (n.N x a d),
      s.F a b c d ⟨e, μ, ν⟩ ⟨x, α, σ⟩ * s.R a x d σ ρ *
      s.F b c a d ⟨x, α, ρ⟩ ⟨g, ell, κ⟩) =
  ∑ β : Fin (n.N b a e), ∑ γ : Fin (n.N a c g),
    s.R a b e μ β * s.F b a c d ⟨e, β, ν⟩ ⟨g, γ, κ⟩ * s.R a c g γ ell

/-- Second hexagon: braid `a ⊗ b` past `c`, or braid both factors past `c`.
The inverse F block occurs when the path re-associates in the reverse direction. -/
def Hexagon₂ : Prop := ∀ a b c d e
    (μ : Fin (n.N a b e)) (ν : Fin (n.N e c d))
    (α : Fin (n.N a b e)) (σ : Fin (n.N c e d)),
  (∑ x : L, ∑ β : Fin (n.N b c x), ∑ γ : Fin (n.N a x d),
    ∑ β' : Fin (n.N c b x), ∑ y : L, ∑ δ : Fin (n.N a c y),
    ∑ ε : Fin (n.N y b d), ∑ δ' : Fin (n.N c a y),
      s.F a b c d ⟨e, μ, ν⟩ ⟨x, β, γ⟩ * s.R b c x β β' *
      s.Finv a c b d ⟨x, β', γ⟩ ⟨y, δ, ε⟩ * s.R a c y δ δ' *
      s.F c a b d ⟨y, δ', ε⟩ ⟨e, α, σ⟩) =
  if μ = α then s.R e c d ν σ else 0

/-- A choice of orthonormal trivalent bases makes every F and R block unitary
when its supplied inverse is its conjugate transpose. Combine with
`Invertible` to ensure that these are genuine unitary matrices. -/
def Unitary [StarRing K] : Prop :=
  (∀ a b c d (i : LeftTree n a b c d) (j : RightTree n a b c d),
    s.Finv a b c d j i = star (s.F a b c d i j)) ∧
  (∀ a b c (i : Fin (n.N a b c)) (j : Fin (n.N b a c)),
    s.Rinv a b c j i = star (s.R a b c i j))

/-- Unitarity relative to a specified complex embedding of the exact
coefficients. This formulation does not require a star instance on the
coefficient field; together with `Invertible` it checks the F/R blocks. -/
def UnitaryVia (ι : K →+* ℂ) : Prop :=
  (∀ a b c d (i : LeftTree n a b c d) (j : RightTree n a b c d),
    ι (s.Finv a b c d j i) = star (ι (s.F a b c d i j))) ∧
  (∀ a b c (i : Fin (n.N a b c)) (j : Fin (n.N b a c)),
    ι (s.Rinv a b c j i) = star (ι (s.R a b c i j)))

/-- A star-preserving injective embedding reflects matrix unitarity. -/
theorem unitaryVia_iff [StarRing K] (ι : K →+* ℂ) (hinj : Function.Injective ι)
    (hstar : ∀ x, ι (star x) = star (ι x)) : s.UnitaryVia ι ↔ s.Unitary := by
  constructor
  · rintro ⟨hf, hr⟩
    constructor
    · intro a b c d i j
      apply hinj
      rw [hstar]
      exact hf a b c d i j
    · intro a b c i j
      apply hinj
      rw [hstar]
      exact hr a b c i j
  · rintro ⟨hf, hr⟩
    constructor
    · intro a b c d i j
      rw [← hstar]
      exact congrArg ι (hf a b c d i j)
    · intro a b c i j
      rw [← hstar]
      exact congrArg ι (hr a b c i j)

/-- The coherence checks, separate from the additional fusion-system axioms. -/
def Coherent : Prop := s.Invertible ∧ s.Pentagon ∧ s.Hexagon₁ ∧ s.Hexagon₂

end MatrixSymbols
end MTC.FRSymbols
