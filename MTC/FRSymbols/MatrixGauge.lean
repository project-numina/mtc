module
public import MTC.FRSymbols.MatrixSymbols

/-!
# Gauge changes of matrix-valued fusion symbols

A gauge change is an invertible change of basis in every trivalent fusion
space, with simple labels fixed. Its action on an F block is induced by the
product changes of basis on its left and right fusion trees; its action on an
R block uses the changes for the two opposite orders of the inputs. Relabeling
simple objects is a separate operation. See Etingof et al., *Tensor
Categories*, Section 9.4, and arXiv:2405.20075, Section 2.3.
-/

@[expose] public section
open scoped BigOperators
namespace MTC.FRSymbols

variable {L K : Type*} [Fintype L] [DecidableEq L] [CommSemiring K]
variable {n : FusionRules L}

/-- Invertible basis changes for all trivalent fusion spaces. -/
structure MatrixGauge (n : FusionRules L) (K : Type*) [CommSemiring K] where
  U : ∀ a b c, Fin (n.N a b c) → Fin (n.N a b c) → K
  Uinv : ∀ a b c, Fin (n.N a b c) → Fin (n.N a b c) → K
  inverse_right : ∀ a b c i j,
    (∑ k, U a b c i k * Uinv a b c k j) = if i = j then 1 else 0
  inverse_left : ∀ a b c i j,
    (∑ k, Uinv a b c i k * U a b c k j) = if i = j then 1 else 0

/-- Fixed-label gauge equivalence for matrix-valued F and R blocks.
These are the cleared-denominator equations `U_left * F' = F * U_right`
and `U_ab * R' = R * U_ba`, indexed at each trivalent vertex. The
corresponding equations for the supplied inverse blocks are included too. -/
def MatrixSymbols.GaugeEquivalent (s t : MatrixSymbols n K) : Prop :=
  ∃ g : MatrixGauge n K,
    (∀ a b c d e f (α : Fin (n.N a b e)) (β : Fin (n.N e c d))
      (γ : Fin (n.N b c f)) (δ : Fin (n.N a f d)),
      (∑ α' : Fin (n.N a b e), ∑ β' : Fin (n.N e c d),
        g.U a b e α α' * g.U e c d β β' *
          t.F a b c d ⟨e, α', β'⟩ ⟨f, γ, δ⟩) =
      ∑ γ' : Fin (n.N b c f), ∑ δ' : Fin (n.N a f d),
        s.F a b c d ⟨e, α, β⟩ ⟨f, γ', δ'⟩ *
          g.U b c f γ' γ * g.U a f d δ' δ) ∧
    (∀ a b c (i : Fin (n.N a b c)) (j : Fin (n.N b a c)),
      (∑ i', g.U a b c i i' * t.R a b c i' j) =
      ∑ j', s.R a b c i j' * g.U b a c j' j) ∧
    (∀ a b c d e f (α : Fin (n.N a b e)) (β : Fin (n.N e c d))
      (γ : Fin (n.N b c f)) (δ : Fin (n.N a f d)),
      (∑ γ' : Fin (n.N b c f), ∑ δ' : Fin (n.N a f d),
        g.U b c f γ γ' * g.U a f d δ δ' *
          t.Finv a b c d ⟨f, γ', δ'⟩ ⟨e, α, β⟩) =
      ∑ α' : Fin (n.N a b e), ∑ β' : Fin (n.N e c d),
        s.Finv a b c d ⟨f, γ, δ⟩ ⟨e, α', β'⟩ *
          g.U a b e α' α * g.U e c d β' β) ∧
    (∀ a b c (i : Fin (n.N b a c)) (j : Fin (n.N a b c)),
      (∑ i', g.U b a c i i' * t.Rinv a b c i' j) =
      ∑ j', s.Rinv a b c i j' * g.U a b c j' j)

/-- The identity basis change fixes all F and R blocks. -/
theorem MatrixSymbols.gaugeEquivalent_refl (s : MatrixSymbols n K) : s.GaugeEquivalent s := by
  let g : MatrixGauge n K :=
    ⟨fun _ _ _ i j => if i = j then 1 else 0,
     fun _ _ _ i j => if i = j then 1 else 0,
     by intros; simp, by intros; simp⟩
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro a b c d e f α β γ δ
    simp [g]
  · intro a b c i j
    simp [g]
  · intro a b c d e f α β γ δ
    simp [g]
  · intro a b c i j
    simp [g]

end MTC.FRSymbols
