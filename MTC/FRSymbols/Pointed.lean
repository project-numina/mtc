module
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Basic.Complex.Basic

/-!
# F and R symbols for pointed braided fusion categories

For a finite abelian group of simple labels, each fusion space is zero- or
one-dimensional. In the standard skeletal gauge the nonzero F-symbols are
`ω(a,b,c)` and R-symbols are `r(a,b)`, both invertible scalars. The pentagon
and the two hexagons are the abelian 3-cocycle equations, in the convention
of Etingof, Gelaki, Nikshych and Ostrik, *Tensor Categories*, Section 8.4,
equation (8.11), https://math.mit.edu/~etingof/egnobookfinal.pdf.
This file treats the pointed case only; general fusion multiplicities require
matrix-valued symbols and additional coherence equations.
-/

@[expose] public section
namespace MTC.FRSymbols.Pointed

variable {G K : Type*} [AddCommGroup G] [CommGroup K]

/-- Normalized skeletal F and R symbols. Values lie in a commutative group,
for example the units of a cyclotomic field. The laws are exactly the
pentagon and both hexagon equations, with no division by symbolic values. -/
structure Symbols (G K : Type*) [AddCommGroup G] [CommGroup K] where
  F : G → G → G → K
  R : G → G → K
  F_zero_left : ∀ b c, F 0 b c = 1
  F_zero_middle : ∀ a c, F a 0 c = 1
  F_zero_right : ∀ a b, F a b 0 = 1
  R_zero_left : ∀ a, R 0 a = 1
  R_zero_right : ∀ a, R a 0 = 1
  pentagon : ∀ a b c d,
    F (a + b) c d * F a b (c + d) = F a b c * F a (b + c) d * F b c d
  hexagon₁ : ∀ a b c,
    F b c a * R a (b + c) * F a b c = R a c * F b a c * R a b
  hexagon₂ : ∀ a b c,
    R (a + b) c * F a c b = R a c * R b c * F c a b * F a b c

/-- A normalized change of basis in one-dimensional fusion spaces. -/
structure Gauge (G K : Type*) [AddCommGroup G] [CommGroup K] where
  u : G → G → K
  zero_left : ∀ a, u 0 a = 1
  zero_right : ∀ a, u a 0 = 1

/-- Gauge equivalence with simple-object labels fixed. The formulas specify
the effect on the associator and braiding; relabeling is a separate operation. -/
def GaugeEquivalent (s t : Symbols G K) : Prop :=
  ∃ g : Gauge G K, (∀ a b c,
    t.F a b c * g.u a b * g.u (a + b) c =
      s.F a b c * g.u b c * g.u a (b + c)) ∧
    (∀ a b, t.R a b * g.u a b = s.R a b * g.u b a)

/-- The identity change of fusion-space bases preserves all symbols. -/
theorem gaugeEquivalent_refl (s : Symbols G K) : GaugeEquivalent s s := by
  refine ⟨⟨fun _ _ => 1, by simp, by simp⟩, ?_, ?_⟩ <;> simp

/-- The self-braiding is invariant under a gauge change with fixed labels. -/
theorem gaugeEquivalent_self_braiding {s t : Symbols G K}
    (h : GaugeEquivalent s t) (a : G) : t.R a a = s.R a a := by
  obtain ⟨g, _, hr⟩ := h
  exact mul_right_cancel (hr a a)

/-- Unitarity for one-dimensional F and R blocks, relative to a chosen
embedding of the exact coefficient field into the complex numbers. -/
def IsUnitary {k : Type*} [Field k] (ι : k →+* ℂ) (s : Symbols G kˣ) : Prop :=
  (∀ a b c, Complex.normSq (ι (s.F a b c : k)) = 1) ∧
  (∀ a b, Complex.normSq (ι (s.R a b : k)) = 1)

end MTC.FRSymbols.Pointed
