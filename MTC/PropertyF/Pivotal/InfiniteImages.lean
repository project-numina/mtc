module
public import MTC.Braided.Cabling.Strands
public import MTC.Fusion.Simples

/-! # Persistence of infinite braid images

Adding identity strands preserves an infinite braid image when tensoring with
its generating object is faithful. In particular this holds for simple
objects in a braided fusion category. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory MTC.Braided MTC.Fusion
namespace MTC.PropertyF.Pivotal
set_option linter.style.haveILetI false
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Adding an identity strand is injective when tensoring by the object is faithful. -/
theorem addLeftStrand_injective (X : C) [Functor.Faithful (tensorLeft X)] (n : ℕ) :
    Function.Injective (addLeftStrand X n) := by
  intro a b h
  apply Subtype.ext
  apply Aut.ext
  apply Iso.ext
  apply (tensorLeft X).map_injective
  have he := congrArg (fun t : braidImage X (n + 1) ↦ t.val.asIso.hom) h
  exact he

/-- Once an image is infinite, every image on more strands is infinite,
provided tensoring by the generating object is faithful. -/
theorem braidImage_infinite_of_le (X : C) [Functor.Faithful (tensorLeft X)]
    {n m : ℕ} (hn : Infinite (braidImage X n)) (h : n ≤ m) :
    Infinite (braidImage X m) := by
  induction m, h using Nat.le_induction with
  | base => exact hn
  | succ m hm ih =>
    letI : Infinite (braidImage X m) := ih
    apply not_finite_iff_infinite.mp
    intro hf
    letI : Finite (braidImage X (m + 1)) := hf
    letI : Finite (braidImage X m) := Finite.of_injective (addLeftStrand X m)
      (addLeftStrand_injective X m)
    exact not_finite (braidImage X m)

/-- An infinite image of a simple object in a braided fusion category remains
infinite after adding any number of strands. -/
theorem simple_braidImage_infinite_of_le (D : BraidedFusionCategory.{v,u})
    (X : D.Obj) [Simple X] {n m : ℕ} (hn : Infinite (braidImage X n)) (h : n ≤ m) :
    Infinite (braidImage X m) := by
  obtain ⟨i, r, hir⟩ := unit_retract_leftDual_tensor X
  letI : Functor.Faithful (tensorLeft X) := tensorLeft_faithful_of_unit_retract i r hir
  exact braidImage_infinite_of_le X hn h

/-- A simple object that fails objectwise property F has infinite braid
images on every sufficiently large number of strands. -/
theorem eventually_infinite_braidImages_of_not_objectPropertyF
    (D : BraidedFusionCategory.{v,u}) (X : D.Obj) [Simple X]
    (h : ¬ ObjectPropertyF X) :
    ∃ n, ∀ m ≥ n, Infinite (braidImage X m) := by
  classical
  have hn : ∃ n, ¬ Finite (braidImage X n) := by
    simpa only [ObjectPropertyF, not_forall] using h
  obtain ⟨n, hn⟩ := hn
  exact ⟨n, fun m hm ↦ simple_braidImage_infinite_of_le D X
    (not_finite_iff_infinite.mp hn) hm⟩

end MTC.PropertyF.Pivotal
