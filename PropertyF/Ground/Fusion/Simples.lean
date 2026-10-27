module
public import PropertyF.Ground.Fusion.Splitting
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Simple representatives chosen by the ground category interface. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace PropertyF.Ground
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable (C : BraidedFusionCategory.{v,u})

theorem simples_simple (i : Fin (rank C)) : Simple (simples C i) :=
  (Classical.choose_spec (Classical.choose_spec
    (IsFusionCategory.finite_semisimple (C := C.Obj)))).1 i

theorem simples_injective (i j : Fin (rank C))
    (h : Nonempty (simples C i ≅ simples C j)) : i = j :=
  (Classical.choose_spec (Classical.choose_spec
    (IsFusionCategory.finite_semisimple (C := C.Obj)))).2.1 i j h

theorem simples_decompose (X : C.Obj) : ∃ m : Fin (rank C) → ℕ,
    Nonempty (X ≅ ⨁ (fun p : Σ i, Fin (m i) => simples C p.1)) :=
  (Classical.choose_spec (Classical.choose_spec
    (IsFusionCategory.finite_semisimple (C := C.Obj)))).2.2 X

/-- Every simple object is isomorphic to one of the chosen representatives. -/
theorem exists_simple_iso (X : C.Obj) [Simple X] :
    ∃ i : Fin (rank C), Nonempty (X ≅ simples C i) := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose C X
  let V : (Σ i, Fin (m i)) → C.Obj := fun p => simples C p.1
  have he : e.hom ≠ 0 := by
    intro h
    have hh := congrArg (fun t => t ≫ e.inv) h
    apply id_nonzero X
    simpa using hh
  have hp : ∃ p, e.hom ≫ biproduct.π V p ≠ 0 := by
    by_contra h
    push Not at h
    apply he
    apply biproduct.hom_ext
    intro p
    simpa using h p
  obtain ⟨p, hp⟩ := hp
  letI : Simple (V p) := simples_simple C p.1
  letI : IsIso (e.hom ≫ biproduct.π V p) := CategoryTheory.isIso_of_hom_simple hp
  exact ⟨p.1, ⟨asIso (e.hom ≫ biproduct.π V p)⟩⟩

/-- The tensor unit occurs among the representatives. -/
theorem exists_unit_iso : ∃ i : Fin (rank C), Nonempty (simples C i ≅ 𝟙_ C.Obj) := by
  letI : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  obtain ⟨i, ⟨e⟩⟩ := exists_simple_iso C (𝟙_ C.Obj)
  exact ⟨i, ⟨e.symm⟩⟩

/-- Hom spaces between the chosen simples have the expected multiplicities. -/
theorem finrank_simples_hom (i j : Fin (rank C)) :
    Module.finrank ℂ (simples C i ⟶ simples C j) = if i = j then 1 else 0 := by
  classical
  letI : Simple (simples C i) := simples_simple C i
  letI : Simple (simples C j) := simples_simple C j
  letI : ∀ X Y : C.Obj, FiniteDimensional ℂ (X ⟶ Y) := IsFusionCategory.hom_finite
  rw [CategoryTheory.finrank_hom_simple_simple ℂ]
  congr 1
  exact propext ⟨simples_injective C i j, fun h => by subst j; exact ⟨Iso.refl _⟩⟩

end PropertyF.Ground
