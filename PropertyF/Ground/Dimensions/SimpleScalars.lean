module
public import PropertyF.Ground.Dimensions.DoubleDualFunctor
public import PropertyF.Ground.Fusion.Multiplicity

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Diagonal scalar maps, indexed by isomorphism classes of simples, commute
with all maps between finite sums of those simples. -/
theorem simple_scalar_biproduct_natural (C : Ground.BraidedFusionCategory.{v,u})
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → Fin (Ground.rank C)) (b : κ → Fin (Ground.rank C))
    (c : Fin (Ground.rank C) → ℂ)
    (f : (⨁ (fun i => Ground.simples C (a i))) ⟶ (⨁ (fun j => Ground.simples C (b j)))) :
    biproduct.map (fun i => c (a i) • 𝟙 (Ground.simples C (a i))) ≫ f =
      f ≫ biproduct.map (fun j => c (b j) • 𝟙 (Ground.simples C (b j))) := by
  classical
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc, biproduct.ι_map_assoc, biproduct.map_π,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  by_cases h : a i = b j
  · rw [show c (a i) = c (b j) from congrArg c h]
  · have hz : biproduct.ι (fun i => Ground.simples C (a i)) i ≫ f ≫
        biproduct.π (fun j => Ground.simples C (b j)) j = 0 := by
      by_contra hne
      let : Simple (Ground.simples C (a i)) := Ground.simples_simple C _
      let : Simple (Ground.simples C (b j)) := Ground.simples_simple C _
      let : IsIso (biproduct.ι (fun i => Ground.simples C (a i)) i ≫ f ≫
        biproduct.π (fun j => Ground.simples C (b j)) j) := isIso_of_hom_simple hne
      exact h (Ground.simples_injective C _ _ ⟨asIso
        (biproduct.ι (fun i => Ground.simples C (a i)) i ≫ f ≫
          biproduct.π (fun j => Ground.simples C (b j)) j)⟩)
    simp [hz]

/-- Index type for the canonical simple summands of an object. -/
abbrev simplePieces (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :=
  Σ i : Fin (Ground.rank C), Fin (Module.finrank ℂ (Ground.simples C i ⟶ X))

instance simplePieces_fintype (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    Fintype (simplePieces C X) := by
  unfold simplePieces
  infer_instance

/-- The actual simple object at each canonical summand. -/
abbrev simplePiecesObject (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    simplePieces C X → C.Obj := fun a => Ground.simples C a.1

/-- A chosen decomposition into simple summands with canonical multiplicities. -/
def simpleDecomposition (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    X ≅ ⨁ (simplePiecesObject C X) :=
  Classical.choice (Ground.exists_canonical_decomposition C X)

/-- On each object, scalar multiplication on simple summands, transported
through a chosen semisimple decomposition. -/
def simpleScalarComponent (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (X : C.Obj) : X ⟶ X :=
  (simpleDecomposition C X).hom ≫
    biproduct.map (fun a : simplePieces C X => c a.1 • 𝟙 (simplePiecesObject C X a)) ≫
    (simpleDecomposition C X).inv

set_option backward.isDefEq.respectTransparency false in
/-- A scalar assigned to each simple isomorphism class extends to a natural
endomorphism of the identity functor. -/
def simpleScalarNatural (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) : 𝟭 C.Obj ⟶ 𝟭 C.Obj where
  app X := simpleScalarComponent C c X
  naturality {X Y} f := by
    let ex := simpleDecomposition C X
    let ey := simpleDecomposition C Y
    let a : simplePieces C X → Fin (Ground.rank C) := fun i => i.1
    let b : simplePieces C Y → Fin (Ground.rank C) := fun i => i.1
    have h := simple_scalar_biproduct_natural C a b c (ex.inv ≫ f ≫ ey.hom)
    apply (cancel_epi ex.inv).1
    apply (cancel_mono ey.hom).1
    simp only [Functor.id_map, simpleScalarComponent]
    dsimp only [ex, ey] at h ⊢
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] at h ⊢
    simpa only [Category.assoc, simplePiecesObject, a, b] using h.symm

/-- The natural extension acts by the prescribed scalar on each simple. -/
theorem simpleScalarNatural_app_simple (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (i : Fin (Ground.rank C)) :
    (simpleScalarNatural C c).app (Ground.simples C i) = c i • 𝟙 (Ground.simples C i) := by
  classical
  let X := Ground.simples C i
  let a : simplePieces C X := ⟨i, ⟨0, by
    change 0 < Module.finrank ℂ (Ground.simples C i ⟶ Ground.simples C i)
    rw [Ground.finrank_simples_hom]
    simp⟩⟩
  let e := simpleDecomposition C X
  let V := simplePiecesObject C X
  let s : X ⟶ X := biproduct.ι V a ≫ e.inv
  let t : X ⟶ X := e.hom ≫ biproduct.π V a
  have hst : s ≫ t = 𝟙 X := by simp [s, t, Category.assoc, V, a, X, simplePiecesObject]
  have hs : s ≠ 0 := by
    intro hz
    have hid : 𝟙 X = 0 := by simpa [hz] using hst.symm
    let : Simple X := Ground.simples_simple C i
    exact id_nonzero X hid
  let : Simple X := Ground.simples_simple C i
  let : IsIso s := isIso_of_hom_simple hs
  apply (cancel_epi s).1
  change s ≫ simpleScalarComponent C c X = s ≫ (c i • 𝟙 X)
  simp [s, simpleScalarComponent, e, V, a, Category.assoc]

end PropertyF.Ground.Dimensions
