module
public import PropertyF.Ground.Dimensions.Drinfeld
public import PropertyF.Ground.Dimensions.GroundNorm
public import PropertyF.Ground.Fusion.Simples
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import PropertyF.Ground.Fusion.Multiplicity

/-! # Scalar natural transformations

Simple objects determine scalar components and natural roots of the fourth-dual isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Right-dual mates are complex-linear in the morphism. -/
theorem rightAdjointMate_smul {X Y : C} (c : ℂ) (f : X ⟶ Y) :
    (c • f)ᘁ = c • (fᘁ) := by simp [rightAdjointMate]

/-- Rescaling an isomorphism by a nonzero scalar preserves invertibility. -/
def scaleIso {X Y : C} (e : X ≅ Y) (c : ℂ) (hc : c ≠ 0) : X ≅ Y where
  hom := c • e.hom
  inv := c⁻¹ • e.inv
  hom_inv_id := by simp [smul_smul, hc]
  inv_hom_id := by simp [smul_smul, hc]

end PropertyF.Ground.Dimensions

namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- For every simple object, any prescribed fourth-dual isomorphism has a
square root through the double dual. No monoidality or naturality is assumed. -/
theorem exists_fourthDual_square_root
    {X : C.Obj} [Simple X] (g : X ≅ ((((Xᘁ)ᘁ)ᘁ)ᘁ)) :
    ∃ a : X ≅ ((Xᘁ)ᘁ), a ≪≫ rightDualIsoMap (rightDualIsoMap a) = g := by
  let e := doubleDualIso C X
  let e2 := e ≪≫ rightDualIsoMap (rightDualIsoMap e)
  let : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  obtain ⟨c, hc0, hc, _⟩ := isomorphisms_scalar e2 g
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) (by decide)
  have hz0 : z ≠ 0 := by
    intro h
    apply hc0
    simpa [h] using hz.symm
  refine ⟨scaleIso e z hz0, ?_⟩
  apply Iso.ext
  change (z • e.hom) ≫ (((z • e.hom)ᘁ)ᘁ) = g.hom
  rw [rightAdjointMate_smul, rightAdjointMate_smul, Linear.smul_comp, Linear.comp_smul, smul_smul]
  rw [← pow_two, hz]
  change c • e2.hom = g.hom
  exact hc.symm

/-- A chosen square root of the natural braided fourth-dual map on each
simple representative. -/
def fourthDualSimpleRoot (C : BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    simples C i ≅ ((simples C i)ᘁ)ᘁ := by
  let : Simple (simples C i) := simples_simple C i
  exact Classical.choose (exists_fourthDual_square_root C
    (fourthDualIso C (simples C i)))

/-- The chosen simple component squares to the natural fourth-dual component. -/
theorem fourthDualSimpleRoot_sq (i : Fin (rank C)) :
    fourthDualSimpleRoot C i ≪≫ rightDualIsoMap (rightDualIsoMap (fourthDualSimpleRoot C i)) =
      fourthDualIso C (simples C i) := by
  let : Simple (simples C i) := simples_simple C i
  exact Classical.choose_spec (exists_fourthDual_square_root C
    (fourthDualIso C (simples C i)))

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The double-right-dual assignment is a covariant endofunctor. -/
def doubleDualFunctor : C ⥤ C where
  obj X := (Xᘁ)ᘁ
  map f := (fᘁ)ᘁ
  map_id X := by simp
  map_comp f g := by simp [comp_rightAdjointMate]


end PropertyF.Ground.Dimensions

namespace PropertyF.Ground.Dimensions
universe v u

/-- The canonical braided double-dual components form a natural isomorphism. -/
def drinfeldNaturalIso (C : BraidedFusionCategory.{v,u}) :
    𝟭 C.Obj ≅ doubleDualFunctor C.Obj :=
  NatIso.ofComponents (doubleDualIso C) (fun f => doubleDualIso_natural C f)

/-- The canonical braided fourth-dual components form a natural
isomorphism. Tensor compatibility is not asserted here. -/
def fourthDualNaturalIso (C : BraidedFusionCategory.{v,u}) :
    𝟭 C.Obj ≅ doubleDualFunctor C.Obj ⋙ doubleDualFunctor C.Obj :=
  NatIso.ofComponents (fourthDualIso C) (fun f => fourthDualIso_natural C f)

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Diagonal scalar maps, indexed by isomorphism classes of simples, commute
with all maps between finite sums of those simples. -/
theorem simple_scalar_biproduct_natural
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → Fin (rank C)) (b : κ → Fin (rank C))
    (c : Fin (rank C) → ℂ)
    (f : (⨁ (fun i => simples C (a i))) ⟶ (⨁ (fun j => simples C (b j)))) :
    biproduct.map (fun i => c (a i) • 𝟙 (simples C (a i))) ≫ f =
      f ≫ biproduct.map (fun j => c (b j) • 𝟙 (simples C (b j))) := by
  classical
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc, biproduct.ι_map_assoc, biproduct.map_π,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  by_cases h : a i = b j
  · rw [show c (a i) = c (b j) from congrArg c h]
  · have hz : biproduct.ι (fun i => simples C (a i)) i ≫ f ≫
        biproduct.π (fun j => simples C (b j)) j = 0 := by
      by_contra hne
      let : Simple (simples C (a i)) := simples_simple C _
      let : Simple (simples C (b j)) := simples_simple C _
      let : IsIso (biproduct.ι (fun i => simples C (a i)) i ≫ f ≫
        biproduct.π (fun j => simples C (b j)) j) := isIso_of_hom_simple hne
      exact h (simples_injective C ⟨asIso
        (biproduct.ι (fun i => simples C (a i)) i ≫ f ≫
          biproduct.π (fun j => simples C (b j)) j)⟩)
    simp [hz]

/-- Index type for the canonical simple summands of an object. -/
abbrev simplePieces (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :=
  Σ i : Fin (rank C), Fin (Module.finrank ℂ (simples C i ⟶ X))

instance instFintypeSimplePieces (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    Fintype (simplePieces C X) := by
  unfold simplePieces
  infer_instance

/-- The actual simple object at each canonical summand. -/
abbrev simplePiecesObject (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    simplePieces C X → C.Obj := fun a => simples C a.1

/-- A chosen decomposition into simple summands with canonical multiplicities. -/
def simpleDecomposition (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    X ≅ ⨁ (simplePiecesObject C X) :=
  Classical.choice (exists_canonical_decomposition C X)

/-- On each object, scalar multiplication on simple summands, transported
through a chosen semisimple decomposition. -/
def simpleScalarComponent (C : BraidedFusionCategory.{v,u})
    (c : Fin (rank C) → ℂ) (X : C.Obj) : X ⟶ X :=
  (simpleDecomposition C X).hom ≫
    biproduct.map (fun a : simplePieces C X => c a.1 • 𝟙 (simplePiecesObject C X a)) ≫
    (simpleDecomposition C X).inv

set_option backward.isDefEq.respectTransparency false in
/-- A scalar assigned to each simple isomorphism class extends to a natural
endomorphism of the identity functor. -/
def simpleScalarNatural (C : BraidedFusionCategory.{v,u})
    (c : Fin (rank C) → ℂ) : 𝟭 C.Obj ⟶ 𝟭 C.Obj where
  app X := simpleScalarComponent C c X
  naturality {X Y} f := by
    let ex := simpleDecomposition C X
    let ey := simpleDecomposition C Y
    let a : simplePieces C X → Fin (rank C) := fun i => i.1
    let b : simplePieces C Y → Fin (rank C) := fun i => i.1
    have h := simple_scalar_biproduct_natural C a b c (ex.inv ≫ f ≫ ey.hom)
    apply (cancel_epi ex.inv).1
    apply (cancel_mono ey.hom).1
    simp only [Functor.id_map, simpleScalarComponent]
    dsimp only [ex, ey] at h ⊢
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] at h ⊢
    simpa only [Category.assoc, simplePiecesObject, a, b] using h.symm

/-- The natural extension acts by the prescribed scalar on each simple. -/
theorem simpleScalarNatural_app_simple
    (c : Fin (rank C) → ℂ) (i : Fin (rank C)) :
    (simpleScalarNatural C c).app (simples C i) = c i • 𝟙 (simples C i) := by
  classical
  let X := simples C i
  let a : simplePieces C X := ⟨i, ⟨0, by
    change 0 < Module.finrank ℂ (simples C i ⟶ simples C i)
    rw [finrank_simples_hom]
    simp⟩⟩
  let e := simpleDecomposition C X
  let V := simplePiecesObject C X
  let s : X ⟶ X := biproduct.ι V a ≫ e.inv
  let t : X ⟶ X := e.hom ≫ biproduct.π V a
  have hst : s ≫ t = 𝟙 X := by simp [s, t, Category.assoc, V, a, X, simplePiecesObject]
  have hs : s ≠ 0 := by
    intro hz
    have hid : 𝟙 X = 0 := by simpa [hz] using hst.symm
    let : Simple X := simples_simple C i
    exact id_nonzero X hid
  let : Simple X := simples_simple C i
  let : IsIso s := isIso_of_hom_simple hs
  apply (cancel_epi s).1
  change s ≫ simpleScalarComponent C c X = s ≫ (c i • 𝟙 X)
  simp [s, simpleScalarComponent, e, V, a, Category.assoc]

/-- Nonzero scalar values on all simples extend to a natural automorphism of
the identity functor. -/
def simpleScalarNaturalIso (C : BraidedFusionCategory.{v,u})
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0) : 𝟭 C.Obj ≅ 𝟭 C.Obj := by
  let component (X : C.Obj) : X ≅ X :=
    simpleDecomposition C X ≪≫
      biproduct.mapIso (fun a : simplePieces C X =>
        scaleIso (Iso.refl (simplePiecesObject C X a)) (c a.1) (hc a.1)) ≪≫
      (simpleDecomposition C X).symm
  have hcomponent (X : C.Obj) : (component X).hom = simpleScalarComponent C c X := by
    simp [component, simpleScalarComponent, scaleIso]
  refine NatIso.ofComponents component ?_
  intro X Y f
  simp only [Functor.id_map, hcomponent]
  exact (simpleScalarNatural C c).naturality f

/-- On each simple, the natural automorphism has the prescribed scalar component. -/
theorem simpleScalarNaturalIso_app_simple
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (i : Fin (rank C)) :
    ((simpleScalarNaturalIso C c hc).app (simples C i)).hom =
      c i • 𝟙 (simples C i) := by
  change simpleScalarComponent C c (simples C i) = _
  exact simpleScalarNatural_app_simple C c i

/-- Maps out of a tensor product of finite biproducts are determined by their
restrictions to the tensor products of summand inclusions. -/
theorem tensorBiproduct_hom_ext
    {ι κ : Type} [Fintype ι] [Fintype κ] (F : ι → C.Obj) (G : κ → C.Obj)
    {Z : C.Obj} (f g : (⨁ F) ⊗ (⨁ G) ⟶ Z)
    (h : ∀ i j, (biproduct.ι F i ⊗ₘ biproduct.ι G j) ≫ f =
      (biproduct.ι F i ⊗ₘ biproduct.ι G j) ≫ g) : f = g := by
  let r : ((⨁ F) ⊗ (⨁ G)) ≅ ⨁ (fun i => F i ⊗ (⨁ G)) := rightDistributor F (⨁ G)
  apply (cancel_epi r.inv).1
  apply biproduct.hom_ext'
  intro i
  dsimp only [r]
  simp only [biproduct_ι_comp_rightDistributor_inv_assoc]
  apply (cancel_epi (leftDistributor (F i) G).inv).1
  apply biproduct.hom_ext'
  intro j
  simp only [biproduct_ι_comp_leftDistributor_inv_assoc]
  simpa only [tensorHom_def', Category.assoc] using h i j

/-- If scalars multiply along every nonzero fusion coefficient, the natural
scalar map has the expected tensor component on pairs of simple objects. -/
theorem simpleScalarNatural_tensor_simples
    (c : Fin (rank C) → ℂ)
    (hmul : ∀ i j k, fusionCoeff C i j k ≠ 0 → c k = c i * c j)
    (i j : Fin (rank C)) :
    (simpleScalarNatural C c).app (simples C i ⊗ simples C j) =
      (c i * c j) • 𝟙 (simples C i ⊗ simples C j) := by
  classical
  let X := simples C i ⊗ simples C j
  let e := simpleDecomposition C X
  let V := simplePiecesObject C X
  apply (cancel_epi e.inv).1
  apply biproduct.hom_ext'
  intro a
  have hn := (simpleScalarNatural C c).naturality (biproduct.ι V a ≫ e.inv)
  simp only [Functor.id_map] at hn
  change (biproduct.ι V a ≫ e.inv) ≫ (simpleScalarNatural C c).app X =
    (simpleScalarNatural C c).app (simples C a.1) ≫ biproduct.ι V a ≫ e.inv at hn
  rw [simpleScalarNatural_app_simple] at hn
  have hcoeff : fusionCoeff C i j a.1 ≠ 0 := by
    change Module.finrank ℂ (simples C a.1 ⟶ X) ≠ 0
    exact Nat.ne_of_gt (Nat.zero_lt_of_lt a.2.isLt)
  simpa [V, X, simplePiecesObject, (hmul i j a.1 hcoeff), Category.assoc] using hn

/-- Scalar values satisfying the fusion support rule extend to a tensor
natural endomorphism of the identity. -/
theorem simpleScalarNatural_tensor
    (c : Fin (rank C) → ℂ)
    (hmul : ∀ i j k, fusionCoeff C i j k ≠ 0 → c k = c i * c j)
    (X Y : C.Obj) :
    (simpleScalarNatural C c).app (X ⊗ Y) =
      (simpleScalarNatural C c).app X ⊗ₘ (simpleScalarNatural C c).app Y := by
  classical
  let ex := simpleDecomposition C X
  let ey := simpleDecomposition C Y
  let V := simplePiecesObject C X
  let W := simplePiecesObject C Y
  apply (cancel_epi (ex.symm ⊗ᵢ ey.symm).hom).1
  apply tensorBiproduct_hom_ext C V W
  intro a b
  let sx : simples C a.1 ⟶ X := biproduct.ι V a ≫ ex.inv
  let sy : simples C b.1 ⟶ Y := biproduct.ι W b ≫ ey.inv
  have hx : sx ≫ (simpleScalarNatural C c).app X = c a.1 • sx := by
    have h := (simpleScalarNatural C c).naturality sx
    simp only [Functor.id_map, simpleScalarNatural_app_simple, Linear.smul_comp] at h
    simpa [Linear.smul_comp] using h
  have hy : sy ≫ (simpleScalarNatural C c).app Y = c b.1 • sy := by
    have h := (simpleScalarNatural C c).naturality sy
    simp only [Functor.id_map, simpleScalarNatural_app_simple, Linear.smul_comp] at h
    simpa [Linear.smul_comp] using h
  have ht : (sx ⊗ₘ sy) ≫
      ((simpleScalarNatural C c).app X ⊗ₘ (simpleScalarNatural C c).app Y) =
      (c a.1 * c b.1) • (sx ⊗ₘ sy) := by
    rw [tensorHom_comp_tensorHom, hx, hy]
    simp [tensorHom_def, smul_smul, mul_comm]
  have hs : (sx ⊗ₘ sy) ≫ (simpleScalarNatural C c).app (X ⊗ Y) =
      (c a.1 * c b.1) • (sx ⊗ₘ sy) := by
    have h := (simpleScalarNatural C c).naturality (sx ⊗ₘ sy)
    simp only [Functor.id_map, simpleScalarNatural_tensor_simples C c hmul,
      Linear.smul_comp] at h
    simpa [Linear.smul_comp] using h
  simpa [sx, sy, ex, ey, V, W, tensorIso_hom, tensorHom_comp_tensorHom,
    Category.assoc] using hs.trans ht.symm

/-- The unit component is the identity when the unit scalar is one. -/
theorem simpleScalarNatural_unit
    (c : Fin (rank C) → ℂ) (hunit : c (unitIndex C) = 1) :
    (simpleScalarNatural C c).app (𝟙_ C.Obj) = 𝟙 _ := by
  obtain ⟨e⟩ := unitIndex_iso C
  apply (cancel_epi e.hom).1
  simpa [simpleScalarNatural_app_simple, hunit] using
    (simpleScalarNatural C c).naturality e.hom

end PropertyF.Ground.Dimensions

end
