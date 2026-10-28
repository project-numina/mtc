module
public import PropertyF.Ground.Dimensions.DualTensorNaturality
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
section
variable {k : Type*} [CommSemiring k] {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [Preadditive C] [Linear k C]
  [MonoidalPreadditive C] [MonoidalLinear k C]

/-- Right-dual mates are linear in the morphism. -/
theorem rightAdjointMate_smul {X Y : C} [HasRightDual X] [HasRightDual Y] (c : k) (f : X ⟶ Y) :
    (c • f)ᘁ = c • (fᘁ) := by simp [rightAdjointMate]

end
variable {k : Type*} [Field k] {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Rescaling an isomorphism by a nonzero scalar preserves invertibility. -/
def scaleIso {X Y : C} (e : X ≅ Y) (c : k) (hc : c ≠ 0) : X ≅ Y where
  hom := c • e.hom
  inv := c⁻¹ • e.inv
  hom_inv_id := by simp [smul_smul, hc]
  inv_hom_id := by simp [smul_smul, hc]

end PropertyF.Ground.Dimensions

namespace PropertyF.Ground.Dimensions
universe v u

variable {k : Type*} [Field k] [IsAlgClosed k]
  {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C] [HasKernels C]

omit [RightRigidCategory C] in
/-- A fourth-dual isomorphism on a simple object has a square root whenever
there is a double-dual isomorphism. -/
theorem exists_fourthDual_square_root
    {X : C} [HasRightDual X] [HasRightDual (Xᘁ)] [HasRightDual ((Xᘁ)ᘁ)]
    [HasRightDual (((Xᘁ)ᘁ)ᘁ)] [Simple X] [FiniteDimensional k (X ⟶ X)]
    (e : X ≅ (Xᘁ)ᘁ) (g : X ≅ ((((Xᘁ)ᘁ)ᘁ)ᘁ)) :
    ∃ a : X ≅ ((Xᘁ)ᘁ), a ≪≫ rightDualIsoMap (rightDualIsoMap a) = g := by
  let e2 := e ≪≫ rightDualIsoMap (rightDualIsoMap e)
  obtain ⟨c, hc0, hc, _⟩ := isomorphisms_scalar (k := k) e2 g
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) (by decide)
  have hz0 : z ≠ 0 := fun h ↦ hc0 (by simpa [h] using hz.symm)
  refine ⟨scaleIso e z hz0, ?_⟩
  apply Iso.ext
  change (z • e.hom) ≫ (((z • e.hom)ᘁ)ᘁ) = g.hom
  rw [rightAdjointMate_smul, rightAdjointMate_smul, Linear.smul_comp, Linear.comp_smul,
    smul_smul, ← pow_two, hz]
  change c • e2.hom = g.hom
  exact hc.symm

end PropertyF.Ground.Dimensions

namespace PropertyF.Ground.Dimensions
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- A chosen square root of the natural braided fourth-dual map on each
simple representative. -/
def fourthDualSimpleRoot (C : BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    simples C i ≅ ((simples C i)ᘁ)ᘁ :=
  letI : Simple (simples C i) := simples_simple C i
  letI : FiniteDimensional ℂ (simples C i ⟶ simples C i) := IsFusionCategory.hom_finite _ _
  Classical.choose (exists_fourthDual_square_root (k := ℂ) (doubleDualIso C _) (fourthDualIso (simples C i)))

/-- The chosen simple component squares to the natural fourth-dual component. -/
theorem fourthDualSimpleRoot_sq (i : Fin (rank C)) :
    fourthDualSimpleRoot C i ≪≫ rightDualIsoMap (rightDualIsoMap (fourthDualSimpleRoot C i)) =
      fourthDualIso (simples C i) :=
  letI : Simple (simples C i) := simples_simple C i
  letI : FiniteDimensional ℂ (simples C i ⟶ simples C i) := IsFusionCategory.hom_finite _ _
  Classical.choose_spec (exists_fourthDual_square_root (k := ℂ) (doubleDualIso C _) (fourthDualIso (simples C i)))

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
def drinfeldNaturalIso (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [RightRigidCategory C] : 𝟭 C ≅ doubleDualFunctor C :=
  NatIso.ofComponents (fun X ↦ drinfeldIso X) (fun f ↦ drinfeldIso_natural f)

/-- The canonical braided fourth-dual components form a natural
isomorphism. Tensor compatibility is not asserted here. -/
def fourthDualNaturalIso (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [RightRigidCategory C] :
    𝟭 C ≅ doubleDualFunctor C ⋙ doubleDualFunctor C :=
  NatIso.ofComponents (fun X ↦ fourthDualIso X) (fun f ↦ fourthDualIso_natural f)

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

/-- Diagonal scalar maps, indexed by isomorphism classes of simples, commute
with all maps between finite sums of those simples. -/
theorem simple_scalar_biproduct_natural
    {k : Type*} [CommSemiring k] {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear k C] [HasKernels C] {L ι κ : Type*} (T : L → C) (hT : ∀ i, Simple (T i))
    (hinj : ∀ {i j}, Nonempty (T i ≅ T j) → i = j)
    (a : ι → L) (b : κ → L) (c : L → k)
    [HasBiproduct (fun i ↦ T (a i))] [HasBiproduct (fun j ↦ T (b j))]
    (f : (⨁ (fun i ↦ T (a i))) ⟶ (⨁ (fun j ↦ T (b j)))) :
    biproduct.map (fun i ↦ c (a i) • 𝟙 (T (a i))) ≫ f =
      f ≫ biproduct.map (fun j ↦ c (b j) • 𝟙 (T (b j))) := by
  classical
  refine biproduct.hom_ext' _ _ fun i ↦ biproduct.hom_ext _ _ fun j ↦ ?_
  simp only [Category.assoc, biproduct.ι_map_assoc, biproduct.map_π,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  let g := biproduct.ι (fun i ↦ T (a i)) i ≫ f ≫ biproduct.π (fun j ↦ T (b j)) j
  change c (a i) • g = c (b j) • g
  by_cases hg : g = 0
  · simp [hg]
  · let : Simple (T (a i)) := hT _
    let : Simple (T (b j)) := hT _
    let : IsIso g := isIso_of_hom_simple hg
    rw [show c (a i) = c (b j) from congrArg c (hinj ⟨asIso g⟩)]

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Index type for the canonical simple summands of an object. -/
abbrev simplePieces (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :=
  Σ i : Fin (rank C), Fin (simpleMultiplicity C i X)

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

/-- The inclusion of a chosen simple summand in the canonical decomposition. -/
def simpleInclusion (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
    (k : Fin (rank C)) (t : Fin (simpleMultiplicity C k X)) :
    simples C k ⟶ X :=
  biproduct.ι (simplePiecesObject C X) ⟨k, t⟩ ≫ (simpleDecomposition C X).inv

/-- Morphisms are determined by their restrictions to the chosen simple summands. -/
theorem simpleInclusion_hom_ext {X Y : C.Obj} {f g : X ⟶ Y}
    (h : ∀ i t, simpleInclusion C X i t ≫ f = simpleInclusion C X i t ≫ g) : f = g :=
  (cancel_epi (simpleDecomposition C X).inv).1 (biproduct.hom_ext' _ _ fun a ↦ by
    simpa [simpleInclusion, Category.assoc] using h a.1 a.2)

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
    have h := simple_scalar_biproduct_natural (simples C) (simples_simple C)
      (fun h ↦ simples_injective C h) a b c (ex.inv ≫ f ≫ ey.hom)
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
    simp [simpleMultiplicity, finrank_simples_hom, X]⟩⟩
  let e := simpleDecomposition C X
  let V := simplePiecesObject C X
  let s : X ⟶ X := biproduct.ι V a ≫ e.inv
  let : Simple X := simples_simple C i
  let : IsIso s := isIso_of_hom_simple (mono_ne_zero_of_id_ne_zero s (id_nonzero X))
  apply (cancel_epi s).1
  simp [simpleScalarNatural, s, simpleScalarComponent, e, V, a, X, Category.assoc]

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
    {c : Fin (rank C) → ℂ} (hc : ∀ i, c i ≠ 0) (i : Fin (rank C)) :
    ((simpleScalarNaturalIso C c hc).app (simples C i)).hom =
      c i • 𝟙 (simples C i) := simpleScalarNatural_app_simple C c i

/-- Maps out of a tensor product of finite biproducts are determined by their
restrictions to the tensor products of summand inclusions. -/
theorem tensorBiproduct_hom_ext
    {E : Type u} [Category.{v} E] [MonoidalCategory E] [Preadditive E]
    [MonoidalPreadditive E] [HasFiniteBiproducts E]
    {ι κ : Type} [Fintype ι] [Fintype κ] {F : ι → E} {G : κ → E}
    {Z : E} {f g : (⨁ F) ⊗ (⨁ G) ⟶ Z}
    (h : ∀ i j, (biproduct.ι F i ⊗ₘ biproduct.ι G j) ≫ f =
      (biproduct.ι F i ⊗ₘ biproduct.ι G j) ≫ g) : f = g := by
  let r : ((⨁ F) ⊗ (⨁ G)) ≅ ⨁ (fun i => F i ⊗ (⨁ G)) := rightDistributor F (⨁ G)
  refine (cancel_epi r.inv).1 (biproduct.hom_ext' _ _ fun i ↦ ?_)
  simp only [r, biproduct_ι_comp_rightDistributor_inv_assoc]
  refine (cancel_epi (leftDistributor (F i) G).inv).1 (biproduct.hom_ext' _ _ fun j ↦ ?_)
  simpa only [biproduct_ι_comp_leftDistributor_inv_assoc, tensorHom_def', Category.assoc] using h i j

/-- Maps out of a tensor product are determined by their composites with
tensors of maps from chosen simple objects. -/
theorem tensor_simples_hom_ext {X Y Z : C.Obj} {f g : X ⊗ Y ⟶ Z}
    (h : ∀ {i j} (sx : simples C i ⟶ X) (sy : simples C j ⟶ Y),
      (sx ⊗ₘ sy) ≫ f = (sx ⊗ₘ sy) ≫ g) : f = g := by
  apply (cancel_epi ((simpleDecomposition C X).symm ⊗ᵢ (simpleDecomposition C Y).symm).hom).1
  refine tensorBiproduct_hom_ext fun i j ↦ ?_
  simpa [simpleInclusion, tensorIso_hom, tensorHom_comp_tensorHom, Category.assoc] using
    h (simpleInclusion C X i.1 i.2) (simpleInclusion C Y j.1 j.2)


end PropertyF.Ground.Dimensions

end
