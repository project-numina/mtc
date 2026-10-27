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

/-- Nonzero scalar values on all simples extend to a natural automorphism of
the identity functor. -/
def simpleScalarNaturalIso (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0) : 𝟭 C.Obj ≅ 𝟭 C.Obj := by
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
theorem simpleScalarNaturalIso_app_simple (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (i : Fin (Ground.rank C)) :
    ((simpleScalarNaturalIso C c hc).app (Ground.simples C i)).hom =
      c i • 𝟙 (Ground.simples C i) := by
  change simpleScalarComponent C c (Ground.simples C i) = _
  exact simpleScalarNatural_app_simple C c i

/-- Maps out of a tensor product of finite biproducts are determined by their
restrictions to the tensor products of summand inclusions. -/
theorem tensorBiproduct_hom_ext (C : Ground.BraidedFusionCategory.{v,u})
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
theorem simpleScalarNatural_tensor_simples (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ)
    (hmul : ∀ i j k, Ground.fusionCoeff C i j k ≠ 0 → c k = c i * c j)
    (i j : Fin (Ground.rank C)) :
    (simpleScalarNatural C c).app (Ground.simples C i ⊗ Ground.simples C j) =
      (c i * c j) • 𝟙 (Ground.simples C i ⊗ Ground.simples C j) := by
  classical
  let X := Ground.simples C i ⊗ Ground.simples C j
  let e := simpleDecomposition C X
  let V := simplePiecesObject C X
  apply (cancel_epi e.inv).1
  apply biproduct.hom_ext'
  intro a
  have hn := (simpleScalarNatural C c).naturality (biproduct.ι V a ≫ e.inv)
  simp only [Functor.id_map] at hn
  change (biproduct.ι V a ≫ e.inv) ≫ (simpleScalarNatural C c).app X =
    (simpleScalarNatural C c).app (Ground.simples C a.1) ≫ biproduct.ι V a ≫ e.inv at hn
  rw [simpleScalarNatural_app_simple] at hn
  have hcoeff : Ground.fusionCoeff C i j a.1 ≠ 0 := by
    change Module.finrank ℂ (Ground.simples C a.1 ⟶ X) ≠ 0
    exact Nat.ne_of_gt (Nat.zero_lt_of_lt a.2.isLt)
  have hscalar := hmul i j a.1 hcoeff
  simpa [V, X, simplePiecesObject, hscalar, Category.assoc] using hn

/-- Scalar values satisfying the fusion support rule extend to a tensor
natural endomorphism of the identity. -/
theorem simpleScalarNatural_tensor (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ)
    (hmul : ∀ i j k, Ground.fusionCoeff C i j k ≠ 0 → c k = c i * c j)
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
  let sx : Ground.simples C a.1 ⟶ X := biproduct.ι V a ≫ ex.inv
  let sy : Ground.simples C b.1 ⟶ Y := biproduct.ι W b ≫ ey.inv
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
theorem simpleScalarNatural_unit (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (hunit : c (Ground.unitIndex C) = 1) :
    (simpleScalarNatural C c).app (𝟙_ C.Obj) = 𝟙 _ := by
  obtain ⟨e⟩ := Ground.unitIndex_iso C
  apply (cancel_epi e.hom).1
  have h := (simpleScalarNatural C c).naturality e.hom
  simp only [Functor.id_map, simpleScalarNatural_app_simple, hunit, one_smul] at h
  simpa using h

/-- Fusion-compatible scalar labels define a monoidal natural transformation. -/
theorem simpleScalarNatural_isMonoidal (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (hunit : c (Ground.unitIndex C) = 1)
    (hmul : ∀ i j k, Ground.fusionCoeff C i j k ≠ 0 → c k = c i * c j) :
    NatTrans.IsMonoidal (simpleScalarNatural C c) where
  unit := by simpa using simpleScalarNatural_unit C c hunit
  tensor X Y := by simpa using simpleScalarNatural_tensor C c hmul X Y

set_option backward.isDefEq.respectTransparency false in
/-- The monoidality conditions for scalar natural maps are exactly the unit
and fusion-support relations on their simple labels. -/
theorem simpleScalarNatural_isMonoidal_iff (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) :
    NatTrans.IsMonoidal (simpleScalarNatural C c) ↔
      c (Ground.unitIndex C) = 1 ∧
      ∀ i j k, Ground.fusionCoeff C i j k ≠ 0 → c k = c i * c j := by
  constructor
  · intro h
    letI := h
    have hu : (simpleScalarNatural C c).app (𝟙_ C.Obj) = 𝟙 _ := by
      simpa using (NatTrans.IsMonoidal.unit (τ := simpleScalarNatural C c))
    constructor
    · obtain ⟨e⟩ := Ground.unitIndex_iso C
      letI : Simple (Ground.simples C (Ground.unitIndex C)) := Ground.simples_simple C _
      have hs : (simpleScalarNatural C c).app (Ground.simples C (Ground.unitIndex C)) = 𝟙 _ := by
        apply (cancel_mono e.hom).1
        have h := (simpleScalarNatural C c).naturality e.hom
        simp only [Functor.id_map, hu, Category.comp_id, Category.id_comp] at h
        simpa using h.symm
      rw [simpleScalarNatural_app_simple] at hs
      apply smul_left_injective ℂ (id_nonzero (Ground.simples C (Ground.unitIndex C)))
      simpa using hs
    · intro i j k hcoeff
      let Z := Ground.simples C i ⊗ Ground.simples C j
      let W := Ground.simples C k
      letI : FiniteDimensional ℂ (W ⟶ Z) := Ground.IsFusionCategory.hom_finite _ _
      have hn : ¬ Subsingleton (W ⟶ Z) := by
        intro hzero
        apply hcoeff
        change Module.finrank ℂ (W ⟶ Z) = 0
        exact Module.finrank_zero_iff.mpr hzero
      have hf : ∃ f : W ⟶ Z, f ≠ 0 := by
        by_contra hh
        apply hn
        push_neg at hh
        constructor
        intro x y
        have hx : x = 0 := by simpa using hh x
        have hy : y = 0 := by simpa using hh y
        rw [hx, hy]
      obtain ⟨f, hf⟩ := hf
      have ht : (simpleScalarNatural C c).app Z = (c i * c j) • 𝟙 Z := by
        have ht := NatTrans.IsMonoidal.tensor (τ := simpleScalarNatural C c)
          (Ground.simples C i) (Ground.simples C j)
        simpa [Z, simpleScalarNatural_app_simple, tensorHom_def, smul_smul, mul_comm] using ht
      have hn := (simpleScalarNatural C c).naturality f
      simp only [Functor.id_map] at hn
      change f ≫ (simpleScalarNatural C c).app Z =
        (simpleScalarNatural C c).app W ≫ f at hn
      rw [ht, simpleScalarNatural_app_simple] at hn
      change f ≫ ((c i * c j) • 𝟙 Z) = (c k • 𝟙 W) ≫ f at hn
      rw [Linear.comp_smul, Category.comp_id, Linear.smul_comp, Category.id_comp] at hn
      exact (smul_left_injective ℂ hf) hn.symm
  · rintro ⟨hu, hm⟩
    exact simpleScalarNatural_isMonoidal C c hu hm

end PropertyF.Ground.Dimensions
