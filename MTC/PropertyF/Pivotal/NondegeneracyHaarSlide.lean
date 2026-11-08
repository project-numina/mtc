module
public import MTC.PropertyF.Pivotal.NondegeneracyHaarSnake

open MTC.Fusion MTC.Modular MTC.CategoryTheory.Dimensions MTC.Center.Induction MTC.Center.Trace
open scoped BigOperators
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory CategoryTheory.Limits
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
attribute [local instance] IsFusionCategory.hom_finite
local instance (j : Fin (rank C)) : Simple ((simples C j)ᘁ) := by
  let : Simple (simples C j) := simples_simple C j
  exact simple_rightDual _

/-- The rotated fusion block: open a pivotal cup for X, apply the
projection mate, the actual boxed morphism, and the inclusion mate, and
then close the X strand. -/
def haarRotatedBlock (X Y U V : C.Obj) (β : End (X ⊗ V))
    (a : (Yᘁ) ⟶ U ⊗ (Xᘁ)) (b : U ⊗ (Xᘁ) ⟶ (Yᘁ)) : U ⊗ V ⟶ U ⊗ V :=
  𝟙 (U ⊗ V) ⊗≫
    (U ◁ ((η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv) ▷ V)) ⊗≫
    (b ▷ (X ⊗ V)) ⊗≫ ((Yᘁ) ◁ β.asHom) ⊗≫ (a ▷ (X ⊗ V)) ⊗≫
    (U ◁ (ε_ X (Xᘁ) ▷ V)) ⊗≫ 𝟙 (U ⊗ V)

/-- The rotated block is bilinear in the two actual mate morphisms. -/
def haarRotatedBilinear (X Y U V : C.Obj) (β : End (X ⊗ V)) :
    ((Yᘁ) ⟶ U ⊗ (Xᘁ)) →ₗ[ℂ] (U ⊗ (Xᘁ) ⟶ (Yᘁ)) →ₗ[ℂ] (U ⊗ V ⟶ U ⊗ V) where
  toFun a := {
    toFun := fun b => haarRotatedBlock C p X Y U V β a b
    map_add' := by intro b c; simp [haarRotatedBlock, monoidalComp]
    map_smul' := by intro r b; simp [haarRotatedBlock, monoidalComp] }
  map_add' := by intro a b; ext c; simp [haarRotatedBlock, monoidalComp]
  map_smul' := by intro r a; ext b; simp [haarRotatedBlock, monoidalComp]

/-- The actual rotated-block contraction can be evaluated in any basis of
the dual-simple Hom space. -/
theorem haarRotatedBlock_contraction (U V : C.Obj) (i j : Fin (rank C))
    {I : Type} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℂ (((simples C j)ᘁ) ⟶ U ⊗ ((simples C i)ᘁ)))
    (β : End (simples C i ⊗ V)) :
    (∑ a, haarRotatedBlock C p (simples C i) (simples C j) U V β
      (haarInclusionMate C (simples C i) (simples C j) U
        (simpleInclusion C (simples C j ⊗ U) i a))
      (simpleDimension C p j • haarProjectionMate C p (simples C i) (simples C j) U
        (pivotalTraceDualProjection C p (simples C j ⊗ U) i a))) =
    ∑ a, haarRotatedBlock C p (simples C i) (simples C j) U V β (b a)
      ((simpleHomPairingEquiv ((simples C j)ᘁ) (U ⊗ ((simples C i)ᘁ))).symm (b.dualBasis a)) := by
  classical
  exact haar_mated_contraction_basis_independent C p U i j b
    (haarRotatedBilinear C p (simples C i) (simples C j) U V β)

set_option backward.isDefEq.respectTransparency false in
/-- Closing the right X strand of the inclusion mate recovers the first
Frobenius transpose, with arbitrary Y and U. -/
theorem haar_inclusion_mate_close (X Y U : C.Obj) (f : X ⟶ Y ⊗ U) :
    𝟙 ((Yᘁ) ⊗ X) ⊗≫ ((haarInclusionMate C X Y U f) ▷ X) ⊗≫
      (U ◁ ε_ X (Xᘁ)) ⊗≫ 𝟙 U =
    𝟙 ((Yᘁ) ⊗ X) ⊗≫ ((Yᘁ) ◁ f) ⊗≫
      (ε_ Y (Yᘁ) ▷ U) ⊗≫ 𝟙 U := by
  have h := haarInclusionMate_uncurry C X Y U f
  dsimp [tensorRightHomLinearEquiv, tensorLeftHomLinearEquiv,
    tensorRightHomEquiv, tensorLeftHomEquiv] at h
  convert h using 1 <;> monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Opening the pivotal X cup before the projection mate recovers its
pivotal Frobenius transpose. -/
theorem haar_projection_mate_open (X Y U : C.Obj) (g : Y ⊗ U ⟶ X) :
    𝟙 U ⊗≫ (U ◁ (η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv)) ⊗≫
      ((haarProjectionMate C p X Y U g) ▷ X) ⊗≫ 𝟙 ((Yᘁ) ⊗ X) =
    𝟙 U ⊗≫ ((η_ (Yᘁ) ((Yᘁ)ᘁ) ≫ (Yᘁ) ◁ (p.iso Y).inv) ▷ U) ⊗≫
      ((Yᘁ) ◁ g) ⊗≫ 𝟙 ((Yᘁ) ⊗ X) := by
  let : ExactPairing (Yᘁ) Y := pivotalLeftPairing C p Y
  letI : ExactPairing (Xᘁ) X := pivotalLeftPairing C p X
  have h := haarProjectionMate_curry C p X Y U g
  dsimp [tensorRightHomLinearEquiv, tensorLeftHomLinearEquiv,
    tensorRightHomEquiv, tensorLeftHomEquiv] at h
  rw [pivotalLeftPairing_coevaluation C p X, pivotalLeftPairing_coevaluation C p Y] at h
  convert h using 1 <;> monoidal

set_option backward.isDefEq.respectTransparency false in
/-- A rotated fusion block is the original pivotal partial-trace summand. -/
theorem haarRotatedBlock_eq_partialTrace (X Y U V : C.Obj) (β : End (X ⊗ V))
    (f : X ⟶ Y ⊗ U) (g : Y ⊗ U ⟶ X) :
    haarRotatedBlock C p X Y U V β (haarInclusionMate C X Y U f)
      (haarProjectionMate C p X Y U g) =
    leftPartialTraceHom C p Y (U ⊗ V) (U ⊗ V)
      ((α_ Y U V).inv ≫ (g ▷ V) ≫ β.asHom ≫ (f ▷ V) ≫ (α_ Y U V).hom) := by
  calc
    _ = 𝟙 (U ⊗ V) ⊗≫
      ((𝟙 U ⊗≫ (U ◁ (η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv)) ⊗≫
        ((haarProjectionMate C p X Y U g) ▷ X) ⊗≫ 𝟙 ((Yᘁ) ⊗ X)) ▷ V) ⊗≫
      ((Yᘁ) ◁ β.asHom) ⊗≫
      ((𝟙 ((Yᘁ) ⊗ X) ⊗≫ ((haarInclusionMate C X Y U f) ▷ X) ⊗≫
        (U ◁ ε_ X (Xᘁ)) ⊗≫ 𝟙 U) ▷ V) ⊗≫ 𝟙 (U ⊗ V) := by
          dsimp [haarRotatedBlock]; monoidal
    _ = 𝟙 (U ⊗ V) ⊗≫
      ((𝟙 U ⊗≫ ((η_ (Yᘁ) ((Yᘁ)ᘁ) ≫ (Yᘁ) ◁ (p.iso Y).inv) ▷ U) ⊗≫
        ((Yᘁ) ◁ g) ⊗≫ 𝟙 ((Yᘁ) ⊗ X)) ▷ V) ⊗≫
      ((Yᘁ) ◁ β.asHom) ⊗≫
      ((𝟙 ((Yᘁ) ⊗ X) ⊗≫ ((Yᘁ) ◁ f) ⊗≫
        (ε_ Y (Yᘁ) ▷ U) ⊗≫ 𝟙 U) ▷ V) ⊗≫ 𝟙 (U ⊗ V) := by
          rw [haar_projection_mate_open, haar_inclusion_mate_close]
    _ = _ := by dsimp [leftPartialTraceHom]; monoidal

/-- Standard simple inclusions transported to the chosen right dual. -/
def haarDualLabelBasis (T : C.Obj) (j : Fin (rank C)) :
    Module.Basis (Fin (Module.finrank ℂ (simples C (dualIndex C j) ⟶ T))) ℂ
      (((simples C j)ᘁ) ⟶ T) :=
  (simpleInclusionBasis C T (dualIndex C j)).map
    (Linear.homCongr ℂ (rightDualLabelIso C j).symm (Iso.refl T))

/-- Standard simple projections transported from the chosen label to its actual dual. -/
def haarDualLabelProjection (T : C.Obj) (j : Fin (rank C))
    (a : Fin (Module.finrank ℂ (simples C (dualIndex C j) ⟶ T))) :
    T ⟶ ((simples C j)ᘁ) :=
  MTC.Center.Induction.simpleProjection T (dualIndex C j) a ≫ (rightDualLabelIso C j).inv

/-- Transported projections are dual to the transported inclusion basis. -/
theorem haarDualLabelProjection_dual (T : C.Obj) (j : Fin (rank C))
    (a : Fin (Module.finrank ℂ (simples C (dualIndex C j) ⟶ T))) :
    simpleHomPairingEquiv ((simples C j)ᘁ) T (haarDualLabelProjection C T j a) =
      (haarDualLabelBasis C T j).dualBasis a := by
  classical
  apply (haarDualLabelBasis C T j).ext
  intro b
  simp [haarDualLabelBasis, haarDualLabelProjection, simpleHomPairingEquiv,
    simpleHomPairing, simpleInclusionBasis_apply, Linear.homCongr_apply,
    Module.Basis.dualBasis_apply] 
  simp only [Linear.homCongr_symm_apply, Iso.symm_hom, Iso.refl_inv, Category.comp_id,
    Category.assoc, Iso.inv_hom_id_assoc, Module.Basis.repr_self, Finsupp.single_apply]
  conv_rhs => rw [← simpleInclusionBasis_apply C T (dualIndex C j) b, Module.Basis.repr_self]
  simp only [Finsupp.single_apply]
  by_cases hab : b = a
  · subst b
    simp [← Category.assoc, simpleInclusion_projection]
    rfl
  · have hz : simpleInclusion C T (dualIndex C j) b ≫
        simpleProjection T (dualIndex C j) a = 0 := by
      simp [simpleInclusion, simpleProjection, Category.assoc, hab]
    simp [← Category.assoc, hz, hab, eq_comm]

/-- Reindex a mated contraction using the standard basis at the dual label. -/
theorem haarRotatedBlock_dualLabel_contraction (U V : C.Obj) (i j : Fin (rank C))
    (β : End (simples C i ⊗ V)) :
    (∑ a, haarRotatedBlock C p (simples C i) (simples C j) U V β
      (haarInclusionMate C (simples C i) (simples C j) U
        (simpleInclusion C (simples C j ⊗ U) i a))
      (simpleDimension C p j • haarProjectionMate C p (simples C i) (simples C j) U
        (pivotalTraceDualProjection C p (simples C j ⊗ U) i a))) =
    ∑ a, haarRotatedBlock C p (simples C i) (simples C j) U V β
      (haarDualLabelBasis C (U ⊗ ((simples C i)ᘁ)) j a)
      (haarDualLabelProjection C (U ⊗ ((simples C i)ᘁ)) j a) := by
  classical
  have h := haarRotatedBlock_contraction C p U V i j
    (haarDualLabelBasis C (U ⊗ ((simples C i)ᘁ)) j) β
  simp_rw [← haarDualLabelProjection_dual] at h
  simpa using h

/-- The dual-label bases and projections still resolve the identity. -/
theorem haarDualLabel_complete (T : C.Obj) :
    (∑ j : Fin (rank C), ∑ a : Fin (Module.finrank ℂ (simples C (dualIndex C j) ⟶ T)),
      haarDualLabelProjection C T j a ≫ haarDualLabelBasis C T j a) = 𝟙 T := by
  classical
  have h : (∑ j : Fin (rank C), ∑ a : Fin (Module.finrank ℂ (simples C j ⟶ T)),
      simpleProjection T j a ≫ simpleInclusion C T j a) = 𝟙 T := by
    simpa only [simplePieces, Fintype.sum_sigma] using (simple_completeness C T)
  rw [← (dualEquiv C).sum_comp] at h <;> try simp
  change (∑ j : Fin (rank C), ∑ a : Fin (Module.finrank ℂ (simples C (dualIndex C j) ⟶ T)),
    simpleProjection T (dualIndex C j) a ≫ simpleInclusion C T (dualIndex C j) a) = 𝟙 T at h
  simpa [haarDualLabelProjection, haarDualLabelBasis,
    Linear.homCongr_apply, simpleInclusionBasis_apply, Category.assoc] using h

/-- A rotated block after composing its two fusion maps. -/
def haarRotatedCore (X U V : C.Obj) (β : End (X ⊗ V))
    (h : U ⊗ (Xᘁ) ⟶ U ⊗ (Xᘁ)) : U ⊗ V ⟶ U ⊗ V :=
  𝟙 (U ⊗ V) ⊗≫
    (U ◁ ((η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv) ▷ V)) ⊗≫
    (h ▷ (X ⊗ V)) ⊗≫ (((U ⊗ (Xᘁ)) ◁ β.asHom)) ⊗≫
    (U ◁ (ε_ X (Xᘁ) ▷ V)) ⊗≫ 𝟙 (U ⊗ V)

set_option backward.isDefEq.respectTransparency false in
/-- Exchange the boxed morphism with the inclusion to compose a rotated pair. -/
theorem haarRotatedBlock_comp (X Y U V : C.Obj) (β : End (X ⊗ V))
    (a : (Yᘁ) ⟶ U ⊗ (Xᘁ)) (b : U ⊗ (Xᘁ) ⟶ (Yᘁ)) :
    haarRotatedBlock C p X Y U V β a b = haarRotatedCore C p X U V β (b ≫ a) := by
  calc
    _ = 𝟙 (U ⊗ V) ⊗≫
      (U ◁ ((η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv) ▷ V)) ⊗≫
      ((b ▷ (X ⊗ V)) ≫ ((Yᘁ) ◁ β.asHom) ≫ (a ▷ (X ⊗ V))) ⊗≫
      (U ◁ (ε_ X (Xᘁ) ▷ V)) ⊗≫ 𝟙 (U ⊗ V) := by dsimp [haarRotatedBlock]; monoidal
    _ = 𝟙 (U ⊗ V) ⊗≫
      (U ◁ ((η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv) ▷ V)) ⊗≫
      ((b ▷ (X ⊗ V)) ≫ (a ▷ (X ⊗ V)) ≫ ((U ⊗ (Xᘁ)) ◁ β.asHom)) ⊗≫
      (U ◁ (ε_ X (Xᘁ) ▷ V)) ⊗≫ 𝟙 (U ⊗ V) := by
        rw [whisker_exchange]
    _ = _ := by dsimp [haarRotatedCore]; rw [comp_whiskerRight]; monoidal

/-- The core depends linearly on the inserted endomorphism. -/
def haarRotatedCoreLinear (X U V : C.Obj) (β : End (X ⊗ V)) :
    (U ⊗ (Xᘁ) ⟶ U ⊗ (Xᘁ)) →ₗ[ℂ] (U ⊗ V ⟶ U ⊗ V) where
  toFun := haarRotatedCore C p X U V β
  map_add' := by intro a b; simp [haarRotatedCore, monoidalComp]
  map_smul' := by intro c a; simp [haarRotatedCore, monoidalComp]

set_option backward.isDefEq.respectTransparency false in
/-- The identity insertion leaves the ordinary pivotal loop on the V strand. -/
theorem haarRotatedCore_id (X U V : C.Obj) (β : End (X ⊗ V)) :
    haarRotatedCore C p X U V β (𝟙 (U ⊗ (Xᘁ))) =
      U ◁ leftPartialTraceHom C p X V V β.asHom := by
  dsimp [haarRotatedCore, leftPartialTraceHom]
  monoidal

/-- Summing the dual-label rotated blocks collapses to the vacuum loop. -/
theorem haarRotatedBlock_dualLabel_sum (X U V : C.Obj) (β : End (X ⊗ V)) :
    (∑ j : Fin (rank C), ∑ a : Fin (Module.finrank ℂ
      (simples C (dualIndex C j) ⟶ U ⊗ (Xᘁ))),
      haarRotatedBlock C p X (simples C j) U V β
        (haarDualLabelBasis C (U ⊗ (Xᘁ)) j a)
        (haarDualLabelProjection C (U ⊗ (Xᘁ)) j a)) =
      U ◁ leftPartialTraceHom C p X V V β.asHom := by
  classical
  simp_rw [haarRotatedBlock_comp]
  change (∑ j : Fin (rank C), ∑ a : Fin (Module.finrank ℂ
      (simples C (dualIndex C j) ⟶ U ⊗ (Xᘁ))),
      haarRotatedCoreLinear C p X U V β
        (haarDualLabelProjection C (U ⊗ (Xᘁ)) j a ≫ haarDualLabelBasis C (U ⊗ (Xᘁ)) j a)) = _
  simp only [← map_sum, haarDualLabel_complete]
  exact haarRotatedCore_id C p X U V β

/-- Restricted dual-label completeness when the object has no simple
summands outside the chosen labels. -/
theorem haarDualLabel_complete_restricted (T : C.Obj) (S : Finset (Fin (rank C)))
    (hs : ∀ j, j ∉ S → Module.finrank ℂ (simples C (dualIndex C j) ⟶ T) = 0) :
    (∑ j ∈ S, ∑ a : Fin (Module.finrank ℂ (simples C (dualIndex C j) ⟶ T)),
      haarDualLabelProjection C T j a ≫ haarDualLabelBasis C T j a) = 𝟙 T := by
  classical
  have he : (∑ j ∈ S, ∑ a : Fin (Module.finrank ℂ (simples C (dualIndex C j) ⟶ T)),
      haarDualLabelProjection C T j a ≫ haarDualLabelBasis C T j a) =
      ∑ j : Fin (rank C), ∑ a : Fin (Module.finrank ℂ (simples C (dualIndex C j) ⟶ T)),
        haarDualLabelProjection C T j a ≫ haarDualLabelBasis C T j a := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro j hj hn
    letI : IsEmpty (Fin (Module.finrank ℂ (simples C (dualIndex C j) ⟶ T))) := by
      rw [hs j hn]
      infer_instance
    simp
  rw [he, haarDualLabel_complete]

/-- A restricted sum collapses when the tensor target has no summands
outside the chosen dual labels. -/
theorem haarRotatedBlock_dualLabel_sum_restricted (X U V : C.Obj) (β : End (X ⊗ V))
    (S : Finset (Fin (rank C)))
    (hs : ∀ j, j ∉ S → Module.finrank ℂ
      (simples C (dualIndex C j) ⟶ U ⊗ (Xᘁ)) = 0) :
    (∑ j ∈ S, ∑ a : Fin (Module.finrank ℂ
      (simples C (dualIndex C j) ⟶ U ⊗ (Xᘁ))),
      haarRotatedBlock C p X (simples C j) U V β
        (haarDualLabelBasis C (U ⊗ (Xᘁ)) j a)
        (haarDualLabelProjection C (U ⊗ (Xᘁ)) j a)) =
      U ◁ leftPartialTraceHom C p X V V β.asHom := by
  classical
  simp_rw [haarRotatedBlock_comp]
  change (∑ j ∈ S, ∑ a : Fin (Module.finrank ℂ
      (simples C (dualIndex C j) ⟶ U ⊗ (Xᘁ))),
      haarRotatedCoreLinear C p X U V β
        (haarDualLabelProjection C (U ⊗ (Xᘁ)) j a ≫ haarDualLabelBasis C (U ⊗ (Xᘁ)) j a)) = _
  simp only [← map_sum, haarDualLabel_complete_restricted C _ S hs]
  exact haarRotatedCore_id C p X U V β

/-- Dimension-weighted original fusion summands are the normalized mated
contraction, with the dimension of the output simple moved outside. -/
theorem haar_weighted_fusion_block (U V : C.Obj) (i j : Fin (rank C))
    (β : End (simples C i ⊗ V)) :
    (∑ a : Fin (Module.finrank ℂ (simples C i ⟶ simples C j ⊗ U)),
      simpleDimension C p j • leftPartialTraceHom C p (simples C j) (U ⊗ V) (U ⊗ V)
        ((α_ (simples C j) U V).inv ≫
          (simpleProjection (simples C j ⊗ U) i a ▷ V) ≫ β.asHom ≫
          (simpleInclusion C (simples C j ⊗ U) i a ▷ V) ≫
          (α_ (simples C j) U V).hom)) =
    simpleDimension C p i • ∑ a, haarRotatedBlock C p (simples C i) (simples C j) U V β
      (haarInclusionMate C (simples C i) (simples C j) U
        (simpleInclusion C (simples C j ⊗ U) i a))
      (simpleDimension C p j • haarProjectionMate C p (simples C i) (simples C j) U
        (pivotalTraceDualProjection C p (simples C j ⊗ U) i a)) := by
  classical
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← haarRotatedBlock_eq_partialTrace]
  change simpleDimension C p j • (haarRotatedBilinear C p (simples C i) (simples C j) U V β)
      _ ((haarProjectionMate C p (simples C i) (simples C j) U)
        (simpleProjection (simples C j ⊗ U) i a)) =
    simpleDimension C p i • (haarRotatedBilinear C p (simples C i) (simples C j) U V β)
      _ (simpleDimension C p j • (haarProjectionMate C p (simples C i) (simples C j) U)
        (pivotalTraceDualProjection C p (simples C j ⊗ U) i a))
  simp only [pivotalTraceDualProjection, map_smul, smul_smul]
  congr 1
  field_simp [simpleDimension_ne_zero C p i]

/-- The pivotal Haar loop restricted to a finite collection of simple labels. -/
def categoricalHaarRestricted (S : Finset (Fin (rank C))) (U V : C.Obj)
    (β : ∀ X : C.Obj, End (X ⊗ V)) : U ⊗ V ⟶ U ⊗ V :=
  ∑ j ∈ S, simpleDimension C p j • leftPartialTraceHom C p (simples C j) (U ⊗ V) (U ⊗ V)
    ((α_ (simples C j) U V).inv ≫ (β (simples C j ⊗ U)).asHom ≫ (α_ (simples C j) U V).hom)

/-- Fusion expansion of a single actual pivotal loop summand. -/
theorem haarSummand_fusion_expansion (U V : C.Obj) (j : Fin (rank C))
    (β : ∀ X : C.Obj, End (X ⊗ V))
    (hβ : ∀ {X Y : C.Obj} (f : X ⟶ Y),
      (f ▷ V) ≫ (β Y).asHom = (β X).asHom ≫ (f ▷ V)) :
    simpleDimension C p j • leftPartialTraceHom C p (simples C j) (U ⊗ V) (U ⊗ V)
      ((α_ (simples C j) U V).inv ≫ (β (simples C j ⊗ U)).asHom ≫ (α_ (simples C j) U V).hom) =
    ∑ i : Fin (rank C), ∑ a : Fin (Module.finrank ℂ (simples C i ⟶ simples C j ⊗ U)),
      simpleDimension C p j • leftPartialTraceHom C p (simples C j) (U ⊗ V) (U ⊗ V)
        ((α_ (simples C j) U V).inv ≫ (simpleProjection (simples C j ⊗ U) i a ▷ V) ≫
          (β (simples C i)).asHom ≫ (simpleInclusion C (simples C j ⊗ U) i a ▷ V) ≫
          (α_ (simples C j) U V).hom) := by
  classical
  rw [natural_tensor_family_simple_expansion C V (simples C j ⊗ U) β hβ]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp]
  let F (q : simplePieces C (simples C j ⊗ U)) :
      (simples C j ⊗ (U ⊗ V)) ⟶ (simples C j ⊗ (U ⊗ V)) :=
    (α_ (simples C j) U V).inv ≫
      ((simpleProjection (simples C j ⊗ U) q.1 q.2 ▷ V) ≫
        (β (simples C q.1)).asHom ≫
          (simpleInclusion C (simples C j ⊗ U) q.1 q.2 ▷ V)) ≫
        (α_ (simples C j) U V).hom
  have he : End.of (∑ q, F q) = ∑ q, End.of (F q) := by
    apply End.ext
    simp
  change simpleDimension C p j • (leftPartialTrace p (End.of (∑ q, F q))).asHom = _
  rw [he, leftPartialTrace_sum]
  simp only [End.sum_asHom, Finset.smul_sum, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  simp only [F, Category.assoc]
  rfl

/-- Relative pivotal Haar sliding, under the two concrete fusion-support
conditions for the chosen label set and free strand. -/
theorem categoricalHaarRestricted_slide (S : Finset (Fin (rank C))) (U V : C.Obj)
    (β : ∀ X : C.Obj, End (X ⊗ V))
    (hβ : ∀ {X Y : C.Obj} (f : X ⟶ Y),
      (f ▷ V) ≫ (β Y).asHom = (β X).asHom ≫ (f ▷ V))
    (hforward : ∀ j ∈ S, ∀ i ∉ S,
      Module.finrank ℂ (simples C i ⟶ simples C j ⊗ U) = 0)
    (hdual : ∀ i ∈ S, ∀ j ∉ S,
      Module.finrank ℂ (simples C (dualIndex C j) ⟶ U ⊗ ((simples C i)ᘁ)) = 0) :
    categoricalHaarRestricted C p S U V β =
      U ◁ (∑ i ∈ S, simpleDimension C p i •
        leftPartialTraceHom C p (simples C i) V V (β (simples C i)).asHom) := by
  classical
  let T (j i : Fin (rank C)) : U ⊗ V ⟶ U ⊗ V :=
    ∑ a : Fin (Module.finrank ℂ (simples C i ⟶ simples C j ⊗ U)),
      simpleDimension C p j • leftPartialTraceHom C p (simples C j) (U ⊗ V) (U ⊗ V)
        ((α_ (simples C j) U V).inv ≫ (simpleProjection (simples C j ⊗ U) i a ▷ V) ≫
          (β (simples C i)).asHom ≫ (simpleInclusion C (simples C j ⊗ U) i a ▷ V) ≫
          (α_ (simples C j) U V).hom)
  have hr (j : Fin (rank C)) (hj : j ∈ S) : (∑ i : Fin (rank C), T j i) = ∑ i ∈ S, T j i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    letI : IsEmpty (Fin (Module.finrank ℂ (simples C i ⟶ simples C j ⊗ U))) := by
      rw [hforward j hj i hi]
      infer_instance
    simp [T]
  unfold categoricalHaarRestricted
  simp_rw [haarSummand_fusion_expansion C p U V _ β hβ]
  change (∑ j ∈ S, ∑ i : Fin (rank C), T j i) = _
  have he : (∑ j ∈ S, ∑ i : Fin (rank C), T j i) = ∑ j ∈ S, ∑ i ∈ S, T j i := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hr j hj
  rw [he, Finset.sum_comm]
  simp only [T]
  simp_rw [haar_weighted_fusion_block]
  simp_rw [haarRotatedBlock_dualLabel_contraction]
  simp only [whiskerLeft_sum, MonoidalLinear.whiskerLeft_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.smul_sum]
  rw [haarRotatedBlock_dualLabel_sum_restricted C p _ U V _ S (hdual i hi)]

theorem leftTrace_monodromy_of_dual_sTest (k i : Fin (rank C))
    (hs : categoricalS C p (dualIndex C i) k =
      simpleDimension C p (dualIndex C i) * simpleDimension C p k) :
    unitScalar C (p.leftTrace (doubleBraiding (simples C i) (simples C k))) =
      star (simpleDimension C p i) * star (simpleDimension C p k) := by
  rw [leftTrace_doubleBraiding_eq_dual]
  have htest := hs
  have hki := MTC.Center.Induction.pivotalDimension_simple_dual_conj p i
  have hkk := MTC.Center.Induction.pivotalDimension_simple_dual_conj p k
  have hi := pivotalDimension_iso p (rightDualLabelIso C i)
  have hk := pivotalDimension_iso p (rightDualLabelIso C k)
  have hidim : simpleDimension C p (dualIndex C i) = star (simpleDimension C p i) := by
    simpa only [simpleDimension] using hi.symm.trans hki
  have hkdim : simpleDimension C p (dualIndex C k) = star (simpleDimension C p k) := by
    simpa only [simpleDimension] using hk.symm.trans hkk
  -- The normalized S character of a dual label is conjugated.
  have hdualtest : categoricalS C p (dualIndex C i) (dualIndex C k) =
      simpleDimension C p (dualIndex C i) * simpleDimension C p (dualIndex C k) := by
    have hh' := categoricalS_star_eq_dual_phase C p (dualIndex C i) k
    have hd : simpleDimension C p (dualIndex C i) ≠ 0 := simpleDimension_ne_zero C p _
    have hdstar : starRingEnd ℂ (simpleDimension C p (dualIndex C i)) ≠ 0 :=
      (map_ne_zero (starRingEnd ℂ)).2 hd
    rw [htest, map_mul] at hh'
    field_simp at hh'
    rw [hkdim]
    exact hh'.symm.trans (mul_comm _ _)
  have he : unitScalar C (p.rightTrace (doubleBraiding ((simples C k)ᘁ) ((simples C i)ᘁ))) =
      categoricalS C p (dualIndex C i) (dualIndex C k) := by
    rw [categoricalS_symmetric C p, categoricalS, ← unitScalar_eq_equiv]
    change unitScalar C (SEntry p ((simples C k)ᘁ) ((simples C i)ᘁ)) = _
    rw [SEntry_iso_left p (rightDualLabelIso C k), SEntry_iso_right p _ (rightDualLabelIso C i)]
  rw [he, hdualtest, hidim, hkdim]

/-- Under the numerical S-test, every closed monodromy loop is the
conjugate pivotal dimension times the identity of the surviving simple. -/
theorem leftPartialTrace_monodromy_of_dual_sTest (k i : Fin (rank C))
    (hs : categoricalS C p (dualIndex C i) k =
      simpleDimension C p (dualIndex C i) * simpleDimension C p k) :
    leftPartialTrace p (End.of (doubleBraiding (simples C i) (simples C k))) =
      star (simpleDimension C p i) • (1 : End (simples C k)) := by
  let : Simple (simples C k) := simples_simple C k
  let : FiniteDimensional ℂ (simples C k ⟶ simples C k) := IsFusionCategory.hom_finite _ _
  let a := leftPartialTrace p (End.of (doubleBraiding (simples C i) (simples C k)))
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ a.asHom
  have ha : a = c • (1 : End (simples C k)) := End.ext hc.symm
  have ht := congrArg (unitScalar C) (leftTrace_partialTrace p
    (End.of (doubleBraiding (simples C i) (simples C k))))
  change unitScalar C (p.leftTrace a.asHom) = _ at ht
  rw [ha] at ht
  simp only [End.smul_asHom, End.one_asHom, PivotalStructure.leftTrace_smul,
    unitScalar_eq_equiv, map_smul, smul_eq_mul] at ht
  have hd : unitScalarEquiv C (p.leftTrace (𝟙 (simples C k))) =
      star (simpleDimension C p k) := by
    have hh := congrArg (unitScalar C) (leftTrace_eq_rightTrace_dual C p (simples C k) 1)
    simp only [End.one_asHom, rightAdjointMate_id] at hh
    change unitScalar C (p.leftTrace (𝟙 (simples C k))) =
      pivotalDimension C p ((simples C k)ᘁ) at hh
    simpa only [unitScalar_eq_equiv] using
      hh.trans (pivotalDimension_dual_conj C p (simples C k))
  rw [hd, ← unitScalar_eq_equiv, leftTrace_monodromy_of_dual_sTest C p k i hs] at ht
  have hn : star (simpleDimension C p k) ≠ 0 := by
    simpa using ((map_ne_zero (starRingEnd ℂ)).2 (simpleDimension_ne_zero C p k))
  have hc' : c = star (simpleDimension C p i) := mul_right_cancel₀ hn ht
  simpa [hc'] using ha

/-- The positive intrinsic dimension of a nonempty family of simples. -/
def restrictedGlobalDimension (S : Finset (Fin (rank C))) : ℂ :=
  ∑ i ∈ S, simpleDimension C p i * star (simpleDimension C p i)

theorem restrictedGlobalDimension_ne_zero (S : Finset (Fin (rank C))) (hS : S.Nonempty) :
    restrictedGlobalDimension C p S ≠ 0 := by
  classical
  have hp : (0 : ℝ) < ∑ i ∈ S, ‖simpleDimension C p i‖ ^ 2 := by
    apply Finset.sum_pos _ hS
    intro i hi
    exact sq_pos_of_pos (norm_pos_iff.mpr (simpleDimension_ne_zero C p i))
  have he : restrictedGlobalDimension C p S =
      ((∑ i ∈ S, ‖simpleDimension C p i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [restrictedGlobalDimension, Complex.ofReal_sum, Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro i hi
    exact Complex.mul_conj' _
  rw [he, Complex.ofReal_ne_zero]
  exact ne_of_gt hp

/-- The restricted Haar loop factors through the braiding and its vacuum. -/
theorem categoricalHaarRestricted_monodromy_factor (S : Finset (Fin (rank C)))
    (U V : C.Obj) :
    categoricalHaarRestricted C p S U V (fun X ↦ End.of (doubleBraiding X V)) =
      (β_ U V).hom ≫
        ((∑ i ∈ S, simpleDimension C p i •
          leftPartialTraceHom C p (simples C i) V V (doubleBraiding (simples C i) V)) ▷ U) ≫
        (β_ V U).hom := by
  classical
  simp only [categoricalHaarRestricted, sum_whiskerRight, MonoidalLinear.smul_whiskerRight,
    Preadditive.sum_comp, Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact monodromyHaar_summand_factor C p (simples C i) U V

/-- The restricted vacuum loop is the restricted global dimension when the
S-test holds against the dual of every chosen label. -/
theorem restrictedVacuum_of_dual_sTest (S : Finset (Fin (rank C))) (k : Fin (rank C))
    (hs : ∀ i ∈ S, categoricalS C p (dualIndex C i) k =
      simpleDimension C p (dualIndex C i) * simpleDimension C p k) :
    (∑ i ∈ S, simpleDimension C p i •
      leftPartialTraceHom C p (simples C i) (simples C k) (simples C k)
        (doubleBraiding (simples C i) (simples C k))) =
      restrictedGlobalDimension C p S • 𝟙 (simples C k) := by
  classical
  calc
    _ = ∑ i ∈ S, (simpleDimension C p i * star (simpleDimension C p i)) • 𝟙 (simples C k) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := leftPartialTrace_monodromy_of_dual_sTest C p k i (hs i hi)
      have hh := congrArg End.asHom h
      change leftPartialTraceHom C p (simples C i) (simples C k) (simples C k)
        (doubleBraiding (simples C i) (simples C k)) =
          star (simpleDimension C p i) • 𝟙 (simples C k) at hh
      rw [hh]
      simp [smul_smul]
    _ = _ := by simp [restrictedGlobalDimension, Finset.sum_smul]

/-- Relative numerical centrality forces actual monodromy to be the identity,
provided the free strand satisfies the concrete fusion-support conditions. -/
theorem doubleBraiding_eq_id_of_restricted_sTest (S : Finset (Fin (rank C)))
    (hS : S.Nonempty) (U : C.Obj) (k : Fin (rank C))
    (hs : ∀ i ∈ S, categoricalS C p (dualIndex C i) k =
      simpleDimension C p (dualIndex C i) * simpleDimension C p k)
    (hforward : ∀ j ∈ S, ∀ i ∉ S,
      Module.finrank ℂ (simples C i ⟶ simples C j ⊗ U) = 0)
    (hdual : ∀ i ∈ S, ∀ j ∉ S,
      Module.finrank ℂ (simples C (dualIndex C j) ⟶ U ⊗ ((simples C i)ᘁ)) = 0) :
    doubleBraiding U (simples C k) = 𝟙 (U ⊗ simples C k) := by
  classical
  have hslide := categoricalHaarRestricted_slide C p S U (simples C k)
    (fun X ↦ End.of (doubleBraiding X (simples C k)))
    (fun f ↦ (doubleBraiding_natural_left f (simples C k)).symm) hforward hdual
  rw [categoricalHaarRestricted_monodromy_factor C p S U (simples C k),
    restrictedVacuum_of_dual_sTest C p S k hs] at hslide
  have hd := restrictedGlobalDimension_ne_zero C p S hS
  apply (smul_right_injective _ hd)
  simpa [doubleBraiding, MonoidalLinear.smul_whiskerRight, MonoidalLinear.whiskerLeft_smul,
    Linear.comp_smul, Linear.smul_comp] using hslide

end MTC.PropertyF.Pivotal
end
