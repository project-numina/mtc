module
public import MTC.PropertyF.Pivotal.NondegeneracyHaarSnake

open MTC.Fusion MTC.Modular MTC.CategoryTheory.Dimensions MTC.Center.Induction MTC.Center.Trace
open scoped BigOperators
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
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

end MTC.PropertyF.Pivotal
end
