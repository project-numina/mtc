module
public import MTC.PropertyF.Pivotal.NondegeneracyHaarMate
public import MTC.Center.Normalization.DualContraction

open MTC.Fusion MTC.Modular MTC.CategoryTheory.Dimensions MTC.Center.Induction MTC.Center.Trace
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion Frobenius mate is the standard cup, fusion morphism,
and cap diagram, with all coherence maps supplied canonically. -/
theorem haarInclusionMate_diagram (X Y U : C.Obj) (f : X ⟶ Y ⊗ U) :
    haarInclusionMate C X Y U f =
      𝟙 (Yᘁ : C.Obj) ⊗≫ ((Yᘁ) ◁ η_ X (Xᘁ)) ⊗≫
        ((Yᘁ) ◁ (f ▷ (Xᘁ))) ⊗≫ (ε_ Y (Yᘁ) ▷ (U ⊗ (Xᘁ))) ⊗≫ 𝟙 _ := by
  dsimp [haarInclusionMate, tensorLeftHomLinearEquiv, tensorRightHomLinearEquiv,
    tensorLeftHomEquiv, tensorRightHomEquiv]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The projection Frobenius mate is the analogous diagram with the actual
pivotal left-dual cup and cap. -/
theorem haarProjectionMate_diagram (X Y U : C.Obj) (g : Y ⊗ U ⟶ X) :
    haarProjectionMate C p X Y U g =
      𝟙 (U ⊗ (Xᘁ)) ⊗≫
        ((η_ (Yᘁ) ((Yᘁ)ᘁ) ≫ (Yᘁ) ◁ (p.iso Y).inv) ▷ (U ⊗ (Xᘁ))) ⊗≫
        ((Yᘁ) ◁ (g ▷ (Xᘁ))) ⊗≫
        ((Yᘁ) ◁ ((p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ))) ⊗≫ 𝟙 _ := by
  dsimp [haarProjectionMate, tensorLeftHomLinearEquiv, tensorRightHomLinearEquiv,
    tensorLeftHomEquiv, tensorRightHomEquiv]
  rw [pivotalLeftPairing_coevaluation C p Y, pivotalLeftPairing_evaluation C p X]
  monoidal

/-- Uncurry the inclusion mate to recover its first Frobenius transpose.
This is the first exact-pairing snake before expanding any coherence maps. -/
theorem haarInclusionMate_uncurry (X Y U : C.Obj) (f : X ⟶ Y ⊗ U) :
    (tensorRightHomLinearEquiv (k := ℂ) (Yᘁ) X (Xᘁ) U).symm
      (haarInclusionMate C X Y U f) =
        (tensorLeftHomLinearEquiv (k := ℂ) X Y (Yᘁ) U).symm f := by
  simp [haarInclusionMate]

/-- Curry the projection mate to recover the pivotal left-dual transpose.
This is the second exact-pairing snake in the mate construction. -/
theorem haarProjectionMate_curry (X Y U : C.Obj) (g : Y ⊗ U ⟶ X) :
    let : ExactPairing (Yᘁ) Y := pivotalLeftPairing C p Y
    letI : ExactPairing (Xᘁ) X := pivotalLeftPairing C p X
    tensorRightHomLinearEquiv (k := ℂ) U (Xᘁ) X (Yᘁ)
      (haarProjectionMate C p X Y U g) =
        tensorLeftHomLinearEquiv (k := ℂ) U (Yᘁ) Y X g := by
  simp [haarProjectionMate]

set_option backward.isDefEq.respectTransparency false in
/-- A fusion morphism passes through a coevaluation/evaluation pair; this is
the first boxed snake needed to regroup the Haar trace diagram. -/
theorem haar_yank_inclusion (X Y U : C.Obj) (f : X ⟶ Y ⊗ U) :
    𝟙 X ⊗≫ (η_ Y (Yᘁ) ▷ X) ⊗≫
      (Y ◁ (𝟙 ((Yᘁ) ⊗ X) ⊗≫ ((Yᘁ) ◁ f) ⊗≫
        (ε_ Y (Yᘁ) ▷ U) ⊗≫ 𝟙 U)) ⊗≫ 𝟙 (Y ⊗ U) = f := by
  have h := (tensorLeftHomEquiv X Y (Yᘁ) U).apply_symm_apply f
  dsimp [tensorLeftHomEquiv] at h
  convert h using 1; monoidal

set_option backward.isDefEq.respectTransparency false in
/-- A projection passes through the transported pivotal cup and cap; this is
the second boxed snake needed for the Haar trace contraction. -/
theorem haar_yank_projection (X Y U : C.Obj) (g : Y ⊗ U ⟶ X) :
    𝟙 (Y ⊗ U) ⊗≫
      (Y ◁ (𝟙 U ⊗≫
        ((η_ (Yᘁ) ((Yᘁ)ᘁ) ≫ (Yᘁ) ◁ (p.iso Y).inv) ▷ U) ⊗≫
        ((Yᘁ) ◁ g) ⊗≫ 𝟙 ((Yᘁ) ⊗ X))) ⊗≫
      (((p.iso Y).hom ▷ (Yᘁ) ≫ ε_ (Yᘁ) ((Yᘁ)ᘁ)) ▷ X) ⊗≫ 𝟙 X = g := by
  let : ExactPairing (Yᘁ) Y := pivotalLeftPairing C p Y
  have h := (tensorLeftHomEquiv U (Yᘁ) Y X).symm_apply_apply g
  dsimp [tensorLeftHomEquiv] at h
  rw [pivotalLeftPairing_coevaluation C p Y, pivotalLeftPairing_evaluation C p Y] at h
  convert h using 1; monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Two independent duality cups exchange without changing their pairing.
This is the first interchange used to bring the two Haar snakes together. -/
theorem haar_coevaluation_exchange (X Y : C.Obj) :
    η_ X (Xᘁ) ⊗≫ (η_ Y (Yᘁ) ▷ (X ⊗ (Xᘁ))) =
      η_ Y (Yᘁ) ⊗≫ ((Y ⊗ (Yᘁ)) ◁ η_ X (Xᘁ)) := by
  calc
    _ = 𝟙 (𝟙_ C.Obj) ⊗≫
        ((𝟙_ C.Obj ◁ η_ X (Xᘁ)) ≫ (η_ Y (Yᘁ) ▷ (X ⊗ (Xᘁ)))) ⊗≫ 𝟙 _ := by
          monoidal
    _ = 𝟙 (𝟙_ C.Obj) ⊗≫
        ((η_ Y (Yᘁ) ▷ (𝟙_ C.Obj)) ≫ ((Y ⊗ (Yᘁ)) ◁ η_ X (Xᘁ))) ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange]
    _ = _ := by monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Move the outer pivotal component across the second cup and an arbitrary
inner box in a closed two-strand diagram. -/
theorem haar_pivotal_closed_slide (X Y : C.Obj)
    (a : (Yᘁ) ⊗ (X ⊗ (Xᘁ)) ⟶ (Yᘁ) ⊗ (X ⊗ (Xᘁ))) :
    η_ Y (Yᘁ) ⊗≫ ((p.iso Y).hom ▷ (Yᘁ)) ⊗≫
      ((((Yᘁ)ᘁ) ⊗ (Yᘁ)) ◁ η_ X (Xᘁ)) ⊗≫ (((Yᘁ)ᘁ) ◁ a) ⊗≫
      (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (X ⊗ (Xᘁ))) ⊗≫
      ((p.iso X).hom ▷ (Xᘁ)) ⊗≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
    η_ Y (Yᘁ) ⊗≫ ((Y ⊗ (Yᘁ)) ◁ η_ X (Xᘁ)) ⊗≫ (Y ◁ a) ⊗≫
      (((p.iso Y).hom ▷ (Yᘁ)) ▷ (X ⊗ (Xᘁ))) ⊗≫
      (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (X ⊗ (Xᘁ))) ⊗≫
      ((p.iso X).hom ▷ (Xᘁ)) ⊗≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := by
  monoidal
  simp
  have hc : (p.iso Y).hom ▷ (Yᘁ) ≫ (ρ_ (((Yᘁ)ᘁ) ⊗ (Yᘁ))).inv ≫
      (α_ ((Yᘁ)ᘁ) (Yᘁ) (𝟙_ C.Obj)).hom ≫ (((Yᘁ)ᘁ) ◁ (Yᘁ) ◁ η_ X (Xᘁ)) =
      (ρ_ (Y ⊗ (Yᘁ))).inv ≫ (α_ Y (Yᘁ) (𝟙_ C.Obj)).hom ≫
        (Y ◁ (Yᘁ) ◁ η_ X (Xᘁ)) ≫
          ((p.iso Y).hom ▷ ((Yᘁ) ⊗ (X ⊗ (Xᘁ)))) := by
    rw [rightUnitor_inv_naturality_assoc, associator_naturality_left_assoc,
      ← whisker_exchange]
  slice_lhs 1 4 => rw [hc]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    associator_inv_naturality_left_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem haar_pivotal_cap_exchange (X Y : C.Obj) :
    ((((Yᘁ : C.Obj)ᘁ) ⊗ (Yᘁ : C.Obj)) ◁ ((p.iso X).hom ▷ (Xᘁ : C.Obj) ≫ ε_ (Xᘁ : C.Obj) ((Xᘁ : C.Obj)ᘁ))) ⊗≫
      ε_ (Yᘁ : C.Obj) ((Yᘁ : C.Obj)ᘁ) =
    (ε_ (Yᘁ : C.Obj) ((Yᘁ : C.Obj)ᘁ) ▷ (X ⊗ (Xᘁ : C.Obj))) ⊗≫
      ((p.iso X).hom ▷ (Xᘁ : C.Obj)) ⊗≫ ε_ (Xᘁ : C.Obj) ((Xᘁ : C.Obj)ᘁ) := by
  calc
    _ = 𝟙 ((((Yᘁ : C.Obj)ᘁ) ⊗ (Yᘁ : C.Obj)) ⊗ (X ⊗ (Xᘁ : C.Obj))) ⊗≫ (((((Yᘁ : C.Obj)ᘁ) ⊗ (Yᘁ : C.Obj)) ◁
        ((p.iso X).hom ▷ (Xᘁ : C.Obj) ≫ ε_ (Xᘁ : C.Obj) ((Xᘁ : C.Obj)ᘁ))) ≫
        (ε_ (Yᘁ : C.Obj) ((Yᘁ : C.Obj)ᘁ) ▷ (𝟙_ C.Obj))) ⊗≫ 𝟙 (𝟙_ C.Obj) := by monoidal
    _ = 𝟙 ((((Yᘁ : C.Obj)ᘁ) ⊗ (Yᘁ : C.Obj)) ⊗ (X ⊗ (Xᘁ : C.Obj))) ⊗≫ ((ε_ (Yᘁ : C.Obj) ((Yᘁ : C.Obj)ᘁ) ▷ (X ⊗ (Xᘁ : C.Obj))) ≫
        ((𝟙_ C.Obj) ◁ ((p.iso X).hom ▷ (Xᘁ : C.Obj) ≫ ε_ (Xᘁ : C.Obj) ((Xᘁ : C.Obj)ᘁ)))) ⊗≫ 𝟙 (𝟙_ C.Obj) := by
          rw [whisker_exchange]
    _ = _ := by monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Rotate the composite of the actual two Frobenius mates into a boxed
fusion endomorphism surrounded by two pivotal cups and caps. -/
theorem haar_mate_trace_boxed (X Y U : C.Obj) (f : X ⟶ Y ⊗ U) (g : Y ⊗ U ⟶ X) :
    let a : (Yᘁ) ⊗ (X ⊗ (Xᘁ)) ⟶ (Yᘁ) ⊗ (X ⊗ (Xᘁ)) :=
      𝟙 _ ⊗≫ ((Yᘁ) ◁ (f ▷ Xᘁ)) ⊗≫ (ε_ Y (Yᘁ) ▷ (U ⊗ Xᘁ)) ⊗≫
       ((η_ (Yᘁ) ((Yᘁ)ᘁ) ≫ (Yᘁ) ◁ (p.iso Y).inv) ▷ (U ⊗ Xᘁ)) ⊗≫
       ((Yᘁ) ◁ (g ▷ Xᘁ)) ⊗≫ 𝟙 _
    p.leftTrace (haarInclusionMate C X Y U f ≫ haarProjectionMate C p X Y U g) =
      End.of (η_ Y (Yᘁ) ⊗≫ ((p.iso Y).hom ▷ (Yᘁ)) ⊗≫
      ((((Yᘁ)ᘁ) ⊗ (Yᘁ)) ◁ η_ X (Xᘁ)) ⊗≫ (((Yᘁ)ᘁ) ◁ a) ⊗≫
      (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (X ⊗ (Xᘁ))) ⊗≫
      ((p.iso X).hom ▷ (Xᘁ)) ⊗≫ ε_ (Xᘁ) ((Xᘁ)ᘁ)) := by
  dsimp only
  rw [haarInclusionMate_diagram, haarProjectionMate_diagram]
  apply End.ext
  simp only [PivotalStructure.leftTrace]
  monoidal
  simp
  slice_lhs 1 2 => rw [pivotalDual_coevaluation_rotate C p Y]
  have hc : (((Yᘁ)ᘁ) ◁ (Yᘁ) ◁ ((p.iso X).hom ▷ (Xᘁ))) ≫
      (((Yᘁ)ᘁ) ◁ (Yᘁ) ◁ ε_ (Xᘁ) ((Xᘁ)ᘁ)) ≫
      (α_ ((Yᘁ)ᘁ) (Yᘁ) (𝟙_ C.Obj)).inv ≫ (ρ_ (((Yᘁ)ᘁ) ⊗ (Yᘁ))).hom ≫
      ε_ (Yᘁ) ((Yᘁ)ᘁ) =
      (α_ ((Yᘁ)ᘁ) (Yᘁ) (X ⊗ (Xᘁ))).inv ≫
      (α_ (((Yᘁ)ᘁ) ⊗ (Yᘁ)) X (Xᘁ)).inv ≫
      (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ X ▷ (Xᘁ)) ≫ (α_ (𝟙_ C.Obj) X (Xᘁ)).hom ≫
      (λ_ (X ⊗ (Xᘁ))).hom ≫ (p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := by
    have hh := congrArg (fun t ↦ (α_ ((Yᘁ)ᘁ) (Yᘁ) (X ⊗ (Xᘁ))).inv ≫ t)
      (haar_pivotal_cap_exchange C p X Y)
    convert hh using 1 <;> monoidal
  simp only [Category.assoc]
  rw [hc]

set_option backward.isDefEq.respectTransparency false in
/-- The other boxed closure is the right trace, by both boxed snakes and cup exchange. -/
theorem haar_right_trace_boxed (X Y U : C.Obj) (f : X ⟶ Y ⊗ U) (g : Y ⊗ U ⟶ X) :
    let a : (Yᘁ) ⊗ (X ⊗ (Xᘁ)) ⟶ (Yᘁ) ⊗ (X ⊗ (Xᘁ)) :=
      𝟙 _ ⊗≫ ((Yᘁ) ◁ (f ▷ Xᘁ)) ⊗≫ (ε_ Y (Yᘁ) ▷ (U ⊗ Xᘁ)) ⊗≫
       ((η_ (Yᘁ) ((Yᘁ)ᘁ) ≫ (Yᘁ) ◁ (p.iso Y).inv) ▷ (U ⊗ Xᘁ)) ⊗≫
       ((Yᘁ) ◁ (g ▷ Xᘁ)) ⊗≫ 𝟙 _
    End.of (η_ Y (Yᘁ) ⊗≫ ((Y ⊗ (Yᘁ)) ◁ η_ X (Xᘁ)) ⊗≫ (Y ◁ a) ⊗≫
      (((p.iso Y).hom ▷ (Yᘁ)) ▷ (X ⊗ (Xᘁ))) ⊗≫
      (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (X ⊗ (Xᘁ))) ⊗≫
      ((p.iso X).hom ▷ (Xᘁ)) ⊗≫ ε_ (Xᘁ) ((Xᘁ)ᘁ)) =
      p.rightTrace (f ≫ g) := by
  dsimp only
  conv_rhs => rw [← haar_yank_inclusion C X Y U f, ← haar_yank_projection C p X Y U g]
  apply End.ext
  simp only [PivotalStructure.rightTrace, rightTraceWith]
  monoidal
  simp
  have hc : η_ Y (Yᘁ) ≫ (ρ_ (Y ⊗ (Yᘁ))).inv ≫
      (α_ Y (Yᘁ) (𝟙_ C.Obj)).hom ≫ Y ◁ (Yᘁ) ◁ η_ X (Xᘁ) =
      η_ X (Xᘁ) ≫ (λ_ (X ⊗ (Xᘁ))).inv ≫ (α_ (𝟙_ C.Obj) X (Xᘁ)).inv ≫
      (η_ Y (Yᘁ) ▷ X ▷ (Xᘁ)) ≫ (α_ (Y ⊗ (Yᘁ)) X (Xᘁ)).hom ≫
      (α_ Y (Yᘁ) (X ⊗ (Xᘁ))).hom := by
    have hh := congrArg (fun t ↦ t ≫ (α_ Y (Yᘁ) (X ⊗ (Xᘁ))).hom)
      (haar_coevaluation_exchange C X Y)
    convert hh.symm using 1 <;> monoidal
  slice_lhs 1 4 => rw [hc]
  simp only [Category.assoc]
  have h₁ : (Yᘁ) ◁ (α_ Y U (Xᘁ)).hom ≫ (α_ (Yᘁ) Y (U ⊗ (Xᘁ))).inv ≫
      (α_ ((Yᘁ) ⊗ Y) U (Xᘁ)).inv =
      (α_ (Yᘁ) (Y ⊗ U) (Xᘁ)).inv ≫ (α_ (Yᘁ) Y U).inv ▷ (Xᘁ) := by monoidal
  have h₂ : (α_ (Yᘁ) (Y ⊗ U) (Xᘁ)).inv ≫ (α_ (Yᘁ) Y U).inv ▷ (Xᘁ) ≫
      (α_ ((Yᘁ) ⊗ Y) U (Xᘁ)).hom ≫ (α_ (Yᘁ) Y (U ⊗ (Xᘁ))).hom ≫
      (Yᘁ) ◁ (α_ Y U (Xᘁ)).inv = 𝟙 _ := by monoidal
  simp only [← whiskerLeft_comp_assoc]
  conv_lhs =>
    pattern (Yᘁ ◁ (f ▷ Xᘁ ≫ (α_ Y U (Xᘁ)).hom))
    rw [whiskerLeft_comp]
  simp only [Category.assoc, reassoc_of% h₁, reassoc_of% h₂]

/-- The two Frobenius mates preserve the pivotal trace pairing. -/
theorem haarMate_trace_pairing (X Y U : C.Obj) (f : X ⟶ Y ⊗ U) (g : Y ⊗ U ⟶ X) :
    p.leftTrace (haarInclusionMate C X Y U f ≫ haarProjectionMate C p X Y U g) =
      p.rightTrace (f ≫ g) := by
  rw [haar_mate_trace_boxed C p X Y U f g]
  rw [haar_pivotal_closed_slide C p X Y]
  exact haar_right_trace_boxed C p X Y U f g

/-- Mating the normalized fusion basis preserves its pivotal trace duality. -/
theorem haar_mated_trace_dual_basis (Y U : C.Obj) (i : Fin (rank C))
    (a b : Fin (Module.finrank ℂ (simples C i ⟶ Y ⊗ U))) :
    unitScalar C (p.leftTrace
      (haarInclusionMate C (simples C i) Y U (simpleInclusion C (Y ⊗ U) i a) ≫
       haarProjectionMate C p (simples C i) Y U (pivotalTraceDualProjection C p (Y ⊗ U) i b))) =
      if a = b then 1 else 0 := by
  rw [haarMate_trace_pairing]
  exact pivotalTrace_dual_basis C p (Y ⊗ U) i a b

attribute [local instance] IsFusionCategory.hom_finite

local instance (j : Fin (rank C)) : Simple ((simples C j)ᘁ) := by
  let : Simple (simples C j) := simples_simple C j
  exact simple_rightDual _

/-- Scalar composition of the mated fusion maps, normalized by the
right pivotal dimension of the simple whose dual is the source. -/
theorem haar_mated_scalar_pairing (U : C.Obj) (i j : Fin (rank C))
    (a b : Fin (Module.finrank ℂ (simples C i ⟶ simples C j ⊗ U))) :
    simpleEndScalar (k := ℂ) ((simples C j)ᘁ) (End.of
      (haarInclusionMate C (simples C i) (simples C j) U (simpleInclusion C (simples C j ⊗ U) i a) ≫
       haarProjectionMate C p (simples C i) (simples C j) U
         (pivotalTraceDualProjection C p (simples C j ⊗ U) i b))) =
      (if a = b then 1 else 0) / simpleDimension C p j := by
  classical
  let h := haarInclusionMate C (simples C i) (simples C j) U (simpleInclusion C (simples C j ⊗ U) i a) ≫
       haarProjectionMate C p (simples C i) (simples C j) U
         (pivotalTraceDualProjection C p (simples C j ⊗ U) i b)
  have ht := haar_mated_trace_dual_basis C p (simples C j) U i a b
  change unitScalar C (p.leftTrace h) = _ at ht
  rw [simpleEndScalar_mul_leftTrace, haar_leftDimension_dual] at ht
  exact (eq_div_iff (simpleDimension_ne_zero C p j)).2 ht

/-- The dimension-normalized mated projections are the scalar dual basis
of the actual mated fusion inclusions. -/
theorem haar_mated_pairing_eq_dualBasis (U : C.Obj) (i j : Fin (rank C))
    (b : Fin (Module.finrank ℂ (simples C i ⟶ simples C j ⊗ U))) :
    simpleHomPairingEquiv ((simples C j)ᘁ) (U ⊗ ((simples C i)ᘁ))
      (simpleDimension C p j • haarProjectionMate C p (simples C i) (simples C j) U
        (pivotalTraceDualProjection C p (simples C j ⊗ U) i b)) =
      (haarMatedInclusionBasis C (simples C i) (simples C j) U
        (simpleInclusionBasis C (simples C j ⊗ U) i)).dualBasis b := by
  classical
  apply (haarMatedInclusionBasis C (simples C i) (simples C j) U
    (simpleInclusionBasis C (simples C j ⊗ U) i)).ext
  intro a
  simp only [Module.Basis.dualBasis_apply, haarMatedInclusionBasis, Module.Basis.map_apply,
    simpleInclusionBasis_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  change simpleDimension C p j * simpleEndScalar (k := ℂ) ((simples C j)ᘁ) (End.of
      (haarInclusionMate C (simples C i) (simples C j) U (simpleInclusion C (simples C j ⊗ U) i a) ≫
       haarProjectionMate C p (simples C i) (simples C j) U
         (pivotalTraceDualProjection C p (simples C j ⊗ U) i b))) = _
  rw [haar_mated_scalar_pairing]
  rw [← simpleInclusionBasis_apply C (simples C j ⊗ U) i a]
  simp only [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, Module.Basis.repr_self]
  simp only [Finsupp.single_apply]
  split_ifs <;> simp_all [simpleDimension_ne_zero C p j]

/-- The mated fusion-basis contraction is independent of the basis chosen
on the dual-simple Hom space. -/
theorem haar_mated_contraction_basis_independent (U : C.Obj) (i j : Fin (rank C))
    {I : Type} [Fintype I] [DecidableEq I] {E : Type*} [AddCommGroup E] [Module ℂ E]
    (b : Module.Basis I ℂ (((simples C j)ᘁ) ⟶ U ⊗ ((simples C i)ᘁ)))
    (F : (((simples C j)ᘁ) ⟶ U ⊗ ((simples C i)ᘁ)) →ₗ[ℂ]
      (U ⊗ ((simples C i)ᘁ) ⟶ ((simples C j)ᘁ)) →ₗ[ℂ] E) :
    (∑ a, F (haarInclusionMate C (simples C i) (simples C j) U
        (simpleInclusion C (simples C j ⊗ U) i a))
      (simpleDimension C p j • haarProjectionMate C p (simples C i) (simples C j) U
        (pivotalTraceDualProjection C p (simples C j ⊗ U) i a))) =
    ∑ a, F (b a) ((simpleHomPairingEquiv ((simples C j)ᘁ)
      (U ⊗ ((simples C i)ᘁ))).symm (b.dualBasis a)) := by
  classical
  have h := MTC.Center.Normalization.pairing_contraction_basis_independent
    (haarMatedInclusionBasis C (simples C i) (simples C j) U
      (simpleInclusionBasis C (simples C j ⊗ U) i)) b
    (simpleHomPairingEquiv ((simples C j)ᘁ) (U ⊗ ((simples C i)ᘁ))) F
  simp_rw [← haar_mated_pairing_eq_dualBasis C p U i j,
    LinearEquiv.symm_apply_apply] at h
  simpa only [haarMatedInclusionBasis, Module.Basis.map_apply, simpleInclusionBasis_apply] using h

end MTC.PropertyF.Pivotal
end
