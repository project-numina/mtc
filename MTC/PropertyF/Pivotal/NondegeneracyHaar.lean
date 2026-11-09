module
public import MTC.PropertyF.Pivotal.Nondegeneracy
public import MTC.Center.Trace.LeftTensorTrace
public import MTC.PropertyF.Pivotal.SlopeTrace
public import MTC.Center.Induction.BasisPairing
public import MTC.Center.Braid.PivotalRegularSupport

open MTC.Fusion MTC.Modular MTC.CategoryTheory.Dimensions MTC.Center.Trace
open scoped BigOperators

/-! The actual pivotal Haar loop used in the categorical centrality criterion. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

/-- Close the first strand of a morphism, leaving arbitrary source and target
on the remaining strand. -/
def leftPartialTraceHom (X A B : C.Obj) (f : X ⊗ A ⟶ X ⊗ B) : A ⟶ B :=
  (λ_ A).inv ≫
    ((η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ ((Xᘁ) ◁ (p.iso X).inv)) ▷ A) ≫
    (α_ (Xᘁ) X A).hom ≫ ((Xᘁ) ◁ f) ≫
    (α_ (Xᘁ) X B).inv ≫ (ε_ X (Xᘁ) ▷ B) ≫ (λ_ B).hom

/-- The extended partial trace agrees with the existing endomorphism trace. -/
theorem leftPartialTraceHom_end (X A : C.Obj) (f : End (X ⊗ A)) :
    leftPartialTraceHom C p X A A f.asHom = (leftPartialTrace p f).asHom := rfl

/-- Closing the first strand preserves finite sums of arbitrary morphisms. -/
theorem leftPartialTraceHom_sum (p : PivotalStructure (C := C.Obj))
    {I : Type*} [Fintype I] (X A B : C.Obj) (f : I → (X ⊗ A ⟶ X ⊗ B)) :
    leftPartialTraceHom C p X A B (∑ i, f i) = ∑ i, leftPartialTraceHom C p X A B (f i) := by
  classical
  simp [leftPartialTraceHom, whiskerLeft_sum, Preadditive.sum_comp, Preadditive.comp_sum]


/-- Postcomposing a free strand commutes with closing the other strand. -/
theorem leftPartialTraceHom_post (X A B E : C.Obj) (f : X ⊗ A ⟶ X ⊗ B)
    (g : B ⟶ E) :
    leftPartialTraceHom C p X A E (f ≫ X ◁ g) =
      leftPartialTraceHom C p X A B f ≫ g := by
  dsimp [leftPartialTraceHom]
  simp only [whiskerLeft_comp]
  monoidal; simp
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    leftUnitor_naturality]

/-- Precomposing a free strand commutes with closing the other strand. -/
theorem leftPartialTraceHom_pre (X A B E : C.Obj) (f : X ⊗ A ⟶ X ⊗ B)
    (g : E ⟶ A) :
    leftPartialTraceHom C p X E B ((X ◁ g) ≫ f) =
      g ≫ leftPartialTraceHom C p X A B f := by
  dsimp [leftPartialTraceHom]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← associator_naturality_right_assoc, ← whisker_exchange_assoc,
    leftUnitor_inv_naturality_assoc]

/-- The Haar loop associated to an actual monodromy family. The summand
closes the simple strand in the monodromy of `simples C i ⊗ U` with `V`;
weights are the actual pivotal dimensions. -/
def monodromyHaar (U V : C.Obj) : End (U ⊗ V) :=
  ∑ i : Fin (rank C), simpleDimension C p i •
    leftPartialTrace p (End.of ((α_ (simples C i) U V).inv ≫
      doubleBraiding (simples C i ⊗ U) V ≫ (α_ (simples C i) U V).hom))

/-- Reassociating a double braiding produces a natural endomorphism in
the middle tensor factor. -/
theorem doubleBraiding_reassociated_natural {D : Type u} [Category.{v} D]
    [MonoidalCategory D] [BraidedCategory D] {S U W V : D} (f : U ⟶ W) :
    ((α_ S U V).inv ≫ doubleBraiding (S ⊗ U) V ≫ (α_ S U V).hom) ≫
        (S ◁ (f ▷ V)) =
      (S ◁ (f ▷ V)) ≫
        ((α_ S W V).inv ≫ doubleBraiding (S ⊗ W) V ≫ (α_ S W V).hom) := by
  have h := doubleBraiding_natural_left (S ◁ f) V
  have ha := associator_naturality_middle S f V
  have hb := associator_inv_naturality_middle S f V
  simp only [Category.assoc] at *
  slice_lhs 3 4 => rw [← ha]
  slice_rhs 1 2 => rw [hb]
  slice_lhs 2 3 => rw [h]
  simp only [Category.assoc]

/-- Each actual monodromy summand of the Haar loop is natural in the
untraced object. -/
theorem monodromyHaar_summand_natural (S U W V : C.Obj) (f : U ⟶ W) :
    (leftPartialTrace p (End.of ((α_ S U V).inv ≫
      doubleBraiding (S ⊗ U) V ≫ (α_ S U V).hom))).asHom ≫ (f ▷ V) =
      (f ▷ V) ≫ (leftPartialTrace p (End.of ((α_ S W V).inv ≫
        doubleBraiding (S ⊗ W) V ≫ (α_ S W V).hom))).asHom := by
  change leftPartialTraceHom C p S _ _ _ ≫ (f ▷ V) =
    (f ▷ V) ≫ leftPartialTraceHom C p S _ _ _
  rw [← leftPartialTraceHom_post, ← leftPartialTraceHom_pre]
  congr 1
  exact doubleBraiding_reassociated_natural f


/-- The Haar loop is natural in its untraced input object. -/
theorem monodromyHaar_natural (U W V : C.Obj) (f : U ⟶ W) :
    (monodromyHaar C p U V).asHom ≫ (f ▷ V) =
      (f ▷ V) ≫ (monodromyHaar C p W V).asHom := by
  classical
  simp only [monodromyHaar, End.sum_asHom, End.smul_asHom,
    Preadditive.sum_comp, Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul,
    monodromyHaar_summand_natural]

/-- The monodromy around a tensor product separates into its two loops. -/
theorem doubleBraiding_tensor_first_factor (S U V : C.Obj) :
    (α_ S U V).inv ≫ doubleBraiding (S ⊗ U) V ≫ (α_ S U V).hom =
      (S ◁ (β_ U V).hom) ≫ (α_ S V U).inv ≫
        (doubleBraiding S V ▷ U) ≫ (α_ S V U).hom ≫ (S ◁ (β_ V U).hom) := by
  simp only [doubleBraiding, braiding_tensor_left_hom, braiding_tensor_right_hom,
    Category.assoc]
  monoidal

/-- The simple-strand monodromy loop used as the Haar vacuum value. -/
def monodromyHaarVacuum (V : C.Obj) : End V :=
  ∑ i : Fin (rank C), simpleDimension C p i •
    leftPartialTrace p (End.of (doubleBraiding (simples C i) V))

/-- Factoring a monodromy loop and closing its simple strand leaves a
conjugated vacuum loop. -/
theorem monodromyHaar_summand_factor (S U V : C.Obj) :
    (leftPartialTrace p (End.of ((α_ S U V).inv ≫
      doubleBraiding (S ⊗ U) V ≫ (α_ S U V).hom))).asHom =
      (β_ U V).hom ≫
        ((leftPartialTrace p (End.of (doubleBraiding S V))).asHom ▷ U) ≫
          (β_ V U).hom := by
  rw [doubleBraiding_tensor_first_factor]
  change leftPartialTraceHom C p S _ _ _ = _
  rw [leftPartialTraceHom_pre]
  simp only [← Category.assoc]
  rw [leftPartialTraceHom_post]
  rw [leftPartialTraceHom_end]
  simp only [Category.assoc]
  rw [leftPartialTrace_whiskerRight]

/-- The Haar loop factors through its vacuum loop and the two braidings. -/
theorem monodromyHaar_factor (U V : C.Obj) :
    (monodromyHaar C p U V).asHom =
      (β_ U V).hom ≫ ((monodromyHaarVacuum C p V).asHom ▷ U) ≫ (β_ V U).hom := by
  classical
  simp only [monodromyHaar, monodromyHaarVacuum, End.sum_asHom, End.smul_asHom,
    sum_whiskerRight, MonoidalLinear.smul_whiskerRight, Preadditive.sum_comp,
    Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul, monodromyHaar_summand_factor]

/-- The left pivotal trace is the right pivotal trace of the dual morphism. -/
theorem leftTrace_eq_rightTrace_dual (X : C.Obj) (f : End X) :
    p.leftTrace f.asHom = p.rightTrace (f.asHomᘁ) :=
  MTC.CategoryTheory.Dimensions.leftTrace_eq_rightTrace_rightDual p f.asHom


/-- The dual of monodromy is monodromy of the dual strands in reverse order. -/
theorem doubleBraiding_dual_tensor (S V : C.Obj) :
    ((doubleBraiding S V)ᘁ) ≫ (rightDualTensorIso S V).hom =
      (rightDualTensorIso S V).hom ≫ doubleBraiding (Vᘁ : C.Obj) (Sᘁ : C.Obj) := by
  simp only [doubleBraiding, comp_rightAdjointMate, Category.assoc]
  rw [rightDualTensorIso_braiding S V, ← Category.assoc,
    rightDualTensorIso_braiding V S, Category.assoc]

/-- The left trace of monodromy is the right trace of the monodromy
of the dual objects. -/
theorem leftTrace_doubleBraiding_eq_dual (S V : C.Obj) :
    p.leftTrace (doubleBraiding S V) =
      p.rightTrace (doubleBraiding (Vᘁ : C.Obj) (Sᘁ : C.Obj)) := by
  rw [leftTrace_eq_rightTrace_dual C p (S ⊗ V) (End.of (doubleBraiding S V))]
  exact p.rightTrace_of_iso_intertwining (rightDualTensorIso S V) _ _
    (doubleBraiding_dual_tensor C S V)

/-- If a label satisfies the numerical S-test against `i`, its dual
satisfies the same test. The pivotal phase cancels using the nonzero
dimension of `i`. -/
theorem categoricalS_dual_of_dimension_product (i k : Fin (rank C))
    (hs : categoricalS C p i k = simpleDimension C p i * simpleDimension C p k) :
    categoricalS C p i (dualIndex C k) =
      simpleDimension C p i * simpleDimension C p (dualIndex C k) := by
  have h := categoricalS_star_eq_dual_phase C p i k
  have hd : simpleDimension C p i ≠ 0 := simpleDimension_ne_zero C p i
  have hdstar : starRingEnd ℂ (simpleDimension C p i) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hd
  rw [hs, map_mul] at h
  field_simp at h
  rw [MTC.Center.Braid.simpleDimension_dual_eq_star (D := C) (p := p) k]
  exact h.symm.trans (mul_comm _ _)

/-- The trace of monodromy on the actual dual objects is the S-entry
at their chosen dual labels. -/
theorem rightTrace_duals_eq_categoricalS (i k : Fin (rank C)) :
    unitScalar C (p.rightTrace (doubleBraiding ((simples C k)ᘁ) ((simples C i)ᘁ))) =
      categoricalS C p (dualIndex C i) (dualIndex C k) := by
  rw [categoricalS_symmetric C p, categoricalS, ← unitScalar_eq_equiv]
  change unitScalar C (SEntry p ((simples C k)ᘁ) ((simples C i)ᘁ)) = _
  rw [SEntry_iso_left p (rightDualLabelIso C k), SEntry_iso_right p _ (rightDualLabelIso C i)]

/-- A numerical S-test against the dual label determines the left trace
of monodromy on the original simple objects. -/
theorem leftTrace_monodromy_of_dual_sTest (k i : Fin (rank C))
    (hs : categoricalS C p (dualIndex C i) k =
      simpleDimension C p (dualIndex C i) * simpleDimension C p k) :
    unitScalar C (p.leftTrace (doubleBraiding (simples C i) (simples C k))) =
      star (simpleDimension C p i) * star (simpleDimension C p k) := by
  rw [leftTrace_doubleBraiding_eq_dual]
  have hidim := MTC.Center.Braid.simpleDimension_dual_eq_star (D := C) (p := p) i
  have hkdim := MTC.Center.Braid.simpleDimension_dual_eq_star (D := C) (p := p) k
  have hdualtest := categoricalS_dual_of_dimension_product C p (dualIndex C i) k hs
  rw [rightTrace_duals_eq_categoricalS, hdualtest, hidim, hkdim]

attribute [local instance] IsFusionCategory.hom_finite

/-- The left trace of a simple endomorphism is its scalar times the left
pivotal dimension. -/
theorem simpleEndScalar_mul_leftTrace (X : C.Obj) [Simple X] (f : End X) :
    unitScalar C (p.leftTrace f.asHom) =
      simpleEndScalar (k := ℂ) X f * unitScalar C (p.leftTrace (𝟙 X)) := by
  rw [eq_smul_one_of_algEquiv (simpleEndScalar (k := ℂ) X) f]
  simp [PivotalStructure.leftTrace_smul, unitScalar_eq_equiv, smul_eq_mul]

/-- The left pivotal dimension of a right dual is the right dimension of its original object. -/
theorem haar_leftDimension_dual (Y : C.Obj) :
    unitScalar C (p.leftTrace (𝟙 (Yᘁ : C.Obj))) = pivotalDimension C p Y := by
  rw [leftTrace_eq_rightTrace_dual C p (Yᘁ) (End.of (𝟙 (Yᘁ : C.Obj)))]
  simpa [pivotalDimension] using (pivotalDimension_iso p (p.iso Y)).symm

/-- For a simple object, the left pivotal dimension is the conjugate
of its right pivotal dimension. -/
theorem leftDimension_simple_eq_star (X : C.Obj) [Simple X] :
    unitScalar C (p.leftTrace (𝟙 X)) = star (pivotalDimension C p X) := by
  change unitScalar C (p.leftTrace (1 : End X).asHom) = _
  rw [leftTrace_eq_rightTrace_dual C p _ (1 : End X)]
  simpa [pivotalDimension] using pivotalDimension_dual_conj C p X

/-- Under the numerical S-test, every closed monodromy loop is the
conjugate pivotal dimension times the identity of the surviving simple. -/
theorem leftPartialTrace_monodromy_of_dual_sTest (k i : Fin (rank C))
    (hs : categoricalS C p (dualIndex C i) k =
      simpleDimension C p (dualIndex C i) * simpleDimension C p k) :
    leftPartialTrace p (End.of (doubleBraiding (simples C i) (simples C k))) =
      star (simpleDimension C p i) • (1 : End (simples C k)) := by
  let : Simple (simples C k) := simples_simple C k
  let a := leftPartialTrace p (End.of (doubleBraiding (simples C i) (simples C k)))
  have ht := congrArg (unitScalar C) (leftTrace_partialTrace p
    (End.of (doubleBraiding (simples C i) (simples C k))))
  change unitScalar C (p.leftTrace a.asHom) = _ at ht
  rw [simpleEndScalar_mul_leftTrace] at ht
  rw [leftDimension_simple_eq_star, leftTrace_monodromy_of_dual_sTest C p k i hs] at ht
  have hn : star (simpleDimension C p k) ≠ 0 :=
    star_ne_zero.mpr (simpleDimension_ne_zero C p k)
  apply (simpleEndScalar (k := ℂ) (simples C k)).injective
  simpa only [map_smul, map_one, smul_eq_mul, mul_one] using mul_right_cancel₀ hn ht

/-- The trace of a simple monodromy loop under the global numerical S-test,
using the left pivotal trace. -/
theorem leftTrace_monodromy_of_sTest (k i : Fin (rank C))
    (hs : ∀ j, categoricalS C p j k = simpleDimension C p j * simpleDimension C p k) :
    unitScalar C (p.leftTrace (doubleBraiding (simples C i) (simples C k))) =
      star (simpleDimension C p i) * star (simpleDimension C p k) :=
  leftTrace_monodromy_of_dual_sTest C p k i (hs (dualIndex C i))

/-- Under the numerical S-test, every closed monodromy loop is the
conjugate pivotal dimension times the identity of the surviving simple. -/
theorem leftPartialTrace_monodromy_of_sTest (k i : Fin (rank C))
    (hs : ∀ j, categoricalS C p j k = simpleDimension C p j * simpleDimension C p k) :
    leftPartialTrace p (End.of (doubleBraiding (simples C i) (simples C k))) =
      star (simpleDimension C p i) • (1 : End (simples C k)) :=
  leftPartialTrace_monodromy_of_dual_sTest C p k i (hs (dualIndex C i))

/-- The Haar vacuum loop on a numerically central simple is the intrinsic
global dimension times the identity. -/
theorem monodromyHaarVacuum_of_sTest (k : Fin (rank C))
    (hs : ∀ j, categoricalS C p j k = simpleDimension C p j * simpleDimension C p k) :
    monodromyHaarVacuum C p (simples C k) =
      globalDimension C • (1 : End (simples C k)) := by
  classical
  simp only [monodromyHaarVacuum, leftPartialTrace_monodromy_of_sTest C p k _ hs,
    smul_smul, ← Finset.sum_smul]
  congr 1
  simpa only [simpleDimension, mul_comm] using
    (MTC.Center.Induction.globalDimension_eq_sum_pivotal_conj_mul p).symm

/-- Under numerical centrality, the actual Haar loop is global dimension
 times the monodromy on the untraced strands. -/
theorem monodromyHaar_of_sTest (U : C.Obj) (k : Fin (rank C))
    (hs : ∀ j, categoricalS C p j k = simpleDimension C p j * simpleDimension C p k) :
    monodromyHaar C p U (simples C k) =
      globalDimension C • End.of (doubleBraiding U (simples C k)) := by
  apply End.ext
  rw [monodromyHaar_factor, monodromyHaarVacuum_of_sTest C p k hs]
  simp [doubleBraiding, MonoidalLinear.smul_whiskerRight, Linear.comp_smul,
    Linear.smul_comp]

/-- The actual Haar loop at the tensor unit is its vacuum value,
transported along the left unitor. -/
theorem monodromyHaar_unit (V : C.Obj) :
    (monodromyHaar C p (𝟙_ C.Obj) V).asHom =
      (λ_ V).hom ≫ (monodromyHaarVacuum C p V).asHom ≫ (λ_ V).inv := by
  rw [monodromyHaar_factor]
  simp only [braiding_tensorUnit_left, braiding_tensorUnit_right, Category.assoc]
  rw [rightUnitor_naturality_assoc, Iso.inv_hom_id_assoc]

/-- Canonical simple inclusions and projections have the Kronecker-delta pairing. -/
theorem simpleInclusion_projection_eq_ite (X : C.Obj) (i : Fin (rank C))
    (a b : Fin (Module.finrank ℂ (simples C i ⟶ X))) :
    simpleInclusion C X i a ≫ MTC.Center.Induction.simpleProjection X i b =
      (if a = b then (1 : ℂ) else 0) • 𝟙 (simples C i) := by
  classical
  have h := simpleInclusionBasis_projection (simpleInclusion C X i a) b
  rw [← simpleInclusionBasis_apply C X i a, Module.Basis.repr_self] at h
  simpa [simpleInclusionBasis_apply, MTC.Center.Induction.simpleProjection, Finsupp.single_apply] using h.symm


/-- Canonical inclusions and projections pair by a Kronecker delta,
with the actual simple pivotal dimension as normalization. -/
theorem pivotalTrace_simpleInclusion_projection (X : C.Obj) (i : Fin (rank C))
    (a b : Fin (Module.finrank ℂ (simples C i ⟶ X))) :
    unitScalar C (p.rightTrace (simpleInclusion C X i a ≫
      MTC.Center.Induction.simpleProjection X i b)) =
      if a = b then simpleDimension C p i else 0 := by
  classical
  rw [simpleInclusion_projection_eq_ite, PivotalStructure.rightTrace_smul,
    unitScalar_eq_equiv, map_smul]
  split_ifs
  · simp [smul_eq_mul, simpleDimension, pivotalDimension, unitScalar_eq_equiv]
  · simp

/-- Projection normalized to be dual to the corresponding inclusion for
the actual pivotal trace pairing. -/
def pivotalTraceDualProjection (X : C.Obj) (i : Fin (rank C))
    (a : Fin (Module.finrank ℂ (simples C i ⟶ X))) : X ⟶ simples C i :=
  (simpleDimension C p i)⁻¹ • MTC.Center.Induction.simpleProjection X i a

/-- The normalized projections form the trace-dual basis to the canonical
inclusions. -/
theorem pivotalTrace_dual_basis (X : C.Obj) (i : Fin (rank C))
    (a b : Fin (Module.finrank ℂ (simples C i ⟶ X))) :
    unitScalar C (p.rightTrace (simpleInclusion C X i a ≫
      pivotalTraceDualProjection C p X i b)) = if a = b then 1 else 0 := by
  classical
  rw [pivotalTraceDualProjection, Linear.comp_smul, PivotalStructure.rightTrace_smul,
    unitScalar_eq_equiv, map_smul, smul_eq_mul, ← unitScalar_eq_equiv,
    pivotalTrace_simpleInclusion_projection]
  split_ifs <;> simp [simpleDimension_ne_zero C p i]

/-- The weighted trace-dual bases resolve the identity on every object. -/
theorem pivotalTrace_dual_basis_complete (X : C.Obj) :
    (∑ q : simplePieces C X, simpleDimension C p q.1 •
      (pivotalTraceDualProjection C p X q.1 q.2 ≫ simpleInclusion C X q.1 q.2)) = 𝟙 X := by
  classical
  simp only [pivotalTraceDualProjection, Linear.smul_comp, smul_smul,
    mul_inv_cancel₀ (simpleDimension_ne_zero C p _), one_smul]
  exact MTC.Center.Induction.simple_completeness C X

end MTC.PropertyF.Pivotal
end
