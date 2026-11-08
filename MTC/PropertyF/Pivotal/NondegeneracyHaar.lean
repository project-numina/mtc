module
public import MTC.PropertyF.Pivotal.Nondegeneracy
public import MTC.Center.Trace.LeftTensorTrace

open MTC.Fusion MTC.Modular MTC.CategoryTheory.Dimensions MTC.Center.Trace
open scoped BigOperators

/-! The actual pivotal Haar loop used in the categorical centrality criterion. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
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
  have h := doubleBraiding_natural_left (S ◁ f) V
  have ha := associator_naturality_middle S f V
  have hb := associator_inv_naturality_middle S f V
  simp only [Category.assoc] at *
  slice_lhs 3 4 => rw [← ha]
  slice_rhs 1 2 => rw [hb]
  slice_lhs 2 3 => rw [h]
  simp only [Category.assoc]


/-- The Haar loop is natural in its untraced input object. -/
theorem monodromyHaar_natural (U W V : C.Obj) (f : U ⟶ W) :
    (monodromyHaar C p U V).asHom ≫ (f ▷ V) =
      (f ▷ V) ≫ (monodromyHaar C p W V).asHom := by
  classical
  simp only [monodromyHaar, End.sum_asHom, End.smul_asHom,
    Preadditive.sum_comp, Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [monodromyHaar_summand_natural]

end MTC.PropertyF.Pivotal
end
