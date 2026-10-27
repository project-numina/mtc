module
public import PropertyF.Ground.CentreRigid.PartialTraceBiproduct
public import PropertyF.Ground.CentreInduction.Averaging

/-! Fusion-strand decomposition of closed centre windings. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreRigid
open scoped BigOperators
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
set_option backward.isDefEq.respectTransparency false in
/-- Winding is natural in the test strand, even for noncentral underlying maps. -/
theorem winding_natural (C : BraidedFusionCategory.{v,u}) (X Y : Center C.Obj) (f : X.1 ⟶ Y.1)
    {T S : C.Obj} (q : T ⟶ S) :
    (X.1 ◁ q) ≫ CentreInduction.winding C X Y S f =
      CentreInduction.winding C X Y T f ≫ (Y.1 ◁ q) := by
  have hx := X.2.naturality q
  have hy : (q ▷ Y.1) ≫ (Y.2.β S).inv = (Y.2.β T).inv ≫ (Y.1 ◁ q) := by
    apply (cancel_epi (Y.2.β T).hom).1
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Y.2.naturality_assoc]
    simp
  dsimp only [CentreInduction.winding]
  calc
    _ = (X.2.β T).hom ≫ ((q ▷ X.1) ≫ (S ◁ f)) ≫ (Y.2.β S).inv := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ (S ◁ f) ≫ (Y.2.β S).inv) hx
    _ = (X.2.β T).hom ≫ ((T ◁ f) ≫ (q ▷ Y.1)) ≫ (Y.2.β S).inv := by rw [whisker_exchange]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun k => (X.2.β T).hom ≫ (T ◁ f) ≫ k) hy

set_option backward.isDefEq.respectTransparency false in
/-- A closed winding distributes over a finite direct sum of test strands. -/
theorem trace_winding_biproduct (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    {ι : Type} [Fintype ι] [DecidableEq ι] (V : ι → C.Obj)
    (X Y : Center C.Obj) (f : X.1 ⟶ Y.1) :
    CentreInduction.partialTraceHom p X.1 Y.1 (⨁ V) (CentreInduction.winding C X Y (⨁ V) f) =
    ∑ i, CentreInduction.partialTraceHom p X.1 Y.1 (V i) (CentreInduction.winding C X Y (V i) f) := by
  rw [CentreRigid.partialTraceHom_biproduct]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← Category.assoc, winding_natural C X Y f (biproduct.ι V i)]
  simp [Category.assoc, ← whiskerLeft_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The winding trace is the fusion-multiplicity-weighted sum of simple winding traces. -/
theorem trace_winding_simple_decomposition (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (X Y : Center C.Obj) (f : X.1 ⟶ Y.1) (T : C.Obj) :
    CentreInduction.partialTraceHom p X.1 Y.1 T (CentreInduction.winding C X Y T f) =
      ∑ i : Fin (rank C), (Module.finrank ℂ (simples C i ⟶ T) : ℂ) •
        CentreInduction.partialTraceHom p X.1 Y.1 (simples C i) (CentreInduction.winding C X Y (simples C i) f) := by
  classical
  let V := Dimensions.simplePiecesObject C T
  let e := Dimensions.simpleDecomposition C T
  have hw : (X.1 ◁ e.inv) ≫ CentreInduction.winding C X Y T f ≫ (Y.1 ◁ e.hom) =
      CentreInduction.winding C X Y (⨁ V) f := by
    rw [← Category.assoc, winding_natural C X Y f e.inv]
    simp [Category.assoc, ← whiskerLeft_comp, V]
  have hc := CentreRigid.partialTraceHom_conjugate p X.1 Y.1 e (CentreInduction.winding C X Y T f)
  rw [hw, trace_winding_biproduct] at hc
  rw [← hc]
  simp only [Dimensions.simplePiecesObject, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ _ : Fin (Module.finrank ℂ (simples C i ⟶ T)),
      CentreInduction.partialTraceHom p X.1 Y.1 (simples C i) (CentreInduction.winding C X Y (simples C i) f)) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

end PropertyF.Ground.CentreRigid
