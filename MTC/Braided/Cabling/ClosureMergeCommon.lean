module
public import MTC.Braided.Cabling.ClosureInterchange

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The canonical transport between two arithmetically equal tensor powers. -/
def powerIndexIso (X : C) {a b : ℕ} (h : a = b) : tensorPower X a ≅ tensorPower X b :=
  eqToIso (congrArg (tensorPower X) h)

omit [BraidedCategory C] in
/-- Transporting a power index commutes with appending a strand. -/
theorem powerIndexIso_append (X : C) {a b : ℕ} (h : a = b) :
    (powerIndexIso X h ⊗ᵢ Iso.refl X) ≪≫ Trace.appendIso X b =
      Trace.appendIso X a ≪≫ powerIndexIso X (congrArg (fun n => n+1) h) := by
  subst b
  apply Iso.ext
  simp [powerIndexIso, tensorIso_hom]

omit [BraidedCategory C] in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
/-- Merging a block with an additional leading strand agrees with ordinary
right-strand insertion, after explicit transport of the strand count. -/
theorem sweepBlockMerge_succ_left (X : C) (s : ℕ) : ∀ r : ℕ,
    sweepBlockMerge X (s+1) r =
      Trace.insertRightPowerIso X s (r+1) ≪≫
        powerIndexIso X (by omega : s+(r+1)+2 = (s+1)+r+2)
  | 0 => by
    apply Iso.ext
    simp [sweepBlockMerge, Trace.insertRightPowerIso, tensorPower, Trace.appendIso,
      powerIndexIso, Category.assoc]
    monoidal
  | r+1 => by
    change ((Iso.refl (tensorPower X ((s+1)+1)) ⊗ᵢ
        (Trace.appendIso X (r+1)).symm) ≪≫
      (α_ (tensorPower X ((s+1)+1)) (tensorPower X (r+1)) X).symm ≪≫
      (sweepBlockMerge X (s+1) r ⊗ᵢ Iso.refl X) ≪≫
        Trace.appendIso X ((s+1)+r+2)) =
      ((Iso.refl (Trace.braidTensorPower X s) ⊗ᵢ
        (Trace.appendIso X (r+1)).symm) ≪≫
      (α_ (Trace.braidTensorPower X s) (tensorPower X (r+1)) X).symm ≪≫
      (Trace.insertRightPowerIso X s (r+1) ⊗ᵢ Iso.refl X) ≪≫
        Trace.appendIso X (s+(r+1)+2)) ≪≫ _
    rw [sweepBlockMerge_succ_left X s r]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
      tensorHom_id, id_tensorHom]
    simp only [comp_whiskerRight, Category.assoc]
    have h := congrArg (fun q => q.hom) (powerIndexIso_append X
      (by omega : s+(r+1)+2 = (s+1)+r+2))
    simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id] at h
    rw [h]

end MTC.Braided
