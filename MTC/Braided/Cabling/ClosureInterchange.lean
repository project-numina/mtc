module
public import MTC.Braided.Cabling.ClosureCanonicalBlocks

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A merge on the first two factors commutes with an independent change of
the third factor, with all reassociation made explicit. -/
theorem merge_iso_interchange {A B D E F : C} (e : A ⊗ B ≅ D) (f : E ≅ F) :
    (α_ A B E).symm ≪≫ (e ⊗ᵢ Iso.refl E) ≪≫ (Iso.refl D ⊗ᵢ f) =
      (Iso.refl A ⊗ᵢ (Iso.refl B ⊗ᵢ f)) ≪≫ (α_ A B F).symm ≪≫
        (e ⊗ᵢ Iso.refl F) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
    id_tensorHom, tensorHom_id]
  rw [← whisker_exchange]
  rw [associator_inv_naturality_right_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The recursive merge can instead append the first strand of the right
block and then append its remainder. -/
theorem sweepBlockMerge_succ_prepend (X : C) (s : ℕ) : ∀ r : ℕ,
    sweepBlockMerge X s (r+1) =
      (α_ (tensorPower X (s+1)) X (tensorPower X (r+1))).symm ≪≫
        (Trace.appendIso X (s+1) ⊗ᵢ Iso.refl (tensorPower X (r+1))) ≪≫
          Trace.insertRightPowerIso X s (r+1)
  | 0 => by
    apply Iso.ext
    simp [sweepBlockMerge, Trace.insertRightPowerIso, tensorPower, Trace.appendIso,
      Category.assoc]
    monoidal
  | r+1 => by
    change ((Iso.refl (tensorPower X (s+1)) ⊗ᵢ (Trace.appendIso X (r+2)).symm) ≪≫
      (α_ (tensorPower X (s+1)) (tensorPower X (r+2)) X).symm ≪≫
      (sweepBlockMerge X s (r+1) ⊗ᵢ Iso.refl X) ≪≫
        Trace.appendIso X (s+(r+1)+2)) =
      (α_ (tensorPower X (s+1)) X (tensorPower X (r+2))).symm ≪≫
        (Trace.appendIso X (s+1) ⊗ᵢ Iso.refl (tensorPower X (r+2))) ≪≫
        ((Iso.refl (Trace.braidTensorPower X s) ⊗ᵢ (Trace.appendIso X (r+1)).symm) ≪≫
          (α_ (Trace.braidTensorPower X s) (tensorPower X (r+1)) X).symm ≪≫
          (Trace.insertRightPowerIso X s (r+1) ⊗ᵢ Iso.refl X) ≪≫
            Trace.appendIso X (s+(r+1)+2))
    rw [sweepBlockMerge_succ_prepend X s r]
    have h := congrArg (fun q => q.hom) (merge_iso_interchange
      (Trace.appendIso X (s+1)) (Trace.appendIso X (r+1)).symm)
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
      tensorHom_id, id_tensorHom] at h
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
      tensorHom_id, id_tensorHom]
    slice_rhs 1 3 => rw [h]
    rw [Trace.appendIso_succ X (r+1)]
    simp only [Iso.trans_inv, tensorIso_inv, Iso.refl_inv, id_tensorHom]
    monoidal

end MTC.Braided
