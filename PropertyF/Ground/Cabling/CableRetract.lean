module
public import PropertyF.Ground.Cabling.Naturality
open CategoryTheory
@[expose] public noncomputable section
namespace PropertyF
universe v u

/-- A cabling diagram for an object induces one for each retract. -/
def CablingWitness.of_retract {C : BraidedFusionCategory.{v,u}} {X Y Z : C.Obj}
    (r : Retract Y Z) {n : ℕ} (W : CablingWitness C X Z n) : CablingWitness C X Y n := by
  let f := braidImageRetractMap r n
  have hf : Function.Surjective f := braidImageRetractMap_surjective r n
  let _ : (W.pureImage.map f).FiniteIndex := Subgroup.FiniteIndex.map_of_surjective W.pureImage hf
  exact {
    blockCount := W.blockCount
    lengths := W.lengths
    pureImage := W.pureImage.map f
    cableImage := W.cableImage
    restriction := (f.subgroupMap W.pureImage).comp W.restriction
    restriction_surjective := (MonoidHom.subgroupMap_surjective f W.pureImage).comp W.restriction_surjective
  }
attribute [local instance] Abelian.hasFiniteBiproducts
open CategoryTheory.Limits

/-- It suffices to construct cabling diagrams for finite sums of tensor
powers: all their retracts inherit diagrams functorially. -/
theorem cabling_of_sumPowers {C : BraidedFusionCategory.{v,u}} (X : C.Obj)
    (hsum : ∀ (count : ℕ) (k : Fin count → ℕ) (n : ℕ),
      Nonempty (CablingWitness C X (⨁ fun i => tensorPower X (k i)) n)) :
    ∀ Y, GeneratedBy X Y → ∀ n, Nonempty (CablingWitness C X Y n) := by
  intro Y hY n
  obtain ⟨count, k, ⟨r⟩⟩ := hY
  obtain ⟨W⟩ := hsum count k n
  exact ⟨W.of_retract r⟩

end PropertyF
