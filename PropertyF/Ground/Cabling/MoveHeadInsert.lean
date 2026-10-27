module
public import PropertyF.Ground.Cabling.MoveHead
public import PropertyF.Ground.Calculus.StrandCoherence
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Repeated right-strand insertion transports an actual braid by the
canonical tensor-power comparison. -/
theorem addRightStrands_hom (X : C) (n k : ℕ) (g : braidImage X n) :
    ((addRightStrands X n k g).val).asIso.hom =
      (insertRightPowerIso X n k).inv ≫
        (g.val.asIso.hom ▷ tensorPower X k) ≫ (insertRightPowerIso X n k).hom := by
  have h := addRightBraidAlgebraIter_asHom X n k (groupInImage (braidEndRepresentation X n) g)
  rw [addRightBraidAlgebraIter_group] at h
  change ((groupInImage (braidEndRepresentation X (n + k))
      (addRightStrands X n k g) : End (tensorPower X (n + k + 2)))).asHom =
      (insertRightPowerIso X n k).inv ≫
        (((groupInImage (braidEndRepresentation X n) g : End (tensorPower X (n + 2))).asHom) ▷ tensorPower X k) ≫
          (insertRightPowerIso X n k).hom at h
  rw [groupInImage_val, groupInImage_val] at h
  exact h

/-- A head-to-tail crossing remains an actual braid when a block of spectator
strands is appended on the right. -/
theorem moveHead_rightSpectators (X : C) (n k : ℕ) :
    ∃ g : braidImage X (n+k), g.val.asIso.hom =
      (insertRightPowerIso X n k).inv ≫
        ((moveHead X (n+1)).asIso.hom ▷ tensorPower X k) ≫
          (insertRightPowerIso X n k).hom := by
  let g : braidImage X n := ⟨moveHead X (n+1), moveHead_mem_braidImage X n⟩
  exact ⟨addRightStrands X n k g, addRightStrands_hom X n k g⟩
end PropertyF
