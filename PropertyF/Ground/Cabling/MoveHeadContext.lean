module
public import PropertyF.Ground.Cabling.MoveHeadInsert
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Repeated left insertion transports an actual braid across a block of
identity strands. -/
theorem addLeftStrands_hom (X : C) (n k : ℕ) (g : braidImage X n) :
    ((addLeftStrands X n k g).val).asIso.hom =
      (insertLeftPowerIso X n k).inv ≫
        (tensorPower X k ◁ g.val.asIso.hom) ≫ (insertLeftPowerIso X n k).hom := by
  have h := addLeftBraidAlgebraIter_asHom X n k (groupInImage (braidEndRepresentation X n) g)
  rw [addLeftBraidAlgebraIter_group] at h
  change ((groupInImage (braidEndRepresentation X (n + k))
      (addLeftStrands X n k g) : End (tensorPower X (n + k + 2)))).asHom =
      (insertLeftPowerIso X n k).inv ≫
        (tensorPower X k ◁ ((groupInImage (braidEndRepresentation X n) g : End (tensorPower X (n + 2))).asHom)) ≫
          (insertLeftPowerIso X n k).hom at h
  rw [groupInImage_val, groupInImage_val] at h
  exact h

/-- One strand crossing a block, surrounded on both sides by arbitrary
spectator blocks, lies in the braid image on the full tensor power. -/
theorem moveHead_spectators (X : C) (n right left : ℕ) :
    ∃ g : braidImage X ((n+right)+left), g.val.asIso.hom =
      (insertLeftPowerIso X (n+right) left).inv ≫
        (tensorPower X left ◁ ((insertRightPowerIso X n right).inv ≫
          ((moveHead X (n+1)).asIso.hom ▷ tensorPower X right) ≫
            (insertRightPowerIso X n right).hom)) ≫
      (insertLeftPowerIso X (n+right) left).hom := by
  let b : braidImage X n := ⟨moveHead X (n+1), moveHead_mem_braidImage X n⟩
  let c := addRightStrands X n right b
  refine ⟨addLeftStrands X (n+right) left c, ?_⟩
  rw [addLeftStrands_hom, addRightStrands_hom]
end PropertyF
