module
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Whiskering

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground.Dimensions
universe v u

/-- If two isomorphisms into a functor have the same functorial square, and
one is a component of a natural isomorphism from the identity, their ratio is
an involution. -/
theorem natural_square_defect_involution {C : Type u} [Category.{v} C]
    (F : C ⥤ C) (a : 𝟭 C ≅ F) (X : C) (b : X ≅ F.obj X)
    (hsq : ((a.app X).hom ≫ F.map (a.app X).hom) = b.hom ≫ F.map b.hom) :
    let d := (a.app X) ≪≫ b.symm
    d.hom ≫ d.hom = 𝟙 X := by
  let d := (a.app X) ≪≫ b.symm
  change d.hom ≫ d.hom = 𝟙 X
  have hd : d.hom ≫ b.hom = (a.app X).hom := by simp [d, Category.assoc]
  have hn := a.hom.naturality d.hom
  simp only [Functor.id_map] at hn
  change d.hom ≫ (a.app X).hom = (a.app X).hom ≫ F.map d.hom at hn
  have hc : b.hom ≫ F.map d.hom = d.hom ≫ b.hom := by
    calc
      _ = d.inv ≫ (a.app X).hom ≫ F.map d.hom := by
        rw [← hd]
        simp [Category.assoc]
      _ = d.inv ≫ d.hom ≫ (a.app X).hom := by
        rw [← hn]
      _ = d.hom ≫ b.hom := by simp [hd, Category.assoc]
  apply (cancel_mono (b.hom ≫ F.map b.hom)).1
  calc
    (d.hom ≫ d.hom) ≫ (b.hom ≫ F.map b.hom) =
        d.hom ≫ (d.hom ≫ b.hom) ≫ F.map b.hom := by simp [Category.assoc]
    _ = d.hom ≫ (b.hom ≫ F.map d.hom) ≫ F.map b.hom := by rw [hc]
    _ = (d.hom ≫ b.hom) ≫ F.map (d.hom ≫ b.hom) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = b.hom ≫ F.map b.hom := by rw [hd, hsq]
    _ = 𝟙 X ≫ (b.hom ≫ F.map b.hom) := by simp

end PropertyF.Ground.Dimensions
