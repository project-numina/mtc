module
public import MTC.PropertyF.Pivotal.MonoidalDual
public import MTC.CategoryTheory.Dimensions.SquaredNorm
/-! # Right quantum trace under strong monoidal functors -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open MTC.CategoryTheory.Dimensions MTC.Braided MTC.PropertyF.Pivotal
namespace MTC.PropertyF.Pivotal
universe v u v' u'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RigidCategory D]
/-- The canonical double-dual comparison of a monoidal functor. -/
def transformedDualIso (F : C ⥤ D) [F.Monoidal] (X : C) :
 F.obj ((Xᘁ)ᘁ) ≅ ((F.obj X)ᘁ)ᘁ :=
  monoidalFunctorDualIso F (Xᘁ) ≪≫ rightDualIsoMap (monoidalFunctorDualIso F X).symm
/-- Transport a double-dual isomorphism along the monoidal functor. -/
def transformedDoubleDual (F : C ⥤ D) [F.Monoidal] {X : C} (j : X ≅ (Xᘁ)ᘁ) :
 F.obj X ≅ ((F.obj X)ᘁ)ᘁ := F.mapIso j ≪≫ transformedDualIso F X
/-- The actual right quantum trace is preserved through a strong monoidal
functor, up to its unit isomorphism. -/
theorem monoidalFunctor_rightQuantumTrace (F : C ⥤ D) [F.Monoidal] {X : C} (j : X ≅ (Xᘁ)ᘁ) :
 ε F ≫ F.map (rightQuantumTrace j).asHom ≫ η F = (rightQuantumTrace (transformedDoubleDual F j)).asHom := by
  let e := monoidalFunctorDualIso F X
  let e' := monoidalFunctorDualIso F (Xᘁ)
  let u := F.map j.hom
  let J := transformedDoubleDual F j
  have htrans : u ≫ e'.hom = J.hom ≫ (e.homᘁ) := by
    apply (Iso.eq_comp_inv (rightDualIsoMap e.symm)).2
    simp [J, transformedDoubleDual, transformedDualIso, rightDualIsoMap, e, e', u, Category.assoc]
  have heval : (e'.hom ▷ F.obj (Xᘁ)) ≫ ε_ (F.obj (Xᘁ)) ((F.obj (Xᘁ))ᘁ) =
      μ F ((Xᘁ)ᘁ) (Xᘁ) ≫ F.map (ε_ (Xᘁ) ((Xᘁ)ᘁ)) ≫ η F :=
    monoidalFunctorDual_evaluation F (Xᘁ)
  have hc := monoidalFunctor_rightClosedDiagram F X (Xᘁ) ((Xᘁ)ᘁ) j.hom
  change (ε F ≫ F.map (rightQuantumTrace j).asHom ≫ η F) = _ at hc
  rw [← heval] at hc
  rw [hc]
  change (ε F ≫ F.map (η_ X (Xᘁ)) ≫ δ F X (Xᘁ)) ≫
     (u ⊗ₘ 𝟙 (F.obj (Xᘁ))) ≫ ((e'.hom ▷ F.obj (Xᘁ)) ≫ ε_ (F.obj (Xᘁ)) ((F.obj (Xᘁ))ᘁ)) = _
  simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, Category.assoc,
    ← comp_whiskerRight_assoc, htrans]
  have ht := trace_change_rightDual (exactPairingOfMonoidalFunctor F X (Xᘁ))
    (HasRightDual.exact (X := F.obj X)) J.hom
  change (ε F ≫ F.map (η_ X (Xᘁ)) ≫ δ F X (Xᘁ)) ≫
      ((J.hom ≫ e.homᘁ) ⊗ₘ 𝟙 (F.obj (Xᘁ))) ≫
        ε_ (F.obj (Xᘁ)) ((F.obj (Xᘁ))ᘁ) =
    η_ (F.obj X) ((F.obj X)ᘁ) ≫ (J.hom ⊗ₘ 𝟙 ((F.obj X)ᘁ)) ≫
      ε_ ((F.obj X)ᘁ) (((F.obj X)ᘁ)ᘁ) at ht
  simpa only [tensorHom_def, whiskerLeft_id, Category.comp_id, Category.assoc,
    rightQuantumTrace] using ht

/-- Double-dual transport commutes with inverse duality up to the canonical
comparison of the functor image of the dual. -/
theorem transformedDoubleDual_dual_natural (F : C ⥤ D) [F.Monoidal] {X : C}
    (j : X ≅ (Xᘁ)ᘁ) :
    (monoidalFunctorDualIso F X).hom ≫
        (rightDualIsoMap (transformedDoubleDual F j)).symm.hom =
      (transformedDoubleDual F (rightDualIsoMap j).symm).hom ≫
        (((monoidalFunctorDualIso F X).homᘁ)ᘁ) := by
  have hn := monoidalFunctorDualIso_natural F j.inv
  have h := congrArg (fun t => t ≫ (monoidalFunctorDualIso F (Xᘁ)).invᘁ ≫
    ((monoidalFunctorDualIso F X).homᘁ)ᘁ) hn.symm
  simpa [transformedDoubleDual, transformedDualIso, rightDualIsoMap,
    comp_rightAdjointMate, Category.assoc] using h

/-- The actual left quantum trace is preserved through a strong monoidal
functor, up to its unit isomorphism. -/
theorem monoidalFunctor_leftQuantumTrace (F : C ⥤ D) [F.Monoidal] {X : C} (j : X ≅ (Xᘁ)ᘁ) :
 ε F ≫ F.map (leftQuantumTrace j).asHom ≫ η F = (leftQuantumTrace (transformedDoubleDual F j)).asHom := by
  rw [leftQuantumTrace_eq_rightDual, leftQuantumTrace_eq_rightDual]
  rw [monoidalFunctor_rightQuantumTrace]
  exact congrArg End.asHom
    (rightQuantumTrace_iso (monoidalFunctorDualIso F X) (transformedDoubleDual_dual_natural F j))


end MTC.PropertyF.Pivotal
end
