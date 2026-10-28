module
public import PropertyF.Ground.Modular.BraidIso

/-!
# Braid images under braided functors

The strong monoidal comparison identifies tensor powers and intertwines the
adjacent generators. A faithful braided functor therefore identifies the braid
image groups, and an essentially surjective one covers every target object.
-/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open CategoryTheory.Functor.Monoidal CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Functor.OplaxMonoidal
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular
universe v u v' u'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
variable (F : C ⥤ D) [F.Braided]
/-- The iterated strong-monoidal comparison for right-associated tensor powers. -/
def tensorPowerComparison (X : C) : ∀ n, tensorPower (F.obj X) n ≅ F.obj (tensorPower X n)
 | 0 => εIso F
 | n+1 => (Iso.refl (F.obj X) ⊗ᵢ tensorPowerComparison X n) ≪≫ μIso F X (tensorPower X n)

/-- A braided functor preserves the first adjacent braid, including associators. -/
lemma braid_first_functor (X A : C) :
    (firstBraiding (F.obj X) (F.obj A)).hom ≫
      (F.obj X ◁ (μIso F X A).hom) ≫ (μIso F X (X ⊗ A)).hom =
      (F.obj X ◁ (μIso F X A).hom) ≫ (μIso F X (X ⊗ A)).hom ≫
        F.map (firstBraiding X A).hom := by
  dsimp only [firstBraiding]
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
    Functor.map_comp, map_associator_inv, map_associator, map_tensor,
    Functor.map_braiding, μIso_hom, Category.assoc]
  simp only [μ_δ_assoc, whiskerLeft_μ_δ_assoc]
  simp only [tensorHom_id]
  rw [F.map_id A]
  simp only [tensorHom_id, ← comp_whiskerRight_assoc]
  simp only [Category.assoc, μ_δ_assoc, μ_δ, Category.comp_id]


/-- The first adjacent braid remains natural after comparing the remaining tensor factors. -/
lemma braid_first_with_comparison (X A : C) {B : D} (g : B ≅ F.obj A) :
    (firstBraiding (F.obj X) B).hom ≫
      (F.obj X ◁ (F.obj X ◁ g.hom)) ≫ (F.obj X ◁ (μIso F X A).hom) ≫
        (μIso F X (X ⊗ A)).hom =
      (F.obj X ◁ (F.obj X ◁ g.hom)) ≫ (F.obj X ◁ (μIso F X A).hom) ≫
        (μIso F X (X ⊗ A)).hom ≫
        F.map (firstBraiding X A).hom := by
  have hn := braid_first (Iso.refl (F.obj X)) g
  simp only [tensorIso_hom, Iso.refl_hom, id_tensorHom] at hn
  rw [← Category.assoc, hn]
  simpa only [Category.assoc] using
    congrArg (fun k => (F.obj X ◁ (F.obj X ◁ g.hom)) ≫ k) (braid_first_functor F X A)


/-- Functoriality of the first generator on any tensor power. -/
lemma braid_first_power (X : C) (n : ℕ) :
    (braidGenerator (F.obj X) n 0).asIso.hom ≫ (tensorPowerComparison F X (n+2)).hom =
      (tensorPowerComparison F X (n+2)).hom ≫ F.map (braidGenerator X n 0).asIso.hom := by
  rw [braidGenerator_zero, braidGenerator_zero]
  let e := (Iso.refl (F.obj X) ⊗ᵢ ((Iso.refl (F.obj X) ⊗ᵢ tensorPowerComparison F X n) ≪≫
    μIso F X (tensorPower X n))) ≪≫ μIso F X (X ⊗ tensorPower X n)
  change (firstBraiding (F.obj X) (tensorPower (F.obj X) n)).hom ≫ e.hom =
    e.hom ≫ F.map (firstBraiding X (tensorPower X n)).hom
  simp only [e, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom, whiskerLeft_comp,
    Category.assoc]
  simpa only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Category.assoc] using
    braid_first_with_comparison F X (tensorPower X n) (tensorPowerComparison F X n)

/-- Every adjacent generator commutes with the tensor-power comparison. -/
theorem braidGenerator_functor (X : C) (n : ℕ) (i : Fin (n + 1)) :
    (braidGenerator (F.obj X) n i).asIso.hom ≫ (tensorPowerComparison F X (n+2)).hom =
      (tensorPowerComparison F X (n+2)).hom ≫ F.map (braidGenerator X n i).asIso.hom := by
  induction n with
  | zero =>
    simpa only [Fin.eq_zero i] using braid_first_power F X 0
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact braid_first_power F X (n+1)
    · change (𝟙 (F.obj X) ⊗ₘ (braidGenerator (F.obj X) n j).asIso.hom) ≫
          ((Iso.refl (F.obj X) ⊗ᵢ tensorPowerComparison F X (n+2)) ≪≫ μIso F X (tensorPower X (n+2))).hom =
        ((Iso.refl (F.obj X) ⊗ᵢ tensorPowerComparison F X (n+2)) ≪≫ μIso F X (tensorPower X (n+2))).hom ≫
          F.map (𝟙 X ⊗ₘ (braidGenerator X n j).asIso.hom)
      simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom, μIso_hom]
      rw [← Category.assoc, ← whiskerLeft_comp, ih, whiskerLeft_comp, Category.assoc,
        μ_natural_right]
      simp [Category.assoc]


/-- The functor map followed by the tensor-power comparison. -/
def braidAutMap (X : C) (n : ℕ) : Aut (tensorPower X (n+2)) →*
    Aut (tensorPower (F.obj X) (n+2)) :=
  ((tensorPowerComparison F X (n+2)).symm.conjAut.toMonoidHom).comp
    (F.mapAut (tensorPower X (n+2)))

/-- The induced map on automorphisms carries each braid generator to its namesake. -/
lemma braidAutMap_generator (X : C) (n : ℕ) (i : Fin (n+1)) :
    braidAutMap F X n (braidGenerator X n i) = braidGenerator (F.obj X) n i := by
  apply Aut.ext
  apply Iso.ext
  simp only [braidAutMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Iso.conjAut_apply, Iso.trans_hom, Iso.symm_hom, Functor.mapAut]
  change (tensorPowerComparison F X (n+2)).hom ≫ F.map (braidGenerator X n i).asIso.hom ≫
      (tensorPowerComparison F X (n+2)).inv = (braidGenerator (F.obj X) n i).asIso.hom
  rw [← Category.assoc, ← braidGenerator_functor F X n i, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Faithfulness makes the induced automorphism map injective. -/
lemma braidAutMap_injective (X : C) (n : ℕ) [F.Faithful] :
    Function.Injective (braidAutMap F X n) := fun _ _ h ↦
  Aut.ext (Iso.ext (F.map_injective (congrArg
    (fun a : Aut (F.obj (tensorPower X (n+2))) => a.asIso.hom)
    ((tensorPowerComparison F X (n+2)).symm.conjAut.injective h))))

/-- The functor map sends the source braid-image subgroup onto the target
braid-image subgroup, even if the functor is not faithful. -/
theorem braidImage_map_eq (X : C) (n : ℕ) :
    (braidImage X n).map (braidAutMap F X n) = braidImage (F.obj X) n := by
  rw [braidImage, MonoidHom.map_closure, ← Set.range_comp,
    show (braidAutMap F X n ∘ braidGenerator X n) = braidGenerator (F.obj X) n from
      funext (braidAutMap_generator F X n)]
  rfl

/-- A braided functor induces a homomorphism on braid-image groups. -/
def braidImageFunctorMap (X : C) (n : ℕ) : braidImage X n →* braidImage (F.obj X) n :=
  ((braidAutMap F X n).comp (braidImage X n).subtype).codRestrict _ (by
    intro a
    rw [← braidImage_map_eq F X n]
    exact Subgroup.mem_map.mpr ⟨a, a.property, rfl⟩)

/-- The map on braid-image groups is always surjective. -/
theorem braidImageFunctorMap_surjective (X : C) (n : ℕ) :
    Function.Surjective (braidImageFunctorMap F X n) := fun y ↦
  (Subgroup.mem_map.mp (show
    (y : Aut (tensorPower (F.obj X) (n + 2))) ∈ (braidImage X n).map (braidAutMap F X n) from
      (braidImage_map_eq F X n).symm ▸ y.property)).elim fun a ⟨ha, hy⟩ ↦
    ⟨⟨a, ha⟩, Subtype.ext hy⟩

/-- A braided functor preserves finiteness of each object's braid images. -/
theorem objectPropertyF_functor (X : C) (hX : ObjectPropertyF X) :
    ObjectPropertyF (F.obj X) := fun n ↦
  letI : Finite (braidImage X n) := hX n
  Finite.of_surjective (braidImageFunctorMap F X n) (braidImageFunctorMap_surjective F X n)

/-- A faithful braided functor induces isomorphisms on braid-image groups. -/
def braidImageFunctorIso (X : C) (n : ℕ) [F.Faithful] :
    braidImage X n ≃* braidImage (F.obj X) n :=
  ((braidImage X n).equivMapOfInjective (braidAutMap F X n) (braidAutMap_injective F X n)).trans
    (MulEquiv.subgroupCongr (braidImage_map_eq F X n))


/-- Essential surjectivity handles arbitrary target objects. -/
theorem braidImages_of_essentiallySurjective [F.Faithful] [F.EssSurj]
    (Y : D) (n : ℕ) : ∃ X : C, Nonempty (braidImage Y n ≃* braidImage X n) :=
  ⟨F.objPreimage Y, ⟨(braidImageIso (F.objObjPreimageIso Y) n).symm.trans
    (braidImageFunctorIso F (F.objPreimage Y) n).symm⟩⟩

end PropertyF.Ground.Modular
