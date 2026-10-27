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
    ((α_ (F.obj X) (F.obj X) (F.obj A)).symm ≪≫
      ((β_ (F.obj X) (F.obj X)) ⊗ᵢ Iso.refl (F.obj A)) ≪≫
       α_ (F.obj X) (F.obj X) (F.obj A)).hom ≫
      (F.obj X ◁ (μIso F X A).hom) ≫ (μIso F X (X ⊗ A)).hom =
      (F.obj X ◁ (μIso F X A).hom) ≫ (μIso F X (X ⊗ A)).hom ≫
        F.map (((α_ X X A).symm ≪≫ ((β_ X X) ⊗ᵢ Iso.refl A) ≪≫ α_ X X A).hom) := by
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
    ((α_ (F.obj X) (F.obj X) B).symm ≪≫
      ((β_ (F.obj X) (F.obj X)) ⊗ᵢ Iso.refl B) ≪≫
       α_ (F.obj X) (F.obj X) B).hom ≫
      (F.obj X ◁ (F.obj X ◁ g.hom)) ≫ (F.obj X ◁ (μIso F X A).hom) ≫
        (μIso F X (X ⊗ A)).hom =
      (F.obj X ◁ (F.obj X ◁ g.hom)) ≫ (F.obj X ◁ (μIso F X A).hom) ≫
        (μIso F X (X ⊗ A)).hom ≫
        F.map (((α_ X X A).symm ≪≫ ((β_ X X) ⊗ᵢ Iso.refl A) ≪≫ α_ X X A).hom) := by
  have hn := braid_first (Iso.refl (F.obj X)) g
  simp only [tensorIso_hom, Iso.refl_hom, id_tensorHom] at hn
  simp only [← Category.assoc, hn]
  have h := congrArg (fun k => (F.obj X ◁ (F.obj X ◁ g.hom)) ≫ k)
    (braid_first_functor F X A)
  simpa only [Category.assoc] using h


/-- Functoriality of the first generator on any tensor power. -/
lemma braid_first_power (X : C) (n : ℕ) :
    (braidGenerator (F.obj X) n 0).asIso.hom ≫ (tensorPowerComparison F X (n+2)).hom =
      (tensorPowerComparison F X (n+2)).hom ≫ F.map (braidGenerator X n 0).asIso.hom := by
  have hgen (Z : C) (k : ℕ) : (braidGenerator Z k 0).asIso.hom =
      ((α_ Z Z (tensorPower Z k)).symm ≪≫ ((β_ Z Z) ⊗ᵢ Iso.refl (tensorPower Z k)) ≪≫
        α_ Z Z (tensorPower Z k)).hom := by
    cases k <;> rfl
  have hgenD (Z : D) (k : ℕ) : (braidGenerator Z k 0).asIso.hom =
      ((α_ Z Z (tensorPower Z k)).symm ≪≫ ((β_ Z Z) ⊗ᵢ Iso.refl (tensorPower Z k)) ≪≫
        α_ Z Z (tensorPower Z k)).hom := by
    cases k <;> rfl
  rw [hgenD, hgen]
  change ((α_ (F.obj X) (F.obj X) (tensorPower (F.obj X) n)).symm ≪≫
      ((β_ (F.obj X) (F.obj X)) ⊗ᵢ Iso.refl (tensorPower (F.obj X) n)) ≪≫
       α_ (F.obj X) (F.obj X) (tensorPower (F.obj X) n)).hom ≫
      ((Iso.refl (F.obj X) ⊗ᵢ ((Iso.refl (F.obj X) ⊗ᵢ tensorPowerComparison F X n) ≪≫
        μIso F X (tensorPower X n))) ≪≫ μIso F X (X ⊗ tensorPower X n)).hom =
      ((Iso.refl (F.obj X) ⊗ᵢ ((Iso.refl (F.obj X) ⊗ᵢ tensorPowerComparison F X n) ≪≫
        μIso F X (tensorPower X n))) ≪≫ μIso F X (X ⊗ tensorPower X n)).hom ≫
      F.map (((α_ X X (tensorPower X n)).symm ≪≫ ((β_ X X) ⊗ᵢ Iso.refl (tensorPower X n)) ≪≫
        α_ X X (tensorPower X n)).hom)
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom, whiskerLeft_comp,
    Category.assoc]
  have h := braid_first_with_comparison F X (tensorPower X n) (tensorPowerComparison F X n)
  simpa only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Category.assoc] using h

/-- Every adjacent generator commutes with the tensor-power comparison. -/
theorem braidGenerator_functor (X : C) (n : ℕ) (i : Fin (n + 1)) :
    (braidGenerator (F.obj X) n i).asIso.hom ≫ (tensorPowerComparison F X (n+2)).hom =
      (tensorPowerComparison F X (n+2)).hom ≫ F.map (braidGenerator X n i).asIso.hom := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact braid_first_power F X 0
  | succ n ih =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => exact braid_first_power F X (n+1)
    | succ i =>
      change (𝟙 (F.obj X) ⊗ₘ (braidGenerator (F.obj X) n ⟨i, Nat.lt_of_succ_lt_succ hi⟩).asIso.hom) ≫
          ((Iso.refl (F.obj X) ⊗ᵢ tensorPowerComparison F X (n+2)) ≪≫ μIso F X (tensorPower X (n+2))).hom =
        ((Iso.refl (F.obj X) ⊗ᵢ tensorPowerComparison F X (n+2)) ≪≫ μIso F X (tensorPower X (n+2))).hom ≫
          F.map (𝟙 X ⊗ₘ (braidGenerator X n ⟨i, Nat.lt_of_succ_lt_succ hi⟩).asIso.hom)
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
  rw [← Category.assoc, ← braidGenerator_functor F X n i, Category.assoc]
  simp

/-- Faithfulness makes the induced automorphism map injective. -/
lemma braidAutMap_injective (X : C) (n : ℕ) [F.Faithful] :
    Function.Injective (braidAutMap F X n) := by
  intro a b h
  have h' := ((tensorPowerComparison F X (n+2)).symm.conjAut.injective h)
  apply Aut.ext
  apply Iso.ext
  apply F.map_injective
  exact congrArg (fun a : Aut (F.obj (tensorPower X (n+2))) => a.asIso.hom) h'

/-- A faithful braided functor induces isomorphisms on braid-image groups. -/
def braidImageFunctorIso (X : C) (n : ℕ) [F.Faithful] :
    braidImage X n ≃* braidImage (F.obj X) n := by
  let m := braidAutMap F X n
  have hm : (braidImage X n).map m = braidImage (F.obj X) n := by
    rw [braidImage, MonoidHom.map_closure, ← Set.range_comp]
    have heq : (m ∘ braidGenerator X n) = braidGenerator (F.obj X) n := by
      funext i
      exact braidAutMap_generator F X n i
    rw [heq]
    rfl
  exact ((braidImage X n).equivMapOfInjective m (braidAutMap_injective F X n)).trans
    (MulEquiv.subgroupCongr hm)


/-- Essential surjectivity handles arbitrary target objects. -/
theorem braidImages_of_essentiallySurjective [F.Faithful] [F.EssSurj]
    (Y : D) (n : ℕ) : ∃ X : C, Nonempty (braidImage Y n ≃* braidImage X n) := by
  let X := F.objPreimage Y
  exact ⟨X, ⟨(braidImageIso (F.objObjPreimageIso Y) n).symm.trans
    (braidImageFunctorIso F X n).symm⟩⟩

/-- The conjugate braid-image input follows from the actual braided equivalence;
semilinearity is not needed for this group-theoretic conclusion. -/
theorem conjugate_images {C D : BraidedFusionCategory.{v,u}} {σ : ℂ ≃+* ℂ}
    (h : GaloisConjugate C D σ) (Y : D.Obj) (n : ℕ) :
    ∃ X : C.Obj, Nonempty (braidImage Y n ≃* braidImage X n) := by
  let _ := h.monoidal
  let _ := h.braided
  exact braidImages_of_essentiallySurjective h.equivalence.functor Y n

end PropertyF.Ground.Modular
