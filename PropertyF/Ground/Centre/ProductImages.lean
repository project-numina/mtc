module
public import PropertyF.Ground.Centre.Product
public import PropertyF.Ground.Centre.ReverseBraiding
public import PropertyF.Ground.Modular.BraidFunctor

/-! Braid images in the ordinary product with mixed braiding. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [bc : BraidedCategory C]
local instance : BraidedCategory (C × C) := mixedBraiding

instance fstMonoidal : (CategoryTheory.Prod.fst C C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso := fun _ _ => Iso.refl _ }

instance sndMonoidal : (CategoryTheory.Prod.snd C C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso := fun _ _ => Iso.refl _ }

/-- The first projection preserves the mixed braiding. -/
instance fstBraided : (CategoryTheory.Prod.fst C C).Braided where
  braided X Y := by
    change 𝟙 _ ≫ (β_ X.1 Y.1).hom = (β_ X.1 Y.1).hom ≫ 𝟙 _
    simp

/-- The second projection preserves the reversed braiding. -/
@[instance_reducible]
def sndBraided : @Functor.Braided (C × C) _ _ (mixedBraiding (C := C))
    C _ _ (CategoryTheory.reverseBraiding C) (CategoryTheory.Prod.snd C C) := by
  let mix := mixedBraiding (C := C)
  letI : BraidedCategory C := CategoryTheory.reverseBraiding C
  letI : BraidedCategory (C × C) := mix
  refine { braided := ?_ }
  intro X Y
  change 𝟙 _ ≫ (@BraidedCategory.braiding C _ _ bc Y.2 X.2).inv =
    (@BraidedCategory.braiding C _ _ bc Y.2 X.2).inv ≫ 𝟙 _
  simp

/-- First projection of the braid automorphism after tensor-power comparison. -/
def fstBraidMap (X Y : C) (n : ℕ) :
    Aut (tensorPower (X,Y) (n+2)) →* Aut (tensorPower X (n+2)) :=
  Modular.braidAutMap (CategoryTheory.Prod.fst C C) (X,Y) n

/-- Second projection, using the reversed braiding. -/
def sndBraidMap (X Y : C) (n : ℕ) :
    Aut (tensorPower (X,Y) (n+2)) →* Aut (tensorPower Y (n+2)) :=
  @Modular.braidAutMap (C × C) _ _ (mixedBraiding (C := C)) C _ _
    (CategoryTheory.reverseBraiding C) (CategoryTheory.Prod.snd C C) sndBraided (X,Y) n

theorem fstBraidMap_generator (X Y : C) (n : ℕ) (i : Fin (n+1)) :
    fstBraidMap X Y n (braidGenerator (X,Y) n i) = braidGenerator X n i :=
  Modular.braidAutMap_generator (CategoryTheory.Prod.fst C C) (X,Y) n i

theorem sndBraidMap_generator (X Y : C) (n : ℕ) (i : Fin (n+1)) :
    sndBraidMap X Y n (braidGenerator (X,Y) n i) = (braidGenerator Y n i)⁻¹ := by
  rw [← reverse_braidGenerator]
  exact @Modular.braidAutMap_generator (C × C) _ _ (mixedBraiding (C := C)) C _ _
    (CategoryTheory.reverseBraiding C) (CategoryTheory.Prod.snd C C) sndBraided (X,Y) n i

/-- The two projected automorphisms jointly detect an automorphism of a tensor power. -/
theorem projections_jointly_injective (X Y : C) (n : ℕ) :
    Function.Injective (fun a : Aut (tensorPower (X,Y) (n+2)) =>
      (fstBraidMap X Y n a, sndBraidMap X Y n a)) := by
  intro a b h
  have hf := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  let p := Modular.tensorPowerComparison (CategoryTheory.Prod.fst C C) (X,Y) (n+2)
  let q := @Modular.tensorPowerComparison (C × C) _ _ (mixedBraiding (C := C)) C _ _
    (CategoryTheory.reverseBraiding C) (CategoryTheory.Prod.snd C C) sndBraided (X,Y) (n+2)
  have hf' : (Functor.mapAut (tensorPower (X,Y) (n+2)) (CategoryTheory.Prod.fst C C)) a =
      (Functor.mapAut (tensorPower (X,Y) (n+2)) (CategoryTheory.Prod.fst C C)) b := by
    apply p.symm.conjAut.injective
    exact hf
  have hs' : (Functor.mapAut (tensorPower (X,Y) (n+2)) (CategoryTheory.Prod.snd C C)) a =
      (Functor.mapAut (tensorPower (X,Y) (n+2)) (CategoryTheory.Prod.snd C C)) b := by
    apply q.symm.conjAut.injective
    exact hs
  apply Aut.ext
  apply Iso.ext
  apply Prod.ext
  · exact congrArg (fun z => z.asIso.hom) hf'
  · exact congrArg (fun z => z.asIso.hom) hs'

/-- The actual braid image of a mixed product object embeds in the product of
its two factor images. -/
theorem product_braidImage_finite (X Y : C) (n : ℕ)
    [Finite (braidImage X n)] [Finite (braidImage Y n)] :
    Finite (braidImage (X,Y) n) := by
  have hf : braidImage (X,Y) n ≤ (braidImage X n).comap (fstBraidMap X Y n) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change fstBraidMap X Y n (braidGenerator (X,Y) n i) ∈ braidImage X n
    rw [fstBraidMap_generator]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hs : braidImage (X,Y) n ≤ (braidImage Y n).comap (sndBraidMap X Y n) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change sndBraidMap X Y n (braidGenerator (X,Y) n i) ∈ braidImage Y n
    rw [sndBraidMap_generator]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i, rfl⟩)
  let j : braidImage (X,Y) n → braidImage X n × braidImage Y n :=
    fun a => (⟨fstBraidMap X Y n a, hf a.property⟩,
      ⟨sndBraidMap X Y n a, hs a.property⟩)
  apply Finite.of_injective j
  intro a b hab
  apply Subtype.ext
  apply projections_jointly_injective X Y n
  apply Prod.ext
  · exact congrArg (fun x : braidImage X n × braidImage Y n => x.1.val) hab
  · exact congrArg (fun x : braidImage X n × braidImage Y n => x.2.val) hab

end PropertyF.Ground.Centre
