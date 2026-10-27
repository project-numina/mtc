module
public import PropertyF.Ground.Centre.Product
public import PropertyF.Ground.Centre.ReverseBraiding
public import PropertyF.Ground.Modular.BraidFunctor
public import PropertyF.Ground.Cabling.Naturality

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

/-- The projected first component of a product braid lies in the first image. -/
theorem fstBraidMap_mem (X Y : C) (n : ℕ) :
    braidImage (X,Y) n ≤ (braidImage X n).comap (fstBraidMap X Y n) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  change fstBraidMap X Y n (braidGenerator (X,Y) n i) ∈ braidImage X n
  rw [fstBraidMap_generator]
  exact Subgroup.subset_closure ⟨i, rfl⟩

/-- The projected second component lies in the original, unreversed image. -/
theorem sndBraidMap_mem (X Y : C) (n : ℕ) :
    braidImage (X,Y) n ≤ (braidImage Y n).comap (sndBraidMap X Y n) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  change sndBraidMap X Y n (braidGenerator (X,Y) n i) ∈ braidImage Y n
  rw [sndBraidMap_generator]
  exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i, rfl⟩)

/-- The actual product braid image maps into the product of the two factor images. -/
def productBraidMap (X Y : C) (n : ℕ) :
    braidImage (X,Y) n →* (braidImage X n × braidImage Y n) where
  toFun a := (⟨fstBraidMap X Y n a, fstBraidMap_mem X Y n a.property⟩,
    ⟨sndBraidMap X Y n a, sndBraidMap_mem X Y n a.property⟩)
  map_one' := by ext <;> simp
  map_mul' := by intro a b; ext <;> simp

/-- The product braid image is a subgroup of the product of its two factor images. -/
theorem productBraidMap_injective (X Y : C) (n : ℕ) :
    Function.Injective (productBraidMap X Y n) := by
  intro a b hab
  apply Subtype.ext
  apply projections_jointly_injective X Y n
  apply Prod.ext
  · exact congrArg (fun x : braidImage X n × braidImage Y n => x.1.val) hab
  · exact congrArg (fun x : braidImage X n × braidImage Y n => x.2.val) hab

/-- Finite factor images imply a finite mixed-product braid image. -/
theorem product_braidImage_finite (X Y : C) (n : ℕ)
    [Finite (braidImage X n)] [Finite (braidImage Y n)] :
    Finite (braidImage (X,Y) n) :=
  Finite.of_injective (productBraidMap X Y n) (productBraidMap_injective X Y n)

/-- Tensoring the positive and negative images preserves finite braid images. -/
theorem productFunctor_objectPropertyF (X Y : C)
    (hX : ObjectPropertyF X) (hY : ObjectPropertyF Y) :
    ObjectPropertyF (productFunctor.obj (X,Y)) := by
  let _ : (productFunctor (C := C)).Braided := productBraided
  apply Modular.objectPropertyF_functor (productFunctor (C := C)) (X,Y)
  intro n
  let _ := hX n
  let _ := hY n
  exact product_braidImage_finite X Y n

/-- The centre image of a pair has braid image a quotient of a subgroup of
its two source braid images. This does not require finite images. -/
theorem productFunctor_image_quotient (X Y : C) (n : ℕ) :
    ∃ H : Subgroup (braidImage X n × braidImage Y n),
      ∃ q : H →* braidImage (productFunctor.obj (X,Y)) n, Function.Surjective q := by
  let _ : (productFunctor (C := C)).Braided := productBraided
  let e := MonoidHom.ofInjective (productBraidMap_injective X Y n)
  let q := (Modular.braidImageFunctorMap (productFunctor (C := C)) (X,Y) n).comp
    e.symm.toMonoidHom
  refine ⟨(productBraidMap X Y n).range, q, ?_⟩
  intro a
  obtain ⟨b, hb⟩ := Modular.braidImageFunctorMap_surjective (productFunctor (C := C)) (X,Y) n a
  exact ⟨e b, by simpa [q] using hb⟩

/-- Every retract of a product-functor image has the same quotient-of-a-subgroup
presentation, without a finiteness assumption. -/
theorem productFunctor_retract_image_quotient (X Y : C) (Z : CategoryTheory.Center C)
    (r : CategoryTheory.Retract Z (productFunctor.obj (X,Y))) (n : ℕ) :
    ∃ H : Subgroup (braidImage X n × braidImage Y n),
      ∃ q : H →* braidImage Z n, Function.Surjective q := by
  obtain ⟨H, q, hq⟩ := productFunctor_image_quotient X Y n
  exact ⟨H, (braidImageRetractMap r n).comp q,
    (braidImageRetractMap_surjective r n).comp hq⟩

/-- Property F transfers to every retract of a product-functor image. -/
theorem productFunctor_retract_objectPropertyF (X Y : C) (Z : CategoryTheory.Center C)
    (r : CategoryTheory.Retract Z (productFunctor.obj (X,Y)))
    (hX : ObjectPropertyF X) (hY : ObjectPropertyF Y) : ObjectPropertyF Z :=
  objectPropertyF_of_retract r (productFunctor_objectPropertyF X Y hX hY)

end PropertyF.Ground.Centre
