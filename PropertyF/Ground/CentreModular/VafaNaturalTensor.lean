module
public import PropertyF.Ground.CentreModular.VafaTensorBiproduct
public import PropertyF.Ground.CentreInduction.FiniteSum
public import PropertyF.Ground.Fusion.SemisimpleSplit

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Every base object is a finite iterated binary sum of simple objects. -/
theorem base_finite_simple_sum (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    CentreInduction.FiniteSimpleSum C.Obj X := by
  let m : C.Obj → ℕ := fun W => Module.finrank ℂ (W ⟶ W)
  induction X using (measure m).wf.induction with
  | h X ih =>
    by_cases hz : IsZero X
    · exact .zero hz
    · obtain ⟨i, hi⟩ := exists_positive_multiplicity C X hz
      let S := simples C i
      let : Simple S := simples_simple C i
      let : FiniteDimensional ℂ (S ⟶ X) := IsFusionCategory.hom_finite _ _
      obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hi
      let : Mono f := mono_of_nonzero_from_simple hf
      obtain ⟨r, hr⟩ := split_from_simple f hf
      let : IsSplitMono f := IsSplitMono.mk' { retraction := r, id := hr }
      let E := ShortComplex.cokernelSequence f
      let split : E.Splitting := ShortComplex.Splitting.ofExactOfRetraction E
        (ShortComplex.cokernelSequence_exact f) (retraction f)
        (IsSplitMono.id f) inferInstance
      let K := cokernel f
      let e : X ≅ S ⊞ K := split.isoBinaryBiproduct
      let : ∀ A B : C.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
      have hs : ¬ IsZero S := by
        intro h
        exact id_nonzero _ ((IsZero.iff_id_eq_zero _).mp h)
      have he : Module.finrank ℂ (X ⟶ X) = Module.finrank ℂ (S ⊞ K ⟶ S ⊞ K) :=
        (CategoryTheory.Linear.homCongr ℂ e e).finrank_eq
      have hk : m K < m X := by
        change Module.finrank ℂ (K ⟶ K) < Module.finrank ℂ (X ⟶ X)
        rw [he]
        exact CentreInduction.finrank_end_complement_lt _ K hs
      exact .cons (simples_simple C i) (ih K hk) ⟨e⟩

/-- Identity automorphisms have zero FP determinant. -/
theorem fpDeterminant_refl (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    fpDeterminant C X (Iso.refl X) = 0 := by
  have h := fpDeterminant_trans C X (Iso.refl X) (Iso.refl X)
  have h' : fpDeterminant C X (Iso.refl X) =
      fpDeterminant C X (Iso.refl X) + fpDeterminant C X (Iso.refl X) := by
    simpa using h
  have h'' := (add_zero (fpDeterminant C X (Iso.refl X))).trans h'
  exact (add_left_cancel h'').symm

/-- The tensor determinant rule holds on any simple object. -/
theorem fpDeterminant_tensor_of_simple (C : BraidedFusionCategory.{v,u})
    (X S : C.Obj) [Simple S] (a : S ≅ S) :
    fpDeterminant C (X ⊗ S) (Iso.refl X ⊗ᵢ a) =
      fpDimension C X • fpDeterminant C S a := by
  let : FiniteDimensional ℂ (S ⟶ S) := IsFusionCategory.hom_finite _ _
  obtain ⟨z, hz⟩ := endomorphism_simple_eq_smul_id ℂ a.hom
  have hne : z ≠ 0 := by
    intro h
    have ha : a.hom = 0 := by simpa [h] using hz.symm
    have hh := a.hom_inv_id
    simp [ha] at hh
    exact id_nonzero _ hh.symm
  have ha : a = scalarIso C S (Units.mk0 z hne) := by
    apply Iso.ext
    exact hz.symm
  rw [ha]
  exact fpDeterminant_tensor_scalar C X S _

/-- A natural automorphism acts block-diagonally on a binary biproduct. -/
theorem natural_app_biprod (C : BraidedFusionCategory.{v,u})
    (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (S K : C.Obj) :
    η.app (S ⊞ K) = biprod.mapIso (η.app S) (η.app K) := by
  apply Iso.ext
  apply biprod.hom_ext'
  · have h := η.hom.naturality (biprod.inl : S ⟶ S ⊞ K)
    change biprod.inl ≫ (η.app (S ⊞ K)).hom = (η.app S).hom ≫ biprod.inl at h
    simpa using h
  · have h := η.hom.naturality (biprod.inr : K ⟶ S ⊞ K)
    change biprod.inr ≫ (η.app (S ⊞ K)).hom = (η.app K).hom ≫ biprod.inr at h
    simpa using h

/-- Naturality transports a component along any object isomorphism. -/
theorem natural_app_conjugate (C : BraidedFusionCategory.{v,u})
    (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) {Y Z : C.Obj} (e : Y ≅ Z) :
    η.app Y = e ≪≫ η.app Z ≪≫ e.symm := by
  apply Iso.ext
  have h := η.hom.naturality e.hom
  change e.hom ≫ (η.app Z).hom = (η.app Y).hom ≫ e.hom at h
  change (η.app Y).hom = e.hom ≫ (η.app Z).hom ≫ e.inv
  rw [← Category.assoc, h]
  simp [Category.assoc]

/-- Tensoring a conjugated automorphism conjugates its tensor extension. -/
theorem tensor_conjugate_iso (C : BraidedFusionCategory.{v,u})
    (X : C.Obj) {Y Z : C.Obj} (e : Y ≅ Z) (a : Z ≅ Z) :
    (Iso.refl X ⊗ᵢ (e ≪≫ a ≪≫ e.symm)) =
      (Iso.refl X ⊗ᵢ e) ≪≫ (Iso.refl X ⊗ᵢ a) ≪≫ (Iso.refl X ⊗ᵢ e).symm := by
  apply Iso.ext
  simp [tensorIso_hom, tensorHom_def, whiskerLeft_comp]

/-- The categorical FP determinant tensor rule holds for components of
any natural automorphism, by semisimplicity. -/
theorem fpDeterminant_tensor_natural (C : BraidedFusionCategory.{v,u})
    (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (X Y : C.Obj) :
    fpDeterminant C (X ⊗ Y) (Iso.refl X ⊗ᵢ η.app Y) =
      fpDimension C X • fpDeterminant C Y (η.app Y) := by
  have hY := base_finite_simple_sum C Y
  induction hY with
  | @zero W hz =>
    have hη : η.app W = Iso.refl W := by
      apply Iso.ext
      exact hz.eq_of_src _ _
    rw [hη]
    have ht : Iso.refl X ⊗ᵢ Iso.refl W = Iso.refl (X ⊗ W) := by
      apply Iso.ext
      simp
    rw [ht, fpDeterminant_refl, fpDeterminant_refl, smul_zero]
  | @cons Y S K hs hk he ih =>
    obtain ⟨e⟩ := he
    have hS : fpDeterminant C (X ⊗ S) (Iso.refl X ⊗ᵢ η.app S) =
        fpDimension C X • fpDeterminant C S (η.app S) := by
      let : Simple S := hs
      exact fpDeterminant_tensor_of_simple C X S (η.app S)
    have hsum := fpDeterminant_tensor_biprod C X S K (η.app S) (η.app K) hS ih
    rw [← natural_app_biprod] at hsum
    have hη := natural_app_conjugate C η e
    rw [hη, tensor_conjugate_iso]
    have hl := fpDeterminant_conjugate C (Iso.refl X ⊗ᵢ e).symm
      (Iso.refl X ⊗ᵢ η.app (S ⊞ K))
    have hr := fpDeterminant_conjugate C e.symm (η.app (S ⊞ K))
    change fpDeterminant C (X ⊗ Y) ((Iso.refl X ⊗ᵢ e) ≪≫
      (Iso.refl X ⊗ᵢ η.app (S ⊞ K)) ≪≫ (Iso.refl X ⊗ᵢ e).symm) = _ at hl
    change fpDeterminant C Y (e ≪≫ η.app (S ⊞ K) ≪≫ e.symm) = _ at hr
    rw [hl, hr]
    exact hsum

end PropertyF.Ground.CentreModular
