module
public import PropertyF.Ground.CentreInduction.FiniteSimples
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

section
open CategoryTheory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

/-- Induction sends every base object to an injective centre object. -/
theorem induction_injective (X : C.Obj) : Injective ((induction C).obj X) := by
  let : (induction C).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (actualAdjunction C)
  let : Injective X := object_injective C X
  infer_instance



end PropertyF.Ground.CentreInduction

end
end

/-! An injective-retract route to centre semisimplicity and fusion. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable {D : Type u} [Category.{v} D] [Abelian D] [MonoidalCategory D] [RigidCategory D]

omit [Abelian D] in
/-- Tensoring with any object preserves injectives in a rigid abelian category. -/
theorem tensor_preserves_injective (J U : D) [Injective J] : Injective (J ⊗ U) := by
  let L := tensorRight (ᘁU)
  let R := tensorRight U
  let adj : L ⊣ R := tensorRightAdjunction (ᘁU) U
  let : L.IsRightAdjoint := ⟨⟨tensorRight (ᘁ(ᘁU)), ⟨tensorRightAdjunction (ᘁ(ᘁU)) (ᘁU)⟩⟩⟩
  let : L.PreservesMonomorphisms := by infer_instance
  let : R.PreservesInjectiveObjects := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  exact R.injective_obj_of_injective (inferInstance : Injective J)

omit [Abelian D] in
/-- A unit retract of a tensor product with an injective makes every object injective. -/
theorem all_injective_of_unit_retract (J U : D) [Injective J]
    (r : Retract (𝟙_ D) (J ⊗ U)) (X : D) : Injective X := by
  let : Injective (J ⊗ U) := tensor_preserves_injective J U
  let : Injective (𝟙_ D) := r.injective
  let : Injective ((𝟙_ D) ⊗ X) := tensor_preserves_injective (𝟙_ D) X
  exact Injective.of_iso (λ_ X) inferInstance

omit [Abelian D] [MonoidalCategory D] [RigidCategory D] in
/-- Every monomorphism out of an injective object splits. -/
theorem mono_splits_of_all_injective {X Y : D} (f : X ⟶ Y) [Mono f]
    [Injective X] : IsSplitMono f := by
  obtain ⟨r, hr⟩ := Injective.factors (𝟙 X) f
  exact IsSplitMono.mk' { retraction := r, id := hr }

variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]

/-- A unit retract of an induced object makes every centre object injective. -/
theorem center_all_injective_of_unit_retract (X : C.Obj) (U : CategoryTheory.Center C.Obj)
    (r : Retract (𝟙_ (CategoryTheory.Center C.Obj)) ((induction C).obj X ⊗ U))
    (Z : CategoryTheory.Center C.Obj) : Injective Z := by
  let : Injective ((induction C).obj X) := induction_injective C X
  exact all_injective_of_unit_retract ((induction C).obj X) U r Z

/-- A unit retract of an induced object splits every centre monomorphism. -/
theorem center_mono_splits_of_unit_retract (X : C.Obj) (U : CategoryTheory.Center C.Obj)
    (r : Retract (𝟙_ (CategoryTheory.Center C.Obj)) ((induction C).obj X ⊗ U))
    {Z W : CategoryTheory.Center C.Obj} (f : Z ⟶ W) [Mono f] : IsSplitMono f := by
  let : Injective Z := center_all_injective_of_unit_retract C X U r Z
  exact mono_splits_of_all_injective f

set_option backward.isDefEq.respectTransparency false in
/-- Under the unit-retract condition every centre object is a finite simple sum. -/
theorem center_finite_simple_sum_of_unit_retract (X : C.Obj) (U : CategoryTheory.Center C.Obj)
    (r : Retract (𝟙_ (CategoryTheory.Center C.Obj)) ((induction C).obj X ⊗ U))
    (Z : CategoryTheory.Center C.Obj) : FiniteSimpleSum (CategoryTheory.Center C.Obj) Z := by
  let m : CategoryTheory.Center C.Obj → ℕ := fun W => Module.finrank ℂ (W ⟶ W)
  induction Z using (measure m).wf.induction with
  | h Z ih =>
    by_cases hz : IsZero Z
    · exact .zero hz
    · let : IsArtinianObject Z := center_artinian C Z
      obtain ⟨P, hP⟩ := exists_simple_subobject hz
      let : Simple (P : CategoryTheory.Center C.Obj) := hP
      let : IsSplitMono P.arrow := center_mono_splits_of_unit_retract C X U r P.arrow
      let E := ShortComplex.cokernelSequence P.arrow
      let split : E.Splitting := ShortComplex.Splitting.ofExactOfRetraction E
        (ShortComplex.cokernelSequence_exact P.arrow) (retraction P.arrow)
        (IsSplitMono.id P.arrow) inferInstance
      let K := cokernel P.arrow
      let e : Z ≅ (P : CategoryTheory.Center C.Obj) ⊞ K := split.isoBinaryBiproduct
      let : ∀ A B : CategoryTheory.Center C.Obj, FiniteDimensional ℂ (A ⟶ B) := by
        intro A B
        let : FiniteDimensional ℂ (A.1 ⟶ B.1) := IsFusionCategory.hom_finite _ _
        exact PropertyF.Ground.Centre.finiteDimensional_hom ℂ A B
      have hs : ¬ IsZero (P : CategoryTheory.Center C.Obj) := by
        intro h
        exact id_nonzero _ ((IsZero.iff_id_eq_zero _).mp h)
      have he : Module.finrank ℂ (Z ⟶ Z) = Module.finrank ℂ ((P : CategoryTheory.Center C.Obj) ⊞ K ⟶ (P : CategoryTheory.Center C.Obj) ⊞ K) :=
        (CategoryTheory.Linear.homCongr ℂ e e).finrank_eq
      have hk : m K < m Z := by
        change Module.finrank ℂ (K ⟶ K) < Module.finrank ℂ (Z ⟶ Z)
        rw [he]
        exact finrank_end_complement_lt _ K hs
      exact .cons hP (ih K hk) ⟨e⟩

/-- Centre rigidity and the explicit unit retract imply centre fusion. -/
theorem center_fusion_of_unit_retract (X : C.Obj) (U : CategoryTheory.Center C.Obj)
    (r : Retract (𝟙_ (CategoryTheory.Center C.Obj)) ((induction C).obj X ⊗ U)) :
    IsFusionCategory (CategoryTheory.Center C.Obj) := by
  obtain ⟨n, S, hS, hinj, hcover⟩ := finite_simple_representatives C
  apply PropertyF.Ground.CentreBundle.fusionOfFiniteSemisimple C
  refine ⟨n, S, hS, hinj, ?_⟩
  intro Z
  obtain ⟨k, V, hV, ⟨e⟩⟩ := finiteSimpleSum_biproduct (center_finite_simple_sum_of_unit_retract C X U r Z)
  obtain ⟨m, ⟨a⟩⟩ := regroup_biproduct S V (fun j => hcover (V j) (hV j))
  exact ⟨m, ⟨e ≪≫ a⟩⟩


set_option backward.isDefEq.respectTransparency false in
/-- A cap with nonzero unit composite gives a unit retract. -/
def unitRetractOfNonzeroCap (J : CategoryTheory.Center C.Obj)
    (cap : J ⊗ Jᘁ ⟶ 𝟙_ (CategoryTheory.Center C.Obj))
    (hne : η_ J (Jᘁ) ≫ cap ≠ 0) :
    Retract (𝟙_ (CategoryTheory.Center C.Obj)) (J ⊗ Jᘁ) := by
  letI : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  letI : Simple (𝟙_ (CategoryTheory.Center C.Obj)) := PropertyF.Ground.Centre.centerUnitSimple
  letI : IsIso (η_ J (Jᘁ) ≫ cap) := isIso_of_hom_simple hne
  refine { i := η_ J (Jᘁ), r := cap ≫ inv (η_ J (Jᘁ) ≫ cap), retract := ?_ }
  simp only [← Category.assoc, IsIso.hom_inv_id]

/-- A nonzero cap on an induced object implies centre fusion. -/
theorem center_fusion_of_nonzero_induced_cap (X : C.Obj)
    (cap : (induction C).obj X ⊗ ((induction C).obj X)ᘁ ⟶ 𝟙_ (CategoryTheory.Center C.Obj))
    (hne : η_ ((induction C).obj X) (((induction C).obj X)ᘁ) ≫ cap ≠ 0) :
    IsFusionCategory (CategoryTheory.Center C.Obj) :=
  center_fusion_of_unit_retract C X (((induction C).obj X)ᘁ)
    (unitRetractOfNonzeroCap C ((induction C).obj X) cap hne)

set_option backward.isDefEq.respectTransparency false in
/-- A centre pivotal structure with nonzero trace on an induced object implies fusion. -/
theorem center_fusion_of_nonzero_induced_trace (X : C.Obj)
    (p : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (hne : p.rightTrace (𝟙 ((induction C).obj X)) ≠ 0) :
    IsFusionCategory (CategoryTheory.Center C.Obj) := by
  let J := (induction C).obj X
  let cap : J ⊗ Jᘁ ⟶ 𝟙_ (CategoryTheory.Center C.Obj) :=
    ((p.iso J).hom ⊗ₘ 𝟙 (Jᘁ)) ≫ ε_ (Jᘁ) ((Jᘁ)ᘁ)
  have hcap : η_ J (Jᘁ) ≫ cap ≠ 0 := by
    intro h
    apply hne
    apply End.ext
    simpa [Dimensions.PivotalStructure.rightTrace, cap, J, Category.assoc] using h
  exact center_fusion_of_nonzero_induced_cap C X cap hcap



end PropertyF.Ground.CentreInduction
