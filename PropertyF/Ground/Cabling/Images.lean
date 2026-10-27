module
public import PropertyF.Definitions
public import Mathlib.CategoryTheory.Conj
public import Mathlib.Algebra.Group.Subgroup.Map

/-! The group-theoretic part of preservation of braid images under functors. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.Monoidal
namespace PropertyF

/-- An injective homomorphism carrying corresponding generators to each other
restricts to an isomorphism of the subgroups they generate. -/
def generatedImageEquiv {G H ι : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (g : ι → G) (h : ι → H)
    (hgen : ∀ i, f (g i) = h i) :
    Subgroup.closure (Set.range g) ≃* Subgroup.closure (Set.range h) := by
  have heq : (Subgroup.closure (Set.range g)).map f = Subgroup.closure (Set.range h) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hgen i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨g i, ⟨i, rfl⟩, hgen i⟩
  exact (Subgroup.closure (Set.range g)).equivMapOfInjective f hf |>.trans (MulEquiv.subgroupCongr heq)

universe v u w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
variable {D : Type z} [Category.{w} D] [MonoidalCategory D] [BraidedCategory D]

/-- The canonical comparison between a tensor power of the image and the
image of a tensor power for a strong monoidal functor. -/
def tensorPowerFunctorIso (F : C ⥤ D) [F.Monoidal] (X : C) : ∀ n,
    tensorPower (F.obj X) n ≅ F.obj (tensorPower X n)
  | 0 => εIso F
  | n + 1 => (Iso.refl (F.obj X) ⊗ᵢ tensorPowerFunctorIso F X n) ≪≫
      μIso F X (tensorPower X n)

/-- The group isomorphism between braid images follows from the coherence
identity on each braid generator and faithfulness of the functor. -/
def braidImageEquivOfGeneratorCoherence (F : C ⥤ D) [F.Monoidal] [F.Faithful]
    (X : C) (n : ℕ)
    (hgen : ∀ i, ((tensorPowerFunctorIso F X (n + 2)).symm.conjAut.toMonoidHom.comp
      (F.mapAut (tensorPower X (n + 2)))) (braidGenerator X n i) =
        braidGenerator (F.obj X) n i) : braidImage X n ≃* braidImage (F.obj X) n := by
  let f := (tensorPowerFunctorIso F X (n + 2)).symm.conjAut.toMonoidHom.comp
    (F.mapAut (tensorPower X (n + 2)))
  have hf : Function.Injective f := by
    intro a b hab
    have h : F.map (a.asIso.hom) = F.map (b.asIso.hom) := by
      have hm := (tensorPowerFunctorIso F X (n + 2)).symm.conjAut.injective hab
      exact congrArg (fun x : Aut (F.obj (tensorPower X (n + 2))) => x.asIso.hom) hm
    apply Aut.ext
    apply Iso.ext
    exact F.map_injective h
  exact generatedImageEquiv f hf _ _ hgen

/-- An equivariant monomorphism forces an automorphism acting trivially on
its codomain to act trivially on its domain. This is the restriction step for
summands in the cabling argument. -/
theorem ker_le_of_mono_intertwiner {G : Type*} [Group G]
    {C : Type*} [Category C] {Y Z : C}
    (ρY : G →* Aut Y) (ρZ : G →* Aut Z) (i : Y ⟶ Z) [Mono i]
    (hi : ∀ g, (ρY g).asIso.hom ≫ i = i ≫ (ρZ g).asIso.hom) :
    ρZ.ker ≤ ρY.ker := by
  intro g hg
  change ρZ g = 1 at hg
  change ρY g = 1
  apply Aut.ext
  apply Iso.ext
  apply (cancel_mono i).mp
  rw [hi, hg]
  simp

end PropertyF
