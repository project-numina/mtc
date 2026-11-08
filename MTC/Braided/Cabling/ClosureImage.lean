module
public import MTC.Braided.Cabling.Naturality

/-! An explicit realization of each cabled generator as an original braid
word gives an injection of the corresponding actual braid images. -/

@[expose] public noncomputable section
open CategoryTheory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- A braid action embeds into another if conjugation carries its generators
into the latter's actual image. -/
def braidImageEmbeddingOfGenerators (X Y : C) (n k : ℕ)
    (e : tensorPower Y (n + 2) ≅ tensorPower X (k + 2))
    (h : ∀ i, e.conjAut (braidGenerator Y n i) ∈ braidImage X k) :
    braidImage Y n →* braidImage X k := by
  let f := e.conjAut.toMonoidHom
  have hf : braidImage Y n ≤ (braidImage X k).comap f := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  exact (f.comp (braidImage Y n).subtype).codRestrict _ (fun a => hf a.property)

/-- The image map constructed from actual conjugated generators is injective. -/
theorem braidImageEmbeddingOfGenerators_injective (X Y : C) (n k : ℕ)
    (e : tensorPower Y (n + 2) ≅ tensorPower X (k + 2))
    (h : ∀ i, e.conjAut (braidGenerator Y n i) ∈ braidImage X k) :
    Function.Injective (braidImageEmbeddingOfGenerators X Y n k e h) := by
  intro a b hab
  apply Subtype.ext
  apply e.conjAut.injective
  exact congrArg Subtype.val hab

/-- Categorical generator realizations prove finiteness of the actual image. -/
theorem finite_braidImage_of_generator_realization (X Y : C) (n k : ℕ)
    (e : tensorPower Y (n + 2) ≅ tensorPower X (k + 2))
    (h : ∀ i, e.conjAut (braidGenerator Y n i) ∈ braidImage X k)
    [Finite (braidImage X k)] : Finite (braidImage Y n) :=
  Finite.of_injective _ (braidImageEmbeddingOfGenerators_injective X Y n k e h)

/-- Explicit original-strand words for the conjugated generators suffice. -/
theorem finite_braidImage_of_generator_words (X Y : C) (n k : ℕ)
    (e : tensorPower Y (n + 2) ≅ tensorPower X (k + 2))
    (w : Fin (n + 1) → BraidWords k)
    (h : ∀ i, e.conjAut (braidGenerator Y n i) = (braidWordAction X k (w i)).val)
    [Finite (braidImage X k)] : Finite (braidImage Y n) :=
  finite_braidImage_of_generator_realization X Y n k e (fun i => by
    rw [h i]
    exact (braidWordAction X k (w i)).property)

end MTC.Braided
