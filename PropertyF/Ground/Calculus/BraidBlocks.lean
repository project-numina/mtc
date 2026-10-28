module
public import PropertyF.Ground.Calculus.GroupBlocks
public import PropertyF.Definitions

/-! The actual linear span of a finite categorical braid image has matrix blocks. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C]

/-- The actual braid image acting by endomorphisms of the tensor power. -/
def braidEndRepresentation (X : C) (n : ℕ) :
    braidImage X n →* End (tensorPower X (n + 2)) :=
  Aut.toEnd.comp (braidImage X n).subtype

/-- The subalgebra spanned by the genuine categorical braid image. -/
def braidAlgebra (X : C) (n : ℕ) : Subalgebra ℂ (End (tensorPower X (n + 2))) :=
  groupImageAlgebra (braidEndRepresentation X n)

end PropertyF.Ground.Calculus
