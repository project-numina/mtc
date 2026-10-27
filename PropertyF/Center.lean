module
public import PropertyF.Axioms
public import PropertyF.GaloisSymmetry

@[expose] public noncomputable section
namespace PropertyF
namespace CenterInputs

universe v u
variable {C : BraidedFusionCategory.{v,u}} (I : CenterInputs C)

/-- Lemma 4.1, containment of Galois images of the unit. Integrality is used
only on the symmetric core. Mutual centralizers and transparency are proved
using actual half-braidings in CenterBasics.lean. -/
theorem galois_unit_mem_generated (τ : ℂ ≃+* ℂ) :
    I.data.galoisLabel τ I.data.unit ∈ I.generated := by
  apply I.double_centralizer
  intro X hpos hneg
  obtain ⟨z, hz⟩ := I.symmetric_integrality X
    (transparent_of_both_centralizers (I.object X) hpos hneg)
  rw [I.data.galois_unit_column, hz, map_intCast, mul_comm]

/-- Property F on the generated subcategory, from the explicit quotient of a
product supplied by the canonical braided functor onto its generated image.
No dominance onto the entire centre is assumed. The groups here
are actual generated categorical braid images. -/
theorem object_propertyF_of_mem (hF : HasPropertyF C.Obj) {Y : Fin I.data.rank}
    (hY : Y ∈ I.generated) : ObjectPropertyF (I.object Y) := by
  intro n
  obtain ⟨X, Z, ⟨W⟩⟩ := I.product_witness Y hY n
  have := hF X n
  have := hF Z n
  exact Finite.of_surjective W.map W.surjective

/-- The combination of the two conclusions of Lemma 4.1 used by the main proof. -/
theorem galois_unit_propertyF (hF : HasPropertyF C.Obj) (τ : ℂ ≃+* ℂ) :
    ObjectPropertyF (I.object (I.data.galoisLabel τ I.data.unit)) :=
  I.object_propertyF_of_mem hF (I.galois_unit_mem_generated τ)

end CenterInputs
end PropertyF
