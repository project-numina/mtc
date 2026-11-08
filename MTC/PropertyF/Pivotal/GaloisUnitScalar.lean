module
public import MTC.PropertyF.Pivotal.Galois
public import MTC.Fusion.UnitScalar

/-! # Scalar transport on tensor-unit endomorphisms -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.Monoidal
open MTC.Fusion
namespace MTC.PropertyF.Pivotal
set_option linter.style.haveILetI false
universe v u
variable {C D : BraidedFusionCategory.{v,u}} {σ : ℂ ≃+* ℂ}

/-- A semilinear monoidal equivalence carries a scalar endomorphism of the
unit to its Galois conjugate, using the actual monoidal unit comparison. -/
theorem unitScalar_galois_transport (h : GaloisConjugate C D σ)
    (f : End (𝟙_ C.Obj)) :
    letI := h.monoidal
    unitScalar D (End.of ((εIso h.equivalence.functor).hom ≫ h.equivalence.functor.map f.asHom ≫
      (εIso h.equivalence.functor).inv)) = σ (unitScalar C f) := by
  let F := h.equivalence.functor
  letI := h.monoidal
  apply (unit_algebraMap_bijective D).1
  rw [algebraMap_unitScalar]
  apply End.ext
  have hf : f.asHom = unitScalar C f • 𝟙 (𝟙_ C.Obj) := by
    have he := congrArg End.asHom (algebraMap_unitScalar C f)
    simpa only [Algebra.algebraMap_eq_smul_one, End.one_asHom, End.smul_asHom] using he.symm
  simp only [Algebra.algebraMap_eq_smul_one, End.smul_asHom, End.one_asHom,
    hf, h.map_smul, Linear.comp_smul, Linear.smul_comp]
  rw [h.equivalence.functor.map_id]
  simp only [Category.id_comp, Iso.hom_inv_id]

end MTC.PropertyF.Pivotal
end
