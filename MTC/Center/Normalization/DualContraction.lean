module
public import MTC.CategoryTheory.Dimensions.SimpleHomBasis

/-! # Bilinear dual-basis contraction under a linear equivalence -/

@[expose] public noncomputable section
open scoped BigOperators
namespace MTC.Center.Normalization
universe u v w z

/-- A bilinear contraction is unchanged when a basis is transported through
an equivalence and its dual basis is transported contragrediently. -/
theorem dualBasis_contraction_of_equiv
    {k : Type*} [CommSemiring k] {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {A B E : Type*} [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    [AddCommMonoid E] [Module k E]
    (a : Module.Basis I k A) (b : Module.Basis J k B) (e : A ≃ₗ[k] B)
    (F : B →ₗ[k] Module.Dual k B →ₗ[k] E) :
    (∑ i, F (e (a i)) (Module.Dual.transpose e.symm.toLinearMap (a.dualBasis i))) =
      ∑ j, F (b j) (b.dualBasis j) := by
  let G := (LinearMap.lcomp k E (Module.Dual.transpose e.symm.toLinearMap)).comp F
  have h := MTC.CategoryTheory.Dimensions.dualBasis_contraction_natural a b e.toLinearMap G
  have he (f : Module.Dual k B) :
      Module.Dual.transpose e.symm.toLinearMap (Module.Dual.transpose e.toLinearMap f) = f := by
    ext x
    simp [Module.Dual.transpose_apply]
  simpa [G, he] using h

/-- A bilinear contraction using dual partners from a perfect pairing is
independent of the choice of basis. -/
theorem pairing_contraction_basis_independent
    {k : Type*} [CommSemiring k] {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {A B E : Type*} [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    [AddCommMonoid E] [Module k E]
    (a : Module.Basis I k A) (b : Module.Basis J k A)
    (pair : B ≃ₗ[k] Module.Dual k A) (F : A →ₗ[k] B →ₗ[k] E) :
    (∑ i, F (a i) (pair.symm (a.dualBasis i))) =
      ∑ j, F (b j) (pair.symm (b.dualBasis j)) := by
  let G := (LinearMap.lcomp k E pair.symm.toLinearMap).comp F
  have h := MTC.CategoryTheory.Dimensions.dualBasis_contraction_natural a b (LinearMap.id) G
  simpa [G, Module.Dual.transpose_apply] using h

end MTC.Center.Normalization
end
