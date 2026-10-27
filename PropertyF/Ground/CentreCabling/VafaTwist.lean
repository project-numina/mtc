module
public import PropertyF.Ground.CentreCabling.VafaAlgebra
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.CentreCabling.TwistFinite

/-!
# Vafa relations for pivotal twists

Fusion multiplicities and Vafa relations imply finite order of pivotal twists
and, under balancing, mixed monodromy.
-/
@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u

/-- Dimension of the multiplicity space Hom(X, X ⊗ X* ⊗ X). -/
def vafaMultiplicity (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (rank C)) : ℕ :=
  ∑ j, fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i

/-- Multiplicity of the simple twist in the three pair-twist determinants. -/
def vafaWeight (C : Ground.BraidedFusionCategory.{v,u})
    (i j : Fin (rank C)) : ℕ :=
  2 * fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i +
    fusionCoeff C i i j * fusionCoeff C j (dualIndex C i) i

/-- Associativity makes the three pair-twist multiplicity sums equal. -/
theorem vafaWeight_sum (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    ∑ j, vafaWeight C i j = 3 * vafaMultiplicity C i := by
  classical
  have h := fusionCoeff_assoc C i i (dualIndex C i) i
  simp_rw [fusionCoeff_comm C i] at h
  unfold vafaWeight vafaMultiplicity
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h' : (∑ j, fusionCoeff C i i j * fusionCoeff C j (dualIndex C i) i) =
      ∑ j, fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i := by
    simpa [fusionCoeff_comm C i] using h.symm
  rw [h']
  simp_rw [show ∀ j, 2 * fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i =
    2 * (fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i) from fun j => by ring]
  rw [← Finset.mul_sum]
  omega

/-- The tensor unit contributes to every Vafa multiplicity. -/
theorem vafaMultiplicity_pos (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    0 < vafaMultiplicity C i := by
  classical
  have h := Finset.single_le_sum
    (f := fun j => fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ (unitIndex C))
  have h' : 1 ≤ vafaMultiplicity C i := by
    simpa [vafaMultiplicity, fusionCoeff_dual_unit, fusionCoeff_unit] using h
  omega

/-- The lantern exponent strictly exceeds the sum of the pair exponents. -/
theorem vafaWeight_sum_lt (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    ∑ j, vafaWeight C i j < 4 * vafaMultiplicity C i := by
  rw [vafaWeight_sum]
  have h := vafaMultiplicity_pos C i
  omega

end PropertyF.Ground.CentreCabling

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u

/-- The actual pivotal twist scalars, viewed as nonzero complex numbers. -/
def pivotalTwistUnit (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (i : Fin (rank C)) : ℂˣ := by
  letI : Simple (simples C i) := simples_simple C i
  exact Units.mk0 (Dimensions.pivotalBraidedTwistScalar C p (simples C i))
    (Dimensions.pivotalBraidedTwistScalar_ne_zero C p (simples C i))

/-- The standard Vafa lantern determinant relations give finite-order simple
pivotal twists. The determinant relations remain explicit hypotheses. -/
theorem pivotal_twist_finite_of_vafa_relations
    (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (h : ∀ i, pivotalTwistUnit C p i ^ (4 * vafaMultiplicity C i) =
      ∏ j, pivotalTwistUnit C p j ^ vafaWeight C i j)
    (i : Fin (rank C)) :
    IsOfFinOrder (End.of ((Dimensions.pivotalBraidedTwist C p (simples C i)).hom)) := by
  have hf := finite_order_of_vafa_relations (vafaWeight C) (fun i => 4 * vafaMultiplicity C i)
    (vafaWeight_sum_lt C) (pivotalTwistUnit C p) h i
  have hf' : IsOfFinOrder ((pivotalTwistUnit C p i : ℂˣ) : ℂ) :=
    Units.isOfFinOrder_val.mpr hf
  letI : Simple (simples C i) := simples_simple C i
  have hmap := (Dimensions.simpleEndScalarEquiv C (simples C i)).symm.toMonoidHom.isOfFinOrder hf'
  simpa [pivotalTwistUnit, Dimensions.pivotalBraidedTwistScalar] using hmap

/-- The lantern determinant relations and the balancing law suffice for all
mixed centre monodromies; neither premise is asserted proved. -/
theorem mixed_monodromy_finite_of_vafa_relations
    (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (h : ∀ i, pivotalTwistUnit C p i ^ (4 * vafaMultiplicity C i) =
      ∏ j, pivotalTwistUnit C p j ^ vafaWeight C i j)
    (hbalance : ∀ X Y, Modular.doubleBraiding X Y ≫
      ((Dimensions.pivotalBraidedTwist C p X).hom ⊗ₘ
        (Dimensions.pivotalBraidedTwist C p Y).hom) =
      (Dimensions.pivotalBraidedTwist C p (X ⊗ Y)).hom)
    (X Y : C.Obj) : IsOfFinOrder (End.of (Modular.doubleBraiding X Y)) := by
  apply mixed_monodromy_finite_of_balanced_finite_twist C
    (Dimensions.pivotalBraidedTwistNaturalIso C p)
  · exact pivotal_twist_finite_of_vafa_relations C p h
  · exact hbalance

end PropertyF.Ground.CentreCabling
