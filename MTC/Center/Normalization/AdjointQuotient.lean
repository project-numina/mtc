module
public import MTC.Center.Normalization.AdjointRelation

open MTC.Fusion MTC.Braided MTC.Center.Braid

/-! # Quotients of fusion labels by adjoint-containing subrings -/

@[expose] public noncomputable section
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u}) {A : Finset (Fin (rank C))}
variable (hA : IsFusionSubring C A)
variable [hseed : Fact (∀ k, AdjointSeed C k → k ∈ A)]

/-- A chosen simple constituent of a product of simple representatives. -/
def fusionProductLabel (i j : Fin (rank C)) : Fin (rank C) :=
  Classical.choose (fusionCoeff_exists_positive C i j)

/-- The chosen representative really occurs in the product. -/
theorem fusionProductLabel_positive (i j : Fin (rank C)) :
    0 < fusionCoeff C i j (fusionProductLabel C i j) :=
  Classical.choose_spec (fusionCoeff_exists_positive C i j)

/-- Fusion labels modulo multiplication by an adjoint-containing fusion subring. -/
abbrev FusionClass := Quotient (fusionSubringSetoid C hA)

/-- The equivalence class of a simple label. -/
def fusionClass (i : Fin (rank C)) : FusionClass C hA := Quotient.mk _ i

/-- Multiplication on classes is well defined by arbitrary positive fusion
constituents. -/
instance fusionClassMul : Mul (FusionClass C hA) where
  mul := Quotient.map₂ (fusionProductLabel C) (fun {_ _} hi {_ _} hj ↦
    related_tensor_both C hA hseed.out hi hj (fusionProductLabel_positive C _ _)
      (fusionProductLabel_positive C _ _))

instance fusionClassOne : One (FusionClass C hA) where
  one := fusionClass C hA (unitIndex C)

variable {C} in
/-- Any simple constituent has the product class. -/
theorem fusionClass_mul_of_fusion {i j k : Fin (rank C)} (h : 0 < fusionCoeff C i j k) :
    fusionClass C hA i * fusionClass C hA j = fusionClass C hA k := by
  apply Quotient.sound
  exact tensor_constituents_related C hseed.out (fusionProductLabel_positive C i j) h

variable {C} in
/-- Multiplication of fusion classes is associative. -/
theorem fusionClass_mul_assoc (x y z : FusionClass C hA) : (x * y) * z = x * (y * z) := by
  induction x, y, z using Quotient.inductionOn₃ with
  | _ i j k =>
    change (fusionClass C hA i * fusionClass C hA j) * fusionClass C hA k =
      fusionClass C hA i * (fusionClass C hA j * fusionClass C hA k)
    let a := fusionProductLabel C i j
    let l := fusionProductLabel C a k
    obtain ⟨b, hb, hi⟩ := fusionCoeff_exists_reassociate C
      (fusionProductLabel_positive C i j) (fusionProductLabel_positive C a k)
    calc
      _ = fusionClass C hA l := by rw [fusionClass_mul_of_fusion hA (fusionProductLabel_positive C i j),
        fusionClass_mul_of_fusion hA (fusionProductLabel_positive C a k)]
      _ = fusionClass C hA i * fusionClass C hA b :=
        (fusionClass_mul_of_fusion hA hi).symm
      _ = _ := by rw [← fusionClass_mul_of_fusion hA hb]

variable {C} in
/-- Multiplication of fusion classes is commutative. -/
theorem fusionClass_mul_comm (x y : FusionClass C hA) : x * y = y * x := by
  induction x, y using Quotient.inductionOn₂ with
  | _ i j =>
    change fusionClass C hA i * fusionClass C hA j = fusionClass C hA j * fusionClass C hA i
    let k := fusionProductLabel C i j
    have hk : 0 < fusionCoeff C j i k := by rw [fusionCoeff_comm]; exact fusionProductLabel_positive C i j
    rw [fusionClass_mul_of_fusion hA (fusionProductLabel_positive C i j), fusionClass_mul_of_fusion hA hk]

variable {C} in
/-- The unit label acts as the identity on fusion classes. -/
theorem fusionClass_one_mul (x : FusionClass C hA) : 1 * x = x := by
  induction x using Quotient.inductionOn with
  | _ i =>
    change fusionClass C hA (unitIndex C) * fusionClass C hA i = fusionClass C hA i
    apply fusionClass_mul_of_fusion
    simp [fusionCoeff_unit]

instance fusionClassCommMonoid : CommMonoid (FusionClass C hA) where
  mul_assoc := fusionClass_mul_assoc hA
  one_mul := fusionClass_one_mul hA
  mul_one x := (fusionClass_mul_comm hA x 1).trans (fusionClass_one_mul hA x)
  mul_comm := fusionClass_mul_comm hA

variable {C} in
/-- Every class is a unit, with the class of a dual simple as its inverse. -/
theorem fusionClass_isUnit (x : FusionClass C hA) : IsUnit x := by
  induction x using Quotient.inductionOn with
  | _ i =>
    apply IsUnit.of_mul_eq_one (fusionClass C hA (dualIndex C i))
    change fusionClass C hA i * fusionClass C hA (dualIndex C i) = fusionClass C hA (unitIndex C)
    apply fusionClass_mul_of_fusion
    rw [fusionCoeff_dual_unit]
    exact Nat.zero_lt_one


/-- The unit of the fusion-class monoid represented by a simple label. -/
def fusionClassUnit (i : Fin (rank C)) : (FusionClass C hA)ˣ :=
  (fusionClass_isUnit hA (fusionClass C hA i)).unit

/-- Forgetting the chosen unit gives the label's quotient class. -/
theorem fusionClassUnit_val (i : Fin (rank C)) :
    (fusionClassUnit C hA i : FusionClass C hA) = fusionClass C hA i :=
  (fusionClass_isUnit hA (fusionClass C hA i)).unit_spec

/-- A simple label represents the unit class exactly when it lies in the
chosen fusion subring. -/
theorem fusionClassUnit_eq_one_iff_mem (i : Fin (rank C)) :
    fusionClassUnit C hA i = 1 ↔ i ∈ A := by
  constructor
  · intro hu
    apply (fusionSubringRelated_unit_iff C i).mp
    change (fusionSubringSetoid C hA).r (unitIndex C) i
    apply Quotient.exact
    change (1 : FusionClass C hA) = fusionClass C hA i
    have h := congrArg (fun z : (FusionClass C hA)ˣ => (z : FusionClass C hA)) hu
    simpa only [fusionClassUnit_val, Units.val_one] using h.symm
  · intro hi
    apply Units.ext
    rw [fusionClassUnit_val]
    change fusionClass C hA i = fusionClass C hA (unitIndex C)
    exact (Quotient.sound ((fusionSubringRelated_unit_iff C i).mpr hi)).symm

/-- The tensor unit maps to the identity in the fusion-class unit group. -/
theorem fusionClassUnit_unit : fusionClassUnit C hA (unitIndex C) = 1 :=
  (fusionClassUnit_eq_one_iff_mem C hA (unitIndex C)).mpr hA.unit

/-- Fusion constituents multiply correctly in the fusion-class unit group. -/
theorem fusionClassUnit_mul {i j k : Fin (rank C)} (h : 0 < fusionCoeff C i j k) :
    fusionClassUnit C hA k = fusionClassUnit C hA i * fusionClassUnit C hA j := by
  apply Units.ext
  simp only [Units.val_mul, fusionClassUnit_val]
  exact (fusionClass_mul_of_fusion hA h).symm

/-- The universal abelian degree group maps to the fusion-class unit group. -/
def fusionDegreeToFusionClass : FusionDegreeGroup C →+ Additive ((FusionClass C hA)ˣ) :=
  fusionDegreeLift C (fun i ↦ Additive.ofMul (fusionClassUnit C hA i))
    (by change fusionClassUnit C hA (unitIndex C) = 1; exact fusionClassUnit_unit C hA)
    (fun i j k h ↦ by
      change fusionClassUnit C hA k = fusionClassUnit C hA i * fusionClassUnit C hA j
      exact fusionClassUnit_mul C hA h)

/-- The induced map takes a simple degree to the unit represented by its class. -/
theorem fusionDegreeToFusionClass_apply (i : Fin (rank C)) :
    fusionDegreeToFusionClass C hA (fusionDegree C i) =
      Additive.ofMul (fusionClassUnit C hA i) := by
  simp [fusionDegreeToFusionClass, fusionDegreeLift_apply]

include hA in
/-- Any fusion subring containing every adjoint generator contains every
simple label of neutral universal degree. -/
theorem neutralDegree_mem_of_contains_adjoint
    {i : Fin (rank C)} (hi : fusionDegree C i = 0) : i ∈ A := by
  apply (fusionClassUnit_eq_one_iff_mem C hA i).mp
  have h := congrArg (fusionDegreeToFusionClass C hA) hi
  rw [fusionDegreeToFusionClass_apply, map_zero] at h
  exact h

/-- The neutral universal degree is exactly the adjoint fusion subring of
simple labels. -/
theorem fusionDegree_zero_iff_adjointLabel (i : Fin (rank C)) :
    fusionDegree C i = 0 ↔ IsAdjointLabel C i := by
  constructor
  · intro hi A hsub hcontains
    let : Fact (∀ k, AdjointSeed C k → k ∈ A) := ⟨hcontains⟩
    exact neutralDegree_mem_of_contains_adjoint C hsub hi
  · exact adjointLabel_neutral C

end MTC.Center.Normalization
end
