module
public import MTC.Center.Normalization.AdjointDegrees

open MTC.Fusion MTC.Braided MTC.Center.Braid

/-! # Fusion-subring adjacency

Fusion multiplication modulo a fusion subring is an equivalence relation on
simple labels. The resulting quotient is used in `AdjointQuotient` to identify
the neutral universal degree with the adjoint subring.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- A positive summand in an associative fusion product can be reassociated
to a positive summand on the other side. -/
theorem fusionCoeff_exists_reassociate (i j k l t : Fin (rank C))
    (hij : 0 < fusionCoeff C i j t) (htk : 0 < fusionCoeff C t k l) :
    ∃ s, 0 < fusionCoeff C j k s ∧ 0 < fusionCoeff C i s l := by
  have hsum : 0 < ∑ r, fusionCoeff C i j r * fusionCoeff C r k l := by
    exact Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _) ⟨t, Finset.mem_univ _, Nat.mul_pos hij htk⟩
  rw [← fusionCoeff_assoc i j k l] at hsum
  obtain ⟨s, _, hs⟩ := Finset.sum_pos_iff.mp hsum
  exact ⟨s, Nat.pos_of_mul_pos_right hs, Nat.pos_of_mul_pos_left hs⟩

variable {A : Finset (Fin (rank C))} (hA : IsFusionSubring C A)

/-- Two simple labels are related if one occurs in the tensor product of the
other with some simple in the chosen fusion subring. -/
def fusionSubringRelated (i j : Fin (rank C)) : Prop :=
  ∃ a ∈ A, 0 < fusionCoeff C i a j

include hA

/-- Fusion-subring adjacency is reflexive. -/
theorem fusionSubringRelated_refl (i : Fin (rank C)) : fusionSubringRelated C (A := A) i i := by
  refine ⟨unitIndex C, hA.unit, ?_⟩
  rw [fusionCoeff_comm C i (unitIndex C), fusionCoeff_unit]
  simp

/-- Fusion-subring adjacency is symmetric by Frobenius reciprocity. -/
theorem fusionSubringRelated_symm {i j : Fin (rank C)}
    (h : fusionSubringRelated C (A := A) i j) : fusionSubringRelated C (A := A) j i := by
  obtain ⟨a, ha, hp⟩ := h
  exact ⟨dualIndex C a, hA.dual a ha, (fusionCoeff_reciprocity_labels i a j) ▸ hp⟩

/-- Fusion-subring adjacency is transitive by associativity and closure under
fusion constituents. -/
theorem fusionSubringRelated_trans {i j k : Fin (rank C)}
    (hij : fusionSubringRelated C (A := A) i j) (hjk : fusionSubringRelated C (A := A) j k) :
    fusionSubringRelated C (A := A) i k := by
  obtain ⟨a, ha, hp⟩ := hij
  obtain ⟨b, hb, hq⟩ := hjk
  obtain ⟨t, ht, hu⟩ := fusionCoeff_exists_reassociate C i a b k j hp hq
  exact ⟨t, hA.fusion a ha b hb t ht, hu⟩

omit hA in
/-- A label is related to the tensor unit precisely when it is in the
fusion subring. -/
theorem fusionSubringRelated_unit_iff (i : Fin (rank C)) :
    fusionSubringRelated C (A := A) (unitIndex C) i ↔ i ∈ A := by
  simp [fusionSubringRelated, fusionCoeff_unit, apply_ite]

omit hA in
/-- If a fusion subring contains the adjoint generators, any two simple
constituents of the same tensor product are related modulo that subring. -/
theorem tensor_constituents_related
    (hseed : ∀ k, AdjointSeed C k → k ∈ A)
    {i j k l : Fin (rank C)} (hk : 0 < fusionCoeff C i j k)
    (hl : 0 < fusionCoeff C i j l) : fusionSubringRelated C (A := A) k l := by
  have hk' : 0 < fusionCoeff C k (dualIndex C j) i := by
    rwa [← fusionCoeff_reciprocity_labels i j k]
  obtain ⟨a, ha, hka⟩ := fusionCoeff_exists_reassociate C k (dualIndex C j) j l i hk' hl
  have hseedA : AdjointSeed C a := ⟨j, by rwa [fusionCoeff_comm]⟩
  exact ⟨a, hseed a hseedA, hka⟩

omit hA in
/-- A positive summand in an associative fusion product can also be
reassociated from the right-associated side to the left-associated side. -/
theorem fusionCoeff_exists_reassociate_reverse (i j k l t : Fin (rank C))
    (hjk : 0 < fusionCoeff C j k t) (hit : 0 < fusionCoeff C i t l) :
    ∃ s, 0 < fusionCoeff C i j s ∧ 0 < fusionCoeff C s k l := by
  obtain ⟨s, hs, ht⟩ := fusionCoeff_exists_reassociate C k j i l t
    (by rwa [fusionCoeff_comm]) (by rwa [fusionCoeff_comm])
  exact ⟨s, by rwa [fusionCoeff_comm], by rwa [fusionCoeff_comm]⟩

/-- Replacing one tensor factor by a related label preserves the relation
between arbitrary simple constituents. -/
theorem related_tensor_left
    (hseed : ∀ k, AdjointSeed C k → k ∈ A)
    {i i' j k l : Fin (rank C)} (hii : fusionSubringRelated C (A := A) i i')
    (hk : 0 < fusionCoeff C i j k) (hl : 0 < fusionCoeff C i' j l) :
    fusionSubringRelated C (A := A) k l := by
  obtain ⟨a, ha, hia⟩ := hii
  obtain ⟨t, ht, hit⟩ := fusionCoeff_exists_reassociate C i a j l i' hia hl
  have ht' : 0 < fusionCoeff C j a t := by rwa [fusionCoeff_comm]
  obtain ⟨q, hq, hqa⟩ := fusionCoeff_exists_reassociate_reverse C i j a l t ht' hit
  exact fusionSubringRelated_trans C hA (tensor_constituents_related C hseed hk hq) ⟨a, ha, hqa⟩

/-- Changing both factors by adjoint-subring-related labels preserves the
relation between arbitrary simple constituents. -/
theorem related_tensor_both
    (hseed : ∀ k, AdjointSeed C k → k ∈ A)
    {i i' j j' k l : Fin (rank C)} (hii : fusionSubringRelated C (A := A) i i')
    (hjj : fusionSubringRelated C (A := A) j j')
    (hk : 0 < fusionCoeff C i j k) (hl : 0 < fusionCoeff C i' j' l) :
    fusionSubringRelated C (A := A) k l := by
  obtain ⟨m, hm⟩ := fusionCoeff_exists_positive C i' j
  apply fusionSubringRelated_trans C hA
    (related_tensor_left C hA hseed hii hk hm)
  have hm' : 0 < fusionCoeff C j i' m := by rwa [fusionCoeff_comm]
  have hl' : 0 < fusionCoeff C j' i' l := by rwa [fusionCoeff_comm]
  exact related_tensor_left C hA hseed hjj hm' hl'

/-- Fusion-subring adjacency defines a setoid on the actual simple labels. -/
def fusionSubringSetoid : Setoid (Fin (rank C)) where
  r := fusionSubringRelated C (A := A)
  iseqv := ⟨fusionSubringRelated_refl C hA, fusionSubringRelated_symm C hA,
    fusionSubringRelated_trans C hA⟩

end MTC.Center.Normalization
end
