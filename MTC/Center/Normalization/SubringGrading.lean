module
public import MTC.Center.Normalization.AdjointDegrees

open MTC.Fusion MTC.Braided MTC.Center.Braid

/-! # Universal degrees of a fusion subring

The induced map on fusion-degree groups has kernel precisely represented by
simple subring labels of neutral ambient degree. The identification of neutral
ambient degree with adjoint fusion labels is a separate theorem.
-/

@[expose] public noncomputable section
namespace MTC.Center.Normalization
universe v u
variable {C : BraidedFusionCategory.{v,u}} {A : Finset (Fin (rank C))}
variable (hA : IsFusionSubring C A)

/-- Fusion-degree relations internal to a fusion subring of simple labels. -/
def subringDegreeRelations : Set (FreeAbelianGroup A) :=
  {x | x = FreeAbelianGroup.of ⟨unitIndex C, hA.unit⟩ ∨
    ∃ i j k : A, 0 < fusionCoeff C i j k ∧
      x = FreeAbelianGroup.of k - FreeAbelianGroup.of i - FreeAbelianGroup.of j}

/-- The presented abelian group of degrees of the subring. -/
abbrev SubringDegreeGroup := FreeAbelianGroup A ⧸ AddSubgroup.closure (subringDegreeRelations hA)

/-- The degree of a simple label in the subring. -/
def subringDegree (i : A) : SubringDegreeGroup hA :=
  QuotientAddGroup.mk (FreeAbelianGroup.of i)

/-- The subring unit has degree zero. -/
theorem subringDegree_unit : subringDegree hA ⟨unitIndex C, hA.unit⟩ = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact AddSubgroup.subset_closure (Or.inl rfl)

/-- Degrees multiply according to the subring fusion rules. -/
theorem subringDegree_tensor {i j k : A} (h : 0 < fusionCoeff C i j k) :
    subringDegree hA k = subringDegree hA i + subringDegree hA j := by
  have hrel : FreeAbelianGroup.of k - FreeAbelianGroup.of i - FreeAbelianGroup.of j ∈
      AddSubgroup.closure (subringDegreeRelations hA) :=
    AddSubgroup.subset_closure (Or.inr ⟨i, j, k, h, rfl⟩)
  have hz := (QuotientAddGroup.eq_zero_iff _).mpr hrel
  change subringDegree hA k - subringDegree hA i - subringDegree hA j = 0 at hz
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hz)).trans (add_comm _ _)

/-- The degree of the dual of a subring label is its inverse. -/
theorem subringDegree_dual (i : A) :
    subringDegree hA ⟨dualIndex C i, hA.dual _ i.property⟩ = -subringDegree hA i := by
  have h := subringDegree_tensor hA
    (i := i) (j := ⟨dualIndex C i, hA.dual _ i.property⟩) (k := ⟨unitIndex C, hA.unit⟩)
    (by rw [fusionCoeff_dual_unit]; exact Nat.zero_lt_one)
  rw [subringDegree_unit] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Every degree of the subring occurs on one of its simple labels. -/
theorem subringDegree_surjective : Function.Surjective (subringDegree hA) := by
  apply presented_generator_surjective
  · exact ⟨⟨unitIndex C, hA.unit⟩, subringDegree_unit hA⟩
  · intro i
    exact ⟨⟨dualIndex C i, hA.dual _ i.property⟩, subringDegree_dual hA i⟩
  · intro i j
    obtain ⟨k, hk⟩ := fusionCoeff_exists_positive C i j
    exact ⟨⟨k, hA.fusion i i.property j j.property k hk⟩, subringDegree_tensor hA hk⟩

/-- The subring degree group is finite. -/
instance subringDegreeGroup_finite : Finite (SubringDegreeGroup hA) :=
  Finite.of_surjective (subringDegree hA) (subringDegree_surjective hA)

/-- A degree assignment on the subring's simple labels that obeys the fusion
relations induces a homomorphism from its degree group. -/
def subringDegreeLift {G : Type*} [AddCommGroup G] (d : A → G)
    (hu : d ⟨unitIndex C, hA.unit⟩ = 0)
    (hmul : ∀ i j k : A, 0 < fusionCoeff C i j k → d k = d i + d j) :
    SubringDegreeGroup hA →+ G :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift d) <| by
    apply (AddSubgroup.closure_le _).mpr
    rintro x (hx | ⟨i, j, k, h, rfl⟩)
    · subst x
      simp [hu]
    · simp [hmul i j k h]

/-- The induced subring homomorphism recovers the assigned simple degrees. -/
theorem subringDegreeLift_apply {G : Type*} [AddCommGroup G] (d : A → G)
    (hu : d ⟨unitIndex C, hA.unit⟩ = 0)
    (hmul : ∀ i j k : A, 0 < fusionCoeff C i j k → d k = d i + d j) (i : A) :
    subringDegreeLift hA d hu hmul (subringDegree hA i) = d i := by
  simp [subringDegreeLift, subringDegree]

/-- Inclusion of a fusion subring induces a map on its presented degree group. -/
def subringDegreeToAmbient : SubringDegreeGroup hA →+ FusionDegreeGroup C :=
  subringDegreeLift hA (fun i : A ↦ fusionDegree C i) (fusionDegree_unit C)
    (fun _ _ _ h ↦ fusionDegree_tensor C h)

/-- The inclusion map takes each subring simple degree to its ambient degree. -/
theorem subringDegreeToAmbient_apply (i : A) :
    subringDegreeToAmbient hA (subringDegree hA i) = fusionDegree C i := by
  simp [subringDegreeToAmbient, subringDegreeLift_apply]

/-- Each kernel element is represented by a subring simple whose ambient
degree is neutral, and conversely. -/
theorem subringDegreeToAmbient_kernel_iff (g : SubringDegreeGroup hA) :
    g ∈ (subringDegreeToAmbient hA).ker ↔
      ∃ i : A, subringDegree hA i = g ∧ fusionDegree C i = 0 := by
  constructor
  · intro hg
    obtain ⟨i, rfl⟩ := subringDegree_surjective hA g
    exact ⟨i, rfl, by simpa [subringDegreeToAmbient_apply] using hg⟩
  · rintro ⟨i, rfl, hi⟩
    simpa [subringDegreeToAmbient_apply] using hi

/-- The induced homomorphism is unique. -/
theorem subringDegreeLift_unique {G : Type*} [AddCommGroup G] (d : A → G)
    (hu : d ⟨unitIndex C, hA.unit⟩ = 0)
    (hmul : ∀ i j k : A, 0 < fusionCoeff C i j k → d k = d i + d j)
    (f : SubringDegreeGroup hA →+ G) (hf : ∀ i, f (subringDegree hA i) = d i) :
    f = subringDegreeLift hA d hu hmul := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨i, rfl⟩ := subringDegree_surjective hA x
  rw [hf, subringDegreeLift_apply]

end MTC.Center.Normalization
end
