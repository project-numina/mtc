module
public import PropertyF.Ground.CentreInduction.Artinian

/-! A finite-step semisimple decomposition from split subobjects. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [HasBinaryBiproducts D]

/-- The block-diagonal map embeds pairs of endomorphisms into endomorphisms
of a binary direct sum. -/
def diagonalEndMap (S K : D) : ((S ⟶ S) × (K ⟶ K)) →ₗ[ℂ] (S ⊞ K ⟶ S ⊞ K) where
  toFun x := biprod.map x.1 x.2
  map_add' x y := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp
  map_smul' r x := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

/-- A block-diagonal endomorphism determines both diagonal blocks. -/
theorem diagonalEndMap_injective (S K : D) : Function.Injective (diagonalEndMap S K) := by
  intro a b h
  apply Prod.ext
  · have h' := congrArg (fun f => biprod.inl ≫ f ≫ biprod.fst) h
    simpa [diagonalEndMap, Category.assoc] using h'
  · have h' := congrArg (fun f => biprod.inr ≫ f ≫ biprod.snd) h
    simpa [diagonalEndMap, Category.assoc] using h'

/-- Removing a nonzero direct summand strictly decreases the dimension of the
endomorphism space. -/
theorem finrank_end_complement_lt (S K : D)
    [FiniteDimensional ℂ (S ⟶ S)] [FiniteDimensional ℂ (K ⟶ K)]
    [FiniteDimensional ℂ (S ⊞ K ⟶ S ⊞ K)] (hS : ¬ IsZero S) :
    Module.finrank ℂ (K ⟶ K) < Module.finrank ℂ (S ⊞ K ⟶ S ⊞ K) := by
  have hpos : 0 < Module.finrank ℂ (S ⟶ S) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨𝟙 S, (IsZero.iff_id_eq_zero S).not.mp hS⟩
  have hle := LinearMap.finrank_le_finrank_of_injective (f := diagonalEndMap S K)
    (diagonalEndMap_injective S K)
  rw [Module.finrank_prod] at hle
  omega

/-- Objects built from finitely many simple objects by binary direct sums,
up to isomorphism. -/
inductive FiniteSimpleSum (D : Type u) [Category.{v} D] [Preadditive D]
    [HasBinaryBiproducts D] : D → Prop
  | zero {X} : IsZero X → FiniteSimpleSum D X
  | cons {X S K} : Simple S → FiniteSimpleSum D K → Nonempty (X ≅ S ⊞ K) →
      FiniteSimpleSum D X

set_option backward.isDefEq.respectTransparency false in
/-- Assuming the finite loop-sliding identity, every object of the actual
centre is a finite binary sum of simple objects. -/
theorem center_finite_simple_sum_of_loop_centrality (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    (X : CategoryTheory.Center C.Obj) : FiniteSimpleSum (CategoryTheory.Center C.Obj) X := by
  let m : CategoryTheory.Center C.Obj → ℕ := fun Z => Module.finrank ℂ (Z ⟶ Z)
  induction X using (measure m).wf.induction with
  | h X ih =>
    by_cases hz : IsZero X
    · exact .zero hz
    · obtain ⟨S, K, hS, ⟨e⟩⟩ := exists_simple_biprod_of_loop_centrality C p hp hslide hne X hz
      letI : Simple S := hS
      letI : ∀ A B : CategoryTheory.Center C.Obj, FiniteDimensional ℂ (A ⟶ B) := by
        intro A B
        letI : FiniteDimensional ℂ (A.1 ⟶ B.1) := IsFusionCategory.hom_finite _ _
        exact Centre.finiteDimensional_hom ℂ A B
      have hs : ¬ IsZero S := by
        intro h
        exact id_nonzero S ((IsZero.iff_id_eq_zero S).mp h)
      have he : Module.finrank ℂ (X ⟶ X) = Module.finrank ℂ (S ⊞ K ⟶ S ⊞ K) :=
        (CategoryTheory.Linear.homCongr ℂ e e).finrank_eq
      have hk : m K < m X := by
        change Module.finrank ℂ (K ⟶ K) < Module.finrank ℂ (X ⟶ X)
        rw [he]
        exact finrank_end_complement_lt S K hs
      exact .cons hS (ih K hk) ⟨e⟩

end PropertyF.Ground.CentreInduction
