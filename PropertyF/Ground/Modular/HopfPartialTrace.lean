module
public import PropertyF.Ground.Modular.SAdditivity
public import PropertyF.Ground.Dimensions.TensorMultiplicativity

/-!
# Partial traces of double braidings

Iterated pivotal trace and Schur's lemma give the normalized S entry as the
scalar partial trace on a simple surviving strand. The Hopf-link product reduces
to the displayed composition law for these partial traces, which remains open.
-/
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Dimensions PropertyF.Ground.Calculus
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular
universe v u

/-- Closing one strand of a double braiding gives the normalized S scalar. -/
theorem partialTrace_doubleBraiding_simple (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (k : Fin (rank D)) (X : D.Obj) :
    rightPartialTrace p (simples D k) X (End.of (doubleBraiding (simples D k) X)) =
      (Ground.unitScalarEquiv D (SEntry p (simples D k) X) / simpleDimension D p k) • 1 := by
  let _ : Simple (simples D k) := simples_simple D k
  let _ : FiniteDimensional ℂ (simples D k ⟶ simples D k) := Ground.IsFusionCategory.hom_finite _ _
  have htrace := rightTrace_partialTrace p (simples D k) X (End.of (doubleBraiding (simples D k) X))
  have h := rightPartialTrace_simple_of_trace_compatibility (simples D k) X p
    (Ground.unitScalarEquiv D) (End.of (doubleBraiding (simples D k) X))
    (simpleDimension_ne_zero D p k) htrace
  exact h

/-- The product formula follows from the precise residual partial-trace
composition law for double braidings. -/
theorem hopf_product_of_partialTrace_composition (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj))
    (hcomp : ∀ i j k : Fin (rank D),
      rightPartialTrace p (simples D k) (simples D i ⊗ simples D j)
          (End.of (doubleBraiding (simples D k) (simples D i ⊗ simples D j))) =
      rightPartialTrace p (simples D k) (simples D i)
          (End.of (doubleBraiding (simples D k) (simples D i))) *
      rightPartialTrace p (simples D k) (simples D j)
          (End.of (doubleBraiding (simples D k) (simples D j)))) :
    ∀ i j k : Fin (rank D),
      Ground.unitScalarEquiv D (SEntry p (simples D i ⊗ simples D j) (simples D k)) *
        simpleDimension D p k = categoricalS D p i k * categoricalS D p j k := by
  intro i j k
  let _ : Simple (simples D k) := simples_simple D k
  have honene : (1 : End (simples D k)) ≠ 0 := by
    intro h
    have hh := congrArg End.asHom h
    exact id_nonzero (simples D k) (by simpa using hh)
  have h := hcomp i j k
  rw [partialTrace_doubleBraiding_simple, partialTrace_doubleBraiding_simple,
    partialTrace_doubleBraiding_simple, smul_mul_smul, one_mul] at h
  have hv := smul_left_injective ℂ honene h
  have hd := simpleDimension_ne_zero D p k
  have hval : Ground.unitScalarEquiv D (SEntry p (simples D k) (simples D i ⊗ simples D j)) *
      simpleDimension D p k =
      Ground.unitScalarEquiv D (SEntry p (simples D k) (simples D i)) *
        Ground.unitScalarEquiv D (SEntry p (simples D k) (simples D j)) := by
    calc
      _ = (Ground.unitScalarEquiv D (SEntry p (simples D k) (simples D i ⊗ simples D j)) /
          simpleDimension D p k) * simpleDimension D p k ^ 2 := by field_simp
      _ = ((Ground.unitScalarEquiv D (SEntry p (simples D k) (simples D i)) /
          simpleDimension D p k) * (Ground.unitScalarEquiv D (SEntry p (simples D k) (simples D j)) /
          simpleDimension D p k)) * simpleDimension D p k ^ 2 := by rw [hv]
      _ = _ := by field_simp
  simpa only [SEntry_symmetric p (simples D k) (simples D i ⊗ simples D j),
    SEntry_symmetric p (simples D k) (simples D i),
    SEntry_symmetric p (simples D k) (simples D j), categoricalS] using hval

end PropertyF.Ground.Modular
