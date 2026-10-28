module
public import PropertyF.Ground.Calculus.EndTrace
public import PropertyF.Ground.Calculus.UnitaryBlocks
public import PropertyF.Ground.Calculus.RepresentationTrace
public import PropertyF.Ground.Calculus.WeightFacts

/-! Multiplicity weights for the pivotal trace on finite braid-image blocks. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Calculus
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The faithful inclusion of the braid algebra in the full endomorphism
algebra, expressed in their respective matrix-block presentations. -/
def braidToEndBlocks (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (m : Fin (Ground.rank C) → ℕ)
    (e : tensorPower X (n + 2) ≅ ⨁ (fun p : Σ i, Fin (m i) => Ground.simples C p.1))
    (r : ℕ) (d : Fin r → ℕ)
    (b : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ]
      (∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :=
  (groundEndBlockEquiv C _ m e).toAlgHom.comp
    ((braidAlgebra X n).val.comp b.symm.toAlgHom)

/-- The categorical inclusion is faithful, so no finite braid-image block is lost. -/
theorem braidToEndBlocks_injective (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj)
    (n : ℕ) (m : Fin (Ground.rank C) → ℕ)
    (e : tensorPower X (n + 2) ≅ ⨁ (fun p : Σ i, Fin (m i) => Ground.simples C p.1))
    (r : ℕ) (d : Fin r → ℕ)
    (b : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    Function.Injective (braidToEndBlocks C X n m e r d b) := by
  intro x y h
  apply b.symm.injective
  apply Subtype.ext
  apply (groundEndBlockEquiv C _ m e).injective
  exact h

/-- The actual categorical trace on the braid algebra has the paper's
multiplicity-weight formula. Every retained braid block occurs in a simple
constituent's multiplicity space. -/
theorem pivotalTrace_braid_multiplicities
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (p : Dimensions.PivotalStructure (C := C.Obj)) (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ)
    (m : Fin (Ground.rank C) → ℕ)
    (e : tensorPower X (n + 2) ≅ ⨁ (fun q : Σ i, Fin (m i) => Ground.simples C q.1))
    (r : ℕ) (d : Fin r → ℕ) (hd : ∀ j, 0 < d j)
    (b : braidAlgebra X n ≃ₐ[ℂ] ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ) :
    ∃ mult : Fin (Ground.rank C) → Fin r → ℕ,
      (∀ j, ∃ i, 0 < mult i j) ∧
      (∀ i, m i = ∑ j, mult i j * d j) ∧
      ∀ a : braidAlgebra X n,
        scalar (p.rightTrace (a : End (tensorPower X (n + 2))).asHom) =
          ∑ j, (∑ i, (mult i j : ℂ) * scalar (p.rightTrace (𝟙 (Ground.simples C i)))) *
            (b a j).trace := by
  let F := braidToEndBlocks C X n m e r d b
  obtain ⟨mult, hmult, hretained⟩ := faithful_block_representation_multiplicities d m hd F
    (braidToEndBlocks_injective C X n m e r d b)
  have hdim : ∀ i, m i = ∑ j, mult i j * d j := by
    intro i
    have h := hmult i 1
    simp only [map_one, Pi.one_apply, Matrix.trace_one, Fintype.card_fin] at h
    exact_mod_cast h
  refine ⟨mult, hretained, hdim, fun a => ?_⟩
  have hi : ∀ i, (groundEndBlockEquiv C _ m e (a : End (tensorPower X (n + 2))) i).trace =
      ∑ j, (mult i j : ℂ) * (b a j).trace := by
    intro i
    have h := hmult i (b a)
    change (groundEndBlockEquiv C _ m e ((b.symm (b a) : braidAlgebra X n) : End _) i).trace = _ at h
    rw [b.symm_apply_apply] at h
    exact h
  rw [pivotalTrace_groundEndBlocks C p scalar _ m e]
  simp_rw [hi]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Finite categorical braid images admit unitary blocks and natural-number
multiplicities with the actual pivotal trace formula and retention. -/
theorem exists_unitary_braid_trace_blocks
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (hfinite : Finite (braidImage X n))
    (p : Dimensions.PivotalStructure (C := C.Obj)) (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ) :
    ∃ (r : ℕ) (d : Fin r → ℕ)
      (b : braidAlgebra X n ≃ₐ[ℂ] ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ)
      (mult : Fin (Ground.rank C) → Fin r → ℕ),
      (∀ j, 0 < d j) ∧
      (∀ g j, b (groupInImage (braidEndRepresentation X n) g) j ∈
        Matrix.unitaryGroup (Fin (d j)) ℂ) ∧
      (∀ j, ∃ i, 0 < mult i j) ∧
      (∀ i, Module.finrank ℂ (Ground.simples C i ⟶ tensorPower X (n + 2)) =
        ∑ j, mult i j * d j) ∧
      ∀ a : braidAlgebra X n,
        scalar (p.rightTrace (a : End (tensorPower X (n + 2))).asHom) =
          ∑ j, (∑ i, (mult i j : ℂ) * scalar (p.rightTrace (𝟙 (Ground.simples C i)))) *
            (b a j).trace := by
  let m : Fin (Ground.rank C) → ℕ := fun i =>
    Module.finrank ℂ (Ground.simples C i ⟶ tensorPower X (n + 2))
  obtain ⟨e⟩ := Ground.exists_canonical_decomposition C (tensorPower X (n + 2))
  obtain ⟨r, d, b, hnonzero, hunitary⟩ := braidAlgebra_unitary_blocks X n hfinite
  have hd : ∀ j, 0 < d j := fun j => Nat.pos_of_ne_zero (hnonzero j).ne
  obtain ⟨mult, hret, hdim, htrace⟩ :=
    pivotalTrace_braid_multiplicities C X n p scalar m e r d hd b
  exact ⟨r, d, b, mult, hd, hunitary, hret, hdim, htrace⟩

end PropertyF.Ground.Calculus
