module
public import PropertyF.Ground.CentreDimensions.PivotalTwist
public import PropertyF.Ground.Dimensions.SimpleHomBasis

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.BraidedCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
set_option backward.isDefEq.respectTransparency false in
/-- Pivotal traces are dimension-weighted ordinary traces on simple Hom spaces. -/
theorem pivotalTrace_eq_simpleHom_trace_sum (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) (g : X ⟶ X) :
    Ground.unitScalar C (p.rightTrace g) =
      ∑ k, LinearMap.trace ℂ _ (Linear.rightComp ℂ (Ground.simples C k) g) *
        pivotalDimension C p (Ground.simples C k) := by
  classical
  let V := simplePiecesObject C X
  let e := simpleDecomposition C X
  let f : (⨁ V) ⟶ (⨁ V) := e.inv ≫ g ≫ e.hom
  have heq : p.rightTrace g = p.rightTrace f := by
    have h := p.rightTrace_cyclic e.hom (e.inv ≫ g)
    simpa [f, Category.assoc] using h
  obtain ⟨c, hc, ht⟩ := rightTrace_biproduct_simple V
    (fun a => Ground.simples_simple C a.1) (fun a => Ground.IsFusionCategory.hom_finite _ _) p f
  rw [heq, ht]
  simp only [← groundUnitScalarEquiv_apply, map_sum, map_smul, smul_eq_mul, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  have hblock : ∀ t, biproduct.ι V ⟨k, t⟩ ≫ e.inv ≫ g ≫ e.hom ≫ biproduct.π V ⟨k, t⟩ =
      c ⟨k, t⟩ • 𝟙 (Ground.simples C k) := by
    intro t
    simpa [f, Category.assoc] using hc ⟨k, t⟩
  have hs := simpleHom_postcomp_trace C X k g (fun t => c ⟨k,t⟩) hblock
  rw [hs, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  change c ⟨k, t⟩ * (groundUnitScalarEquiv C (p.rightTrace (𝟙 (Ground.simples C k)))) =
    c ⟨k, t⟩ * pivotalDimension C p (Ground.simples C k)
  rw [groundUnitScalarEquiv_apply]
  rfl
/-- A categorical involution has real pivotal trace when all simple
pivotal dimensions are real. -/
theorem pivotalTrace_involution_real (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (d : Fin (Ground.rank C) → ℝ)
    (hd : ∀ k, pivotalDimension C p (Ground.simples C k) = (d k : ℂ))
    (X : C.Obj) (g : X ⟶ X) (hg : g ≫ g = 𝟙 X) :
    (Ground.unitScalar C (p.rightTrace g)).im = 0 := by
  rw [pivotalTrace_eq_simpleHom_trace_sum]
  simp only [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro k _
  let : FiniteDimensional ℂ (Ground.simples C k ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
  let T := Linear.rightComp ℂ (Ground.simples C k) g
  have hT : T * T = 1 := by
    ext f
    change (f ≫ g) ≫ g = f
    rw [Category.assoc, hg, Category.comp_id]
  obtain ⟨n, hn, _⟩ := involution_trace_integer_bound T hT
  change (LinearMap.trace ℂ _ T * pivotalDimension C p (Ground.simples C k)).im = 0
  rw [hn, hd]
  simp

/-- A self-transparent simple has real twist scalar whenever the pivotal
simple dimensions are real. -/
theorem pivotalBraidedTwistScalar_real_of_involutive (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (d : Fin (Ground.rank C) → ℝ)
    (hd : ∀ k, pivotalDimension C p (Ground.simples C k) = (d k : ℂ))
    (i : Fin (Ground.rank C))
    (hc : (β_ (Ground.simples C i) (Ground.simples C i)).hom ≫
        (β_ (Ground.simples C i) (Ground.simples C i)).hom = 𝟙 _) :
    letI : Simple (Ground.simples C i) := Ground.simples_simple C i
    (pivotalBraidedTwistScalar C p (Ground.simples C i)).im = 0 := by
  let X := Ground.simples C i
  let : Simple X := Ground.simples_simple C i
  have h := pivotalTrace_involution_real C p d hd (X ⊗ X) (β_ X X).hom hc
  rw [pivotalTrace_selfBraiding, hd] at h
  have hn : d i ≠ 0 := by
    intro hz
    have hdim := pivotalDimension_simple_ne_zero C p i
    apply hdim
    rw [hd, hz]
    rfl
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_right hn

/-- A finite-order twist on a self-transparent simple is a sign. -/
theorem pivotalBraidedTwistScalar_sign_of_finite_order (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (d : Fin (Ground.rank C) → ℝ)
    (hd : ∀ k, pivotalDimension C p (Ground.simples C k) = (d k : ℂ))
    (i : Fin (Ground.rank C))
    (hc : (β_ (Ground.simples C i) (Ground.simples C i)).hom ≫
        (β_ (Ground.simples C i) (Ground.simples C i)).hom = 𝟙 _)
    (n : ℕ) (hn : n ≠ 0)
    (hfinite : letI : Simple (Ground.simples C i) := Ground.simples_simple C i
      pivotalBraidedTwistScalar C p (Ground.simples C i) ^ n = 1) :
    letI : Simple (Ground.simples C i) := Ground.simples_simple C i
    pivotalBraidedTwistScalar C p (Ground.simples C i) = 1 ∨
      pivotalBraidedTwistScalar C p (Ground.simples C i) = -1 := by
  let : Simple (Ground.simples C i) := Ground.simples_simple C i
  let z := pivotalBraidedTwistScalar C p (Ground.simples C i)
  have him : z.im = 0 := pivotalBraidedTwistScalar_real_of_involutive C p d hd i hc
  have hz : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  change z ^ n = 1 at hfinite
  change z = 1 ∨ z = -1
  have hp : z.re ^ n = 1 := by
    rw [hz] at hfinite
    exact_mod_cast hfinite
  rcases (pow_eq_one_iff_of_ne_zero hn).1 hp with h | ⟨h, _⟩
  · left
    rw [hz, h]
    rfl
  · right
    rw [hz, h]
    simp

end PropertyF.Ground.Dimensions
