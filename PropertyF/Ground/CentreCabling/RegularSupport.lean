module
public import PropertyF.Ground.Modular.CharacterStar
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Modular.SSquare
public import PropertyF.Ground.Fusion.Reciprocity

/-!
# Fusion centralizers and Fourier support

The equality locus of a fusion character is closed under constituents.
Fourier inversion and the FP-weighted regular eigenvector then give the
numerical double-centralizer inclusion.
-/
@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u
variable (D : Ground.BraidedFusionCategory.{v,u})
  (p : Dimensions.PivotalStructure (C := D.Obj))

/-- Two simple labels satisfy the numerical S-matrix centrality test. -/
abbrev sCentralizes (i j : Fin (rank D)) : Prop :=
  Modular.categoricalS D p i j = Modular.simpleDimension D p i * Modular.simpleDimension D p j

/-- The labels satisfying the numerical S-centrality test against a set. -/
abbrev sCentralizer (A : Set (Fin (rank D))) : Set (Fin (rank D)) :=
  {j | ∀ i ∈ A, sCentralizes D p i j}

/-- Numerical S-centrality is symmetric. -/
theorem sCentralizes_symm {D : Ground.BraidedFusionCategory.{v,u}}
    {p : Dimensions.PivotalStructure (C := D.Obj)} {i j : Fin (rank D)}
    (h : sCentralizes D p i j) : sCentralizes D p j i :=
  (Modular.categoricalS_symmetric D p j i).trans <|
    h.trans (mul_comm (Modular.simpleDimension D p i) (Modular.simpleDimension D p j))

/-- FP-valued simple dimensions are fixed by complex conjugation. -/
theorem realSimpleDimensions_of_fp {D : Ground.BraidedFusionCategory.{v,u}}
    {p : Dimensions.PivotalStructure (C := D.Obj)} (hdim : Modular.HasFPSimpleDimensions D p) :
    Modular.HasRealSimpleDimensions D p := fun j ↦ by
  rw [hdim]
  simp

/-- The numerical S-centralizer is closed under dual labels when dimensions
are the positive FP dimensions. -/
theorem sCentralizes_dual {D : Ground.BraidedFusionCategory.{v,u}}
    {p : Dimensions.PivotalStructure (C := D.Obj)} (hdim : Modular.HasFPSimpleDimensions D p)
    {i y : Fin (rank D)} (hi : sCentralizes D p i y) :
    sCentralizes D p (dualIndex D i) y := by
  dsimp only [sCentralizes] at hi ⊢
  have hreal := realSimpleDimensions_of_fp hdim
  rw [Modular.categoricalS_dual_conj D p hreal i y, hi, map_mul, hreal, hreal]
  rw [hdim (dualIndex D i), fpSimple_dual, ← hdim i]

end PropertyF.Ground.CentreCabling

open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u
variable {D : Ground.BraidedFusionCategory.{v,u}}
  {p : Dimensions.PivotalStructure (C := D.Obj)}
  (hp : p.IsSpherical) (hdet : (Modular.categoricalS D p).det ≠ 0)
  (hreal : Modular.HasRealSimpleDimensions D p)

include hp hdet hreal in
/-- The S-transform of a vector, inverted using the categorical S-square identity. -/
theorem categoricalS_fourier_inversion
    (f : Fin (rank D) → ℂ) (x : Fin (rank D)) :
    (∑ y, Modular.categoricalS D p x y *
      (∑ i, Modular.categoricalS D p y i * f i)) =
      globalDimension D * f (dualIndex D x) := by
  classical
  calc
    _ = ∑ i, (∑ y, Modular.categoricalS D p x y * Modular.categoricalS D p y i) * f i := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ i, (if x = dualIndex D i then globalDimension D else 0) * f i := by
      simp_rw [Modular.categoricalS_square D p hp hdet hreal]
    _ = globalDimension D * f (dualIndex D x) := by
      simp only [(dualIndex_involutive D).eq_iff.symm, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- A weighted sum may be factored using an equality on the weight's support. -/
theorem sum_mul_eq_mul_sum_of_supported {ι R : Type*} [Fintype ι] [Semiring R]
    (s : Set ι) (f g w : ι → R) (c : R)
    (hw : ∀ i ∉ s, w i = 0) (hfg : ∀ i ∈ s, f i = c * g i) :
    (∑ i, f i * w i) = c * ∑ i, g i * w i := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hi : i ∈ s
  · rw [hfg i hi, mul_assoc]
  · simp [hw i hi]

include hp hdet hreal in
/-- If the S-transform of a vector is supported on a set of labels and its
unit coefficient is nonzero, any label centralizing that support has a
nonzero dual coefficient in the original vector. -/
theorem nonzero_dual_coefficient_of_sCentralizer
    {f : Fin (rank D) → ℂ} {core : Set (Fin (rank D))}
    (hunit : f (unitIndex D) ≠ 0)
    (hsupport : ∀ y, y ∉ core → ∑ i, Modular.categoricalS D p y i * f i = 0)
    {x : Fin (rank D)} (hx : ∀ y ∈ core, sCentralizes D p x y) :
    f (dualIndex D x) ≠ 0 := by
  classical
  let T (y : Fin (rank D)) := ∑ i, Modular.categoricalS D p y i * f i
  have heq : (∑ y, Modular.categoricalS D p x y * T y) =
      Modular.simpleDimension D p x *
        (∑ y, Modular.categoricalS D p (unitIndex D) y * T y) := by
    refine sum_mul_eq_mul_sum_of_supported core _ _ T _ hsupport fun y hy ↦ ?_
    rw [hx y hy, Modular.categoricalS_symmetric D p (unitIndex D) y,
      Modular.categoricalS_unit]
  dsimp only [T] at heq
  rw [categoricalS_fourier_inversion hp hdet hreal f x,
    categoricalS_fourier_inversion hp hdet hreal f (unitIndex D), Ground.dualIndex_unit D] at heq
  exact fun hz ↦ (mul_ne_zero (Modular.simpleDimension_ne_zero D p x)
    (mul_ne_zero (Modular.globalDimension_ne_zero_of_invertibleS D p hp hdet hreal) hunit))
      (by simpa only [hz, mul_zero] using heq.symm)

include hp hdet in
/-- A vector supported on generated labels proves the exact double-centralizer
inclusion once its S-transform is supported on the chosen core. The support
hypotheses are explicit: this theorem does not establish the required
regular-vector identity. -/
theorem doubleCentralizer_of_fourier_support
    (hdim : Modular.HasFPSimpleDimensions D p)
    {f : Fin (rank D) → ℂ} {core generated : Set (Fin (rank D))}
    (hunit : f (unitIndex D) ≠ 0)
    (hgenerated : ∀ y, f y ≠ 0 → y ∈ generated)
    (hsupport : ∀ y, y ∉ core → ∑ i, Modular.categoricalS D p y i * f i = 0) :
    sCentralizer D p core ⊆ generated := fun x hx ↦ hgenerated x <| by
  simpa only [dualIndex_involutive D x] using
    nonzero_dual_coefficient_of_sCentralizer hp hdet (realSimpleDimensions_of_fp hdim)
      hunit hsupport (x := dualIndex D x)
      (fun y hy ↦ sCentralizes_dual hdim (sCentralizes_symm (hx y hy)))

end PropertyF.Ground.CentreCabling

open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u
variable {D : Ground.BraidedFusionCategory.{v,u}}
  {p : Dimensions.PivotalStructure (C := D.Obj)}

/-- A character pairing with an eigenvector has the same eigenvalue on both sides. -/
theorem sum_mul_eigenvalue {ι R : Type*} [Fintype ι] [CommSemiring R]
    (N : ι → ι → R) (χ f : ι → R) {c d : R}
    (hχ : ∀ i, c * χ i = ∑ k, N i k * χ k)
    (hf : ∀ k, ∑ i, N i k * f i = d * f k) :
    c * (∑ i, χ i * f i) = d * ∑ i, χ i * f i := by
  classical
  calc
    _ = ∑ i, (c * χ i) * f i := by simp [Finset.mul_sum, mul_assoc]
    _ = ∑ i, ∑ k, N i k * χ k * f i := by simp_rw [hχ, Finset.sum_mul]
    _ = ∑ k, χ k * ∑ i, N i k * f i := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, mul_left_comm, mul_comm]
    _ = d * ∑ i, χ i * f i := by
      simp_rw [hf, Finset.mul_sum]
      simp only [mul_left_comm]

/-- The S-transform of a common FP eigenvector vanishes at every label whose
normalized S character differs from the FP character on a chosen label. -/
theorem fourier_eq_zero_of_fusion_eigenvector
    (hdim : Modular.HasFPSimpleDimensions D p)
    {f : Fin (rank D) → ℂ} {a y : Fin (rank D)}
    (heigen : ∀ k, ∑ i, (fusionCoeff D a i k : ℂ) * f i = (fpSimple D a : ℂ) * f k)
    (hne : Modular.categoricalS D p a y ≠
      Modular.simpleDimension D p a * Modular.simpleDimension D p y) :
    ∑ i, Modular.categoricalS D p y i * f i = 0 := by
  classical
  let χ (i : Fin (rank D)) := Modular.categoricalS D p i y / Modular.simpleDimension D p y
  let T : ℂ := ∑ i, χ i * f i
  have ht : χ a * T = (fpSimple D a : ℂ) * T := by
    apply sum_mul_eigenvalue (fun i k ↦ (fusionCoeff D a i k : ℂ)) χ f
    · intro i
      exact Modular.categoricalS_verlinde D p a i y
    · exact heigen
  have hχ : χ a ≠ (fpSimple D a : ℂ) := fun h ↦ hne <| by
    simpa [χ, hdim] using (div_eq_iff (Modular.simpleDimension_ne_zero D p y)).mp h
  have hT : T = 0 := (mul_eq_mul_right_iff.mp ht).resolve_left hχ
  have hs : (∑ i, Modular.categoricalS D p y i * f i) = Modular.simpleDimension D p y * T := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Modular.categoricalS_symmetric D p y i]
    dsimp [χ]
    field_simp [Modular.simpleDimension_ne_zero D p y]
  rw [hs, hT, mul_zero]

/-- A set of simple labels is closed under fusion constituents. -/
abbrev IsFusionClosed (D : Ground.BraidedFusionCategory.{v,u}) (A : Finset (Fin (rank D))) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ k, 0 < fusionCoeff D a b k → k ∈ A

/-- Fusion coefficients vanish outside a fusion-closed set. -/
theorem IsFusionClosed.fusionCoeff_eq_zero {A : Finset (Fin (rank D))}
    (hA : IsFusionClosed D A) {a b k : Fin (rank D)}
    (ha : a ∈ A) (hb : b ∈ A) (hk : k ∉ A) : fusionCoeff D a b k = 0 :=
  Nat.eq_zero_of_not_pos (fun h ↦ hk (hA a ha b hb k h))

/-- The FP-weighted regular vector of a dual- and fusion-closed set of labels
is an eigenvector for multiplication by each label in that set. -/
theorem regular_vector_fusion_eigenvector
    {A : Finset (Fin (rank D))}
    (hdual : ∀ a ∈ A, dualIndex D a ∈ A)
    (hclosed : IsFusionClosed D A)
    {a : Fin (rank D)} (ha : a ∈ A) (k : Fin (rank D)) :
    (∑ i, (fusionCoeff D a i k : ℂ) * (if i ∈ A then (fpSimple D i : ℂ) else 0)) =
      (fpSimple D a : ℂ) * (if k ∈ A then (fpSimple D k : ℂ) else 0) := by
  classical
  by_cases hk : k ∈ A
  · simp only [hk, ite_true]
    calc
      _ = ∑ i, (fusionCoeff D (dualIndex D a) k i : ℂ) * (fpSimple D i : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Modular.fusionCoeff_dual_adjoint D a i k]
        by_cases hi : i ∈ A
        · simp [hi]
        · simp [hi, hclosed.fusionCoeff_eq_zero (hdual a ha) hk hi]
      _ = (fpSimple D a : ℂ) * (fpSimple D k : ℂ) := by
        have hh := congrArg (fun z : ℝ => (z : ℂ)) (fpSimple_mul D (dualIndex D a) k)
        simpa [fpSimple_dual] using hh.symm
  · simp only [hk, ite_false, mul_zero]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ A
    · simp [hi, hclosed.fusionCoeff_eq_zero ha hi hk]
    · simp [hi]

/-- Numerical double-centralizer theorem for a fusion-closed set of simple
labels. The supplied core must contain its numerical S-centralizer. -/
theorem doubleCentralizer_of_fusion_closed
    (hp : p.IsSpherical)
    (hdet : (Modular.categoricalS D p).det ≠ 0)
    (hdim : Modular.HasFPSimpleDimensions D p)
    {A : Finset (Fin (rank D))} {core : Set (Fin (rank D))}
    (hunit : unitIndex D ∈ A)
    (hdual : ∀ a ∈ A, dualIndex D a ∈ A)
    (hclosed : IsFusionClosed D A)
    (hcore : sCentralizer D p (↑A : Set _) ⊆ core) :
    sCentralizer D p core ⊆ (↑A : Set _) := by
  classical
  let f (i : Fin (rank D)) : ℂ := if i ∈ A then (fpSimple D i : ℂ) else 0
  have hu : f (unitIndex D) ≠ 0 := by
    simp [f, hunit, ne_of_gt (fpSimple_pos D (unitIndex D))]
  have hgen (i) (hi : f i ≠ 0) : i ∈ A := by
    by_contra hn
    exact hi (by simp [f, hn])
  have hs (y) (hy : y ∉ core) : ∑ i, Modular.categoricalS D p y i * f i = 0 := by
    obtain ⟨a, ha, hne⟩ : ∃ a ∈ A, ¬sCentralizes D p a y := by
      simpa only [sCentralizer, Set.mem_ofPred_eq, Finset.mem_coe, not_forall, exists_prop] using
        (show y ∉ sCentralizer D p (↑A : Set _) from fun h ↦ hy (hcore h))
    exact fourier_eq_zero_of_fusion_eigenvector hdim
      (regular_vector_fusion_eigenvector hdual hclosed ha) hne
  exact doubleCentralizer_of_fourier_support hp hdet hdim hu hgen hs

end PropertyF.Ground.CentreCabling
