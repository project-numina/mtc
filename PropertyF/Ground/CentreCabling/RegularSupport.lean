module
public import PropertyF.Ground.Modular.CharacterStar
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Modular.SSquare
public import PropertyF.Ground.Fusion.Reciprocity

/-!
# Fusion centralizers and Fourier support

The equality locus of a fusion character is closed under constituents.
Fourier inversion and the FP-weighted regular eigenvector then give the
numerical double-centralizer inclusion. The local notations `S D p` and
`dim D p` denote the categorical S-matrix and simple dimensions.
-/
@[expose] public noncomputable section
open PropertyF.Ground.Modular
  (HasFPSimpleDimensions HasRealSimpleDimensions IsFPSpherical sCentralizes sCentralizer)
open PropertyF.Ground.Dimensions
open scoped BigOperators
local notation "S" => PropertyF.Ground.Modular.categoricalS
local notation "dim" => PropertyF.Ground.Modular.simpleDimension
namespace PropertyF.Ground.CentreCabling
universe v u
variable {D : Ground.BraidedFusionCategory.{v,u}}
  {p : PivotalStructure (C := D.Obj)}

/-- The S-matrix transform of a vector on the simple labels. -/
abbrev sFourier (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (f : Fin (rank D) → ℂ) (y : Fin (rank D)) : ℂ :=
  ∑ i, S D p y i * f i

/-- The S-transform of a vector vanishes outside the given set. -/
abbrev FourierSupportedOn (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (f : Fin (rank D) → ℂ)
    (core : Set (Fin (rank D))) : Prop :=
  ∀ y ∉ core, sFourier D p f y = 0

/-- Numerical S-centrality is symmetric. -/
theorem sCentralizes_symm {i j : Fin (rank D)}
    (h : sCentralizes D p i j) : sCentralizes D p j i :=
  (Modular.categoricalS_symmetric D p j i).trans <|
    h.trans (mul_comm (dim D p i) (dim D p j))

/-- FP-valued simple dimensions are fixed by complex conjugation. -/
theorem realSimpleDimensions_of_fp (hdim : HasFPSimpleDimensions D p) :
    HasRealSimpleDimensions D p := fun j ↦ by simp [hdim]

/-- The numerical S-centralizer is closed under dual labels when dimensions
are the positive FP dimensions. -/
theorem sCentralizes_dual (hdim : HasFPSimpleDimensions D p)
    {i y : Fin (rank D)} (hi : sCentralizes D p i y) :
    sCentralizes D p (dualIndex D i) y := by
  dsimp only [sCentralizes] at hi ⊢
  have hreal := realSimpleDimensions_of_fp hdim
  rw [Modular.categoricalS_dual_conj D p hreal i y, hi, map_mul, hreal, hreal,
    hdim (dualIndex D i), fpSimple_dual, ← hdim i]

end PropertyF.Ground.CentreCabling

open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u
variable {D : Ground.BraidedFusionCategory.{v,u}}
  {p : PivotalStructure (C := D.Obj)}
  (hp : p.IsSpherical) (hdet : (S D p).det ≠ 0)
  (hreal : HasRealSimpleDimensions D p)

include hp hdet hreal in
/-- The S-transform of a vector, inverted using the categorical S-square identity. -/
theorem categoricalS_fourier_inversion
    (f : Fin (rank D) → ℂ) (x : Fin (rank D)) :
    sFourier D p (sFourier D p f) x = globalDimension D * f (dualIndex D x) := by
  classical
  dsimp only [sFourier]
  calc
    _ = ∑ i, (∑ y, S D p x y * S D p y i) * f i := by
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

variable {f : Fin (rank D) → ℂ} {core : Set (Fin (rank D))}

include hp hdet hreal in
/-- If the S-transform of a vector is supported on a set of labels and its
unit coefficient is nonzero, any label centralizing that support has a
nonzero dual coefficient in the original vector. -/
theorem nonzero_dual_coefficient_of_sCentralizer
    (hunit : f (unitIndex D) ≠ 0)
    (hsupport : FourierSupportedOn D p f core)
    {x : Fin (rank D)} (hx : ∀ y ∈ core, sCentralizes D p x y) :
    f (dualIndex D x) ≠ 0 := by
  classical
  have heq : sFourier D p (sFourier D p f) x =
      dim D p x * sFourier D p (sFourier D p f) (unitIndex D) := by
    refine sum_mul_eq_mul_sum_of_supported core _ _ (sFourier D p f) _ hsupport fun y hy ↦ ?_
    rw [hx y hy, Modular.categoricalS_symmetric D p (unitIndex D) y,
      Modular.categoricalS_unit]
  rw [categoricalS_fourier_inversion hp hdet hreal f x,
    categoricalS_fourier_inversion hp hdet hreal f (unitIndex D), Ground.dualIndex_unit D] at heq
  exact fun hz ↦ (mul_ne_zero (Modular.simpleDimension_ne_zero D p x)
    (mul_ne_zero (Modular.globalDimension_ne_zero_of_invertibleS D p hp hdet hreal) hunit))
      (by simpa only [hz, mul_zero] using heq.symm)

include hdet in
/-- A vector supported on generated labels proves the exact double-centralizer
inclusion once its S-transform is supported on the chosen core. The support
hypotheses are explicit: this theorem does not establish the required
regular-vector identity. -/
theorem doubleCentralizer_of_fourier_support
    (hfp : IsFPSpherical D p) {generated : Set (Fin (rank D))}
    (hunit : f (unitIndex D) ≠ 0)
    (hgenerated : Function.support f ⊆ generated)
    (hsupport : FourierSupportedOn D p f core) :
    sCentralizer D p core ⊆ generated := fun x hx ↦ hgenerated <|
  (dualIndex_involutive D x) ▸
    nonzero_dual_coefficient_of_sCentralizer hfp.1 hdet (realSimpleDimensions_of_fp hfp.2)
      hunit hsupport (x := dualIndex D x)
      (fun y hy ↦ sCentralizes_dual hfp.2 (sCentralizes_symm (hx y hy)))

end PropertyF.Ground.CentreCabling

open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u
variable {D : Ground.BraidedFusionCategory.{v,u}}
  {p : PivotalStructure (C := D.Obj)}

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
      simp_rw [hf, Finset.mul_sum, mul_left_comm]

/-- The S-transform of a common FP eigenvector vanishes at every label whose
normalized S character differs from the FP character on a chosen label. -/
theorem fourier_eq_zero_of_fusion_eigenvector
    (hdim : HasFPSimpleDimensions D p)
    {f : Fin (rank D) → ℂ} {a y : Fin (rank D)}
    (heigen : ∀ k, ∑ i, (fusionCoeff D a i k : ℂ) * f i = (fpSimple D a : ℂ) * f k)
    (hne : S D p a y ≠
      dim D p a * dim D p y) :
    sFourier D p f y = 0 := by
  classical
  let χ (i : Fin (rank D)) := S D p i y / dim D p y
  let T : ℂ := ∑ i, χ i * f i
  have ht : χ a * T = (fpSimple D a : ℂ) * T := by
    apply sum_mul_eigenvalue (fun i k ↦ (fusionCoeff D a i k : ℂ)) χ f
    · intro i
      exact Modular.categoricalS_verlinde D p a i y
    · exact heigen
  have hχ : χ a ≠ (fpSimple D a : ℂ) := fun h ↦ hne <| by
    simpa [χ, hdim] using (div_eq_iff (Modular.simpleDimension_ne_zero D p y)).mp h
  apply (div_eq_zero_iff.mp ?_).resolve_right (Modular.simpleDimension_ne_zero D p y)
  simpa only [sFourier, T, χ, div_mul_eq_mul_div, ← Finset.sum_div,
    Modular.categoricalS_symmetric D p y] using (mul_eq_mul_right_iff.mp ht).resolve_left hχ

/-- A set of simple labels is closed under fusion constituents. -/
abbrev IsFusionClosed (D : Ground.BraidedFusionCategory.{v,u}) (A : Finset (Fin (rank D))) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ k, 0 < fusionCoeff D a b k → k ∈ A

/-- A set of simple labels closed under duals and fusion constituents. -/
structure IsDualFusionClosed (D : Ground.BraidedFusionCategory.{v,u})
    (A : Finset (Fin (rank D))) : Prop where
  dual : ∀ a ∈ A, dualIndex D a ∈ A
  fusion : IsFusionClosed D A

/-- A set of labels containing the unit and closed under duals and fusion. -/
structure IsFusionSubring (D : Ground.BraidedFusionCategory.{v,u})
    (A : Finset (Fin (rank D))) : Prop extends IsDualFusionClosed D A where
  unit : unitIndex D ∈ A

/-- Fusion coefficients vanish outside a fusion-closed set. -/
theorem IsFusionClosed.fusionCoeff_eq_zero {A : Finset (Fin (rank D))}
    (hA : IsFusionClosed D A) {a b k : Fin (rank D)}
    (ha : a ∈ A) (hb : b ∈ A) (hk : k ∉ A) : fusionCoeff D a b k = 0 :=
  Nat.eq_zero_of_not_pos (fun h ↦ hk (hA a ha b hb k h))

/-- The FP-weighted regular vector supported on a set of simple labels. -/
abbrev regularVector (D : Ground.BraidedFusionCategory.{v,u})
    (A : Finset (Fin (rank D))) (i : Fin (rank D)) : ℂ :=
  if i ∈ A then (fpSimple D i : ℂ) else 0

/-- The support of the regular vector is precisely the chosen set. -/
theorem regularVector_ne_zero_iff {A : Finset (Fin (rank D))} {i : Fin (rank D)} :
    regularVector D A i ≠ 0 ↔ i ∈ A := by
  simp [regularVector, ne_of_gt (fpSimple_pos D i)]

/-- Fusion by a label in a fusion-closed set leaves the regular vector supported there. -/
theorem regularVector_mul_eq_zero_of_not_mem {A : Finset (Fin (rank D))}
    (hA : IsFusionClosed D A) {a k : Fin (rank D)} (ha : a ∈ A) (hk : k ∉ A) :
    ∑ i, (fusionCoeff D a i k : ℂ) * regularVector D A i = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ A
  · simp [regularVector, hi, hA.fusionCoeff_eq_zero ha hi hk]
  · rw [show regularVector D A i = 0 from ite_eq_right hi, mul_zero]

/-- On its support, the regular vector has the FP eigenvalue. -/
theorem regularVector_mul_of_mem {A : Finset (Fin (rank D))}
    (hA : IsDualFusionClosed D A) {a k : Fin (rank D)} (ha : a ∈ A) (hk : k ∈ A) :
    (∑ i, (fusionCoeff D a i k : ℂ) * regularVector D A i) =
      (fpSimple D a : ℂ) * (fpSimple D k : ℂ) := by
  classical
  calc
    _ = ∑ i, (fusionCoeff D (dualIndex D a) k i : ℂ) * (fpSimple D i : ℂ) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Modular.fusionCoeff_dual_adjoint D a i k]
      by_cases hi : i ∈ A
      · rw [show regularVector D A i = (fpSimple D i : ℂ) from ite_eq_left hi]
      · simp [regularVector, hi, hA.fusion.fusionCoeff_eq_zero (hA.dual a ha) hk hi]
    _ = (fpSimple D a : ℂ) * (fpSimple D k : ℂ) := by
      simpa [fpSimple_dual] using
        (congrArg (fun z : ℝ ↦ (z : ℂ)) (fpSimple_mul D (dualIndex D a) k)).symm

/-- The FP-weighted regular vector of a dual- and fusion-closed set of labels
is an eigenvector for multiplication by each label in that set. -/
theorem regular_vector_fusion_eigenvector {A : Finset (Fin (rank D))}
    (hA : IsDualFusionClosed D A) {a : Fin (rank D)} (ha : a ∈ A) (k : Fin (rank D)) :
    (∑ i, (fusionCoeff D a i k : ℂ) * regularVector D A i) =
      (fpSimple D a : ℂ) * regularVector D A k := by
  by_cases hk : k ∈ A <;> simp only [regularVector, hk, ↓reduceIte, mul_zero]
  · exact regularVector_mul_of_mem hA ha hk
  · exact regularVector_mul_eq_zero_of_not_mem hA.fusion ha hk

/-- The regular vector's S-transform is supported on a set containing its centralizer. -/
theorem regularVector_fourier_support
    (hdim : HasFPSimpleDimensions D p)
    {A : Finset (Fin (rank D))} {core : Set (Fin (rank D))}
    (hA : IsDualFusionClosed D A) (hcore : sCentralizer D p (↑A : Set _) ⊆ core) :
    FourierSupportedOn D p (regularVector D A) core := by
  intro y hy
  obtain ⟨a, ha, hne⟩ : ∃ a ∈ A, ¬sCentralizes D p a y := by
    simpa only [sCentralizer, Set.mem_ofPred_eq, Finset.mem_coe, not_forall, exists_prop] using
      (show y ∉ sCentralizer D p (↑A : Set _) from fun h ↦ hy (hcore h))
  exact fourier_eq_zero_of_fusion_eigenvector hdim
    (regular_vector_fusion_eigenvector hA ha) hne

/-- Numerical double-centralizer theorem for a fusion-closed set of simple
labels. The supplied core must contain its numerical S-centralizer. -/
theorem doubleCentralizer_of_fusion_closed
    (hfp : IsFPSpherical D p) (hdet : (S D p).det ≠ 0)
    {A : Finset (Fin (rank D))} {core : Set (Fin (rank D))}
    (hA : IsFusionSubring D A)
    (hcore : sCentralizer D p (↑A : Set _) ⊆ core) :
    sCentralizer D p core ⊆ (↑A : Set _) :=
  doubleCentralizer_of_fourier_support hdet hfp (f := regularVector D A)
    (regularVector_ne_zero_iff.mpr hA.unit) (fun _ hi ↦ regularVector_ne_zero_iff.mp hi)
    (regularVector_fourier_support hfp.2 hA.toIsDualFusionClosed hcore)

end PropertyF.Ground.CentreCabling
