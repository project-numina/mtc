module
public import PropertyF.Ground.Dimensions.PivotalTwist
public import PropertyF.Ground.Fusion.Agreement

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

/-- An average of signs can equal a sign only when all positive-weight terms
have that sign. -/
theorem sign_weighted_support {ι : Type} [Fintype ι] (w s : ι → ℝ) (t : ℝ)
    (hw : ∀ k, 0 ≤ w k) (hs : ∀ k, s k * s k = 1) (ht : t * t = 1)
    (heq : ∑ k, w k * s k = t * ∑ k, w k) :
    ∀ k, 0 < w k → s k = t := by
  classical
  have hn : ∀ k, 0 ≤ w k * (1 - t * s k) := by
    intro k
    apply mul_nonneg (hw k)
    have hsq : (t * s k) * (t * s k) = 1 := by rw [show (t * s k) * (t * s k) = (t * t) * (s k * s k) by ring, ht, hs k]; norm_num
    nlinarith [sq_nonneg (t * s k - 1)]
  have hsum : ∑ k, w k * (1 - t * s k) = 0 := by
    calc
      _ = (∑ k, w k) - t * (∑ k, w k * s k) := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = 0 := by rw [heq, ← mul_assoc, ht, one_mul, sub_self]
  intro k hk
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hn k)).1 hsum k (Finset.mem_univ k)
  have hs1 : 1 - t * s k = 0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hk)
  nlinarith [sq_nonneg (s k - t)]

/-- A real fusion character whose absolute values are the positive character
has signs compatible with every nonzero fusion coefficient. -/
theorem sign_character_fusion_support (C : Ground.BraidedFusionCategory.{v,u})
    (d : Fin (Ground.rank C) → ℝ)
    (hd : ∀ i, |d i| = Ground.fpSimple C i)
    (hchar : ∀ i j, d i * d j =
      ∑ k, (Ground.fusionCoeff C i j k : ℝ) * d k) :
    ∀ i j k, Ground.fusionCoeff C i j k ≠ 0 →
      d k / Ground.fpSimple C k =
        (d i / Ground.fpSimple C i) * (d j / Ground.fpSimple C j) := by
  classical
  let f := Ground.fpSimple C
  let s : Fin (Ground.rank C) → ℝ := fun i => d i / f i
  have hf : ∀ i, 0 < f i := Ground.fpSimple_pos C
  have hs : ∀ i, s i * s i = 1 := by
    intro i
    have hsq : d i * d i = f i * f i := by
      have h := congrArg (fun x : ℝ => x * x) (hd i)
      simpa only [abs_mul_abs_self] using h
    dsimp [s]
    field_simp [ne_of_gt (hf i)]
    nlinarith [hsq]
  intro i j k hcoeff
  let w : Fin (Ground.rank C) → ℝ := fun l => (Ground.fusionCoeff C i j l : ℝ) * f l
  have hw : ∀ l, 0 ≤ w l := by
    intro l
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (hf l))
  have ht : (s i * s j) * (s i * s j) = 1 := by
    rw [show (s i * s j) * (s i * s j) = (s i * s i) * (s j * s j) by ring, hs i, hs j]
    norm_num
  have heq : ∑ l, w l * s l = (s i * s j) * ∑ l, w l := by
    calc
      _ = ∑ l, (Ground.fusionCoeff C i j l : ℝ) * d l := by
        apply Finset.sum_congr rfl
        intro l _
        dsimp [w, s]
        field_simp [ne_of_gt (hf l)]
      _ = d i * d j := (hchar i j).symm
      _ = (s i * s j) * (f i * f j) := by
        dsimp [s]
        field_simp [ne_of_gt (hf i), ne_of_gt (hf j)]
      _ = _ := by
        change (s i * s j) * (Ground.fpSimple C i * Ground.fpSimple C j) = _
        rw [Ground.fpSimple_mul]
  apply sign_weighted_support w s (s i * s j) hw hs ht heq k
  exact mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcoeff)) (hf k)

/-- If a pseudo-unitary category already has a spherical structure with real
simple dimensions, twisting it by its signs gives a positive spherical structure. -/
theorem positive_spherical_of_real_spherical_pseudoUnitary
    (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (hpu : Ground.PseudoUnitary C) :
    ∃ q : PivotalStructure (C := C.Obj), q.IsSpherical ∧
      ∀ i, pivotalDimension C q (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  classical
  have hd := (pseudoUnitary_iff_simple_saturation C p hp d hreal).1 hpu
  have hchar : ∀ i j, d i * d j =
      ∑ k, (Ground.fusionCoeff C i j k : ℝ) * d k := by
    intro i j
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast, ← hreal] using
      pivotalDimension_character C p i j
  let s : Fin (Ground.rank C) → ℝ := fun i => d i / Ground.fpSimple C i
  let c : Fin (Ground.rank C) → ℂ := fun i => (s i : ℂ)
  have hsq : ∀ i, d i * d i = Ground.fpSimple C i * Ground.fpSimple C i := by
    intro i
    have h := congrArg (fun x : ℝ => x * x) (hd i)
    simpa only [abs_mul_abs_self] using h
  have hsign : ∀ i, c i * c i = 1 := by
    intro i
    have hfp := ne_of_gt (Ground.fpSimple_pos C i)
    have hr : s i * s i = 1 := by
      dsimp [s]
      field_simp [hfp]
      nlinarith [hsq i]
    change (s i : ℂ) * (s i : ℂ) = 1
    exact_mod_cast hr
  have hc : ∀ i, c i ≠ 0 := by
    intro i h
    have := hsign i
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have hunit : c (Ground.unitIndex C) = 1 := by
    have h := hreal (Ground.unitIndex C)
    obtain ⟨e⟩ := Ground.unitIndex_iso C
    rw [pivotalDimension_iso C p e, pivotalDimension_unit] at h
    have hdunit : d (Ground.unitIndex C) = 1 := by exact_mod_cast h.symm
    simp [c, s, hdunit, Ground.fpSimple_unit]
  have hmul : ∀ i j k, Ground.fusionCoeff C i j k ≠ 0 → c k = c i * c j := by
    intro i j k hk
    have h := sign_character_fusion_support C d hd hchar i j k hk
    change ((d k / Ground.fpSimple C k : ℝ) : ℂ) =
      ((d i / Ground.fpSimple C i : ℝ) : ℂ) * ((d j / Ground.fpSimple C j : ℝ) : ℂ)
    exact_mod_cast h
  let q := pivotalScalarTwist C p c hc hunit hmul
  refine ⟨q, pivotalScalarTwist_spherical C p hp c hc hunit hmul hsign, ?_⟩
  intro i
  rw [pivotalDimension_scalarTwist_simple, hreal]
  have hfp := ne_of_gt (Ground.fpSimple_pos C i)
  have hvalue : s i * d i = Ground.fpSimple C i := by
    dsimp [s]
    field_simp [hfp]
    nlinarith [hsq i]
  change (s i : ℂ) * (d i : ℂ) = (Ground.fpSimple C i : ℂ)
  exact_mod_cast hvalue

end PropertyF.Ground.Dimensions
