module
public import PropertyF.Ground.Cabling.MixedBraid
public import PropertyF.Ground.Cabling.TransportTuple
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C]
attribute [local instance] Abelian.hasFiniteBiproducts

def swapTuple {I : Type} {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 2) → I) : Fin (n + 2) → I :=
  fun j => t (Equiv.swap i.castSucc i.succ j)

lemma swapTuple_zero {I : Type} {n : ℕ} (t : Fin (n + 2) → I) :
    swapTuple 0 t = Fin.cons (t 1) (Fin.cons (t 0) (Fin.tail (Fin.tail t))) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [swapTuple]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [swapTuple]
    · dsimp [swapTuple]
      rw [Equiv.swap_apply_of_ne_of_ne (by intro h; have := congrArg Fin.val h; simp at this) (by intro h; have := congrArg Fin.val h; simp at this)]
      rfl

lemma swapTuple_succ {I : Type} {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 3) → I) :
    swapTuple i.succ t = Fin.cons (t 0) (swapTuple i (Fin.tail t)) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · dsimp [swapTuple]
    rw [Equiv.swap_apply_of_ne_of_ne (by intro h; have := congrArg Fin.val h; simp at this) (by intro h; have := congrArg Fin.val h; simp at this)]
    rfl
  · have heq : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
    simp only [swapTuple, Fin.cons_succ, heq, Equiv.swap_apply_def, Fin.succ_inj, Fin.tail]
    split_ifs <;> rfl

/-- An adjacent crossing carries each tensor tuple into its swapped tuple. -/
theorem tuple_cross {I : Type} [Fintype I] (f : I → C) :
    ∀ (n : ℕ) (i : Fin (n + 1)) (t : Fin (n + 2) → I),
      ∃ g : tupleTensor f (n + 2) t ⟶ tupleTensor f (n + 2) (swapTuple i t),
        tupleTensorInclusion f (n + 2) t ≫ (braidGenerator (⨁ f) n i).asIso.hom =
          g ≫ tupleTensorInclusion f (n + 2) (swapTuple i t) := by
  intro n
  induction n with
  | zero =>
    intro i t
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rw [swapTuple_zero]
    refine ⟨(firstMixedBraid (f (t 0)) (f (t 1)) (tupleTensor f 0 (Fin.tail (Fin.tail t)))).hom, ?_⟩
    exact firstBraid_components f (t 0) (t 1) 0 (Fin.tail (Fin.tail t))
  | succ n ih =>
    intro i t
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [swapTuple_zero]
      refine ⟨(firstMixedBraid (f (t 0)) (f (t 1)) (tupleTensor f (n+1) (Fin.tail (Fin.tail t)))).hom, ?_⟩
      exact firstBraid_components f (t 0) (t 1) (n+1) (Fin.tail (Fin.tail t))
    · obtain ⟨g, hg⟩ := ih j (Fin.tail t)
      rw [swapTuple_succ]
      refine ⟨𝟙 (f (t 0)) ⊗ₘ g, ?_⟩
      exact
        tailBraid_components f (t 0) n j _ _ _ _ g hg
/-- Each categorical crossing permutes the power-sum blocks by its
strand transposition. -/
theorem powerSum_crossing_permutesBlocks (X : C) (k : Fin count → ℕ)
    (n : ℕ) (i : Fin (n + 1)) :
    permutesBlocks (powerSumBlock X k n)
      (sumPowerWordAction X k n (FreeGroup.of i))
      (((tuplePermutation (Fin count) (n + 2)).comp (strandPermutation n)) (FreeGroup.of i)) := by
  let p := ((tuplePermutation (Fin count) (n + 2)).comp (strandPermutation n)) (FreeGroup.of i)
  have hp (t : Fin (n + 2) → Fin count) : p t = swapTuple i t := by
    funext j
    simp [p, tuplePermutation, strandPermutation, swapTuple, Equiv.arrowCongr]
  have h := powerSum_permutesBlocks_of_tupleInclusions X k n i p (fun t => by
    rw [hp t]
    exact tuple_cross (fun a => tensorPower X (k a)) n i t)
  have heval : sumPowerWordAction X k n (FreeGroup.of i) =
      (sumPowersTensorPowerIso X k (n + 2)).conjAut
        (braidGenerator (⨁ fun a => tensorPower X (k a)) n i) := by
    change (sumPowersTensorPowerIso X k (n + 2)).conjAut
      ((FreeGroup.lift (braidGenerator (⨁ fun a => tensorPower X (k a)) n)) (FreeGroup.of i)) = _
    rw [FreeGroup.lift_apply_of]
  change permutesBlocks (powerSumBlock X k n) (sumPowerWordAction X k n (FreeGroup.of i)) p
  rw [heval]
  exact h
end PropertyF
