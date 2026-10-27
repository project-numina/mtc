module
public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! A finite balanced nonnegative flow cannot enter a closed set. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground

/-- In a finite balanced flow, a set with no outgoing edges also has no
incoming edges. -/
theorem balanced_flow_no_entry {ι : Type*} [Fintype ι] (b : ι → ι → ℝ)
    (hb : ∀ i j, 0 ≤ b i j)
    (hbalance : ∀ i, (∑ j, b i j) = ∑ j, b j i)
    (s : Finset ι) (hclosed : ∀ i ∈ s, ∀ j ∉ s, b i j = 0)
    (i j : ι) (hi : i ∉ s) (hj : j ∈ s) : b i j = 0 := by
  classical
  have hout : ∑ x ∈ s, ∑ y, b x y = ∑ x ∈ s, ∑ y ∈ s, b x y := by
    apply Finset.sum_congr rfl
    intro x hx
    exact (Finset.sum_subset (Finset.subset_univ s) (fun y _ hy => hclosed x hx y hy)).symm
  have hbal : ∑ x ∈ s, ∑ y, b x y = ∑ x ∈ s, ∑ y, b y x := by
    apply Finset.sum_congr rfl
    intro x _
    exact hbalance x
  have hin : ∑ y ∈ s, ∑ x ∈ s, b x y = ∑ y ∈ s, ∑ x, b x y := by
    calc
      _ = ∑ x ∈ s, ∑ y ∈ s, b x y := Finset.sum_comm
      _ = ∑ x ∈ s, ∑ y, b x y := hout.symm
      _ = _ := hbal
  have hrow (y : ι) (hy : y ∈ s) : ∑ x ∈ s, b x y = ∑ x, b x y := by
    have hle (z : ι) (_ : z ∈ s) : ∑ x ∈ s, b x z ≤ ∑ x, b x z :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun x _ _ => hb x z)
    exact Finset.sum_eq_sum_iff_of_le hle |>.mp hin y hy
  have hzero : ∑ x ∈ Finset.univ \ s, b x j = 0 := by
    have h := Finset.sum_sdiff (f := fun x => b x j) (Finset.subset_univ s)
    rw [← hrow j hj] at h
    linarith
  have hmem : i ∈ Finset.univ \ s := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hb x j)).mp hzero i hmem

/-- Every vertex with an outgoing edge in a finite balanced nonnegative flow
lies on a directed cycle. -/
theorem balanced_flow_cycle {ι : Type*} [Fintype ι] (b : ι → ι → ℝ)
    (hb : ∀ i j, 0 ≤ b i j)
    (hbalance : ∀ i, (∑ j, b i j) = ∑ j, b j i)
    (o : ι) (hout : ∃ j, 0 < b o j) :
    ∃ j, 0 < b o j ∧ Relation.ReflTransGen (fun i j => 0 < b i j) j o := by
  classical
  let r : ι → ι → Prop := fun i j => 0 < b i j
  let s : Finset ι := Finset.univ.filter (fun i => ¬ Relation.ReflTransGen r i o)
  have hc : ∀ i ∈ s, ∀ j ∉ s, b i j = 0 := by
    intro i hi j hj
    have hni : ¬ Relation.ReflTransGen r i o := (Finset.mem_filter.mp hi).2
    have hrj : Relation.ReflTransGen r j o := by
      simpa [s] using hj
    have hnot : ¬ 0 < b i j := fun h => hni (Relation.ReflTransGen.head h hrj)
    exact le_antisymm (not_lt.mp hnot) (hb i j)
  obtain ⟨j, hj⟩ := hout
  have ho : o ∉ s := by simp [s, Relation.ReflTransGen.refl]
  have hjs : j ∉ s := by
    intro hjs
    have hz := balanced_flow_no_entry b hb hbalance s hc o j ho hjs
    linarith
  refine ⟨j, hj, ?_⟩
  simpa [s] using hjs

end PropertyF.Ground
