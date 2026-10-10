module

public import Camus.DP.Correctness

/-!
# Section 2.4: the recurrence for an exact number of reticulations

Section 2.4 of the paper modifies the dynamic program so that it returns, for each `k = 1, …, m`, a
level-1 network `N_k` that contains `T`, has exactly `k` non-tree edges, and maximizes the number of
quartets of `Q` among such networks. The paper describes the array `M[v, k]` ("the solution found
for subtree `T_v` of the network limited to allowing k non-tree edges") but gives no recurrence.
The formalization's recurrence, which follows that description, is defined with the other shared
definitions in `Camus/Defs.lean`, since the Challenge states Section 2.4 with it: a row
`M[v][k]` is a finite set of naturals, empty when no family of exactly `k` added edges is feasible
below `v`, and otherwise the singleton of the best value (`BudgetDP.best`). At a leaf the row of
budget `0` is `{0}` and the others are empty. At an internal vertex `v` (`BudgetDP.cases`), either

* no added edge has target `v`: the budget is split between the two children, by the max-plus
  convolution of their rows (`BudgetDP.convolution`); or
* the edge added above some `(u, w) ∈ Pairs(v)` has target `v` (Equation (3)): it uses one unit of
  budget and contributes its weight `s_e(u, w)`, and the remaining `k − 1` units are distributed
  over the subtrees hanging off the cycle `γ(u, w)`, whose rows are combined as in Equations (4)
  and (5) by a knapsack (`BudgetDP.forest`), which keeps only the maximum after each convolution.

This file proves the basic properties of `best` and `convolution`, and defines `allocations`, the
unpruned set of the values of all distributions of the budget over the hanging subtrees, which is
the specification of `forest` used in the proofs.

## Main results

* `BudgetDP.mem_best`, `BudgetDP.best_card_le_one`: `best S` is empty or the maximum of `S`.
* `BudgetDP.mem_convolution`: the elements of a convolution.
* `BudgetDP.allocations`: all distributions of the budget over a list of subtrees.
-/

@[expose] public section

namespace Camus.BudgetDP

open DynamicProgramming

/-- `z ∈ best S` iff `z` is the maximum of `S`. -/
 theorem mem_best {S : Finset ℕ} {z : ℕ} : z ∈ best S ↔ z ∈ S ∧ ∀ x ∈ S, x ≤ z := by
  constructor
  · intro hz
    obtain ⟨hz, heq⟩ := Finset.mem_filter.mp hz
    exact ⟨hz, fun x hx => heq ▸ Finset.le_sup (f := id) hx⟩
  · rintro ⟨hz,hmax⟩
    apply Finset.mem_filter.mpr
    exact ⟨hz, Nat.le_antisymm (Finset.le_sup (f := id) hz) (Finset.sup_le hmax)⟩

/-- Every element of `S` is at most the value kept in `best S`. -/
 theorem exists_best_ge {S : Finset ℕ} {z : ℕ} (hz : z ∈ S) :
    ∃ m ∈ best S, z ≤ m := by
  have hn : S.Nonempty := ⟨z,hz⟩
  refine ⟨S.sup id, ?_, Finset.le_sup (f := id) hz⟩
  apply (mem_best).mpr
  exact ⟨by simpa using (Finset.sup_mem_of_nonempty (f := id) hn), fun x hx => Finset.le_sup (f :=
      id) hx⟩

/-- `best S` has at most one element. -/
 theorem best_card_le_one (S : Finset ℕ) : (best S).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm

/-- `z ∈ convolution A B k` iff `z = a + b` with `a ∈ A i`, `b ∈ B j` and `i + j = k`. -/
 theorem mem_convolution {A B : ℕ → Finset ℕ} {k z : ℕ} :
    z ∈ convolution A B k ↔
      ∃ i j a b, i+j=k ∧ a ∈ A i ∧ b ∈ B j ∧ a+b=z := by
  classical
  constructor
  · intro hz
    obtain ⟨i,hi,hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨⟨a,b⟩,hab,heq⟩ := Finset.mem_image.mp hz
    have hi' : i ≤ k := by have := Finset.mem_range.mp hi; omega
    exact ⟨i,k-i,a,b,by omega,(Finset.mem_product.mp hab).1,(Finset.mem_product.mp hab).2,heq⟩
  · rintro ⟨i,j,a,b,hij,ha,hb,rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_range.mpr (by omega),Finset.mem_image.mpr ?_⟩
    exact ⟨(a,b),Finset.mem_product.mpr ⟨ha,by simpa [show k-i=j by omega] using hb⟩,rfl⟩

/-- The values of all distributions of the budget `k` over the subtrees `rs`: the sums `Σ_r s_r`
with `s_r ∈ M r (b_r)` and `Σ_r b_r = k` (`mem_allocations`). This is the specification of the
knapsack `forest`, which keeps only the maxima and has the same maximum (`forest_sound`,
`forest_upper`). -/
def allocations (M : Address → ℕ → Finset ℕ) : List Address → ℕ → Finset ℕ
  | [], k => if k=0 then {0} else ∅
  | r::rs, k => convolution (M r) (allocations M rs) k

end Camus.BudgetDP
