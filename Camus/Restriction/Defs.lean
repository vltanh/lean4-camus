module

public import Camus.DP.Correctness

/-!
# Section 2.4: the recurrence for an exact number of reticulations

Section 2.4 of the paper modifies the dynamic program so that it returns, for each `k = 1, …, m`, a
level-1 network `N_k` that contains `T`, has exactly `k` non-tree edges, and maximizes the number of
quartets of `Q` among such networks. The paper describes the array `M[v, k]` ("the solution found
for subtree `T_v` of the network limited to allowing k non-tree edges") but gives no recurrence.
This file defines the formalization's own recurrence, following that description.

A family of added edges is feasible below `v` (`DynamicProgramming.FeasibleBelow`) when its pairs
are admissible, their cycles share no vertex of `T` (`EdgeAbove.CycleSeparated`, so that the network
is level-1), and their targets lie in `T_v`; its value is the sum of the weights of its edges. A
row `M[v][k]` is a finite set of naturals: empty when no family of exactly `k` added edges is
feasible below `v`, and otherwise the singleton of the best value (`best`). At a leaf the row of
budget `0` is `{0}` and the others are empty. At an internal vertex `v` (`cases`), either

* no added edge has target `v`: the budget is split between the two children, by the max-plus
  convolution of their rows (`convolution`); or
* the edge added above some `(u, w) ∈ Pairs(v)` has target `v` (Equation (3)): it uses one unit of
  budget and contributes its weight `s_e(u, w)`, and the remaining `k − 1` units are distributed
  over the subtrees hanging off the cycle `γ(u, w)`, whose rows are combined as in Equations (4)
  and (5) by a knapsack (`forest`).

`forest` keeps only the maximum after each convolution. `allocations` is the unpruned set of the
values of all distributions of the budget; it is the specification of `forest` used in the proofs.

## Main definitions

* `BudgetDP.best`, `BudgetDP.convolution`, `BudgetDP.allocations`, `BudgetDP.forest`.
* `BudgetDP.cases`: the candidate values of a row, from the two cases above.
* `BudgetDP.Array`: `M` satisfies the recurrence at every vertex and budget.
-/

@[expose] public section

namespace Camus.BudgetDP

open DynamicProgramming

/-- The row kept from a finite set `S` of candidate values: empty if `S` is empty, and otherwise the
singleton of the maximum of `S`. -/
def best (S : Finset ℕ) : Finset ℕ := S.filter (fun z => z = S.sup id)

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
  exact ⟨by simpa using (Finset.sup_mem_of_nonempty (f := id) hn), fun x hx => Finset.le_sup (f := id) hx⟩

/-- `best S` has at most one element. -/
 theorem best_card_le_one (S : Finset ℕ) : (best S).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm

/-- The ways to split the budget `k` between two rows `A` and `B`: the sums `a + b` with `a ∈ A i`,
`b ∈ B j` and `i + j = k`. Followed by `best`, this is the max-plus convolution of the rows. -/
def convolution (A B : ℕ → Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (k+1)).biUnion fun i =>
    (A i ×ˢ B (k-i)).image (fun xy => xy.1 + xy.2)

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

/-- The knapsack over the subtrees `rs` hanging off a cycle: their rows are combined one at a time
by `convolution`, keeping only the maximum after each step, so every intermediate row is empty or a
singleton. -/
def forest (M : Address → ℕ → Finset ℕ) : List Address → ℕ → Finset ℕ
  | [], k => if k=0 then {0} else ∅
  | r::rs, k => best (convolution (M r) (forest M rs) k)

/-- Section 2.4, the formalization's recurrence: the candidate values of row `k` at the vertex `v`,
for edge weights `w` (in applications, `s_e` of Equation (1)). At a leaf, `0` for `k = 0` and none
otherwise. At an internal vertex, the values of `convolution` of the children's rows (no added edge
has target `v`, the first case of Equation (2)), together with, for `k ≥ 1`, the values `w e + z`
where `e ∈ Pairs(v)` and `z` is in row `k − 1` of the knapsack over the subtrees hanging off the
cycle of `e` (Equations (3)–(5)). -/
noncomputable def cases (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (v : Address) (k : ℕ) : Finset ℕ :=
  match t.nodeAt v with
  | some (.leaf _) => if k=0 then {0} else ∅
  | some (.fork _ _) => convolution (M (v++[false])) (M (v++[true])) k ∪
      if k=0 then ∅ else (pairsAt t v).biUnion fun e =>
        (forest M (hanging t e).toList (k-1)).image (fun z => w e + z)
  | none => ∅

/-- Section 2.4: `M` satisfies the recurrence. At every vertex `v` of `T` and every budget `k`, the
row `M v k` is `best (cases t w M v k)`. Such an `M` exists (`exists_array`). -/
def Array (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ) : Prop :=
  ∀ v ∈ t.nodes, ∀ k, M v k = best (cases t w M v k)

end Camus.BudgetDP
