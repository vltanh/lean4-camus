module

public import Camus.Complexity.Program
public import Camus.Restriction.Main

/-!
# Section 2.4: the reticulation-restricted program and its running time

Section 2.4 of the paper turns the array `M` into a matrix with a column for each number `k` of
added edges, and states that "we need to solve each of the n original subproblems O(m) times. It
takes O(m²) time to find the correct DP look-ups to solve each problem optimally, thus the running
time of the overall algorithm goes from O(n²(|Q|+n)) to O(n²(|Q|+m³n))". The paper gives no
recurrence for the matrix; the formalization's is `BudgetDP.cases` (`Camus/Defs.lean`). This file
writes the matrix version as a program in the cost monad and proves, for that recurrence, that the
computed rows satisfy it for the budgets `0, …, m` (the program computes the `m + 1` columns
`0, …, m`), and that it performs at most `1000 n²(|Q| + m³n)` operations for `m ≥ 1`. Backtracking
through the matrix, for every budget, is in `Camus/Complexity/BudgetBacktracking.lean`
(`Complexity.camusBudgetNetworks_time`), and the peak memory in
`Camus/Complexity/PeakMemoryBudget.lean`.

The program (`Complexity.camusBudget`) shares the preprocessing, the enumeration of the candidate
pairs with their weights, and the walks of `Camus/Complexity/Program.lean`. A cell of the matrix is
a value of `WithBot ℕ`: `⊥` for an infeasible budget (an empty row of `BudgetDP.Array`) and `z` for
the row `{z}` (`Complexity.toRow`). As in the paper, the columns are computed in order of increasing
`k`, and in each column the vertices bottom-up (`Complexity.budgetFill`). The cell `(v, k)`
(`Complexity.budgetCell`) is the best of the max-plus convolution of the children's columns at `k`
(`Complexity.convAt`, `k + 1` look-ups of each) and, for `k ≥ 1`, of `s_e` plus the knapsack at
budget `k − 1` over the subtrees hanging off the cycle of each pair `e` of the bucket of `v`
(`Complexity.knapsack`: the subtrees one at a time, each convolved with the current row at every
budget `i ≤ k − 1`, `O(k²)` look-ups). The walks list the hanging subtrees in their own order; the
knapsack does not depend on it (`Complexity.forest_congr_perm`).

## Main results

* `Complexity.camusBudget`: the program.
* `Complexity.camusBudget_rows`: for a well-labelled `T`, its rows satisfy
  `M v k = BudgetDP.best (BudgetDP.cases t w M v k)` for all `k ≤ m`, with `w` the weights of
  Equation (1); the candidate values at budget `k` read only the budgets `≤ k`
  (`Complexity.cases_congr_le`).
* `Complexity.camusBudget_agrees`: they agree with the rows of any `BudgetDP.Array` for `k ≤ m`.
* `Complexity.camusBudget_time`: Section 2.4's running time, at most `1000 n² (|Q| + m³ n)`
  operations for `m ≥ 1`.

## Proof (the paper's)

Each of the `|V(T)|` subproblems is solved `m + 1` times, once per column (`Complexity.budgetFill`,
`Complexity.time_budgetFill`). Solving it at `(v, k)` takes `O(m)` look-ups for the convolution of
the children and, for each pair of the bucket of `v`, the walks (`O(n)`) and the knapsack, whose
`O(m²)` look-ups per hanging subtree are the paper's "O(m²) time to find the correct DP look-ups",
over at most `|V(T)|` hanging subtrees (`Complexity.time_knapsack`, `Complexity.time_budgetCell`).
Each candidate pair is in one bucket (`Complexity.candidate_visits`), so the total is `O(n²|Q|)`
for the weights and `O(m · |candidates| · n · m²) = O(n³m³)` for the matrix
(`Complexity.camusBudget_time`).
-/

@[expose] public section

namespace Camus

namespace Complexity

open Timed DynamicProgramming BudgetDP

/-! ### Rows as cells of `WithBot ℕ` -/

/-- The value of a row of candidate values: its maximum, or `⊥` if it is empty. -/
def rowMax (S : Finset ℕ) : WithBot ℕ := S.sup fun z => (z : WithBot ℕ)

/-- The row of a cell: `{z}` for the value `z`, the empty row for `⊥`. -/
def toRow (x : WithBot ℕ) : Finset ℕ := WithBot.recBotCoe ∅ (fun z => {z}) x

@[simp] theorem toRow_bot : toRow ⊥ = ∅ := rfl
@[simp] theorem toRow_coe (z : ℕ) : toRow (z : WithBot ℕ) = {z} := rfl

@[simp] theorem rowMax_toRow (x : WithBot ℕ) : rowMax (toRow x) = x := by
  induction x using WithBot.recBotCoe with
  | bot => rfl
  | coe z =>
    change ({z} : Finset ℕ).sup (fun z => (z : WithBot ℕ)) = z
    simp

/-- `best S` is the row of the value of `S`. -/
theorem best_eq_toRow (S : Finset ℕ) : best S = toRow (rowMax S) := by
  by_cases hS : S.Nonempty
  · have hsup : rowMax S = ((S.sup id : ℕ) : WithBot ℕ) := by
      unfold rowMax
      exact (Finset.coe_sup_of_nonempty hS id).symm
    rw [hsup, toRow_coe]
    ext z
    rw [mem_best, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hmax⟩
      exact le_antisymm (Finset.le_sup (f := id) hz) (Finset.sup_le hmax)
    · rintro rfl
      obtain ⟨y, hy, hyeq⟩ := Finset.exists_mem_eq_sup S hS id
      exact ⟨hyeq ▸ hy, fun x hx => Finset.le_sup (f := id) hx⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    subst hS
    simp [best, rowMax]

@[simp] theorem rowMax_best (S : Finset ℕ) : rowMax (best S) = rowMax S := by
  rw [best_eq_toRow, rowMax_toRow]

theorem rowMax_union (A B : Finset ℕ) : rowMax (A ∪ B) = rowMax A ⊔ rowMax B :=
  Finset.sup_union

/-- Adding a constant to all values of a row adds it to the value of the row. -/
theorem rowMax_image_add (c : ℕ) (A : Finset ℕ) :
    rowMax (A.image (fun z => c + z)) = (c : WithBot ℕ) + rowMax A := by
  unfold rowMax
  rw [Finset.sup_image]
  have h := Finset.apply_sup_eq_sup_comp_of_linearOrder (s := A) (f := fun z => (z : WithBot ℕ))
    (fun x : WithBot ℕ => (c : WithBot ℕ) + x) (fun x y h => add_le_add le_rfl h) (by simp)
  rw [h]
  rfl

/-- The value of the sums of two rows is the sum of their values. -/
theorem rowMax_image_sum (A B : Finset ℕ) :
    rowMax ((A ×ˢ B).image fun xy => xy.1 + xy.2) = rowMax A + rowMax B := by
  unfold rowMax
  rw [Finset.sup_image, Finset.sup_product_left]
  have hinner : ∀ a : ℕ, (B.sup fun b => ((a + b : ℕ) : WithBot ℕ)) =
      (a : WithBot ℕ) + B.sup fun z => (z : WithBot ℕ) := by
    intro a
    rw [Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x : WithBot ℕ => (a : WithBot ℕ) + x)
      (fun x y h => add_le_add le_rfl h) (by simp)]
    simp [Function.comp_def]
  have houter : (A.sup fun a => (a : WithBot ℕ) + B.sup fun z => (z : WithBot ℕ)) =
      (A.sup fun z => (z : WithBot ℕ)) + B.sup fun z => (z : WithBot ℕ) := by
    rw [Finset.apply_sup_eq_sup_comp_of_linearOrder
      (fun x : WithBot ℕ => x + B.sup fun z => (z : WithBot ℕ))
      (fun x y h => add_le_add h le_rfl) (by simp)]
    rfl
  simp only [Function.comp_def]
  simp only [hinner, houter]

/-- The value of the convolution of two rows at the budget `k`: the best sum over the splits
`i + (k − i)` of `k`. -/
theorem rowMax_convolution (A B : ℕ → Finset ℕ) (k : ℕ) :
    rowMax (convolution A B k) =
      (Finset.range (k + 1)).sup fun i => rowMax (A i) + rowMax (B (k - i)) := by
  unfold convolution rowMax
  rw [Finset.sup_biUnion]
  apply Finset.sup_congr rfl
  intro i _
  exact rowMax_image_sum (A i) (B (k - i))

/-- The value of the union of the rows `F x`, `x ∈ s`. -/
theorem rowMax_biUnion {α : Type} [DecidableEq α] (s : Finset α) (F : α → Finset ℕ) :
    rowMax (s.biUnion F) = s.sup fun x => rowMax (F x) := by
  unfold rowMax
  rw [Finset.sup_biUnion]

/-- A loop keeping the larger value computes the supremum over the elements of the list. -/
theorem foldl_sup_eq {α : Type} [DecidableEq α] (f : α → WithBot ℕ) (l : List α) (a : WithBot ℕ) :
    l.foldl (fun acc x => acc ⊔ f x) a = a ⊔ l.toFinset.sup f := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons, ih, List.toFinset_cons, Finset.sup_insert, sup_assoc]

/-! ### The knapsack does not depend on the order of the subtrees -/

/-- The knapsack keeps the best value of all distributions of the budget. -/
theorem forest_eq_best (M : Address → ℕ → Finset ℕ) (rs : List Address) (k : ℕ) :
    forest M rs k = best (allocations M rs k) := by
  ext z
  rw [mem_best]
  constructor
  · intro hz
    refine ⟨forest_sound hz, fun x hx => ?_⟩
    obtain ⟨m, hm, hxm⟩ := forest_upper hx
    have hmz : m = z := Finset.card_le_one.mp (forest_row_card M rs k) m hm z hz
    exact hmz ▸ hxm
  · rintro ⟨hz, hmax⟩
    obtain ⟨m, hm, hzm⟩ := forest_upper hz
    have hmz : m = z := le_antisymm (hmax m (forest_sound hm)) hzm
    exact hmz ▸ hm

/-- The distributions of the budget over a list of distinct subtrees depend only on its set. -/
theorem allocations_congr (M : Address → ℕ → Finset ℕ) {l₁ l₂ : List Address} (h₁ : l₁.Nodup)
    (h₂ : l₂.Nodup) (h : l₁.toFinset = l₂.toFinset) (k : ℕ) :
    allocations M l₁ k = allocations M l₂ k := by
  ext z
  rw [mem_allocations h₁, mem_allocations h₂, h]

/-- The knapsack over a list of distinct subtrees depends only on its set. -/
theorem forest_congr_perm (M : Address → ℕ → Finset ℕ) {l₁ l₂ : List Address} (h₁ : l₁.Nodup)
    (h₂ : l₂.Nodup) (h : l₁.toFinset = l₂.toFinset) (k : ℕ) :
    forest M l₁ k = forest M l₂ k := by
  rw [forest_eq_best, forest_eq_best, allocations_congr M h₁ h₂ h]

/-- The knapsack at budget `k` reads the rows of the subtrees at budgets `≤ k` only. -/
theorem forest_congr_le {M N : Address → ℕ → Finset ℕ} {rs : List Address} {k : ℕ}
    (h : ∀ r ∈ rs, ∀ i ≤ k, M r i = N r i) : forest M rs k = forest N rs k := by
  induction rs generalizing k with
  | nil => rfl
  | cons r rs ih =>
    simp only [forest]
    congr 1
    unfold convolution
    apply Finset.biUnion_congr rfl
    intro i hi
    have hi' : i ≤ k := by have := Finset.mem_range.mp hi; omega
    rw [h r (by simp) i hi', ih (k := k - i) (fun s hs j hj => h s (by simp [hs]) j (by omega))]

/-- Section 2.4: the candidate values at `(v, k)` read the rows of the vertices strictly below `v`
at budgets `≤ k` only. -/
theorem cases_congr_le (t : PhyloTree) (w : Pair → ℕ) {M N : Address → ℕ → Finset ℕ}
    {v : Address} (hv : v ∈ t.nodes) {k : ℕ}
    (h : ∀ r ∈ t.nodes, v <+: r → v ≠ r → ∀ i ≤ k, M r i = N r i) :
    cases t w M v k = cases t w N v k := by
  classical
  obtain ⟨sub, hnode⟩ := (t.mem_nodes_iff v).mp hv
  cases sub with
  | leaf a => simp [cases, hnode]
  | fork l r =>
    have hc (b : Bool) : ∀ i ≤ k, M (v ++ [b]) i = N (v ++ [b]) i :=
      h _ (PhyloTree.child_mem_nodes hnode b) (List.prefix_append _ _) (by simp)
    simp only [cases, hnode]
    congr 1
    · unfold convolution
      apply Finset.biUnion_congr rfl
      intro i hi
      have hi' : i ≤ k := by have := Finset.mem_range.mp hi; omega
      rw [hc false i hi', hc true (k - i) (by omega)]
    · split_ifs with hk
      · rfl
      · apply Finset.biUnion_congr rfl
        intro e he
        obtain ⟨hec, het⟩ := Finset.mem_filter.mp he
        have hae := (Finset.mem_filter.mp hec).2
        rw [forest_congr_le]
        intro r hr i hi
        have hr' : r ∈ hanging t e := Finset.mem_toList.mp hr
        have hgeo := frontier_below (EdgeAbove.footprint_region t e hae) hr'
        exact h r (Finset.mem_filter.mp hr').1 (het ▸ hgeo.1) (het ▸ hgeo.2) i (by omega)

theorem list_range_toFinset (n : ℕ) : (List.range n).toFinset = Finset.range n := by
  ext i
  simp

/-- In `List.range n = K ++ k :: K'`, the budgets before `k` are those below `k`. -/
theorem mem_range_prefix {n k : ℕ} {K K' : List ℕ} (h : List.range n = K ++ k :: K') (i : ℕ) :
    i ∈ K ↔ i < k := by
  have hpw := List.pairwise_lt_range (n := n)
  rw [h, List.pairwise_append] at hpw
  have hk : k < n := List.mem_range.mp (by rw [h]; simp)
  constructor
  · intro hi
    exact hpw.2.2 i hi k (by simp)
  · intro hik
    have hin : i ∈ List.range n := List.mem_range.mpr (by omega)
    rw [h] at hin
    rcases List.mem_append.mp hin with hK | hK
    · exact hK
    · rcases List.mem_cons.mp hK with rfl | hK'
      · omega
      · have := (List.pairwise_cons.mp hpw.2.1).1 i hK'
        omega

/-! ### The program -/

/-- The max-plus convolution of the columns `A` and `B` at the budget `k`: the best sum
`A i + B (k − i)` over `i ≤ k` (`BudgetDP.convolution`). `k + 1` iterations of six operations:
two look-ups, a subtraction, an addition, a comparison and the iteration. -/
def convAt (A B : ℕ → WithBot ℕ) (k : ℕ) : Timed (WithBot ℕ) :=
  forList (fun acc i => do
    let a ← step (A i)
    let b ← steps 2 (B (k - i))
    steps 2 (acc ⊔ (a + b))) (List.range (k + 1)) ⊥

theorem val_convAt (A B : ℕ → WithBot ℕ) (k : ℕ) :
    (convAt A B k).val = (Finset.range (k + 1)).sup fun i => A i + B (k - i) := by
  simp only [convAt, val_forList, val_bind, val_step, val_steps]
  rw [foldl_sup_eq (fun i => A i + B (k - i)), list_range_toFinset, bot_sup_eq]

theorem time_convAt (A B : ℕ → WithBot ℕ) (k : ℕ) : (convAt A B k).time = 6 * (k + 1) := by
  unfold convAt
  rw [time_forList_eq _ _ _ (fun _ => 5) (fun _ _ _ => rfl)]
  simp only [sum_map_const_nat, List.length_range]
  ring

/-- The knapsack over the subtrees `L` at budget `j` (`BudgetDP.forest`): starting from the row of
the empty forest, the column of each subtree in turn is convolved with the current row at every
budget `i ≤ j`. Returns the cell at budget `j`. -/
def knapsack (R : Address × ℕ → WithBot ℕ) (L : List Address) (j : ℕ) : Timed (WithBot ℕ) := do
  let F₀ ← forList (fun F i => steps 2 (Function.update F i (if i = 0 then (0 : WithBot ℕ) else ⊥)))
    (List.range (j + 1)) fun _ => ⊥
  let F ← forList (fun F r => forList (fun F' i => do
      let c ← convAt (fun i => R (r, i)) F i
      step (Function.update F' i c)) (List.range (j + 1)) F) L F₀
  step (F j)

/-- A loop of updates at the keys `0, …, j` writes the value of each key. -/
theorem foldl_update_range {β : Type} (f : ℕ → β) (F : ℕ → β) {j i : ℕ} (hi : i ≤ j) :
    ((List.range (j + 1)).foldl (fun F i => Function.update F i (f i)) F) i = f i := by
  have h := foldl_update_of_mem (fun i => i) f (List.range (j + 1)) F
    (by simpa using List.nodup_range) (List.mem_range.mpr (Nat.lt_succ_of_le hi))
  exact h

/-- The knapsack computes the value of `BudgetDP.forest` over the reversed list. -/
theorem val_knapsack (R : Address × ℕ → WithBot ℕ) (L : List Address) (j : ℕ) :
    (knapsack R L j).val = rowMax (forest (fun r i => toRow (R (r, i))) L.reverse j) := by
  set Mr : Address → ℕ → Finset ℕ := fun r i => toRow (R (r, i)) with hMr
  -- the rows after the subtrees processed so far
  have hloop : ∀ (A : List Address) (F : ℕ → WithBot ℕ),
      (∀ i ≤ j, F i = rowMax (forest Mr A.reverse i)) →
      ∀ i ≤ j, (L.foldl (fun F r => (forList (fun F' i => do
          let c ← convAt (fun i => R (r, i)) F i
          step (Function.update F' i c)) (List.range (j + 1)) F).val) F) i =
        rowMax (forest Mr (A ++ L).reverse i) := by
    induction L with
    | nil => intro A F hF i hi; simpa using hF i hi
    | cons r L ih =>
      intro A F hF i hi
      simp only [List.foldl_cons]
      have hstep : ∀ i ≤ j, ((forList (fun F' i => do
          let c ← convAt (fun i => R (r, i)) F i
          step (Function.update F' i c)) (List.range (j + 1)) F).val) i =
            rowMax (forest Mr (A ++ [r]).reverse i) := by
        intro i hi
        simp only [val_forList, val_bind, val_step]
        rw [foldl_update_range (fun i => (convAt (fun i => R (r, i)) F i).val) F hi,
          val_convAt, List.reverse_append, List.reverse_singleton, List.singleton_append,
          forest, rowMax_best, rowMax_convolution]
        apply Finset.sup_congr rfl
        intro i' hi'
        rw [hF (i - i') (by omega), hMr, rowMax_toRow]
      have := ih (A ++ [r]) _ hstep i hi
      rw [this, List.append_assoc, List.singleton_append]
  simp only [knapsack, val_bind, val_step, val_forList, val_steps]
  have h0 : ∀ i ≤ j, ((List.range (j + 1)).foldl (fun F i => Function.update F i
      (if i = 0 then (0 : WithBot ℕ) else ⊥)) fun _ => ⊥) i = rowMax (forest Mr [].reverse i) := by
    intro i hi
    rw [foldl_update_range _ _ hi]
    by_cases h : i = 0 <;> simp [h, forest, rowMax]
  have := hloop [] _ h0 j le_rfl
  simpa using this

/-- The knapsack takes `O(|L| j²)` time: at most `3 (j + 1) + 1 + |L| (1 + (j + 1)(6 j + 8))`
operations. -/
theorem time_knapsack (R : Address × ℕ → WithBot ℕ) (L : List Address) (j : ℕ) :
    (knapsack R L j).time ≤ 3 * (j + 1) + 1 + L.length * (1 + (j + 1) * (6 * j + 8)) := by
  have hinit : ∀ F : ℕ → WithBot ℕ, (forList (fun F i => steps 2 (Function.update F i
      (if i = 0 then (0 : WithBot ℕ) else ⊥))) (List.range (j + 1)) F).time = 3 * (j + 1) := by
    intro F
    rw [time_forList_eq _ _ _ (fun _ => 2) (fun _ _ _ => rfl)]
    simp only [sum_map_const_nat, List.length_range]
    ring
  have hrow : ∀ (F : ℕ → WithBot ℕ) (r : Address), (forList (fun F' i => do
      let c ← convAt (fun i => R (r, i)) F i
      step (Function.update F' i c)) (List.range (j + 1)) F).time ≤ (j + 1) * (6 * j + 8) := by
    intro F r
    calc
      _ ≤ ((List.range (j + 1)).map fun _ => (6 * j + 7) + 1).sum := by
        apply time_forList_le
        intro F' i hi
        have := List.mem_range.mp hi
        simp only [time_bind, time_convAt, time_step]
        nlinarith
      _ = _ := by simp only [sum_map_const_nat, List.length_range]
  have hmain : ∀ F : ℕ → WithBot ℕ, (forList (fun F r => forList (fun F' i => do
      let c ← convAt (fun i => R (r, i)) F i
      step (Function.update F' i c)) (List.range (j + 1)) F) L F).time ≤
        L.length * (1 + (j + 1) * (6 * j + 8)) := by
    intro F
    calc
      _ ≤ (L.map fun _ => (j + 1) * (6 * j + 8) + 1).sum :=
        time_forList_le _ _ _ _ (fun F r _ => hrow F r)
      _ = _ := by simp only [sum_map_const_nat]; ring
  simp only [knapsack, time_bind, time_step]
  have h1 := hinit fun _ => ⊥
  have h2 := hmain ((forList (fun F i => steps 2 (Function.update F i
      (if i = 0 then (0 : WithBot ℕ) else ⊥))) (List.range (j + 1)) fun _ => ⊥).val)
  omega

/-- The cell `(v, k)` of the matrix (Section 2.4, `BudgetDP.cases`): at a leaf, `0` for `k = 0`
and `⊥` otherwise; at an internal vertex, the best of the convolution of the children's columns at
`k` and, for `k ≥ 1`, of `s_e` plus the knapsack at budget `k − 1` over the subtrees hanging off the
cycle of each pair `e` of the bucket of `v`. -/
def budgetCell (T : Tables) (B : Address → List (Address × Address)) (W : Address × Address → ℕ)
    (R : Address × ℕ → WithBot ℕ) (v : Address) (k : ℕ) : Timed (WithBot ℕ) := do
  let kd ← step (T.kind v)
  match kd with
  | .leaf _ => steps 2 (if k = 0 then (0 : WithBot ℕ) else ⊥)
  | .fork l r => do
      let c ← convAt (fun i => R (l, i)) (fun i => R (r, i)) k
      let b ← steps 2 (if k = 0 then [] else B v)
      forList (fun acc e => do
          let L ← hangingList T e
          let f ← knapsack R L (k - 1)
          let s ← steps 2 (W e)
          steps 2 (acc ⊔ ((s : WithBot ℕ) + f))) b c

/-- `best` keeps a row that is empty or a singleton. -/
theorem best_best (S : Finset ℕ) : best (best S) = best S := by
  rw [best_eq_toRow (best S), rowMax_best, ← best_eq_toRow]

/-- The rows of a solution of the recurrence are their own `best`. -/
theorem toRow_rowMax_of_array {t : PhyloTree} {w : Pair → ℕ} {A : Address → ℕ → Finset ℕ}
    (hA : BudgetDP.Array t w A) {x : Address} (hx : x ∈ t.nodes) (i : ℕ) :
    toRow (rowMax (A x i)) = A x i := by
  rw [← best_eq_toRow, hA x hx i, best_best]

/-- One cell of the matrix: if the cells of the vertices strictly below `v` at the budgets `≤ k`
hold the values of a solution `A` of the recurrence, `budgetCell` returns the value of `A` at
`(v, k)`. -/
theorem val_budgetCell {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    {w : Pair → ℕ} {W : Address × Address → ℕ} (hW : ∀ e ∈ EdgeAbove.candidates t, W e = w e)
    {A : Address → ℕ → Finset ℕ} (hA : BudgetDP.Array t w A) {R : Address × ℕ → WithBot ℕ}
    {v : Address} (hv : v ∈ t.nodes) {k : ℕ}
    (hbelow : ∀ y ∈ t.nodes, v <+: y → v ≠ y → ∀ i ≤ k, R (y, i) = rowMax (A y i)) :
    (budgetCell T B W R v k).val = rowMax (A v k) := by
  rw [hA v hv k, rowMax_best]
  obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff v).mp hv
  have hk := hT.kind v hv
  cases sub with
  | leaf a =>
    have hk' : T.kind v = .leaf a := by rw [hk]; simp [kindAt, hsub]
    simp only [budgetCell, val_bind, val_step, hk', val_steps, cases, hsub]
    by_cases h0 : k = 0 <;> simp [h0, rowMax]
  | fork l r =>
    have hk' : T.kind v = .fork (v ++ [false]) (v ++ [true]) := by rw [hk]; simp [kindAt, hsub]
    have hchild (b : Bool) (i : ℕ) (hi : i ≤ k) : R (v ++ [b], i) = rowMax (A (v ++ [b]) i) :=
      hbelow _ (PhyloTree.child_mem_nodes hsub b) (List.prefix_append _ _) (by simp) i hi
    simp only [budgetCell, val_bind, val_step, hk', val_steps, val_forList]
    rw [foldl_sup_eq (fun e => (W e : WithBot ℕ) + (knapsack R (hangingList T e).val (k - 1)).val)]
    simp only [cases, hsub, rowMax_union, val_convAt, rowMax_convolution]
    congr 1
    · apply Finset.sup_congr rfl
      intro i hi
      have hi' : i ≤ k := by have := Finset.mem_range.mp hi; omega
      rw [hchild false i hi', hchild true (k - i) (by omega)]
    · by_cases h0 : k = 0
      · simp [h0, rowMax]
      · simp only [h0, ↓reduceIte, rowMax_biUnion]
        have hfin : (B v).toFinset = pairsAt t v := by
          ext e
          simp [hB]
        rw [hfin]
        apply Finset.sup_congr rfl
        intro e he
        obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp he
        have hae := (Finset.mem_filter.mp hc).2
        obtain ⟨hnd, hmem⟩ := hangingList_spec hT hae
        rw [rowMax_image_add, hW e hc, val_knapsack]
        congr 1
        rw [forest_congr_perm (l₂ := (hanging t e).toList) _ (List.nodup_reverse.mpr hnd)
          (Finset.nodup_toList _) (by ext r; simp [hmem])]
        congr 1
        apply forest_congr_le
        intro y hy i hi
        have hy' : y ∈ hanging t e := Finset.mem_toList.mp hy
        have hgeo := frontier_below (EdgeAbove.footprint_region t e hae) hy'
        have hyn := (Finset.mem_filter.mp hy').1
        rw [hbelow y hyn (htarget ▸ hgeo.1) (htarget ▸ hgeo.2) i (by omega),
          toRow_rowMax_of_array hA hyn]

/-- Section 2.4: fill the matrix column by column, in order of increasing budget `k ≤ m`, and in
each column vertex by vertex in the order `order`. -/
def budgetFill (T : Tables) (B : Address → List (Address × Address)) (W : Address × Address → ℕ)
    (m : ℕ) (order : List Address) : Timed (Address × ℕ → WithBot ℕ) :=
  forList (fun R k => forList (fun R v => do
      let x ← budgetCell T B W R v k
      step (Function.update R (v, k) x)) order R) (List.range (m + 1)) fun _ => ⊥

/-- Filled in order of increasing budget, and in each column in the reverse of the preorder, the
matrix holds the values of any solution of the recurrence at the budgets `≤ m`. -/
theorem budgetFill_rows {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    {w : Pair → ℕ} {W : Address × Address → ℕ} (hW : ∀ e ∈ EdgeAbove.candidates t, W e = w e)
    {A : Address → ℕ → Finset ℕ} (hA : BudgetDP.Array t w A) (m : ℕ) :
    ∀ x ∈ t.nodes, ∀ i ≤ m,
      (budgetFill T B W m t.preorder.reverse).val (x, i) = rowMax (A x i) := by
  have hout : ∀ x ∈ t.nodes, ∀ i ∈ List.range (m + 1),
      (budgetFill T B W m t.preorder.reverse).val (x, i) = rowMax (A x i) := by
    simp only [budgetFill, val_forList]
    refine foldl_invariant (List.range (m + 1)) _
      (fun (K : List ℕ) (R : Address × ℕ → WithBot ℕ) =>
        ∀ x ∈ t.nodes, ∀ i ∈ K, R (x, i) = rowMax (A x i)) (by simp) ?_
    intro K k K' R hsplit hR
    -- the column `k`, vertex by vertex
    have hin : (∀ x ∈ t.nodes, ∀ i ∈ K, (t.preorder.reverse.foldl (fun R v =>
        (do let x ← budgetCell T B W R v k
            step (Function.update R (v, k) x) : Timed _).val) R) (x, i) = rowMax (A x i)) ∧
        ∀ x ∈ t.preorder.reverse, (t.preorder.reverse.foldl (fun R v =>
          (do let x ← budgetCell T B W R v k
              step (Function.update R (v, k) x) : Timed _).val) R) (x, k) =
          rowMax (A x k) := by
      refine foldl_invariant t.preorder.reverse _
        (fun (V : List Address) (R : Address × ℕ → WithBot ℕ) =>
          (∀ x ∈ t.nodes, ∀ i ∈ K, R (x, i) = rowMax (A x i)) ∧
            ∀ x ∈ V, R (x, k) = rowMax (A x k)) ⟨hR, by simp⟩ ?_
      intro V v V' U hsplit' hU
      obtain ⟨hK, hV⟩ := hU
      have hv : v ∈ t.nodes := by
        rw [← PhyloTree.mem_preorder, ← List.mem_reverse, hsplit']; simp
      have hvV : v ∉ V := by
        have hnd := List.nodup_reverse.mpr (PhyloTree.preorder_nodup t)
        rw [hsplit'] at hnd
        exact fun h => List.disjoint_of_nodup_append hnd h (by simp)
      have hcell := val_budgetCell hT hB hW hA hv (R := U) (k := k) (by
        intro y hy hvy hne i hi
        rcases Nat.lt_or_eq_of_le hi with hlt | rfl
        · exact hK y hy i ((mem_range_prefix hsplit i).mpr hlt)
        · exact hV y (PhyloTree.reverse_preorder_descendant_before hsplit' hy hvy hne))
      simp only [val_bind, val_step, hcell]
      refine ⟨fun x hx i hi => ?_, fun x hx => ?_⟩
      · have hik : i ≠ k := by
          have := (mem_range_prefix hsplit i).mp hi
          omega
        rw [Function.update_of_ne (fun h => hik (Prod.mk.inj h).2)]
        exact hK x hx i hi
      · rcases List.mem_append.mp hx with hx | hx
        · rw [Function.update_of_ne (fun h => hvV (by
            simp only [Prod.mk.injEq] at h
            rw [← h.1]
            exact hx))]
          exact hV x hx
        · rw [List.mem_singleton.mp hx]
          simp
    intro x hx i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hin.1 x hx i hi
    · rw [List.mem_singleton.mp hi]
      exact hin.2 x (List.mem_reverse.mpr ((PhyloTree.mem_preorder t x).mpr hx))
  intro x hx i hi
  exact hout x hx i (List.mem_range.mpr (by omega))

/-- **Section 2.4**, as a program: the matrix version of CAMUS with the budget columns
`0, …, m`. The preprocessing and the enumeration of the candidate pairs with their weights are
those of `camus`; the matrix is filled column by column (`budgetFill`). The result is read as rows
of `BudgetDP.Array`: the row of `(v, k)` is `{z}` for a cell `z` and empty for `⊥`, and the columns
above `m` are not computed (empty). -/
def camusBudget (t : PhyloTree) (Q : Multiset Quartet) (m : ℕ) :
    Timed (Address → ℕ → Finset ℕ) := do
  let P ← preprocess t
  let S ← enumerate P.1 Q P.2
  let order ← reverseList P.2
  let R ← budgetFill P.1 S.1 S.2 m order
  pure fun v k => if k ≤ m then toRow (R (v, k)) else ∅

/-- Section 2.4: for a well-labelled tree `T`, the rows computed by `camusBudget` agree, at every
vertex and every budget `k ≤ m`, with the rows of any solution of the recurrence
(`BudgetDP.Array`) for the weights `s_e` of Equation (1). -/
theorem camusBudget_agrees {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet) (m : ℕ)
    {A : Address → ℕ → Finset ℕ} (hA : BudgetDP.Array t (edgeWeight t Q) A) :
    ∀ v ∈ t.nodes, ∀ k ≤ m, (camusBudget t Q m).val v k = A v k := by
  have hT := preprocess_correct t
  have hpre := preprocess_order t
  obtain ⟨hB, hW⟩ := enumerate_buckets hT Q
  have hrows := budgetFill_rows hT (fun v e => (hB v).2 e)
    (fun e he => (hW e he).trans (val_weightScan ht hT Q he)) hA m
  intro v hv k hk
  simp only [camusBudget, val_bind, val_pure, val_reverseList, hpre, hk, ↓reduceIte]
  rw [hrows v hv k hk, toRow_rowMax_of_array hA hv]

/-- **Section 2.4**, computed. For a well-labelled tree `T`, the rows `M` computed by
`camusBudget` satisfy the recurrence at every vertex and every budget `k ≤ m`:
`M v k = BudgetDP.best (BudgetDP.cases t w M v k)`, with `w` the weights of Equation (1). The
candidate values at budget `k` only read the budgets `≤ k` (`cases_congr_le`). -/
theorem camusBudget_rows {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet) (m : ℕ) :
    ∀ v ∈ t.nodes, ∀ k ≤ m, (camusBudget t Q m).val v k =
      best (cases t (edgeWeight t Q) (camusBudget t Q m).val v k) := by
  obtain ⟨A, hA⟩ := exists_array t (edgeWeight t Q)
  have hag := camusBudget_agrees ht Q m hA
  intro v hv k hk
  rw [hag v hv k hk, hA v hv k]
  congr 1
  apply cases_congr_le t _ hv
  intro r hr _ _ i hi
  exact (hag r hr i (by omega)).symm

/-! ### Running time -/

/-- Section 2.4: the cell `(v, k)`, for `k ≤ m`, takes `O(m + |Pairs(v)| · n · m²)` time: the
convolution of the children's columns (`O(m)`), and for each pair of the bucket of `v` the walks
(`O(n)`) and the knapsack over at most `|V(T)|` subtrees, `O(m²)` look-ups each. -/
theorem time_budgetCell {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} {v : Address}
    (hB : ∀ e, e ∈ B v ↔ e ∈ pairsAt t v) (W : Address × Address → ℕ)
    (R : Address × ℕ → WithBot ℕ) {k m : ℕ} (hk : k ≤ m) :
    (budgetCell T B W R v k).time ≤ 6 * m + 9 + (B v).length *
      (14 + 3 * m + 7 * t.nodes.card + t.nodes.card * m * (6 * m + 2)) := by
  set N := t.nodes.card
  have hbody : ∀ (acc : WithBot ℕ) (e : Address × Address), e ∈ (if k = 0 then [] else B v) →
      (do let L ← hangingList T e
          let f ← knapsack R L (k - 1)
          let s ← steps 2 (W e)
          steps 2 (acc ⊔ ((s : WithBot ℕ) + f)) : Timed (WithBot ℕ)).time ≤
        13 + 3 * m + 7 * N + N * m * (6 * m + 2) := by
    intro acc e he
    have hk0 : k ≠ 0 := by intro h; simp [h] at he
    have hbe : e ∈ B v := by simpa [hk0] using he
    have hae := (Finset.mem_filter.mp (Finset.mem_filter.mp ((hB e).mp hbe)).1).2
    have h1 := time_hangingList T e
    have h2 := length_hangingList hT hae
    have h3 := time_knapsack R (hangingList T e).val (k - 1)
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1] at h3
    have h4 : (hangingList T e).val.length * (1 + k * (6 * (k - 1) + 8)) ≤
        N * (1 + m * (6 * m + 2)) := by
      apply Nat.mul_le_mul h2
      have : 6 * (k - 1) + 8 ≤ 6 * m + 2 := by omega
      nlinarith [Nat.mul_le_mul hk this]
    simp only [time_bind, time_steps]
    nlinarith
  unfold budgetCell
  cases hkd : T.kind v with
  | leaf a =>
    simp only [time_bind, time_step, val_step, time_steps]
    omega
  | fork l r =>
    simp only [time_bind, time_step, val_step, time_steps, val_steps, time_convAt]
    have hloop := time_forList_le _ (if k = 0 then [] else B v)
      (convAt (fun i => R (l, i)) (fun i => R (r, i)) k).val
      (fun _ => 13 + 3 * m + 7 * N + N * m * (6 * m + 2)) hbody
    rw [sum_map_const_nat] at hloop
    have hlen : (if k = 0 then [] else B v).length ≤ (B v).length := by
      split_ifs <;> simp
    have := Nat.mul_le_mul_right (13 + 3 * m + 7 * N + N * m * (6 * m + 2) + 1) hlen
    nlinarith

/-- Section 2.4: filling the matrix takes `O(m · (n m + |candidates| · n · m²))` time: each of the
`|V(T)|` subproblems is solved once per column, and each candidate pair is in one bucket
(`candidate_visits`). -/
theorem time_budgetFill {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    (hnd : ∀ v, (B v).Nodup) (W : Address × Address → ℕ) (m : ℕ) :
    (budgetFill T B W m t.preorder.reverse).time ≤ (m + 1) * (1 + t.nodes.card * (6 * m + 11) +
      (EdgeAbove.candidates t).card *
        (14 + 3 * m + 7 * t.nodes.card + t.nodes.card * m * (6 * m + 2))) := by
  set N := t.nodes.card
  set X := 14 + 3 * m + 7 * N + N * m * (6 * m + 2)
  have hlen : ∀ v, (B v).length = (pairsAt t v).card := by
    intro v
    rw [← List.toFinset_card_of_nodup (hnd v)]
    congr 1
    ext e
    simp [hB]
  -- one column: each subproblem once, and each candidate pair in one bucket
  have hcol : ∀ (R : Address × ℕ → WithBot ℕ) (k : ℕ), k ∈ List.range (m + 1) →
      (forList (fun R v => do
        let x ← budgetCell T B W R v k
        step (Function.update R (v, k) x)) t.preorder.reverse R).time ≤
        N * (6 * m + 11) + (EdgeAbove.candidates t).card * X := by
    intro R k hk
    have hk' : k ≤ m := by have := List.mem_range.mp hk; omega
    calc
      _ ≤ (t.preorder.reverse.map fun v => (6 * m + 10 + (B v).length * X) + 1).sum := by
        apply time_forList_le
        intro U v _
        simp only [time_bind, time_step]
        have h := time_budgetCell hT (hB v) W U hk'
        change _ ≤ 6 * m + 9 + (B v).length * X at h
        omega
      _ = ∑ v ∈ t.nodes, (6 * m + 11 + (pairsAt t v).card * X) := by
        rw [← List.sum_toFinset _ (List.nodup_reverse.mpr (PhyloTree.preorder_nodup t)),
          List.toFinset_reverse, PhyloTree.preorder_toFinset]
        apply Finset.sum_congr rfl
        intro v _
        rw [hlen]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, candidate_visits]
        simp [N]
  -- the `m + 1` columns: each subproblem is solved `m + 1` times
  unfold budgetFill
  calc
    _ ≤ ((List.range (m + 1)).map fun _ =>
        (N * (6 * m + 11) + (EdgeAbove.candidates t).card * X) + 1).sum :=
      time_forList_le _ _ _ _ hcol
    _ = _ := by
      simp only [sum_map_const_nat, List.length_range]
      ring

/-- **Section 2.4: the running time `O(n²(|Q| + m³n))`.** For a well-labelled tree `T` with `n`
leaves, a multiset `Q` with `|Q|` distinct quartets, and `m ≥ 1` budget columns, `camusBudget t Q m`
performs at most `1000 n² (|Q| + m³ n)` operations. The paper also has `m ≤ n − 1`
(`RootedNetwork.anchored_reticulation_bound`); the bound does not need it. -/
theorem camusBudget_time {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet) {m : ℕ}
    (hm : 1 ≤ m) :
    (camusBudget t Q m).time ≤
      1000 * t.taxa.card ^ 2 * (Q.toFinset.card + m ^ 3 * t.taxa.card) := by
  have hT := preprocess_correct t
  have hpre := preprocess_order t
  obtain ⟨hB, -⟩ := enumerate_buckets hT Q
  -- the preprocessing and the weights, as in Section 2.3: `O(n²|Q|)`
  have t1 := preprocess_time t
  have t2 := time_enumerate hT Q
  have t3 := time_reverseList t.preorder
  -- the matrix: each subproblem solved `m + 1` times, with `O(m²)` look-ups per hanging subtree
  have t4 := time_budgetFill hT (fun v e => (hB v).2 e) (fun v => (hB v).1)
    (enumerate (preprocess t).val.1 Q t.preorder).val.2 m
  simp only [camusBudget, time_bind, val_reverseList, time_pure]
  rw [hpre]
  rw [PhyloTree.preorder_length] at t3
  have hnodes := t.nodes_count
  have htaxa : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  have hn := t.labels_nonempty
  have hc := candidates_bound t
  rw [htaxa]
  set N := t.nodes.card
  set n := t.labels.length
  set C := (EdgeAbove.candidates t).card
  set q := Q.toFinset.card
  have hN : N ≤ 2 * n := by omega
  have hC : C ≤ 4 * n ^ 2 := by
    have := Nat.mul_le_mul hN hN
    nlinarith
  -- the pieces, against `n² q` and `n³ m³`
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hn3 : n ^ 2 ≤ n ^ 3 := by nlinarith
  have hm2 : m ≤ m ^ 2 := by nlinarith
  have hm3 : m ^ 2 ≤ m ^ 3 := by nlinarith
  have hnm2 : n * m ^ 2 ≤ n ^ 3 * m ^ 3 := Nat.mul_le_mul (hn2.trans hn3) hm3
  have hnm : n * m ≤ n * m ^ 2 := Nat.mul_le_mul_left n hm2
  have h1nm : 1 ≤ n * m := Nat.mul_le_mul hn hm
  have hm_nm : m ≤ n * m ^ 2 := by
    have := Nat.mul_le_mul hn hm2
    linarith
  have hn_nm : n ≤ n * m ^ 2 := by
    have := Nat.mul_le_mul_left n (hm.trans hm2)
    linarith
  have hX : 14 + 3 * m + 7 * N + N * m * (6 * m + 2) ≤ 47 * (n * m ^ 2) := by
    have h1 : N * m * (6 * m + 2) ≤ 2 * n * m * (8 * m) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right m hN) (by omega)
    have h2 : 2 * n * m * (8 * m) = 16 * (n * m ^ 2) := by ring
    linarith
  have e1 : (m + 1) * (1 + N * (6 * m + 11)) ≤ 70 * (n ^ 3 * m ^ 3) := by
    have h1 : N * (6 * m + 11) ≤ 2 * n * (17 * m) := Nat.mul_le_mul hN (by omega)
    have h2 : 1 + N * (6 * m + 11) ≤ 35 * (n * m) := by linarith
    have h3 : (m + 1) * (1 + N * (6 * m + 11)) ≤ (2 * m) * (35 * (n * m)) :=
      Nat.mul_le_mul (by omega) h2
    have h4 : (2 * m) * (35 * (n * m)) = 70 * (n * m ^ 2) := by ring
    linarith
  have e2 : (m + 1) * (C * (14 + 3 * m + 7 * N + N * m * (6 * m + 2))) ≤
      376 * (n ^ 3 * m ^ 3) := by
    have h2 : C * (14 + 3 * m + 7 * N + N * m * (6 * m + 2)) ≤
        (4 * n ^ 2) * (47 * (n * m ^ 2)) := Nat.mul_le_mul hC hX
    have h3 : (m + 1) * (C * (14 + 3 * m + 7 * N + N * m * (6 * m + 2))) ≤
        (2 * m) * ((4 * n ^ 2) * (47 * (n * m ^ 2))) := Nat.mul_le_mul (by omega) h2
    have h4 : (2 * m) * ((4 * n ^ 2) * (47 * (n * m ^ 2))) = 376 * (n ^ 3 * m ^ 3) := by ring
    linarith
  have hfill : (m + 1) * (1 + N * (6 * m + 11) + C * (14 + 3 * m + 7 * N +
      N * m * (6 * m + 2))) ≤ 446 * (n ^ 3 * m ^ 3) := by
    have : (m + 1) * (1 + N * (6 * m + 11) + C * (14 + 3 * m + 7 * N +
        N * m * (6 * m + 2))) = (m + 1) * (1 + N * (6 * m + 11)) +
          (m + 1) * (C * (14 + 3 * m + 7 * N + N * m * (6 * m + 2))) := by ring
    linarith
  have hP : n ^ 3 ≤ n ^ 3 * m ^ 3 := by
    have := Nat.mul_le_mul_left (n ^ 3) (Nat.one_le_pow 3 m hm)
    linarith
  have hrest : 20 * N ^ 2 + 8 * N ^ 2 + C * 4 + 2 * N ≤ 132 * (n ^ 3 * m ^ 3) := by
    have h1 : N ^ 2 ≤ 4 * n ^ 2 := by
      have := Nat.mul_le_mul hN hN
      nlinarith
    have h2 : N ≤ 2 * n ^ 2 := by linarith
    linarith
  have hQ : C * (133 * q) ≤ 532 * (n ^ 2 * q) := by
    have := Nat.mul_le_mul_right (133 * q) hC
    have h : 4 * n ^ 2 * (133 * q) = 532 * (n ^ 2 * q) := by ring
    linarith
  have hgoal : 1000 * n ^ 2 * (q + m ^ 3 * n) = 1000 * (n ^ 2 * q) + 1000 * (n ^ 3 * m ^ 3) := by
    ring
  have ht2 : C * (133 * q + 4) = C * (133 * q) + C * 4 := by ring
  rw [hgoal]
  rw [ht2] at t2
  linarith

end Complexity

end Camus
