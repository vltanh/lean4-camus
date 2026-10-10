module

public import Camus.Complexity.BudgetProgram
public import Camus.Complexity.Backtracking
public import Camus.Restriction.Backtracking

/-!
# Section 2.4: backtracking through the matrix, within the running time

Section 2.4 of the paper modifies the dynamic program so that it "returns m networks
N_1, N_2, …, N_m", and Section 2.2 obtains a network from the array by backtracking. This file
writes the backtracking through the matrix of `Complexity.camusBudget` as a program in the cost
monad (`Complexity.budgetBacktrack`) and the whole of the modified program, matrix and networks
(`Complexity.camusBudgetNetworks`). It proves that, for every budget `k ≤ m` whose row at the
root is nonempty, the program returns a backtracking trace (`BudgetDP.Trace`), so that, by
`BudgetDP.trace_graph_optimal`, its network is the network `N_k` of Section 2.4, and that the
whole computation, the matrix and the backtracking for every `k ≤ m`, runs in time
`O(n²(|Q| + m³n))`.

The backtracking from a vertex `v` with budget `k` follows the two cases of the recurrence
(`BudgetDP.cases`). It first looks for a split `k = i + (k − i)` of the budget whose values at the
two children add up to the cell `(v, k)` (`Complexity.findSplit`), and continues at the children
with these budgets. Otherwise it looks in the bucket of `v` for a pair `e` whose weight `s_e`
plus the knapsack at budget `k − 1` over the subtrees hanging off its cycle is the cell
(`Complexity.gallTest`); it computes the knapsack of `e` again, keeping all its rows
(`Complexity.knapsackTable`), backtracks through it to distribute the budget `k − 1` over the
hanging subtrees (`Complexity.knapsackBack`), and continues at these subtrees with their budgets.
The choices are computed again during the backtracking; nothing is stored while the matrix is
filled. The knapsack takes the hanging subtrees in the order of the walks of
`Complexity.hangingList`, while `BudgetDP.Trace` asks for a backtracking through the knapsack in
the order of `Finset.toList`: budgets that attain the knapsack in one order attain it in every
order (`BudgetDP.Knapsack.reorder`).

The subtrees where the backtracking continues are disjoint and lie strictly below `v`, and the
budgets never increase. So, from the root with a budget `k ≤ m`, the backtracking spends at a
vertex `x` at most `O(m + |Pairs(x)| · n · m²)` operations of its own, as many as the cell
`(x, m)` of the matrix up to a constant, and `O(n m + |candidates| · n · m²)` in all
(`Complexity.time_budgetBacktrack`, `Complexity.sum_ownCostBudget`). For the `m + 1` budgets this
is `O(n³m³)`, within the bound of the matrix.

## Main results

* `BudgetDP.Knapsack.reorder`: a backtracking through the knapsack over a list of distinct
  subtrees is one over every list of the same subtrees.
* `Complexity.findSplit`, `Complexity.knapsackTable`, `Complexity.knapsackBack`: backtracking
  through a max-plus convolution, and through the knapsack.
* `Complexity.budgetBacktrack_trace`: the backtracking returns a trace of the matrix.
* `Complexity.camusBudgetNetworks`: the modified program of Section 2.4 with backtracking.
* `Complexity.camusBudgetNetworks_trace`: for every `k ≤ m` with a nonempty row at the root, the
  family returned for `k` is a backtracking trace from the root with budget `k`.
* `Complexity.camusBudgetNetworks_optimal`, `Complexity.camusBudgetNetworks_networks`: its network
  is the network `N_k` of Section 2.4.
* `Complexity.camusBudgetNetworks_time`: at most `2100 n² (|Q| + m³ n)` operations for `m ≥ 1`,
  the matrix and the backtracking for every `k ≤ m` together.

## Proof (the paper's)

The paper analyses the matrix only: "we need to solve each of the n original subproblems O(m)
times. It takes O(m²) time to find the correct DP look-ups to solve each problem optimally"
(`Complexity.camusBudget_time`). The backtracking for one budget solves each subproblem at most
once more, at a budget `≤ m`: it visits each vertex of `T` at most once (`Complexity.cone_children`,
`Complexity.cone_hanging`, `Complexity.time_budgetBacktrack`), and at a vertex `x` it scans the
bucket of `x` with the knapsack of each pair (`Complexity.time_gallTest`) and backtracks through
one knapsack (`Complexity.time_knapsackTable`, `Complexity.time_knapsackBack`). Each candidate
pair is in one bucket (`Complexity.sum_ownCostBudget`), so the `m + 1` backtrackings add
`O(m · |candidates| · n · m²) = O(n³m³)` (`Complexity.budgetNetworks_arith`). Correctness follows
the paper's proof of Theorem 1, for the matrix: the value of the cell comes from one of the two
cases of the recurrence (`Complexity.budgetBacktrack_trace`), as in `BudgetDP.exists_trace`.
-/

@[expose] public section

namespace Camus

/-! ### Backtracking through the knapsack, in any order -/

namespace BudgetDP

open DynamicProgramming

/-- Section 2.4: budgets `b` and values `s` with `s r ∈ M r (b r)` that attain the knapsack over a
list of distinct subtrees form a backtracking through the knapsack (`BudgetDP.Knapsack`): if the
values of a tail did not attain the knapsack of the tail at its budget, a better distribution of
that budget over the tail would beat the whole. -/
theorem Knapsack.of_mem_forest {M : Address → ℕ → Finset ℕ} {b s : Address → ℕ} :
    ∀ {rs : List Address}, rs.Nodup → (∀ r ∈ rs, s r ∈ M r (b r)) →
      (rs.map s).sum ∈ forest M rs (rs.map b).sum →
      Knapsack M b s rs (rs.map b).sum (rs.map s).sum
  | [], _, _, _ => by simpa using (Knapsack.nil : Knapsack M b s [] 0 0)
  | r :: rs, hnd, hrow, hmem => by
    have hrs := (List.nodup_cons.mp hnd).2
    simp only [List.map_cons, List.sum_cons] at hmem ⊢
    -- the tail attains the knapsack of the tail at its budget
    have htail : (rs.map s).sum ∈ forest M rs (rs.map b).sum := by
      rw [Complexity.forest_eq_best, mem_best]
      refine ⟨?_, fun x hx => ?_⟩
      · rw [mem_allocations hrs]
        exact ⟨b, s, List.sum_toFinset _ hrs, List.sum_toFinset _ hrs,
          fun r' hr' => hrow r' (List.mem_cons_of_mem _ (List.mem_toFinset.mp hr'))⟩
      · -- otherwise `s r + x` would beat the whole
        have hx' : s r + x ∈ allocations M (r :: rs) (b r + (rs.map b).sum) := by
          simp only [allocations]
          exact mem_convolution.mpr ⟨b r, _, s r, x, rfl, hrow r (by simp), hx, rfl⟩
        rw [Complexity.forest_eq_best, mem_best] at hmem
        have := hmem.2 _ hx'
        omega
    exact Knapsack.cons r rs _ _ (hrow r (by simp))
      (Knapsack.of_mem_forest hrs (fun r' hr' => hrow r' (by simp [hr'])) htail) hmem

/-- Section 2.4: a backtracking through the knapsack over a list of distinct subtrees is one over
every list without repetition of the same subtrees, with the same budgets and values. -/
theorem Knapsack.reorder {M : Address → ℕ → Finset ℕ} {b s : Address → ℕ}
    {rs rs' : List Address} {k z : ℕ} (h : Knapsack M b s rs k z) (hnd : rs.Nodup)
    (hnd' : rs'.Nodup) (hset : rs.toFinset = rs'.toFinset) : Knapsack M b s rs' k z := by
  have hb : (rs'.map b).sum = k := by
    rw [h.budget_eq, ← List.sum_toFinset _ hnd, ← List.sum_toFinset _ hnd', hset]
  have hs : (rs'.map s).sum = z := by
    rw [h.value_eq, ← List.sum_toFinset _ hnd, ← List.sum_toFinset _ hnd', hset]
  have hrow : ∀ r ∈ rs', s r ∈ M r (b r) := fun r hr =>
    h.row_mem r (List.mem_toFinset.mp (hset ▸ List.mem_toFinset.mpr hr))
  have hmem : (rs'.map s).sum ∈ forest M rs' (rs'.map b).sum := by
    rw [hb, hs, ← Complexity.forest_congr_perm M hnd hnd' hset]
    exact h.mem_forest
  rw [← hb, ← hs]
  exact Knapsack.of_mem_forest hnd' hrow hmem

end BudgetDP

namespace Complexity

/-! ### Finding the first element that passes a test -/

namespace Timed

variable {α : Type}

/-- The first element of the list that passes the test `p` (`none` if there is none): one
iteration and the test per element examined. -/
def findList (p : α → Timed Bool) : List α → Timed (Option α)
  | [] => pure none
  | a :: l => do
      tick
      let ok ← p a
      if ok then pure (some a) else findList p l

/-- The element found is in the list and passes the test. -/
theorem findList_sound (p : α → Timed Bool) :
    ∀ (l : List α) (a : α), (findList p l).val = some a → a ∈ l ∧ (p a).val = true := by
  intro l
  induction l with
  | nil => intro a h; simp [findList] at h
  | cons b l ih =>
    intro a h
    by_cases hb : (p b).val = true
    · simp only [findList, val_bind, hb, ↓reduceIte, val_pure, Option.some.injEq] at h
      subst h
      exact ⟨by simp, hb⟩
    · simp only [findList, val_bind, hb, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨ha, hp⟩ := ih a h
      exact ⟨by simp [ha], hp⟩

/-- If some element passes the test, an element is found. -/
theorem findList_complete (p : α → Timed Bool) :
    ∀ (l : List α), (∃ a ∈ l, (p a).val = true) → ∃ a, (findList p l).val = some a := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons b l ih =>
    intro h
    by_cases hb : (p b).val = true
    · exact ⟨b, by simp [findList, hb]⟩
    · obtain ⟨a, ha, hp⟩ := h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact (hb hp).elim
      · obtain ⟨a', h'⟩ := ih ⟨a, ha, hp⟩
        exact ⟨a', by simp [findList, hb, h']⟩

/-- If each test of an element `a` of `l` costs at most `c a`, the search costs at most
`Σ_{a ∈ l} (c a + 1)`. -/
theorem time_findList_le (p : α → Timed Bool) (c : α → ℕ) :
    ∀ (l : List α), (∀ a ∈ l, (p a).time ≤ c a) →
      (findList p l).time ≤ (l.map fun a => c a + 1).sum := by
  intro l
  induction l with
  | nil => intro _; simp [findList]
  | cons b l ih =>
    intro h
    have hb := h b (by simp)
    have hl := ih (fun a ha => h a (by simp [ha]))
    by_cases hp : (p b).val = true
    · simp only [findList, time_bind, time_tick, hp, ↓reduceIte, time_pure, List.map_cons,
        List.sum_cons]
      omega
    · simp only [findList, time_bind, time_tick, hp, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons]
      omega

end Timed

open Timed DynamicProgramming BudgetDP

/-! ### Backtracking through a max-plus convolution -/

/-- Whether the split `k = i + (k − i)` of the budget between the columns `A` and `B` attains the
value `x`: `A i + B (k − i) = x`. Five operations: two look-ups, a subtraction, an addition and a
comparison. -/
def splitTest (A B : ℕ → WithBot ℕ) (x : WithBot ℕ) (k i : ℕ) : Timed Bool := do
  let a ← step (A i)
  let b ← steps 2 (B (k - i))
  steps 2 (decide (a + b = x))

@[simp] theorem time_splitTest (A B : ℕ → WithBot ℕ) (x : WithBot ℕ) (k i : ℕ) :
    (splitTest A B x k i).time = 5 := rfl

@[simp] theorem val_splitTest (A B : ℕ → WithBot ℕ) (x : WithBot ℕ) (k i : ℕ) :
    (splitTest A B x k i).val = decide (A i + B (k - i) = x) := rfl

/-- Backtracking through the max-plus convolution `convAt A B k`: the first budget `i ≤ k` with
`A i + B (k − i) = x`. -/
def findSplit (A B : ℕ → WithBot ℕ) (x : WithBot ℕ) (k : ℕ) : Timed (Option ℕ) :=
  findList (splitTest A B x k) (List.range (k + 1))

/-- The split found attains the value `x`. -/
theorem findSplit_sound {A B : ℕ → WithBot ℕ} {x : WithBot ℕ} {k i : ℕ}
    (h : (findSplit A B x k).val = some i) : i ≤ k ∧ A i + B (k - i) = x := by
  obtain ⟨hi, hp⟩ := findList_sound _ _ i h
  exact ⟨Nat.lt_succ_iff.mp (List.mem_range.mp hi), by simpa using hp⟩

/-- If some split attains the value `x`, a split is found. -/
theorem findSplit_complete {A B : ℕ → WithBot ℕ} {x : WithBot ℕ} {k : ℕ}
    (h : ∃ i ≤ k, A i + B (k - i) = x) : ∃ i, (findSplit A B x k).val = some i := by
  obtain ⟨i, hik, hi⟩ := h
  exact findList_complete _ _ ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hik), by simpa using hi⟩

/-- The value of the convolution at the budget `k` is attained by a split: if `x` is the value of
`convAt A B k`, a split is found. -/
theorem findSplit_complete_sup {A B : ℕ → WithBot ℕ} {k : ℕ} {x : WithBot ℕ}
    (hx : x = (Finset.range (k + 1)).sup fun i => A i + B (k - i)) :
    ∃ i, (findSplit A B x k).val = some i := by
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup (Finset.range (k + 1))
    ⟨0, by simp⟩ fun i => A i + B (k - i)
  exact findSplit_complete ⟨i, Nat.lt_succ_iff.mp (Finset.mem_range.mp hi), (hx.trans hsup).symm⟩

/-- The search for a split takes at most `6 (k + 1)` operations, as `convAt`. -/
theorem time_findSplit (A B : ℕ → WithBot ℕ) (x : WithBot ℕ) (k : ℕ) :
    (findSplit A B x k).time ≤ 6 * (k + 1) := by
  unfold findSplit
  calc
    _ ≤ ((List.range (k + 1)).map fun _ => 5 + 1).sum :=
      time_findList_le _ (fun _ => 5) _ (fun i _ => le_of_eq (time_splitTest A B x k i))
    _ = _ := by simp only [sum_map_const_nat, List.length_range]; ring

/-- The split found is at most the budget. -/
theorem findSplit_le {A B : ℕ → WithBot ℕ} {x : WithBot ℕ} {k i : ℕ}
    (h : (findSplit A B x k).val = some i) : i ≤ k := (findSplit_sound h).1

/-! ### Rows and cells -/

/-- A value of a row that is empty or a singleton is the value of its cell. -/
theorem rowMax_of_mem {S : Finset ℕ} {z : ℕ} (hz : z ∈ S) (hS : S.card ≤ 1) :
    rowMax S = z := by
  have hSz : S = {z} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hz, fun y hy => Finset.card_le_one.mp hS y hy z hz⟩
  rw [hSz]
  simp [rowMax]

/-- The value of a cell is in its row. -/
theorem mem_of_rowMax_eq {S : Finset ℕ} {z : ℕ} (h : rowMax S = z) : z ∈ S := by
  by_cases hS : S.Nonempty
  · obtain ⟨y, hy, hsup⟩ := Finset.exists_mem_eq_sup S hS fun z => (z : WithBot ℕ)
    have hyz : y = z := WithBot.coe_injective (hsup.symm.trans h)
    exact hyz ▸ hy
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    subst hS
    simp [rowMax] at h

/-! ### The knapsack with all its rows, and backtracking through it -/

/-- The knapsack table over the subtrees `L` up to the budget `j` (Section 2.4). Its row `i` is
the knapsack over the first `i` subtrees of `L`: row `0` is the row of the empty forest, and row
`i + 1` is the max-plus convolution of the column of the `(i + 1)`-th subtree with row `i`, at
every budget `≤ j`. These are the rows that `knapsack` computes one after the other, keeping only
the last; backtracking through the knapsack reads the others. -/
def knapsackTable (R : Address × ℕ → WithBot ℕ) (L : List Address) (j : ℕ) :
    Timed (ℕ × ℕ → WithBot ℕ) := do
  let F₀ ← forList (fun F b => steps 2 (Function.update F (0, b)
    (if b = 0 then (0 : WithBot ℕ) else ⊥))) (List.range (j + 1)) fun _ => ⊥
  let S ← forList (fun (S : ℕ × (ℕ × ℕ → WithBot ℕ)) r => do
      let i ← step (S.1 + 1)
      let F ← forList (fun F b => do
          let c ← convAt (fun i => R (r, i)) (fun i => S.2 (S.1, i)) b
          step (Function.update F (i, b) c)) (List.range (j + 1)) S.2
      pure (i, F)) L (0, F₀)
  pure S.2

/-- A loop of updates at the keys `(c, 0), …, (c, j)` writes the value of each of them and leaves
the other keys unchanged. -/
theorem foldl_update_row {β : Type} (c : ℕ) (f : ℕ → β) (F : ℕ × ℕ → β) (j : ℕ) (x : ℕ × ℕ) :
    ((List.range (j + 1)).foldl (fun F b => Function.update F (c, b) (f b)) F) x =
      if x.1 = c ∧ x.2 ≤ j then f x.2 else F x := by
  have hnd : ((List.range (j + 1)).map fun b => (c, b)).Nodup :=
    List.nodup_range.map (fun a b h => (Prod.mk.inj h).2)
  split_ifs with hx
  · obtain ⟨x1, x2⟩ := x
    obtain ⟨rfl, hx2⟩ := hx
    exact foldl_update_of_mem (fun b => (x1, b)) f _ F hnd
      (List.mem_range.mpr (Nat.lt_succ_of_le hx2))
  · apply foldl_update_of_not_mem (fun b => (c, b)) f
    intro b hb h
    apply hx
    rw [← h]
    exact ⟨rfl, Nat.lt_succ_iff.mp (List.mem_range.mp hb)⟩

/-- The rows of the knapsack table: row `i ≤ |L|` at the budget `b ≤ j` is the value of the
knapsack (`BudgetDP.forest`) over the first `i` subtrees of `L`, in reverse order, as for
`knapsack` (`Complexity.val_knapsack`). -/
theorem val_knapsackTable (R : Address × ℕ → WithBot ℕ) (L : List Address) (j : ℕ) :
    ∀ i ≤ L.length, ∀ b ≤ j, (knapsackTable R L j).val (i, b) =
      rowMax (forest (fun r i => toRow (R (r, i))) (L.take i).reverse b) := by
  set Mr : Address → ℕ → Finset ℕ := fun r i => toRow (R (r, i)) with hMr
  -- the first row: the empty forest
  have h0 : ∀ b ≤ j, ((List.range (j + 1)).foldl (fun (F : ℕ × ℕ → WithBot ℕ) b =>
      Function.update F (0, b) (if b = 0 then (0 : WithBot ℕ) else ⊥)) fun _ => ⊥) (0, b) =
        rowMax (forest Mr [] b) := by
    intro b hb
    rw [foldl_update_row 0 (fun b => if b = 0 then (0 : WithBot ℕ) else ⊥) _ j (0, b)]
    simp only [true_and, hb, ↓reduceIte]
    by_cases h : b = 0 <;> simp [h, forest, rowMax]
  -- the invariant of the loop over the subtrees
  intro i hi b hb
  simp only [knapsackTable, val_bind, val_forList, val_steps, val_pure, val_step]
  refine (foldl_invariant L _ (fun (P : List Address) (S : ℕ × (ℕ × ℕ → WithBot ℕ)) =>
      S.1 = P.length ∧
        ∀ i ≤ P.length, ∀ b ≤ j, S.2 (i, b) = rowMax (forest Mr (P.take i).reverse b))
      ⟨rfl, fun i hi b hb => ?_⟩ ?_).2 i hi b hb
  · simp only [List.length_nil, Nat.le_zero] at hi
    subst hi
    simpa using h0 b hb
  · intro P r P' S _ hS
    obtain ⟨hS1, hS2⟩ := hS
    refine ⟨by simp [hS1], fun i hi b hb => ?_⟩
    dsimp only
    rw [foldl_update_row]
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · -- an earlier row is unchanged
      have hne : ¬(i = S.1 + 1 ∧ b ≤ j) := fun h => by omega
      simp only [hne, ↓reduceIte]
      rw [hS2 i (by omega) b hb, List.take_append_of_le_length (by omega)]
    · -- the row of `r`: its column convolved with the row before it
      simp only [hS1, true_and, hb, ↓reduceIte]
      rw [val_convAt, List.take_of_length_le (by simp), List.reverse_append,
        List.reverse_singleton, List.singleton_append, forest, rowMax_best,
        rowMax_convolution]
      apply Finset.sup_congr rfl
      intro i' hi'
      have hi'' : i' ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
      rw [hS2 P.length le_rfl (b - i') (by omega), List.take_of_length_le le_rfl]
      congr 1
      exact (rowMax_toRow _).symm

/-- Backtracking through the knapsack table `F` (Section 2.4). The list `rs` holds the subtrees of
`L` in reverse order, and `F` the knapsack table over `L`, so that row `i` of `F` is the knapsack
over the last `i` subtrees of `rs`. From the cell of row `i = |rs|` at the budget `j`, the first
subtree `r` of `rs` gets the first budget `b ≤ j` whose value, added to the cell of row `i − 1` at
the budget `j − b`, is the cell; then the same for the other subtrees, from row `i − 1` at the
budget `j − b`. The budgets are written in the table `bud`. -/
def knapsackBack (R : Address × ℕ → WithBot ℕ) (F : ℕ × ℕ → WithBot ℕ) :
    List Address → ℕ → ℕ → (Address → ℕ) → Timed (Address → ℕ)
  | [], _, _, bud => pure bud
  | r :: rs, i, j, bud => do
      let x ← step (F (i, j))
      let i' ← step (i - 1)
      let found ← findSplit (fun b => R (r, b)) (fun b => F (i', b)) x j
      match found with
      | none => pure bud
      | some b => do
          let bud ← step (Function.update bud r b)
          let j' ← step (j - b)
          knapsackBack R F rs i' j' bud

/-- Backtracking through the knapsack only writes the budgets of the subtrees of `rs`. -/
theorem knapsackBack_of_not_mem (R : Address × ℕ → WithBot ℕ) (F : ℕ × ℕ → WithBot ℕ) :
    ∀ (rs : List Address) (i j : ℕ) (bud : Address → ℕ) (x : Address), x ∉ rs →
      (knapsackBack R F rs i j bud).val x = bud x := by
  intro rs
  induction rs with
  | nil => intro i j bud x _; rfl
  | cons r rs ih =>
    intro i j bud x hx
    have hxr : x ≠ r := fun h => hx (h ▸ List.mem_cons_self)
    have hxrs : x ∉ rs := fun h => hx (List.mem_cons_of_mem _ h)
    cases hf : (findSplit (fun b => R (r, b)) (fun b => F (i - 1, b)) (F (i, j)) j).val with
    | none => simp [knapsackBack, hf]
    | some b =>
      simp only [knapsackBack, val_bind, val_step, hf]
      rw [ih _ _ _ x hxrs, Function.update_of_ne hxr]

/-- The budgets written by the backtracking through the knapsack at the budget `j` are at most
`j`: if the budgets of the table `bud` and `j` are at most `c`, so are those of the result. -/
theorem knapsackBack_le (R : Address × ℕ → WithBot ℕ) (F : ℕ × ℕ → WithBot ℕ) :
    ∀ (rs : List Address) (i j c : ℕ) (bud : Address → ℕ), (∀ x, bud x ≤ c) → j ≤ c →
      ∀ x, (knapsackBack R F rs i j bud).val x ≤ c := by
  intro rs
  induction rs with
  | nil => intro i j c bud h _ x; exact h x
  | cons r rs ih =>
    intro i j c bud h hj x
    cases hf : (findSplit (fun b => R (r, b)) (fun b => F (i - 1, b)) (F (i, j)) j).val with
    | none => simpa [knapsackBack, hf] using h x
    | some b =>
      have hb := findSplit_le hf
      simp only [knapsackBack, val_bind, val_step, hf]
      refine ih _ (j - b) c _ (fun y => ?_) (by omega) x
      by_cases hy : y = r
      · subst hy; simp; omega
      · rw [Function.update_of_ne hy]
        exact h y

/-- Section 2.4, backtracking through the knapsack. Let the columns `R` of the subtrees of `rs`
hold the values of the rows of `A` up to the budget `j`, and let row `i ≤ |rs|` of the table `F`
hold the knapsack over the last `i` subtrees of `rs`. If the cell of row `|rs|` at a budget
`b ≤ j` holds the value `c`, the budgets written by `knapsackBack`, with some values `s`, form a
backtracking through the knapsack over `rs` with budget `b` and total value `c`
(`BudgetDP.Knapsack`). -/
theorem knapsackBack_knapsack {A : Address → ℕ → Finset ℕ} {R : Address × ℕ → WithBot ℕ}
    {F : ℕ × ℕ → WithBot ℕ} {j : ℕ} :
    ∀ (rs : List Address), rs.Nodup → (∀ r ∈ rs, ∀ i ≤ j, R (r, i) = rowMax (A r i)) →
      (∀ i ≤ rs.length, ∀ b ≤ j, F (i, b) = rowMax (forest A (rs.drop (rs.length - i)) b)) →
      ∀ (b : ℕ) (bud : Address → ℕ) (c : ℕ), b ≤ j → F (rs.length, b) = c →
        ∃ s, Knapsack A (knapsackBack R F rs rs.length b bud).val s rs b c := by
  intro rs
  induction rs with
  | nil =>
    intro _ _ hF b bud c hb hc
    -- the empty forest: budget `0` and value `0`
    simp only [List.length_nil] at hc hF
    rw [hF 0 le_rfl b hb] at hc
    have hmem := mem_of_rowMax_eq hc
    simp only [Nat.sub_zero, List.drop_nil, forest] at hmem
    split_ifs at hmem with hb0
    · rw [Finset.mem_singleton.mp hmem, hb0]
      exact ⟨fun _ => 0, Knapsack.nil⟩
    · exact (Finset.notMem_empty _ hmem).elim
  | cons r rs ih =>
    intro hnd hR hF b bud c hb hc
    have hr : r ∉ rs := (List.nodup_cons.mp hnd).1
    have hRr : ∀ i ≤ j, R (r, i) = rowMax (A r i) := hR r (by simp)
    -- the rows of the tail
    have hF' : ∀ i ≤ rs.length, ∀ b ≤ j,
        F (i, b) = rowMax (forest A (rs.drop (rs.length - i)) b) := by
      intro i hi b hb
      rw [hF i (by simp; omega) b hb]
      congr 2
      rw [List.length_cons, show rs.length + 1 - i = rs.length - i + 1 by omega,
        List.drop_succ_cons]
    have hlen : (r :: rs).length - 1 = rs.length := by simp
    -- the cell is the best split of the budget between `r` and the tail
    have hcell : F ((r :: rs).length, b) =
        (Finset.range (b + 1)).sup fun i => R (r, i) + F (rs.length, b - i) := by
      rw [hF _ le_rfl b hb, Nat.sub_self, List.drop_zero, forest, rowMax_best,
        rowMax_convolution]
      apply Finset.sup_congr rfl
      intro i hi
      have hi' : i ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [hRr i (by omega), hF' rs.length le_rfl (b - i) (by omega), Nat.sub_self,
        List.drop_zero]
    obtain ⟨b', hfound⟩ := findSplit_complete_sup (A := fun i => R (r, i))
      (B := fun i => F (rs.length, i)) (k := b) (x := F ((r :: rs).length, b)) hcell
    obtain ⟨hb', hsplit⟩ := findSplit_sound hfound
    rw [hc] at hsplit
    obtain ⟨x, y, hx, hy, hxy⟩ := WithBot.add_eq_coe.mp hsplit
    simp only [Nat.cast_id] at hxy
    -- the tail, with the budget `b - b'` and the value `y`
    obtain ⟨s', hs'⟩ := ih (List.nodup_cons.mp hnd).2 (fun q hq => hR q (by simp [hq])) hF'
      (b - b') (Function.update bud r b') y (by omega) hy.symm
    set BUD := (knapsackBack R F rs rs.length (b - b') (Function.update bud r b')).val with hBUD
    have hval : (knapsackBack R F (r :: rs) (r :: rs).length b bud).val = BUD := by
      simp only [knapsackBack, val_bind, val_step, hfound, hlen]
      rfl
    have hBr : BUD r = b' := by
      rw [hBUD, knapsackBack_of_not_mem R F rs _ _ _ r hr]
      simp
    let s := Function.update s' r x
    have hsr : s r = x := by simp [s]
    have hss : ∀ q ∈ rs, s q = s' q := fun q hq =>
      Function.update_of_ne (fun h : q = r => hr (h ▸ hq)) _ _
    have hcons := Knapsack.cons r rs (b - b') y (b := BUD) (s := s)
      (by rw [hsr, hBr]; exact mem_of_rowMax_eq ((hRr b' (by omega)).symm.trans hx.symm))
      (hs'.congr (fun _ _ => rfl) hss)
      (by
        rw [hsr, hBr, hxy, show b' + (b - b') = b by omega]
        have hcF := hF _ le_rfl b hb
        rw [hc, Nat.sub_self, List.drop_zero] at hcF
        exact mem_of_rowMax_eq hcF.symm)
    rw [hBr, hsr, hxy, show b' + (b - b') = b by omega] at hcons
    exact ⟨s, hval ▸ hcons⟩

/-! ### Backtracking through the matrix -/

/-- Whether the pair `e` attains the value `x` of a cell of budget `j + 1` (Section 2.4): its
weight `s_e` plus the knapsack at the budget `j` over the subtrees hanging off its cycle, listed by
the walks, is `x`. -/
def gallTest (T : Tables) (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ)
    (x : WithBot ℕ) (j : ℕ) (e : Address × Address) : Timed Bool := do
  let L ← hangingList T e
  let c ← knapsack R L j
  let s ← step (W e)
  steps 2 (decide ((s : WithBot ℕ) + c = x))

@[simp] theorem val_gallTest (T : Tables) (W : Address × Address → ℕ)
    (R : Address × ℕ → WithBot ℕ) (x : WithBot ℕ) (j : ℕ) (e : Address × Address) :
    (gallTest T W R x j e).val =
      decide ((W e : WithBot ℕ) + (knapsack R (hangingList T e).val j).val = x) := rfl

/-- Backtracking through the matrix of Section 2.4 from the vertex `v` with the budget `k`, with
fuel `n`. At a leaf, nothing. At an internal vertex, with `x` the cell `(v, k)`: if a split
`k = i + (k − i)` of the budget between the children attains `x` (`findSplit`), the results at the
two children with these budgets; otherwise, for `k ≥ 1`, a pair `e` of the bucket of `v` that
attains `x` (`gallTest`), the knapsack of `e` with all its rows (`knapsackTable`), the budgets of
the subtrees hanging off its cycle found by backtracking through it (`knapsackBack`), and the
results at these subtrees with their budgets. The pairs found are put in front of `acc`. -/
def budgetBacktrack (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) :
    ℕ → Address → ℕ → List (Address × Address) → Timed (List (Address × Address))
  | 0, _, _, acc => pure acc
  | n + 1, v, k, acc => do
      let kd ← step (T.kind v)
      match kd with
      | .leaf _ => pure acc
      | .fork l r => do
          let x ← step (R (v, k))
          let split ← findSplit (fun i => R (l, i)) (fun i => R (r, i)) x k
          match split with
          | some i => do
              let acc ← budgetBacktrack T B W R n l i acc
              let k' ← step (k - i)
              budgetBacktrack T B W R n r k' acc
          | none => do
              let bucket ← steps 2 (if k = 0 then [] else B v)
              let j ← step (k - 1)
              let found ← findList (gallTest T W R x j) bucket
              match found with
              | none => pure acc
              | some e => do
                  let L ← hangingList T e
                  let F ← knapsackTable R L j
                  let Lr ← reverseList L
                  let p ← forList (fun c _ => step (c + 1)) L 0
                  let bud ← knapsackBack R F Lr p j fun _ => 0
                  forList (fun acc r => do
                      let b ← step (bud r)
                      budgetBacktrack T B W R n r b acc) L (e :: acc)

/-- Counting the elements of a list in a loop. -/
theorem foldl_count {α : Type} (l : List α) (c : ℕ) :
    l.foldl (fun s _ => s + 1) c = c + l.length := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, ih, List.length_cons]; omega

/-- The backtracking only puts pairs in front of the accumulator. -/
theorem budgetBacktrack_acc (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) :
    ∀ (n : ℕ) (v : Address) (k : ℕ) (acc : List (Address × Address)),
      (budgetBacktrack T B W R n v k acc).val = (budgetBacktrack T B W R n v k []).val ++ acc := by
  intro n
  induction n with
  | zero => intro v k acc; simp [budgetBacktrack]
  | succ n ih =>
    intro v k acc
    cases hk : T.kind v with
    | leaf a => simp [budgetBacktrack, hk]
    | fork l r =>
      cases hs : (findSplit (fun i => R (l, i)) (fun i => R (r, i)) (R (v, k)) k).val with
      | some i =>
        simp only [budgetBacktrack, val_bind, val_step, hk, hs]
        rw [ih r (k - i), ih l i, ih r (k - i) (budgetBacktrack T B W R n l i []).val,
          List.append_assoc]
      | none =>
        cases hf : (findList (gallTest T W R (R (v, k)) (k - 1))
            (if k = 0 then [] else B v)).val with
        | none => simp [budgetBacktrack, hk, hs, hf]
        | some e =>
          have hfun : ∀ bud : Address → ℕ,
              (fun (acc : List (Address × Address)) r =>
                (budgetBacktrack T B W R n r (bud r) acc).val) =
              fun acc r => (budgetBacktrack T B W R n r (bud r) []).val ++ acc := by
            intro bud
            funext acc r
            exact ih r (bud r) acc
          simp only [budgetBacktrack, val_bind, val_step, val_steps, hk, hs, hf, val_forList,
            hfun]
          rw [show e :: acc = [e] ++ acc from rfl, foldl_prepend]

/-- The knapsack of a pair with target `v`, computed from the cells: if the cells of the subtrees
hanging off the cycle of `e` hold the values of the rows of `A` up to the budget `j`, the knapsack
over the walks of `e` is the value of `BudgetDP.forest` over the hanging subtrees. -/
theorem val_knapsack_hanging {t : PhyloTree} {T : Tables} (hT : T.Correct t) {w : Pair → ℕ}
    {A : Address → ℕ → Finset ℕ} (hA : BudgetDP.Array t w A) {R : Address × ℕ → WithBot ℕ}
    {e : Address × Address} (hae : EdgeAbove.Admissible t e) {j : ℕ}
    (hR : ∀ y ∈ hanging t e, ∀ i ≤ j, R (y, i) = rowMax (A y i)) :
    (knapsack R (hangingList T e).val j).val = rowMax (forest A (hanging t e).toList j) := by
  obtain ⟨hnd, hmem⟩ := hangingList_spec hT hae
  rw [val_knapsack, forest_congr_perm (l₂ := (hanging t e).toList) _
    (List.nodup_reverse.mpr hnd) (Finset.nodup_toList _) (by ext r; simp [hmem])]
  congr 1
  apply forest_congr_le
  intro y hy i hi
  have hy' : y ∈ hanging t e := Finset.mem_toList.mp hy
  rw [hR y hy' i hi, toRow_rowMax_of_array hA (Finset.mem_filter.mp hy').1]

/-- **Section 2.4, backtracking.** If the cells `R` hold the values of the rows of a solution `A`
of the recurrence (`BudgetDP.Array`) at the budgets `≤ m`, then the backtracking from a vertex `v`
with a budget `k ≤ m` whose row is nonempty, with fuel larger than the height of `T_v`, returns a
backtracking trace from `v` with budget `k` (`BudgetDP.Trace`). -/
theorem budgetBacktrack_trace {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    {w : Pair → ℕ} {W : Address × Address → ℕ} (hW : ∀ e ∈ EdgeAbove.candidates t, W e = w e)
    {A : Address → ℕ → Finset ℕ} (hA : BudgetDP.Array t w A) {R : Address × ℕ → WithBot ℕ}
    {m : ℕ} (hR : ∀ x ∈ t.nodes, ∀ i ≤ m, R (x, i) = rowMax (A x i)) :
    ∀ (n : ℕ) (v : Address) (k : ℕ), v ∈ t.nodes → remainingDepth t v < n → k ≤ m →
      (A v k).Nonempty →
        BudgetDP.Trace t w A v k (budgetBacktrack T B W R n v k []).val.toFinset := by
  intro n
  induction n with
  | zero => intro v k _ h; omega
  | succ n ih =>
    intro v k hv hn hk hne
    obtain ⟨z, hz⟩ := hne
    have hRv : R (v, k) = z :=
      (hR v hv k hk).trans (rowMax_of_mem hz (array_row_card t w A hA hv k))
    have hzc := (mem_best.mp ((hA v hv k) ▸ hz)).1
    obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff v).mp hv
    have hkd := hT.kind v hv
    cases sub with
    | leaf a =>
      -- a leaf: only the budget `0` has a value
      have hk' : T.kind v = .leaf a := by rw [hkd]; simp [kindAt, hsub]
      simp only [cases, hsub] at hzc
      split_ifs at hzc with hk0
      · subst hk0
        simpa [budgetBacktrack, hk'] using BudgetDP.Trace.leaf (w := w) (M := A) v a hsub
      · exact (Finset.notMem_empty _ hzc).elim
    | fork l r =>
      have hk' : T.kind v = .fork (v ++ [false]) (v ++ [true]) := by
        rw [hkd]; simp [kindAt, hsub]
      have hl := PhyloTree.child_mem_nodes hsub false
      have hr := PhyloTree.child_mem_nodes hsub true
      have hchild (b : Bool) {i : ℕ} (hi : i ≤ m) (hne : (A (v ++ [b]) i).Nonempty) :
          BudgetDP.Trace t w A (v ++ [b]) i
            (budgetBacktrack T B W R n (v ++ [b]) i []).val.toFinset := by
        have hmem := PhyloTree.child_mem_nodes hsub b
        exact ih _ _ hmem (by
          have := remainingDepth_lt hmem (List.prefix_append _ _) (by simp)
          omega) hi hne
      cases hs : (findSplit (fun i => R (v ++ [false], i)) (fun i => R (v ++ [true], i))
          (R (v, k)) k).val with
      | some i =>
        -- the first case of the recurrence: the budget is split between the two children
        obtain ⟨hik, hsplit⟩ := findSplit_sound hs
        rw [hRv] at hsplit
        obtain ⟨x, y, hx, hy, hxy⟩ := WithBot.add_eq_coe.mp hsplit
        simp only [Nat.cast_id] at hxy
        have hxA : x ∈ A (v ++ [false]) i :=
          mem_of_rowMax_eq ((hR _ hl i (by omega)).symm.trans hx.symm)
        have hyA : y ∈ A (v ++ [true]) (k - i) :=
          mem_of_rowMax_eq ((hR _ hr (k - i) (by omega)).symm.trans hy.symm)
        have hval : (budgetBacktrack T B W R (n + 1) v k []).val =
            (budgetBacktrack T B W R n (v ++ [true]) (k - i) []).val ++
              (budgetBacktrack T B W R n (v ++ [false]) i []).val := by
          simp only [budgetBacktrack, val_bind, val_step, hk', hs]
          rw [budgetBacktrack_acc]
        have htr := BudgetDP.Trace.fork v l r i (k - i) x y _ _ hsub
          (hchild false (by omega) ⟨x, hxA⟩) (hchild true (by omega) ⟨y, hyA⟩) hxA hyA
          (by rw [hxy, show i + (k - i) = k by omega]; exact hz)
        rw [show i + (k - i) = k by omega] at htr
        rw [hval, List.toFinset_append, Finset.union_comm]
        exact htr
      | none =>
        -- no split attains the cell, so it comes from an edge with target `v`
        have hnotconv : z ∉ convolution (A (v ++ [false])) (A (v ++ [true])) k := by
          intro hconv
          obtain ⟨i, j, x, y, hij, hx, hy, hxy⟩ := mem_convolution.mp hconv
          obtain ⟨i', hi'⟩ := findSplit_complete (A := fun i => R (v ++ [false], i))
            (B := fun i => R (v ++ [true], i)) (x := R (v, k)) (k := k) ⟨i, by omega, by
              rw [hR _ hl i (by omega), hR _ hr (k - i) (by omega), show k - i = j by omega,
                rowMax_of_mem hx (array_row_card t w A hA hl i),
                rowMax_of_mem hy (array_row_card t w A hA hr j), hRv, ← hxy, Nat.cast_add]⟩
          rw [hs] at hi'
          simp at hi'
        simp only [cases, hsub] at hzc
        rcases Finset.mem_union.mp hzc with hconv | hgall
        · exact (hnotconv hconv).elim
        split_ifs at hgall with hk0
        · exact (Finset.notMem_empty _ hgall).elim
        obtain ⟨e₀, he₀, hz₀⟩ := Finset.mem_biUnion.mp hgall
        obtain ⟨c₀, hc₀, hcz₀⟩ := Finset.mem_image.mp hz₀
        -- the knapsack of a pair with target `v`, from the cells
        have hknap : ∀ e ∈ pairsAt t v, (knapsack R (hangingList T e).val (k - 1)).val =
            rowMax (forest A (hanging t e).toList (k - 1)) := by
          intro e he
          obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp he
          have hae := (Finset.mem_filter.mp hc).2
          refine val_knapsack_hanging hT hA hae fun y hy i hi => hR y (Finset.mem_filter.mp hy).1 i
            (by omega)
        -- the pair `e₀` attains the cell, so the search finds a pair `e`
        have hcard₀ : (forest A (hanging t e₀).toList (k - 1)).card ≤ 1 := by
          rw [forest_eq_best]
          exact best_card_le_one _
        obtain ⟨e, hfound⟩ := findList_complete (gallTest T W R (R (v, k)) (k - 1))
          (if k = 0 then [] else B v) ⟨e₀, by simp [hk0, (hB v e₀).mpr he₀], by
            rw [val_gallTest, decide_eq_true_iff, hknap e₀ he₀, rowMax_of_mem hc₀ hcard₀, hRv,
              hW e₀ (Finset.mem_filter.mp he₀).1, ← hcz₀, Nat.cast_add]⟩
        obtain ⟨heB, hetest⟩ := findList_sound _ _ e hfound
        simp only [hk0, ↓reduceIte] at heB hfound
        have he := (hB v e).mp heB
        obtain ⟨hec, htarget⟩ := Finset.mem_filter.mp he
        have hae := (Finset.mem_filter.mp hec).2
        rw [val_gallTest, decide_eq_true_iff, hknap e he, hRv, hW e hec] at hetest
        obtain ⟨a', c, ha', hc, hac⟩ := WithBot.add_eq_coe.mp hetest
        simp only [Nat.cast_id] at hac
        have hwa : a' = w e := WithBot.coe_injective ha'
        subst hwa
        have hcF : c ∈ forest A (hanging t e).toList (k - 1) := mem_of_rowMax_eq hc.symm
        -- the walks, the knapsack table, and the budgets found by backtracking through it
        obtain ⟨hnd, hmem⟩ := hangingList_spec hT hae
        set L := (hangingList T e).val with hL
        have hLset : L.toFinset = hanging t e := by ext r; simp [hmem]
        set F := (knapsackTable R L (k - 1)).val with hF
        have hrows : ∀ y ∈ L, ∀ i ≤ k - 1, R (y, i) = rowMax (A y i) := fun y hy i hi =>
          hR y (Finset.mem_filter.mp ((hmem y).mp hy)).1 i (by omega)
        have hFrows : ∀ i ≤ L.reverse.length, ∀ b ≤ k - 1,
            F (i, b) = rowMax (forest A (L.reverse.drop (L.reverse.length - i)) b) := by
          intro i hi b hb
          rw [List.length_reverse] at hi ⊢
          rw [hF, val_knapsackTable R L (k - 1) i hi b hb, List.reverse_take]
          congr 1
          apply forest_congr_le
          intro y hy i' hi'
          have hyL : y ∈ L := List.mem_reverse.mp (List.mem_of_mem_drop hy)
          rw [hrows y hyL i' (by omega), toRow_rowMax_of_array hA
            (Finset.mem_filter.mp ((hmem y).mp hyL)).1]
        have hstart : F (L.reverse.length, k - 1) = c := by
          rw [hFrows _ le_rfl _ le_rfl, Nat.sub_self, List.drop_zero,
            forest_congr_perm A (List.nodup_reverse.mpr hnd) (Finset.nodup_toList _)
              (by rw [List.toFinset_reverse, hLset, Finset.toList_toFinset])]
          exact rowMax_of_mem hcF (by rw [forest_eq_best]; exact best_card_le_one _)
        set bud := (knapsackBack R F L.reverse L.reverse.length (k - 1) fun _ => 0).val with hbud
        obtain ⟨s, hks⟩ := knapsackBack_knapsack L.reverse (List.nodup_reverse.mpr hnd)
          (fun y hy => hrows y (List.mem_reverse.mp hy)) hFrows (k - 1) (fun _ => 0) c le_rfl
          hstart
        have hks' : Knapsack A bud s (hanging t e).toList (k - 1) c :=
          hks.reorder (List.nodup_reverse.mpr hnd) (Finset.nodup_toList _)
            (by rw [List.toFinset_reverse, hLset, Finset.toList_toFinset])
        have hbudle : ∀ y, bud y ≤ k - 1 :=
          knapsackBack_le R F L.reverse _ (k - 1) (k - 1) _ (fun _ => Nat.zero_le _) le_rfl
        -- the results at the hanging subtrees, with their budgets
        have hbranches : ∀ y ∈ hanging t e, BudgetDP.Trace t w A y (bud y)
            (budgetBacktrack T B W R n y (bud y) []).val.toFinset := by
          intro y hy
          have hgeo := frontier_below (EdgeAbove.footprint_region t e hae) hy
          have hyn := (Finset.mem_filter.mp hy).1
          exact ih y (bud y) hyn (by
              have := remainingDepth_lt hyn (htarget ▸ hgeo.1) (htarget ▸ hgeo.2)
              omega) (by have := hbudle y; omega)
            ⟨s y, hks'.row_mem y (Finset.mem_toList.mpr hy)⟩
        have htr := BudgetDP.Trace.gall v e (k - 1) c bud s
          (fun y => (budgetBacktrack T B W R n y (bud y) []).val.toFinset) he hks' hbranches
          (by rw [show k - 1 + 1 = k by omega, hac]; exact hz)
        rw [show k - 1 + 1 = k by omega] at htr
        -- the pairs returned: `e` and the results at the hanging subtrees
        have hfun : (fun (acc : List (Address × Address)) y =>
            (budgetBacktrack T B W R n y (bud y) acc).val) =
            fun acc y => (budgetBacktrack T B W R n y (bud y) []).val ++ acc := by
          funext acc y
          exact budgetBacktrack_acc T B W R n y (bud y) acc
        have hval : (budgetBacktrack T B W R (n + 1) v k []).val =
            L.foldl (fun acc y => (budgetBacktrack T B W R n y (bud y) []).val ++ acc) [e] := by
          simp only [budgetBacktrack, val_bind, val_step, val_steps, hk', hs, hk0, ↓reduceIte,
            hfound, val_forList, val_reverseList, foldl_count, Nat.zero_add]
          rw [← hL, ← hF, ← List.length_reverse, ← hbud, hfun]
        rw [hval, toFinset_foldl_prepend, hLset]
        have hset : ([e] : List (Address × Address)).toFinset ∪ (hanging t e).biUnion
            (fun y => (budgetBacktrack T B W R n y (bud y) []).val.toFinset) =
              insert e ((hanging t e).biUnion
                fun y => (budgetBacktrack T B W R n y (bud y) []).val.toFinset) := by
          ext x
          simp
        rw [hset]
        exact htr

/-! ### Running time of the backtracking -/

/-- The knapsack table over `L` up to the budget `j` takes `O(|L| j²)` time: at most
`3 (j + 1) + |L| (2 + (j + 1)(6 j + 8))` operations, as `knapsack`. -/
theorem time_knapsackTable (R : Address × ℕ → WithBot ℕ) (L : List Address) (j : ℕ) :
    (knapsackTable R L j).time ≤ 3 * (j + 1) + L.length * (2 + (j + 1) * (6 * j + 8)) := by
  have hinit : ∀ F : ℕ × ℕ → WithBot ℕ, (forList (fun F b => steps 2 (Function.update F (0, b)
      (if b = 0 then (0 : WithBot ℕ) else ⊥))) (List.range (j + 1)) F).time = 3 * (j + 1) := by
    intro F
    rw [time_forList_eq _ _ _ (fun _ => 2) (fun _ _ _ => rfl)]
    simp only [sum_map_const_nat, List.length_range]
    ring
  have hrow : ∀ (S : ℕ × (ℕ × ℕ → WithBot ℕ)) (r : Address) (i : ℕ), (forList (fun F b => do
      let c ← convAt (fun i => R (r, i)) (fun i => S.2 (S.1, i)) b
      step (Function.update F (i, b) c)) (List.range (j + 1)) S.2).time ≤
        (j + 1) * (6 * j + 8) := by
    intro S r i
    calc
      _ ≤ ((List.range (j + 1)).map fun _ => (6 * j + 7) + 1).sum := by
        apply time_forList_le
        intro F b hb
        have := List.mem_range.mp hb
        simp only [time_bind, time_convAt, time_step]
        nlinarith
      _ = _ := by simp only [sum_map_const_nat, List.length_range]
  have hmain : ∀ S : ℕ × (ℕ × ℕ → WithBot ℕ), (forList (fun (S : ℕ × (ℕ × ℕ → WithBot ℕ)) r => do
      let i ← step (S.1 + 1)
      let F ← forList (fun F b => do
          let c ← convAt (fun i => R (r, i)) (fun i => S.2 (S.1, i)) b
          step (Function.update F (i, b) c)) (List.range (j + 1)) S.2
      pure (i, F)) L S).time ≤ L.length * (2 + (j + 1) * (6 * j + 8)) := by
    intro S
    calc
      _ ≤ (L.map fun _ => ((j + 1) * (6 * j + 8) + 1) + 1).sum := by
        apply time_forList_le
        intro S' r _
        simp only [time_bind, time_step, time_pure, val_step]
        have := hrow S' r (S'.1 + 1)
        omega
      _ = _ := by simp only [sum_map_const_nat]; ring
  simp only [knapsackTable, time_bind, time_pure]
  have h1 := hinit fun _ => ⊥
  have h2 := hmain (0, (forList (fun F b => steps 2 (Function.update F (0, b)
      (if b = 0 then (0 : WithBot ℕ) else ⊥))) (List.range (j + 1)) fun _ => ⊥).val)
  omega

/-- Backtracking through the knapsack over `rs` from a budget `≤ j` takes at most
`|rs| (10 + 6 j)` operations: per subtree, `O(j)` for the split of the budget. -/
theorem time_knapsackBack (R : Address × ℕ → WithBot ℕ) (F : ℕ × ℕ → WithBot ℕ) :
    ∀ (rs : List Address) (i j c : ℕ) (bud : Address → ℕ), j ≤ c →
      (knapsackBack R F rs i j bud).time ≤ rs.length * (10 + 6 * c) := by
  intro rs
  induction rs with
  | nil => intro i j c bud _; simp [knapsackBack]
  | cons r rs ih =>
    intro i j c bud hj
    have hsplit := time_findSplit (fun b => R (r, b)) (fun b => F (i - 1, b)) (F (i, j)) j
    cases hf : (findSplit (fun b => R (r, b)) (fun b => F (i - 1, b)) (F (i, j)) j).val with
    | none =>
      simp only [knapsackBack, time_bind, time_step, val_step, hf, time_pure,
        List.length_cons]
      nlinarith
    | some b =>
      have hb := findSplit_le hf
      have hrest := ih (i - 1) (j - b) c (Function.update bud r b) (by omega)
      simp only [knapsackBack, time_bind, time_step, val_step, hf, List.length_cons]
      nlinarith

/-- The test of one pair takes `O(n + |L| j²)` time, where `L` lists the subtrees hanging off its
cycle. -/
theorem time_gallTest (T : Tables) (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ)
    (x : WithBot ℕ) (j : ℕ) (e : Address × Address) :
    (gallTest T W R x j e).time ≤ 12 + 3 * (j + 1) + 7 * (hangingList T e).val.length +
      (hangingList T e).val.length * ((j + 1) * (6 * j + 8)) := by
  have h1 := time_hangingList T e
  have h2 := time_knapsack R (hangingList T e).val j
  simp only [gallTest, time_bind, time_step, time_steps]
  nlinarith

/-- The operations that the backtracking through the matrix performs at the vertex `x` itself,
for budgets `≤ m`, at most: the reads and the search for a split of the budget (`O(m)`), the scan
of the bucket of `x` with the walks and the knapsack of each pair (`O(n m²)` per pair), and for the
pair found the walks, the knapsack table and the backtracking through it (`O(n m²)`). -/
def ownCostBudget (t : PhyloTree) (B : Address → List (Address × Address)) (m : ℕ)
    (x : Address) : ℕ :=
  11 + 6 * m + (B x).length * (21 + 6 * m + 25 * t.nodes.card + 6 * (t.nodes.card * m) +
    2 * (t.nodes.card * (m * (6 * m + 2))))

/-- Section 2.4 for the backtracking: from `v` with a budget `k ≤ m`, the backtracking takes at
most `ownCostBudget` operations at each vertex of `T_v`, since the subtrees where it continues are
disjoint and lie strictly below `v`, and their budgets are at most `k`. -/
theorem time_budgetBacktrack {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) (m : ℕ) :
    ∀ (n : ℕ) (v : Address) (k : ℕ) (acc : List (Address × Address)), v ∈ t.nodes → k ≤ m →
      (budgetBacktrack T B W R n v k acc).time ≤ ∑ x ∈ cone t v, ownCostBudget t B m x := by
  intro n
  induction n with
  | zero => intro v k acc _ _; simp [budgetBacktrack]
  | succ n ih =>
    intro v k acc hv hk
    have hvc : v ∈ cone t v := mem_cone.mpr ⟨hv, List.prefix_refl v⟩
    rw [← Finset.add_sum_erase _ _ hvc]
    set N := t.nodes.card with hN
    -- the cost per pair of the bucket, and its pieces
    set P := N * (m * (6 * m + 2)) with hP
    set X := 21 + 6 * m + 25 * N + 6 * (N * m) + 2 * P with hX
    have hown : ownCostBudget t B m v = 11 + 6 * m + (B v).length * X := rfl
    obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff v).mp hv
    have hkd := hT.kind v hv
    cases sub with
    | leaf a =>
      have hk' : T.kind v = .leaf a := by rw [hkd]; simp [kindAt, hsub]
      simp only [budgetBacktrack, time_bind, time_step, val_step, hk', time_pure]
      omega
    | fork l r =>
      have hk' : T.kind v = .fork (v ++ [false]) (v ++ [true]) := by
        rw [hkd]; simp [kindAt, hsub]
      have hl := PhyloTree.child_mem_nodes hsub false
      have hr := PhyloTree.child_mem_nodes hsub true
      have hfs := time_findSplit (fun i => R (v ++ [false], i)) (fun i => R (v ++ [true], i))
        (R (v, k)) k
      cases hs : (findSplit (fun i => R (v ++ [false], i)) (fun i => R (v ++ [true], i))
          (R (v, k)) k).val with
      | some i =>
        -- the two children, with the budgets `i` and `k - i`
        obtain ⟨hik, -⟩ := findSplit_sound hs
        obtain ⟨hdisj, hsubset⟩ := cone_children (t := t) (v := v)
        have hchildren : ∑ x ∈ cone t (v ++ [false]), ownCostBudget t B m x +
            ∑ x ∈ cone t (v ++ [true]), ownCostBudget t B m x ≤
              ∑ x ∈ (cone t v).erase v, ownCostBudget t B m x := by
          rw [← Finset.sum_union hdisj]
          exact Finset.sum_le_sum_of_subset hsubset
        have h1 := ih (v ++ [false]) i acc hl (by omega)
        have h2 := ih (v ++ [true]) (k - i) (budgetBacktrack T B W R n (v ++ [false]) i acc).val
          hr (by omega)
        simp only [budgetBacktrack, time_bind, time_step, val_step, hk', hs]
        have : 0 ≤ (B v).length * X := Nat.zero_le _
        omega
      | none =>
        -- the scan of the bucket: the walks and the knapsack of each pair
        have hscan : (findList (gallTest T W R (R (v, k)) (k - 1))
            (if k = 0 then [] else B v)).time ≤ (B v).length * (13 + 3 * m + 7 * N + P) := by
          calc
            _ ≤ ((if k = 0 then [] else B v).map fun _ => (12 + 3 * m + 7 * N + P) + 1).sum := by
              apply time_findList_le
              intro e he
              have hk0 : k ≠ 0 := by intro h; simp [h] at he
              have hbe : e ∈ B v := by simpa [hk0] using he
              have hae := (Finset.mem_filter.mp (Finset.mem_filter.mp ((hB v e).mp hbe)).1).2
              have hL := length_hangingList hT hae
              have hg := time_gallTest T W R (R (v, k)) (k - 1) e
              rw [show k - 1 + 1 = k by omega] at hg
              have h6 : 6 * (k - 1) + 8 = 6 * k + 2 := by omega
              rw [h6] at hg
              have hkm : k * (6 * k + 2) ≤ m * (6 * m + 2) :=
                Nat.mul_le_mul hk (by omega)
              have hLP : (hangingList T e).val.length * (k * (6 * k + 2)) ≤ P :=
                Nat.mul_le_mul hL hkm
              omega
            _ ≤ (B v).length * (13 + 3 * m + 7 * N + P) := by
              rw [sum_map_const_nat]
              exact Nat.mul_le_mul (by split_ifs <;> simp) (by omega)
        cases hf : (findList (gallTest T W R (R (v, k)) (k - 1))
            (if k = 0 then [] else B v)).val with
        | none =>
          simp only [budgetBacktrack, time_bind, time_step, val_step, hk', hs, time_steps,
            val_steps, hf, time_pure]
          have : (B v).length * (13 + 3 * m + 7 * N + P) ≤ (B v).length * X :=
            Nat.mul_le_mul_left _ (by omega)
          omega
        | some e =>
          -- the pair found: its walks, its knapsack table, and the backtracking through it
          obtain ⟨heB, -⟩ := findList_sound _ _ e hf
          have hk0 : k ≠ 0 := by intro h; simp [h] at heB
          have hbe : e ∈ B v := by simpa [hk0] using heB
          have hlen1 : 1 ≤ (B v).length := List.length_pos_of_mem hbe
          have he := (hB v e).mp hbe
          obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp he
          have hae := (Finset.mem_filter.mp hc).2
          obtain ⟨hnd, hmem⟩ := hangingList_spec hT hae
          set L := (hangingList T e).val with hLdef
          have hL : L.length ≤ N := length_hangingList hT hae
          have hhl := time_hangingList T e
          rw [← hLdef] at hhl
          have htab := time_knapsackTable R L (k - 1)
          rw [show k - 1 + 1 = k by omega, show 6 * (k - 1) + 8 = 6 * k + 2 by omega] at htab
          have hkm : k * (6 * k + 2) ≤ m * (6 * m + 2) := Nat.mul_le_mul hk (by omega)
          have hLP : L.length * (k * (6 * k + 2)) ≤ P := Nat.mul_le_mul hL hkm
          have hw : L.length * (2 + k * (6 * k + 2)) =
              2 * L.length + L.length * (k * (6 * k + 2)) := by ring
          have hrev := time_reverseList L
          have hcnt := time_count L
          set F := (knapsackTable R L (k - 1)).val
          set Lr := (reverseList L).val
          set p := (forList (fun c _ => step (c + 1)) L 0).val
          have hback := time_knapsackBack R F Lr p (k - 1) (k - 1) (fun _ => 0) le_rfl
          have hLr : Lr.length = L.length := by simp [Lr, val_reverseList]
          rw [hLr] at hback
          have hback' : L.length * (10 + 6 * (k - 1)) ≤ 4 * N + 6 * (N * m) := by
            have h1 : L.length * (10 + 6 * (k - 1)) ≤ N * (4 + 6 * m) :=
              Nat.mul_le_mul hL (by omega)
            have h2 : N * (4 + 6 * m) = 4 * N + 6 * (N * m) := by ring
            omega
          set bud := (knapsackBack R F Lr p (k - 1) fun _ => 0).val with hbud
          have hbudle : ∀ y, bud y ≤ m := fun y =>
            le_trans (knapsackBack_le R F Lr p (k - 1) (k - 1) _ (fun _ => Nat.zero_le _) le_rfl y)
              (by omega)
          -- the recursive calls at the hanging subtrees
          obtain ⟨hpd, hsub'⟩ := cone_hanging hae
          rw [htarget] at hsub'
          have hloop : (forList (fun acc r => do
              let b ← step (bud r)
              budgetBacktrack T B W R n r b acc) L (e :: acc)).time ≤
                2 * N + ∑ x ∈ (cone t v).erase v, ownCostBudget t B m x := by
            calc
              _ ≤ (L.map fun r => ((∑ x ∈ cone t r, ownCostBudget t B m x) + 1) + 1).sum := by
                apply time_forList_le
                intro acc' r hr'
                have hrh : r ∈ hanging t e := (hmem r).mp hr'
                have := ih r (bud r) acc' (Finset.mem_filter.mp hrh).1 (hbudle r)
                simp only [time_bind, time_step, val_step]
                omega
              _ = 2 * L.length + ∑ r ∈ hanging t e, ∑ x ∈ cone t r, ownCostBudget t B m x := by
                rw [List.sum_map_add, List.sum_map_add, sum_map_const_nat,
                  ← List.sum_toFinset _ hnd]
                have hLs : L.toFinset = hanging t e := by ext r; simp [hmem]
                rw [hLs]
                ring
              _ ≤ 2 * N + ∑ x ∈ (cone t v).erase v, ownCostBudget t B m x := by
                rw [← Finset.sum_biUnion hpd]
                exact Nat.add_le_add (by omega) (Finset.sum_le_sum_of_subset hsub')
          simp only [budgetBacktrack, time_bind, time_step, val_step, hk', hs, time_steps,
            val_steps, hf]
          have hX : (B v).length * (13 + 3 * m + 7 * N + P) +
              (8 + 3 * m + 18 * N + 6 * (N * m) + P) ≤ (B v).length * X := by
            have h1 : (B v).length * X = (B v).length * (13 + 3 * m + 7 * N + P) +
                (B v).length * (8 + 3 * m + 18 * N + 6 * (N * m) + P) := by
              rw [hX]; ring
            have h2 : 8 + 3 * m + 18 * N + 6 * (N * m) + P ≤
                (B v).length * (8 + 3 * m + 18 * N + 6 * (N * m) + P) :=
              Nat.le_mul_of_pos_left _ hlen1
            omega
          linarith

/-- From the root, the backtracking spends `O(n m + |candidates| · n · m²)` operations in all:
each candidate pair is in one bucket (`candidate_visits`). -/
theorem sum_ownCostBudget {t : PhyloTree} {B : Address → List (Address × Address)}
    (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v) (hnd : ∀ v, (B v).Nodup) (m : ℕ) :
    ∑ x ∈ cone t [], ownCostBudget t B m x = t.nodes.card * (11 + 6 * m) +
      (EdgeAbove.candidates t).card * (21 + 6 * m + 25 * t.nodes.card +
        6 * (t.nodes.card * m) + 2 * (t.nodes.card * (m * (6 * m + 2)))) := by
  have hcone : cone t [] = t.nodes := by
    ext x
    simp [mem_cone]
  have hlen : ∀ v, (B v).length = (pairsAt t v).card := by
    intro v
    rw [← List.toFinset_card_of_nodup (hnd v)]
    congr 1
    ext e
    simp [hB]
  rw [hcone]
  unfold ownCostBudget
  rw [Finset.sum_add_distrib]
  simp only [hlen, ← Finset.sum_mul, candidate_visits, Finset.sum_const, smul_eq_mul]

/-! ### The program of Section 2.4 with backtracking -/

/-- The backtracking from the root for every budget `k ≤ m` whose cell at the root is not `⊥`
(whose row is nonempty), with fuel `N`: the pairs found for `k` are written at `k`. -/
def budgetNetworks (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) (N m : ℕ) :
    Timed (ℕ → List (Address × Address)) :=
  forList (fun E k => do
      let x ← step (R ([], k))
      let ok ← step (decide (x ≠ ⊥))
      if ok then do
        let Ek ← budgetBacktrack T B W R N [] k []
        step (Function.update E k Ek)
      else pure E) (List.range (m + 1)) fun _ => []

/-- The loop over the budgets writes, at each budget `k ≤ m` whose cell at the root is not `⊥`,
the result of the backtracking with budget `k`. -/
theorem val_budgetNetworks (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) (N m : ℕ) {k : ℕ} (hk : k ≤ m)
    (hx : R ([], k) ≠ ⊥) :
    (budgetNetworks T B W R N m).val k = (budgetBacktrack T B W R N [] k []).val := by
  simp only [budgetNetworks, val_forList]
  refine (foldl_invariant (List.range (m + 1)) _
    (fun (K : List ℕ) (E : ℕ → List (Address × Address)) =>
      k ∈ K → E k = (budgetBacktrack T B W R N [] k []).val) (by simp) ?_)
    (List.mem_range.mpr (by omega))
  intro K i K' E hsplit hE hkK
  by_cases hik : i = k
  · subst hik
    simp [hx]
  · have hkK' : k ∈ K := by
      rcases List.mem_append.mp hkK with h | h
      · exact h
      · exact (hik (List.mem_singleton.mp h).symm).elim
    by_cases hi : R ([], i) ≠ ⊥
    · simp only [val_bind, val_step, hi, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
      rw [Function.update_of_ne (Ne.symm hik)]
      exact hE hkK'
    · simp only [val_bind, val_step, hi, decide_false, Bool.false_eq_true, ↓reduceIte, val_pure]
      exact hE hkK'

/-- The backtracking from the root for the `m + 1` budgets takes at most `m + 1` times the
operations of one backtracking from the root and four more. -/
theorem time_budgetNetworks {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) (N m : ℕ) :
    (budgetNetworks T B W R N m).time ≤
      (m + 1) * (∑ x ∈ cone t [], ownCostBudget t B m x + 4) := by
  unfold budgetNetworks
  calc
    _ ≤ ((List.range (m + 1)).map fun _ =>
        (∑ x ∈ cone t [], ownCostBudget t B m x + 3) + 1).sum := by
      apply time_forList_le
      intro E k hk
      have hk' : k ≤ m := Nat.lt_succ_iff.mp (List.mem_range.mp hk)
      have := time_budgetBacktrack hT hB W R m N [] k [] (PhyloTree.root_mem_nodes t) hk'
      by_cases hx : R ([], k) ≠ ⊥
      · simp only [time_bind, time_step, val_step, hx, ne_eq, not_false_eq_true,
          decide_true, ↓reduceIte]
        omega
      · simp only [time_bind, time_step, val_step, hx, decide_false, Bool.false_eq_true,
          ↓reduceIte, time_pure]
        omega
    _ = _ := by simp only [sum_map_const_nat, List.length_range]

/-- **Section 2.4 with backtracking**, as a program: the matrix of `camusBudget`, with the budget
columns `0, …, m`, then, for each budget `k ≤ m` whose cell at the root is not `⊥` (whose row is
nonempty), the backtracking from the root with fuel `|V(T)|`, larger than the height of `T`
(`budgetNetworks`). Returns for each `k` the pairs `(u, w)` of the edges added in `N_k`; for
`k > m`, or a row that is empty, no pairs. -/
def camusBudgetNetworks (t : PhyloTree) (Q : Multiset Quartet) (m : ℕ) :
    Timed (ℕ → List (Address × Address)) := do
  let P ← preprocess t
  let S ← enumerate P.1 Q P.2
  let order ← reverseList P.2
  let R ← budgetFill P.1 S.1 S.2 m order
  let N ← forList (fun c _ => step (c + 1)) P.2 0
  budgetNetworks P.1 S.1 S.2 R N m

/-- **Section 2.4, backtracking, computed.** For a well-labelled tree `T`, a multiset `Q` and a
solution `A` of the recurrence with the weights `s_e` of Equation (1) (`BudgetDP.Array`), for every
budget `k ≤ m` whose row at the root is nonempty, the pairs returned by `camusBudgetNetworks` for
`k` form a backtracking trace of `A` from the root with budget `k` (`BudgetDP.Trace`). -/
theorem camusBudgetNetworks_trace {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet)
    (m : ℕ) {A : Address → ℕ → Finset ℕ} (hA : BudgetDP.Array t (edgeWeight t Q) A) {k : ℕ}
    (hk : k ≤ m) (hrow : (A [] k).Nonempty) :
    BudgetDP.Trace t (edgeWeight t Q) A [] k ((camusBudgetNetworks t Q m).val k).toFinset := by
  have hT := preprocess_correct t
  have hpre := preprocess_order t
  obtain ⟨hB, hW⟩ := enumerate_buckets hT Q
  have hW' : ∀ e ∈ EdgeAbove.candidates t,
      (enumerate (preprocess t).val.1 Q t.preorder).val.2 e = edgeWeight t Q e :=
    fun e he => (hW e he).trans (val_weightScan ht hT Q he)
  have hR := budgetFill_rows hT (fun v e => (hB v).2 e) hW' hA m
  -- the cell at the root is not `⊥`
  obtain ⟨z, hz⟩ := hrow
  have hx : (budgetFill (preprocess t).val.1 (enumerate (preprocess t).val.1 Q t.preorder).val.1
      (enumerate (preprocess t).val.1 Q t.preorder).val.2 m t.preorder.reverse).val ([], k) ≠
        ⊥ := by
    rw [hR [] t.root_mem_nodes k hk,
      rowMax_of_mem hz (array_row_card t _ A hA t.root_mem_nodes k)]
    exact WithBot.coe_ne_bot
  simp only [camusBudgetNetworks, val_bind, val_reverseList, hpre, count_eq_length,
    PhyloTree.preorder_length]
  rw [val_budgetNetworks _ _ _ _ _ m hk hx]
  exact budgetBacktrack_trace hT (fun v e => (hB v).2 e) hW' hA hR t.nodes.card []
    k t.root_mem_nodes (by
      unfold remainingDepth
      have hle : t.nodes.sup List.length < t.nodes.card := by
        rw [Finset.sup_lt_iff (Finset.card_pos.mpr ⟨[], PhyloTree.root_mem_nodes t⟩)]
        intro p hp
        exact PhyloTree.length_lt_card hp
      simpa using hle) hk ⟨z, hz⟩

/-- **Section 2.4, the networks `N_k`, computed** (with Theorem 1's argument for the matrix,
`BudgetDP.trace_graph_optimal`). For a well-labelled tree `T`, a multiset `Q`, and a budget
`k ≤ m` whose row at the root of the matrix computed by `camusBudget` is nonempty, the network
`N_k = Realization.graph t E` of the pairs `E` returned by `camusBudgetNetworks` for `k`
* is built on `T`, with the root of `T` at its root;
* has exactly `k` reticulations;
* satisfies the value of that row quartets of `Q`, counted with multiplicity;
* satisfies, and displays, at least as many quartets of `Q` as every network built on `T` with
  exactly `k` reticulations. -/
theorem camusBudgetNetworks_optimal {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet)
    (m : ℕ) {k : ℕ} (hk : k ≤ m) (hrow : ((camusBudget t Q m).val [] k).Nonempty) :
    let E := ((camusBudgetNetworks t Q m).val k).toFinset
    (Realization.graph t E).AnchoredExtension t ∧
      (Realization.graph t E).reticulationCount = k ∧
      score Q (novel t Q (Realization.graph t E)) ∈ (camusBudget t Q m).val [] k ∧
      (∀ N : RootedNetwork, N.AnchoredExtension t → N.reticulationCount = k →
        score Q (novel t Q N) ≤ score Q (novel t Q (Realization.graph t E))) ∧
      (∀ N : RootedNetwork, N.AnchoredExtension t → N.reticulationCount = k →
        score Q (repertoire Q N) ≤ score Q (repertoire Q (Realization.graph t E))) := by
  intro E
  obtain ⟨A, hA⟩ := exists_array t (edgeWeight t Q)
  have hag := camusBudget_agrees ht Q m hA [] t.root_mem_nodes k hk
  rw [hag] at hrow ⊢
  exact trace_graph_optimal t ht Q A hA (camusBudgetNetworks_trace ht Q m hA hk hrow)

/-- **Section 2.4: the networks `N_1, …, N_m`, computed.** For a well-labelled tree `T`, a multiset
`Q`, and a budget `k ≤ m` whose row at the root of the computed matrix is nonempty (every
`k ≤ n − 1`, `BudgetDP.root_row_nonempty_iff_le`), the network
`N_k = Realization.graph t (E k)` of the pairs returned by `camusBudgetNetworks` for `k` has the
four properties of Section 2.4: it is level-1; it contains `T`, as the switching
`Realization.supportEdges t (E k)`, a subdivision of `T`; it has exactly `k` edges outside that
switching; and it displays at least as many quartets of `Q` as every level-1 network with a
switching that is a subdivision of `T` and exactly `k` edges outside it. -/
theorem camusBudgetNetworks_networks {t : PhyloTree} (ht : t.WellLabelled)
    (Q : Multiset Quartet) (m : ℕ) {k : ℕ} (hk : k ≤ m)
    (hrow : ((camusBudget t Q m).val [] k).Nonempty) :
    let E := fun k => ((camusBudgetNetworks t Q m).val k).toFinset
    (Realization.graph t (E k)).RootedBinaryLevelOne ∧
      Nonempty (SupportSubdivision t (Realization.graph t (E k))
        (Realization.supportEdges t (E k))) ∧
      ((Realization.graph t (E k)).edges \ Realization.supportEdges t (E k)).card = k ∧
      ∀ (N : RootedNetwork) (S : Finset (ℕ × ℕ)), N.RootedBinaryLevelOne →
        Nonempty (SupportSubdivision t N S) → (N.edges \ S).card = k →
        score Q (repertoire Q N) ≤ score Q (repertoire Q (Realization.graph t (E k))) := by
  intro E
  obtain ⟨A, hA⟩ := exists_array t (edgeWeight t Q)
  have hag : ∀ j ≤ m, (camusBudget t Q m).val [] j = A [] j :=
    fun j hj => camusBudget_agrees ht Q m hA [] t.root_mem_nodes j hj
  exact backtracking_networks t ht Q A hA m E
    (fun j hj hjrow => camusBudgetNetworks_trace ht Q m hA hj hjrow) hk ((hag k hk) ▸ hrow)

/-- The arithmetic of `camusBudgetNetworks_time`: with `N ≤ 2n` vertices, `C ≤ 4n²` candidate
pairs and `m ≥ 1`, the matrix and `m + 1` backtrackings from the root take at most
`2100 n² (q + m³ n)` operations. -/
theorem budgetNetworks_arith {n m N C q Tm : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hN : N ≤ 2 * n)
    (hC : C ≤ 4 * n ^ 2) (hmat : Tm ≤ 1000 * n ^ 2 * (q + m ^ 3 * n)) :
    Tm + 2 * N + (m + 1) * (N * (11 + 6 * m) + C * (21 + 6 * m + 25 * N + 6 * (N * m) +
      2 * (N * (m * (6 * m + 2)))) + 4) ≤ 2100 * n ^ 2 * (q + m ^ 3 * n) := by
  have hnm : 1 ≤ n * m := Nat.mul_le_mul hn hm
  have hm2 : m ≤ m ^ 2 := by nlinarith
  have hn3 : n ≤ n ^ 3 := by nlinarith
  -- one backtracking from the root: at most `522 n³ m²` operations
  have hY1 : 4 + N * (11 + 6 * m) ≤ 38 * (n * m) := by
    have : N * (11 + 6 * m) ≤ 2 * n * (17 * m) := Nat.mul_le_mul hN (by omega)
    nlinarith
  have hY2 : 21 + 6 * m + 25 * N + 6 * (N * m) + 2 * (N * (m * (6 * m + 2))) ≤
      121 * (n * m ^ 2) := by
    have h1 : N * (m * (6 * m + 2)) ≤ 2 * n * (8 * m ^ 2) := Nat.mul_le_mul hN (by nlinarith)
    have h2 : N * m ≤ 2 * n * m := Nat.mul_le_mul_right m hN
    have h3 : n * m ≤ n * m ^ 2 := Nat.mul_le_mul_left n hm2
    have h4 : n ≤ n * m ^ 2 := by nlinarith
    have h5 : m ≤ n * m ^ 2 := by nlinarith
    nlinarith
  have hY3 : C * (21 + 6 * m + 25 * N + 6 * (N * m) + 2 * (N * (m * (6 * m + 2)))) ≤
      484 * (n ^ 3 * m ^ 2) := by
    have := Nat.mul_le_mul hC hY2
    have h : 4 * n ^ 2 * (121 * (n * m ^ 2)) = 484 * (n ^ 3 * m ^ 2) := by ring
    linarith
  have hnm3 : n * m ≤ n ^ 3 * m ^ 2 := Nat.mul_le_mul hn3 hm2
  have hY4 : N * (11 + 6 * m) + C * (21 + 6 * m + 25 * N + 6 * (N * m) +
      2 * (N * (m * (6 * m + 2)))) + 4 ≤ 522 * (n ^ 3 * m ^ 2) := by
    linarith
  -- the `m + 1` budgets
  have hback : (m + 1) * (N * (11 + 6 * m) + C * (21 + 6 * m + 25 * N + 6 * (N * m) +
      2 * (N * (m * (6 * m + 2)))) + 4) ≤ 1044 * (n ^ 3 * m ^ 3) := by
    have h1 := Nat.mul_le_mul (show m + 1 ≤ 2 * m by omega) hY4
    have h2 : (2 * m) * (522 * (n ^ 3 * m ^ 2)) = 1044 * (n ^ 3 * m ^ 3) := by ring
    linarith
  have hcount : 2 * N ≤ 4 * (n ^ 3 * m ^ 3) := by
    have h2 : 1 ≤ m ^ 3 := Nat.one_le_pow 3 m hm
    have h3 : n ^ 3 ≤ n ^ 3 * m ^ 3 := Nat.le_mul_of_pos_right _ h2
    omega
  have hgoal : 2100 * n ^ 2 * (q + m ^ 3 * n) = 2100 * (n ^ 2 * q) + 2100 * (n ^ 3 * m ^ 3) := by
    ring
  have hmat' : 1000 * n ^ 2 * (q + m ^ 3 * n) = 1000 * (n ^ 2 * q) + 1000 * (n ^ 3 * m ^ 3) := by
    ring
  rw [hgoal]
  rw [hmat'] at hmat
  omega

/-- **Section 2.4 with backtracking: the running time `O(n²(|Q| + m³n))`.** For a well-labelled
tree `T` with `n` leaves, a multiset `Q` with `|Q|` distinct quartets, and `m ≥ 1` budget columns,
`camusBudgetNetworks t Q m`, which computes the matrix and backtracks the networks `N_k` for every
`k ≤ m`, performs at most `2100 n² (|Q| + m³ n)` operations. -/
theorem camusBudgetNetworks_time {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet)
    {m : ℕ} (hm : 1 ≤ m) :
    (camusBudgetNetworks t Q m).time ≤
      2100 * t.taxa.card ^ 2 * (Q.toFinset.card + m ^ 3 * t.taxa.card) := by
  have hT := preprocess_correct t
  have hpre := preprocess_order t
  obtain ⟨hB, -⟩ := enumerate_buckets hT Q
  -- the matrix, as in `camusBudget`
  have hmat := camusBudget_time ht Q hm
  -- the backtracking from the root, for each budget `k ≤ m`
  have hloop := time_budgetNetworks hT (fun v e => (hB v).2 e)
    (enumerate (preprocess t).val.1 Q t.preorder).val.2
    (budgetFill (preprocess t).val.1 (enumerate (preprocess t).val.1 Q t.preorder).val.1
      (enumerate (preprocess t).val.1 Q t.preorder).val.2 m t.preorder.reverse).val
    t.nodes.card m
  rw [sum_ownCostBudget (fun v e => (hB v).2 e) (fun v => (hB v).1)] at hloop
  have hsplit : (camusBudgetNetworks t Q m).time = (camusBudget t Q m).time +
      2 * t.nodes.card + (budgetNetworks (preprocess t).val.1
        (enumerate (preprocess t).val.1 Q t.preorder).val.1
        (enumerate (preprocess t).val.1 Q t.preorder).val.2
        (budgetFill (preprocess t).val.1 (enumerate (preprocess t).val.1 Q t.preorder).val.1
          (enumerate (preprocess t).val.1 Q t.preorder).val.2 m t.preorder.reverse).val
        t.nodes.card m).time := by
    simp only [camusBudgetNetworks, camusBudget, time_bind, val_reverseList, hpre, time_pure,
      count_eq_length, time_count, PhyloTree.preorder_length]
    omega
  rw [hsplit]
  have hnodes := t.nodes_count
  have htaxa : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  have hc := candidates_bound t
  rw [htaxa] at hmat ⊢
  have hN : t.nodes.card ≤ 2 * t.labels.length := by omega
  have hC : (EdgeAbove.candidates t).card ≤ 4 * t.labels.length ^ 2 := by
    have := Nat.mul_le_mul hN hN
    nlinarith
  have := budgetNetworks_arith t.labels_nonempty hm hN hC hmat (q := Q.toFinset.card)
  omega

end Complexity

end Camus
