module

public import Camus.Complexity.PeakMemory
public import Camus.Complexity.BudgetBacktracking

/-!
# Section 2.4: the peak memory of the modified program

The paper bounds the running time of the modified dynamic program of Section 2.4, not its memory.
This file writes the matrix of `Complexity.camusBudget` and the backtracking of
`Complexity.camusBudgetNetworks` (`Camus/Complexity/BudgetProgram.lean`,
`Camus/Complexity/BudgetBacktracking.lean`) with their memory, in the semantics of
`Camus/Complexity/Space.lean`, and bounds the peak of a run: `O(n² + m n)` cells besides the input
(`Complexity.peak_camusBudgetS`, `Complexity.peak_camusBudgetNetworksS`), so `O(n⁴ + m n)` with
the input, and `O(n⁴)` for `m ≤ n − 1`, the budgets whose rows at the root are nonempty
(`BudgetDP.root_row_nonempty_iff_le`).

What is charged, in cells, besides what `Camus/Complexity/PeakMemory.lean` charges for the
preprocessing, the enumeration and the reverse of the preorder:

* the matrix (`Complexity.budgetFillS`): `(m + 1) |V(T)|` cells, one per vertex and budget
  `0, …, m`, allocated first and written in place;
* in a cell `(v, k)` (`Complexity.budgetCellS`), for each pair of the bucket of `v`, the list of the
  subtrees hanging off its cycle and the two rows of its knapsack, `2 k` cells (`knapsack` reads
  the previous row while it writes the next one), released once the pair is examined;
* the backtracking (`Complexity.budgetBacktrackS`): a frame per call, one cell per pair found; the
  test of each pair of a bucket as in the cell (`Complexity.gallTestS`); in a call that adds an
  edge, the list of the hanging subtrees and the table of their budgets, held while the
  backtracking continues there, and, while the budgets are found (`Complexity.budgetsS`), the
  knapsack table, `(|L| + 1) k` cells for `|L|` hanging subtrees, and the reverse of the list,
  released once the budgets are found;
* the families returned (`Complexity.budgetNetworksS`): a table of `m + 1` entries, and the pairs
  found for each budget.

The matrix, the knapsack table and the table of the budgets are written at the keys of their arrays
(`Complexity.budgetFill_support`, `Complexity.knapsackTable_support`,
`Complexity.knapsackBack_support`).

## Main results

* `Complexity.camusBudgetS`, `Complexity.run_camusBudgetS`: the matrix with its memory.
* `Complexity.peak_camusBudgetS`: at most `9 |V(T)| + 3 |V(T)|² + m |V(T)| + 2 m` cells.
* `Complexity.camusBudgetNetworksS`, `Complexity.run_camusBudgetNetworksS`: the matrix and the
  backtracking for every `k ≤ m`, with their memory.
* `Complexity.peak_camusBudgetNetworksS`: at most `5 |V(T)|² + 3 m |V(T)| + 14 |V(T)| + 4 m + 3`
  cells.
* `Complexity.camusBudgetNetworks_memory`: with the input, at most `85 n⁴ + 6 m n + 4 m`.
* `Complexity.camusBudgetNetworksS_section24`: the traces, the running time and the memory of
  Section 2.4 with backtracking together.
-/

@[expose] public section

namespace Camus.Complexity

open Timed DynamicProgramming BudgetDP

/-! ### The matrix -/

/-- The cell `(v, k)` of the matrix (`budgetCell`), with its memory: for each pair of the bucket of
`v`, the list of the subtrees hanging off its cycle and the two rows of its knapsack, released once
the pair is examined. -/
def budgetCellS (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) (v : Address) (k : ℕ) :
    Spaced (WithBot ℕ) := do
  let kd ← Spaced.op (step (T.kind v))
  match kd with
  | .leaf _ => Spaced.op (steps 2 (if k = 0 then (0 : WithBot ℕ) else ⊥))
  | .fork l r => do
      let c ← Spaced.op (convAt (fun i => R (l, i)) (fun i => R (r, i)) k)
      let b ← Spaced.op (steps 2 (if k = 0 then [] else B v))
      Spaced.forList (fun acc e => Spaced.scope (fun _ => 0) (do
          let L ← Spaced.build List.length (hangingList T e)
          let f ← Spaced.withAlloc (2 * (k - 1 + 1)) (Spaced.op (knapsack R L (k - 1)))
          let s ← Spaced.op (steps 2 (W e))
          Spaced.op (steps 2 (acc ⊔ ((s : WithBot ℕ) + f))))) b c

/-- The program of `budgetCellS` is `budgetCell`. -/
theorem run_budgetCellS (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) (v : Address) (k : ℕ) :
    (budgetCellS T B W R v k).run = budgetCell T B W R v k := by
  unfold budgetCellS budgetCell
  simp only [Spaced.run_bind, Spaced.run_op]
  congr 1
  funext kd
  cases kd <;> rfl

/-- With correct tables and buckets, a cell of budget `k ≤ m` keeps nothing and holds at most
`|V(T)| + 2 m` cells. -/
theorem budgetCellS_memory {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) (v : Address) {k m : ℕ}
    (hk : k ≤ m) :
    (budgetCellS T B W R v k).kept = 0 ∧
      (budgetCellS T B W R v k).peak ≤ t.nodes.card + 2 * m := by
  unfold budgetCellS
  cases T.kind v with
  | leaf a => simp
  | fork l r =>
    -- each pair of the bucket: its hanging subtrees and the two rows of its knapsack
    have hpair : ∀ (acc : WithBot ℕ) (e : Address × Address),
        e ∈ (if k = 0 then [] else B v) →
          (Spaced.scope (fun _ => 0) (do
            let L ← Spaced.build List.length (hangingList T e)
            let f ← Spaced.withAlloc (2 * (k - 1 + 1)) (Spaced.op (knapsack R L (k - 1)))
            let s ← Spaced.op (steps 2 (W e))
            Spaced.op (steps 2 (acc ⊔ ((s : WithBot ℕ) + f)))) : Spaced (WithBot ℕ)).kept = 0 ∧
          (Spaced.scope (fun _ => 0) (do
            let L ← Spaced.build List.length (hangingList T e)
            let f ← Spaced.withAlloc (2 * (k - 1 + 1)) (Spaced.op (knapsack R L (k - 1)))
            let s ← Spaced.op (steps 2 (W e))
            Spaced.op (steps 2 (acc ⊔ ((s : WithBot ℕ) + f)))) : Spaced (WithBot ℕ)).peak ≤
            t.nodes.card + 2 * m := by
      intro acc e he
      have hk0 : k ≠ 0 := by intro h; simp [h] at he
      have hbe : e ∈ B v := by simpa [hk0] using he
      have hae := (Finset.mem_filter.mp (Finset.mem_filter.mp ((hB v e).mp hbe)).1).2
      have hL := length_hangingList hT hae
      simp only [Spaced.kept_scope, Spaced.peak_scope, Spaced.peak_bind, Spaced.kept_build,
        Spaced.peak_build, Spaced.kept_withAlloc, Spaced.peak_withAlloc, Spaced.kept_op,
        Spaced.peak_op, true_and]
      omega
    have hloop := Spaced.loopPeak_le _ (t.nodes.card + 2 * m) (if k = 0 then [] else B v)
      (convAt (fun i => R (l, i)) (fun i => R (r, i)) k).val
      (fun acc e he => (hpair acc e he).1) (fun acc e he => (hpair acc e he).2)
    simp only [Spaced.kept_bind, Spaced.peak_bind, Spaced.kept_op, Spaced.peak_op, Spaced.run_op,
      val_step, val_steps, Spaced.kept_forList, Spaced.peak_forList, Nat.zero_add]
    refine ⟨?_, by omega⟩
    have := Spaced.loopKept_le _ 0 (if k = 0 then [] else B v)
      (convAt (fun i => R (l, i)) (fun i => R (r, i)) k).val
      (fun acc e he => by rw [(hpair acc e he).1])
    simpa using this

/-- The matrix (`budgetFill`), with its memory: `(m + 1)` cells per vertex of `order`, allocated
first and written in place. -/
def budgetFillS (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (m : ℕ) (order : List Address) :
    Spaced (Address × ℕ → WithBot ℕ) :=
  Spaced.withAlloc ((m + 1) * order.length) (Spaced.forList (fun R k =>
    Spaced.forList (fun R v => do
      let x ← budgetCellS T B W R v k
      Spaced.op (step (Function.update R (v, k) x))) order R) (List.range (m + 1)) fun _ => ⊥)

/-- The program of `budgetFillS` is `budgetFill`. -/
theorem run_budgetFillS (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (m : ℕ) (order : List Address) :
    (budgetFillS T B W m order).run = budgetFill T B W m order := by
  simp only [budgetFillS, budgetFill, Spaced.run_withAlloc, Spaced.run_forList, Spaced.run_bind,
    run_budgetCellS, Spaced.run_op]

/-- With correct tables and buckets, the matrix over the vertices `order` keeps its
`(m + 1) |order|` cells and holds at most `|V(T)| + 2 m` more. -/
theorem budgetFillS_memory {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    (W : Address × Address → ℕ) (m : ℕ) (order : List Address) :
    (budgetFillS T B W m order).kept = (m + 1) * order.length ∧
      (budgetFillS T B W m order).peak ≤ (m + 1) * order.length + (t.nodes.card + 2 * m) := by
  -- one column
  have hcol : ∀ (R : Address × ℕ → WithBot ℕ) (k : ℕ), k ∈ List.range (m + 1) →
      (Spaced.forList (fun R v => do
        let x ← budgetCellS T B W R v k
        Spaced.op (step (Function.update R (v, k) x))) order R).kept = 0 ∧
      (Spaced.forList (fun R v => do
        let x ← budgetCellS T B W R v k
        Spaced.op (step (Function.update R (v, k) x))) order R).peak ≤
          t.nodes.card + 2 * m := by
    intro R k hk
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (List.mem_range.mp hk)
    have hcell : ∀ (R : Address × ℕ → WithBot ℕ) (v : Address), v ∈ order →
        (do let x ← budgetCellS T B W R v k
            Spaced.op (step (Function.update R (v, k) x)) :
              Spaced (Address × ℕ → WithBot ℕ)).kept = 0 ∧
        (do let x ← budgetCellS T B W R v k
            Spaced.op (step (Function.update R (v, k) x)) :
              Spaced (Address × ℕ → WithBot ℕ)).peak ≤ t.nodes.card + 2 * m := by
      intro R v _
      obtain ⟨h1, h2⟩ := budgetCellS_memory hT hB W R v hk'
      simp only [Spaced.kept_bind, Spaced.peak_bind, Spaced.kept_op, Spaced.peak_op, h1,
        true_and]
      omega
    have h1 := Spaced.loopKept_le _ 0 order R (fun R v hv => by rw [(hcell R v hv).1])
    have h2 := Spaced.loopPeak_le _ _ order R (fun R v hv => (hcell R v hv).1)
      (fun R v hv => (hcell R v hv).2)
    simp only [Spaced.kept_forList, Spaced.peak_forList]
    simp only [Nat.mul_zero, Nat.le_zero] at h1
    exact ⟨h1, h2⟩
  have h1 := Spaced.loopKept_le _ 0 (List.range (m + 1)) (fun _ => ⊥)
    (fun R k hk => by rw [(hcol R k hk).1])
  have h2 := Spaced.loopPeak_le _ _ (List.range (m + 1)) (fun _ => ⊥)
    (fun R k hk => (hcol R k hk).1) (fun R k hk => (hcol R k hk).2)
  simp only [budgetFillS, Spaced.kept_withAlloc, Spaced.peak_withAlloc, Spaced.kept_forList,
    Spaced.peak_forList]
  simp only [Nat.mul_zero, Nat.le_zero] at h1
  omega

/-- **Section 2.4**, the matrix (`camusBudget`), with its memory. -/
def camusBudgetS (t : PhyloTree) (Q : Multiset Quartet) (m : ℕ) :
    Spaced (Address → ℕ → Finset ℕ) := do
  let P ← preprocessS t
  let S ← enumerateS P.1 Q P.2
  let order ← Spaced.build List.length (reverseList P.2)
  let R ← budgetFillS P.1 S.1 S.2 m order
  pure fun v k => if k ≤ m then toRow (R (v, k)) else ∅

/-- The program of `camusBudgetS` is `camusBudget`: same result, same running time. -/
theorem run_camusBudgetS (t : PhyloTree) (Q : Multiset Quartet) (m : ℕ) :
    (camusBudgetS t Q m).run = camusBudget t Q m := by
  simp only [camusBudgetS, camusBudget, Spaced.run_bind, run_preprocessS, run_enumerateS,
    Spaced.run_build, run_budgetFillS, Spaced.run_pure]

/-- **Section 2.4: the memory of the matrix.** A run of `camusBudget` with the budget columns
`0, …, m` holds, besides its input, at most `9 |V(T)| + 3 |V(T)|² + m |V(T)| + 2 m` cells at every
step: the tables of Section 2.3 and the `(m + 1) |V(T)|` cells of the matrix. -/
theorem peak_camusBudgetS (t : PhyloTree) (Q : Multiset Quartet) (m : ℕ) :
    (camusBudgetS t Q m).peak ≤
      9 * t.nodes.card + 3 * t.nodes.card ^ 2 + m * t.nodes.card + 2 * m := by
  have hT := preprocess_correct t
  have hpre := preprocess_order t
  obtain ⟨hB, -⟩ := enumerate_buckets hT Q
  obtain ⟨hk1, hp1⟩ := preprocessS_memory t
  have hP : (preprocessS t).run.val = (preprocess t).val := by rw [run_preprocessS]
  obtain ⟨hk2, hp2⟩ := enumerateS_memory (preprocessS t).run.val.1 Q (preprocessS t).run.val.2
  rw [hP, hpre, PhyloTree.preorder_length] at hk2 hp2
  obtain ⟨hk4, hp4⟩ := budgetFillS_memory hT (fun v e => (hB v).2 e)
    (enumerate (preprocess t).val.1 Q t.preorder).val.2 m t.preorder.reverse
  rw [List.length_reverse, PhyloTree.preorder_length] at hk4 hp4
  simp only [camusBudgetS, Spaced.peak_bind, Spaced.kept_build, Spaced.peak_build,
    Spaced.run_build, run_enumerateS, hP, hpre, val_reverseList, List.length_reverse,
    PhyloTree.preorder_length, Spaced.peak_pure]
  unfold tableCells at hk1 hp1
  have : (m + 1) * t.nodes.card = m * t.nodes.card + t.nodes.card := by ring
  omega

/-! ### Backtracking through the matrix -/

/-- Sequential composition in the cost monad is associative. -/
theorem Timed.bind_assoc {α β γ : Type} (x : Timed α) (f : α → Timed β) (g : β → Timed γ) :
    (x >>= f) >>= g = x >>= fun a => f a >>= g := by
  change Timed.mk _ _ = Timed.mk _ _
  congr 1
  exact Nat.add_assoc _ _ _

/-- `findList p l` (`Timed.findList`), with its memory declared directly: it keeps nothing, and its
peak is the largest peak of a test. The declaration is valid when every test keeps nothing, as in
its one use, whose test `Complexity.gallTestS` runs in a scope that keeps nothing. -/
def Spaced.findList {α : Type} (p : α → Spaced Bool) (l : List α) : Spaced (Option α) :=
  ⟨Timed.findList (fun a => (p a).run) l, 0, (l.map fun a => (p a).peak).foldr max 0⟩

@[simp] theorem Spaced.run_findList {α : Type} (p : α → Spaced Bool) (l : List α) :
    (Spaced.findList p l).run = Timed.findList (fun a => (p a).run) l := rfl

@[simp] theorem Spaced.kept_findList {α : Type} (p : α → Spaced Bool) (l : List α) :
    (Spaced.findList p l).kept = 0 := rfl

/-- If each test holds at most `c` cells, the search holds at most `c`. -/
theorem Spaced.peak_findList_le {α : Type} (p : α → Spaced Bool) (c : ℕ) :
    ∀ (l : List α), (∀ a ∈ l, (p a).peak ≤ c) → (Spaced.findList p l).peak ≤ c := by
  intro l
  induction l with
  | nil => intro _; simp [Spaced.findList]
  | cons a l ih =>
    intro h
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    simp only [Spaced.findList, List.map_cons, List.foldr_cons] at hl ⊢
    omega

/-- The test of a pair (`gallTest`), with its memory: the list of the subtrees hanging off its cycle
and the two rows of its knapsack, released once the test returns. -/
def gallTestS (T : Tables) (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ)
    (x : WithBot ℕ) (j : ℕ) (e : Address × Address) : Spaced Bool :=
  Spaced.scope (fun _ => 0) (do
    let L ← Spaced.build List.length (hangingList T e)
    let c ← Spaced.withAlloc (2 * (j + 1)) (Spaced.op (knapsack R L j))
    let s ← Spaced.op (step (W e))
    Spaced.op (steps 2 (decide ((s : WithBot ℕ) + c = x))))

/-- The program of `gallTestS` is `gallTest`. -/
theorem run_gallTestS (T : Tables) (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ)
    (x : WithBot ℕ) (j : ℕ) (e : Address × Address) :
    (gallTestS T W R x j e).run = gallTest T W R x j e := rfl

/-- With correct tables, the test of an admissible pair holds at most `|V(T)| + 2 (j + 1)`
cells. -/
theorem peak_gallTestS {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) (x : WithBot ℕ) (j : ℕ)
    {e : Address × Address} (he : EdgeAbove.Admissible t e) :
    (gallTestS T W R x j e).peak ≤ t.nodes.card + 2 * (j + 1) := by
  have hL := length_hangingList hT he
  simp only [gallTestS, Spaced.peak_scope, Spaced.peak_bind, Spaced.kept_build,
    Spaced.peak_build, Spaced.kept_withAlloc, Spaced.peak_withAlloc, Spaced.kept_op,
    Spaced.peak_op]
  omega

/-- The budgets of the hanging subtrees `L` at the budget `j`, found by backtracking through the
knapsack table, with their memory: the knapsack table, `(|L| + 1)(j + 1)` cells, and the reverse of
`L` are released once the budgets are found; the table of the budgets, `|L|` cells, is kept. -/
def budgetsS (R : Address × ℕ → WithBot ℕ) (L : List Address) (j : ℕ) :
    Spaced (Address → ℕ) :=
  Spaced.scope (fun _ => L.length) (do
    let F ← Spaced.withAlloc ((L.length + 1) * (j + 1)) (Spaced.op (knapsackTable R L j))
    let Lr ← Spaced.build List.length (reverseList L)
    let p ← Spaced.op (forList (fun c _ => step (c + 1)) L 0)
    Spaced.withAlloc L.length (Spaced.op (knapsackBack R F Lr p j fun _ => 0)))

/-- The program of `budgetsS`: the knapsack table, the reverse of `L`, its length, and the
backtracking through the knapsack table. -/
theorem run_budgetsS (R : Address × ℕ → WithBot ℕ) (L : List Address) (j : ℕ) :
    (budgetsS R L j).run = (do
      let F ← knapsackTable R L j
      let Lr ← reverseList L
      let p ← forList (fun c _ => step (c + 1)) L 0
      knapsackBack R F Lr p j fun _ => 0) := rfl

/-- Finding the budgets keeps their table, `|L|` cells, and holds at most
`(|L| + 1)(j + 1) + 2 |L|`; the budgets found are at most `j`. -/
theorem budgetsS_memory (R : Address × ℕ → WithBot ℕ) (L : List Address) (j : ℕ) :
    (budgetsS R L j).kept = L.length ∧
      (budgetsS R L j).peak ≤ (L.length + 1) * (j + 1) + 2 * L.length ∧
      ∀ y, (budgetsS R L j).run.val y ≤ j := by
  refine ⟨rfl, ?_, fun y => ?_⟩
  · simp only [budgetsS, Spaced.peak_scope, Spaced.peak_bind, Spaced.kept_withAlloc,
      Spaced.peak_withAlloc, Spaced.kept_op, Spaced.peak_op, Spaced.kept_build,
      Spaced.peak_build, Spaced.run_withAlloc, Spaced.run_op, Spaced.run_build, val_reverseList,
      List.length_reverse, max_le_iff]
    omega
  · rw [run_budgetsS]
    simp only [val_bind]
    exact knapsackBack_le R _ _ _ j j _ (fun _ => Nat.zero_le _) le_rfl y

/-- Backtracking through the matrix (`budgetBacktrack`, Section 2.4), with its memory: each call
holds its frame; the test of each pair of the bucket runs in its own scope; a call that adds an
edge holds the list of the hanging subtrees and the table of their budgets while it continues
there, and the knapsack table and the reverse of the list only while it finds the budgets; the
pairs found are kept, one cell each, and the rest is released at the end of the call. -/
def budgetBacktrackS (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) :
    ℕ → Address → ℕ → List (Address × Address) → Spaced (List (Address × Address))
  | 0, _, _, acc => pure acc
  | n + 1, v, k, acc => Spaced.frame (Spaced.scope (fun res => res.length - acc.length) (do
      let kd ← Spaced.op (step (T.kind v))
      match kd with
      | .leaf _ => pure acc
      | .fork l r => do
          let x ← Spaced.op (step (R (v, k)))
          let split ← Spaced.op (findSplit (fun i => R (l, i)) (fun i => R (r, i)) x k)
          match split with
          | some i => do
              let acc ← budgetBacktrackS T B W R n l i acc
              let k' ← Spaced.op (step (k - i))
              budgetBacktrackS T B W R n r k' acc
          | none => do
              let bucket ← Spaced.op (steps 2 (if k = 0 then [] else B v))
              let j ← Spaced.op (step (k - 1))
              let found ← Spaced.findList (gallTestS T W R x j) bucket
              match found with
              | none => pure acc
              | some e => do
                  let L ← Spaced.build List.length (hangingList T e)
                  let bud ← budgetsS R L j
                  Spaced.withAlloc 1 (Spaced.forList (fun acc r => do
                      let b ← Spaced.op (step (bud r))
                      budgetBacktrackS T B W R n r b acc) L (e :: acc))))

/-- The program of `budgetBacktrackS` is `budgetBacktrack`. -/
theorem run_budgetBacktrackS (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) :
    ∀ (n : ℕ) (v : Address) (k : ℕ) (acc : List (Address × Address)),
      (budgetBacktrackS T B W R n v k acc).run = budgetBacktrack T B W R n v k acc := by
  intro n
  induction n with
  | zero => intro v k acc; rfl
  | succ n ih =>
    intro v k acc
    simp only [budgetBacktrackS, budgetBacktrack, Spaced.run_frame, Spaced.run_scope,
      Spaced.run_bind, Spaced.run_op]
    congr 1
    funext kd
    cases kd with
    | leaf a => rfl
    | fork l r =>
      simp only [Spaced.run_bind, Spaced.run_op]
      congr 1; funext x; congr 1; funext split
      cases split with
      | some i => simp only [Spaced.run_bind, Spaced.run_op, ih]
      | none =>
        simp only [Spaced.run_bind, Spaced.run_op, Spaced.run_findList, run_gallTestS]
        congr 1; funext bucket; congr 1; funext j; congr 1; funext found
        cases found with
        | none => rfl
        | some e =>
          simp only [Spaced.run_bind, Spaced.run_build, run_budgetsS, Spaced.run_withAlloc,
            Spaced.run_op, Spaced.run_forList, ih, Timed.bind_assoc]

/-- With correct tables and buckets, the backtracking through the matrix from `v` finds at most
one pair per vertex of `T_v`. -/
theorem length_budgetBacktrack {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) :
    ∀ (n : ℕ) (v : Address) (k : ℕ), v ∈ t.nodes →
      (budgetBacktrack T B W R n v k []).val.length ≤ (cone t v).card := by
  intro n
  induction n with
  | zero => intro v k _; simp [budgetBacktrack]
  | succ n ih =>
    intro v k hv
    have hvc : v ∈ cone t v := mem_cone.mpr ⟨hv, List.prefix_refl v⟩
    have hcard := Finset.card_erase_add_one hvc
    obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff v).mp hv
    have hkd := hT.kind v hv
    cases sub with
    | leaf a =>
      have hk' : T.kind v = .leaf a := by rw [hkd]; simp [kindAt, hsub]
      simp [budgetBacktrack, hk']
    | fork l r =>
      have hk' : T.kind v = .fork (v ++ [false]) (v ++ [true]) := by
        rw [hkd]; simp [kindAt, hsub]
      have hl := PhyloTree.child_mem_nodes hsub false
      have hr := PhyloTree.child_mem_nodes hsub true
      cases hs : (findSplit (fun i => R (v ++ [false], i)) (fun i => R (v ++ [true], i))
          (R (v, k)) k).val with
      | some i =>
        -- the two children: disjoint subtrees below `v`
        obtain ⟨hdisj, hsubset⟩ := cone_children (t := t) (v := v)
        have hc := Finset.card_le_card hsubset
        rw [Finset.card_union_of_disjoint hdisj] at hc
        have h1 := ih (v ++ [false]) i hl
        have h2 := ih (v ++ [true]) (k - i) hr
        simp only [budgetBacktrack, val_bind, val_step, hk', hs]
        rw [budgetBacktrack_acc, List.length_append]
        omega
      | none =>
        cases hf : (findList (gallTest T W R (R (v, k)) (k - 1))
            (if k = 0 then [] else B v)).val with
        | none => simp [budgetBacktrack, hk', hs, hf]
        | some e =>
          -- one pair, and the subtrees hanging off its cycle: disjoint, below `v`
          obtain ⟨heB, -⟩ := findList_sound _ _ e hf
          have hk0 : k ≠ 0 := by intro h; simp [h] at heB
          have hbe : e ∈ B v := by simpa [hk0] using heB
          have he := (hB v e).mp hbe
          obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp he
          have hae := (Finset.mem_filter.mp hc).2
          obtain ⟨hnd, hmem⟩ := hangingList_spec hT hae
          obtain ⟨hpd, hsub'⟩ := cone_hanging hae
          rw [htarget] at hsub'
          have hfun : ∀ bud : Address → ℕ, (fun (acc : List (Address × Address)) r =>
              (budgetBacktrack T B W R n r (bud r) acc).val) =
              fun acc r => (budgetBacktrack T B W R n r (bud r) []).val ++ acc := by
            intro bud
            funext acc r
            exact budgetBacktrack_acc T B W R n r (bud r) acc
          simp only [budgetBacktrack, val_bind, val_step, val_steps, hk', hs, hf, val_forList,
            hfun]
          rw [length_foldl_prepend]
          have hsum : ∀ bud : Address → ℕ, ((hangingList T e).val.map
              fun r => (budgetBacktrack T B W R n r (bud r) []).val.length).sum ≤
                ((cone t v).erase v).card := by
            intro bud
            calc
              _ ≤ ((hangingList T e).val.map fun r => (cone t r).card).sum :=
                List.sum_le_sum fun r hr =>
                  ih r (bud r) (Finset.mem_filter.mp ((hmem r).mp hr)).1
              _ = ∑ r ∈ hanging t e, (cone t r).card := by
                rw [← List.sum_toFinset _ hnd]
                congr 1
                ext r
                simp [hmem]
              _ = ((hanging t e).biUnion (cone t)).card := (Finset.card_biUnion hpd).symm
              _ ≤ _ := Finset.card_le_card hsub'
          simp only [List.length_singleton]
          calc
            _ ≤ 1 + ((cone t v).erase v).card := Nat.add_le_add_left (hsum _) 1
            _ = (cone t v).card := by omega

/-- The cells that the backtracking through the matrix holds besides one frame, one pair, the list
of the hanging subtrees and the table of their budgets per level of calls, for budgets `≤ m` and
`N` vertices: the test of a pair, and the knapsack table with the reverse of the list while the
budgets are found. -/
def budgetTransient (N m : ℕ) : ℕ := (N + 1) * (m + 1) + N + 2 * m + 1

/-- With correct tables and buckets, the backtracking through the matrix from `v` with a budget
`k ≤ m` and fuel `n` keeps at most one cell per vertex of `T_v`, the pairs it finds, and holds at
most `|T_v| + n (2 |V(T)| + 2) + budgetTransient |V(T)| m` cells: at each of at most `n` levels of
calls, a frame, a pair, the list of the hanging subtrees and the table of their budgets, and at the
deepest level the test of a pair or the knapsack table. -/
theorem budgetBacktrackS_memory {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) (m : ℕ) :
    ∀ (n : ℕ) (v : Address) (k : ℕ) (acc : List (Address × Address)), v ∈ t.nodes → k ≤ m →
      (budgetBacktrackS T B W R n v k acc).kept ≤ (cone t v).card ∧
        (budgetBacktrackS T B W R n v k acc).peak ≤ (cone t v).card +
          n * (2 * t.nodes.card + 2) + budgetTransient t.nodes.card m := by
  intro n
  induction n with
  | zero => intro v k acc _ _; simp [budgetBacktrackS]
  | succ n ih =>
    intro v k acc hv hk
    set N := t.nodes.card with hN
    set Z := budgetTransient N m with hZ
    have hvc : v ∈ cone t v := mem_cone.mpr ⟨hv, List.prefix_refl v⟩
    have hcard := Finset.card_erase_add_one hvc
    -- the pairs kept: those found
    have hkept : (budgetBacktrackS T B W R (n + 1) v k acc).kept ≤ (cone t v).card := by
      have := length_budgetBacktrack hT hB W R (n + 1) v k hv
      have hkeq : (budgetBacktrackS T B W R (n + 1) v k acc).kept =
          (budgetBacktrackS T B W R (n + 1) v k acc).run.val.length - acc.length := rfl
      rw [hkeq, run_budgetBacktrackS, budgetBacktrack_acc, List.length_append]
      omega
    refine ⟨hkept, ?_⟩
    have hkept' := hkept
    simp only [budgetBacktrackS, Spaced.kept_frame, Spaced.kept_scope] at hkept'
    simp only [budgetBacktrackS, Spaced.peak_frame, Spaced.peak_scope]
    suffices hin : (do
        let kd ← Spaced.op (step (T.kind v))
        match kd with
        | .leaf _ => pure acc
        | .fork l r => do
            let x ← Spaced.op (step (R (v, k)))
            let split ← Spaced.op (findSplit (fun i => R (l, i)) (fun i => R (r, i)) x k)
            match split with
            | some i => do
                let acc ← budgetBacktrackS T B W R n l i acc
                let k' ← Spaced.op (step (k - i))
                budgetBacktrackS T B W R n r k' acc
            | none => do
                let bucket ← Spaced.op (steps 2 (if k = 0 then [] else B v))
                let j ← Spaced.op (step (k - 1))
                let found ← Spaced.findList (gallTestS T W R x j) bucket
                match found with
                | none => pure acc
                | some e => do
                    let L ← Spaced.build List.length (hangingList T e)
                    let bud ← budgetsS R L j
                    Spaced.withAlloc 1 (Spaced.forList (fun acc r => do
                        let b ← Spaced.op (step (bud r))
                        budgetBacktrackS T B W R n r b acc) L (e :: acc)) :
          Spaced (List (Address × Address))).peak ≤
          (cone t v).card + n * (2 * N + 2) + 2 * N + 1 + Z by
      have : n * (2 * N + 2) + (2 * N + 2) = (n + 1) * (2 * N + 2) := by ring
      omega
    obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff v).mp hv
    have hkd := hT.kind v hv
    cases sub with
    | leaf a =>
      have hk' : T.kind v = .leaf a := by rw [hkd]; simp [kindAt, hsub]
      simp [hk']
    | fork l r =>
      have hk' : T.kind v = .fork (v ++ [false]) (v ++ [true]) := by
        rw [hkd]; simp [kindAt, hsub]
      have hl := PhyloTree.child_mem_nodes hsub false
      have hr := PhyloTree.child_mem_nodes hsub true
      simp only [Spaced.peak_bind, Spaced.kept_op, Spaced.peak_op, Spaced.run_op, val_step,
        hk', Nat.zero_add]
      cases hs : (findSplit (fun i => R (v ++ [false], i)) (fun i => R (v ++ [true], i))
          (R (v, k)) k).val with
      | some i =>
        -- the two children, with the budgets `i` and `k - i`
        obtain ⟨hik, -⟩ := findSplit_sound hs
        obtain ⟨hdisj, hsubset⟩ := cone_children (t := t) (v := v)
        have hc := Finset.card_le_card hsubset
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hvc] at hc
        obtain ⟨h1k, h1p⟩ := ih (v ++ [false]) i acc hl (by omega)
        obtain ⟨h2k, h2p⟩ := ih (v ++ [true]) (k - i)
          (budgetBacktrackS T B W R n (v ++ [false]) i acc).run.val hr (by omega)
        simp only [Spaced.peak_bind, Spaced.kept_op, Spaced.peak_op, Spaced.run_op, val_step,
          Nat.zero_add]
        omega
      | none =>
        simp only [Spaced.peak_bind, Spaced.kept_op, Spaced.peak_op, Spaced.run_op, val_step,
          val_steps, Nat.zero_add, Spaced.kept_findList]
        -- the scan of the bucket: the test of each pair
        have hscan : (Spaced.findList (gallTestS T W R (R (v, k)) (k - 1))
            (if k = 0 then [] else B v)).peak ≤ N + 2 * m := by
          apply Spaced.peak_findList_le
          intro e he
          have hk0 : k ≠ 0 := by intro h; simp [h] at he
          have hbe : e ∈ B v := by simpa [hk0] using he
          have hae := (Finset.mem_filter.mp (Finset.mem_filter.mp ((hB v e).mp hbe)).1).2
          have := peak_gallTestS hT W R (R (v, k)) (k - 1) hae
          omega
        cases hf : (Spaced.findList (gallTestS T W R (R (v, k)) (k - 1))
            (if k = 0 then [] else B v)).run.val with
        | none =>
          simp only [Spaced.peak_pure]
          have : N + 2 * m ≤ Z := by rw [hZ]; unfold budgetTransient; omega
          omega
        | some e =>
          -- the pair found, its hanging subtrees, and the budgets found through its knapsack
          rw [Spaced.run_findList] at hf
          obtain ⟨heB, -⟩ := findList_sound _ _ e hf
          have hk0 : k ≠ 0 := by intro h; simp [h] at heB
          have hbe : e ∈ B v := by simpa [hk0] using heB
          have he := (hB v e).mp hbe
          obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp he
          have hae := (Finset.mem_filter.mp hc).2
          obtain ⟨hnd, hmem⟩ := hangingList_spec hT hae
          obtain ⟨hpd, hsub'⟩ := cone_hanging hae
          rw [htarget] at hsub'
          have hL := length_hangingList hT hae
          set L := (hangingList T e).val with hLdef
          -- the budgets, at most `k - 1 ≤ m`, through the knapsack table
          obtain ⟨hbk, hbp, hble⟩ := budgetsS_memory R L (k - 1)
          have htab : (L.length + 1) * (k - 1 + 1) ≤ (N + 1) * (m + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
          -- the recursive calls at the hanging subtrees
          have hloop := Spaced.loopPeak_le_sum (fun acc r => do
                let b ← Spaced.op (step ((budgetsS R L (k - 1)).run.val r))
                budgetBacktrackS T B W R n r b acc)
            (fun r => (cone t r).card) (n * (2 * N + 2) + Z) L (e :: acc) (by
              intro acc' r hr
              obtain ⟨h1, h2⟩ := ih r ((budgetsS R L (k - 1)).run.val r) acc'
                (Finset.mem_filter.mp ((hmem r).mp hr)).1 (by have := hble r; omega)
              simp only [Spaced.kept_bind, Spaced.peak_bind, Spaced.kept_op, Spaced.peak_op,
                Spaced.run_op, val_step, Nat.zero_add]
              omega)
          have hsum : (L.map fun r => (cone t r).card).sum ≤ ((cone t v).erase v).card := by
            calc
              _ = ∑ r ∈ hanging t e, (cone t r).card := by
                rw [← List.sum_toFinset _ hnd]
                congr 1
                ext r
                simp [hmem]
              _ = ((hanging t e).biUnion (cone t)).card := (Finset.card_biUnion hpd).symm
              _ ≤ _ := Finset.card_le_card hsub'
          rw [Finset.card_erase_of_mem hvc] at hsum
          have hZ' : 3 * N + (N + 1) * (m + 1) ≤ 2 * N + 1 + Z := by
            rw [hZ]; unfold budgetTransient; omega
          have hZ'' : N + 2 * m ≤ Z := by rw [hZ]; unfold budgetTransient; omega
          simp only [Spaced.peak_bind, Spaced.kept_build, Spaced.peak_build, Spaced.run_build,
            Spaced.peak_withAlloc, Spaced.peak_forList, max_le_iff, ← hLdef, hbk]
          omega

/-! ### The tables are written at the keys of their arrays -/

/-- The matrix is written at the keys `(v, k)` with `v` in `order` and `k ≤ m`: the
`(m + 1) |order|` cells allocated for it by `budgetFillS`. -/
theorem budgetFill_support (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (m : ℕ) (order : List Address) :
    SupportedIn (budgetFill T B W m order).val ⊥ (order.toFinset ×ˢ Finset.range (m + 1)) := by
  intro x hx
  simp only [budgetFill, val_forList]
  refine foldl_invariant (List.range (m + 1)) _
    (fun _ (R : Address × ℕ → WithBot ℕ) => R x = ⊥) rfl ?_
  intro K k K' R hsplit hR
  have hk : k ∈ Finset.range (m + 1) := by
    rw [Finset.mem_range, ← List.mem_range, hsplit]; simp
  refine foldl_invariant order _ (fun _ (R : Address × ℕ → WithBot ℕ) => R x = ⊥) hR ?_
  intro V v V' U hsplit' hU
  have hv : v ∈ order.toFinset := by rw [List.mem_toFinset, hsplit']; simp
  have hne : x ≠ (v, k) := fun h => hx (h ▸ Finset.mem_product.mpr ⟨hv, hk⟩)
  simp only [val_bind, val_step]
  rw [Function.update_of_ne hne]
  exact hU

/-- The knapsack table over `L` up to the budget `j` is written at the keys `(i, b)` with
`i ≤ |L|` and `b ≤ j`: the `(|L| + 1)(j + 1)` cells allocated for it by `budgetsS`. -/
theorem knapsackTable_support (R : Address × ℕ → WithBot ℕ) (L : List Address) (j : ℕ) :
    SupportedIn (knapsackTable R L j).val ⊥
      (Finset.range (L.length + 1) ×ˢ Finset.range (j + 1)) := by
  intro x hx
  simp only [knapsackTable, val_bind, val_forList, val_steps, val_pure, val_step]
  have h0 : ((List.range (j + 1)).foldl (fun (F : ℕ × ℕ → WithBot ℕ) b =>
      Function.update F (0, b) (if b = 0 then (0 : WithBot ℕ) else ⊥)) fun _ => ⊥) x = ⊥ ∨
      (x.1 = 0 ∧ x.2 ≤ j) := by
    rw [foldl_update_row]
    by_cases h : x.1 = 0 ∧ x.2 ≤ j
    · exact Or.inr h
    · left
      simp only [h, ↓reduceIte]
  -- the rows written so far are those of the subtrees processed
  refine (foldl_invariant L _ (fun (P : List Address) (S : ℕ × (ℕ × ℕ → WithBot ℕ)) =>
      S.1 = P.length ∧ (S.2 x = ⊥ ∨ (x.1 ≤ P.length ∧ x.2 ≤ j))) ⟨rfl, h0.imp_right
        fun h => ⟨by simp [h.1], h.2⟩⟩ ?_).2.resolve_right ?_
  · intro P r P' S hsplit hS
    obtain ⟨hS1, hS2⟩ := hS
    refine ⟨by simp [hS1], ?_⟩
    dsimp only
    rw [foldl_update_row]
    by_cases h : x.1 = S.1 + 1 ∧ x.2 ≤ j
    · exact Or.inr ⟨by simp [h.1, hS1], h.2⟩
    · simp only [h, ↓reduceIte]
      rcases hS2 with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨by simp; omega, h'.2⟩
  · rintro ⟨h1, h2⟩
    exact hx (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩)

/-- The table of the budgets found by backtracking through the knapsack is written at the
subtrees of `rs`: the `|L|` cells allocated for it by `budgetsS`. -/
theorem knapsackBack_support (R : Address × ℕ → WithBot ℕ) (F : ℕ × ℕ → WithBot ℕ)
    (rs : List Address) (i j : ℕ) :
    SupportedIn (knapsackBack R F rs i j fun _ => 0).val 0 rs.toFinset := fun x hx =>
  knapsackBack_of_not_mem R F rs i j _ x (fun h => hx (List.mem_toFinset.mpr h))

/-! ### The networks `N_k` -/

/-- The backtracking from the root for every budget `k ≤ m` (`budgetNetworks`), with its memory:
the table of the families, `m + 1` entries, allocated first, and the pairs found for each budget,
kept. -/
def budgetNetworksS (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) (N m : ℕ) :
    Spaced (ℕ → List (Address × Address)) :=
  Spaced.withAlloc (m + 1) (Spaced.forList (fun E k => do
      let x ← Spaced.op (step (R ([], k)))
      let ok ← Spaced.op (step (decide (x ≠ ⊥)))
      if ok then do
        let Ek ← budgetBacktrackS T B W R N [] k []
        Spaced.op (step (Function.update E k Ek))
      else pure E) (List.range (m + 1)) fun _ => [])

/-- The program of `budgetNetworksS` is `budgetNetworks`. -/
theorem run_budgetNetworksS (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) (N m : ℕ) :
    (budgetNetworksS T B W R N m).run = budgetNetworks T B W R N m := by
  simp only [budgetNetworksS, budgetNetworks, Spaced.run_withAlloc, Spaced.run_forList,
    Spaced.run_bind, Spaced.run_op, Spaced.run_ite, run_budgetBacktrackS, Spaced.run_pure]

/-- With correct tables and buckets, the backtracking from the root of a tree with `N` vertices
for the `m + 1` budgets holds at most `(m + 1)(N + 1) + N (2 N + 3) + budgetTransient N m`
cells. -/
theorem budgetNetworksS_memory {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    (W : Address × Address → ℕ) (R : Address × ℕ → WithBot ℕ) (m : ℕ) :
    (budgetNetworksS T B W R t.nodes.card m).peak ≤ (m + 1) * (t.nodes.card + 1) +
      t.nodes.card * (2 * t.nodes.card + 3) + budgetTransient t.nodes.card m := by
  have hcone : (cone t []).card = t.nodes.card := by
    congr 1
    ext x
    simp [mem_cone]
  have hloop := Spaced.loopPeak_le_sum (fun E k => do
      let x ← Spaced.op (step (R ([], k)))
      let ok ← Spaced.op (step (decide (x ≠ ⊥)))
      if ok then do
        let Ek ← budgetBacktrackS T B W R t.nodes.card [] k []
        Spaced.op (step (Function.update E k Ek))
      else pure E) (fun _ => t.nodes.card)
    (t.nodes.card * (2 * t.nodes.card + 2) + budgetTransient t.nodes.card m)
    (List.range (m + 1)) (fun _ => []) (by
      intro E k hk
      have hk' : k ≤ m := Nat.lt_succ_iff.mp (List.mem_range.mp hk)
      obtain ⟨h1, h2⟩ := budgetBacktrackS_memory hT hB W R m t.nodes.card [] k []
        (PhyloTree.root_mem_nodes t) hk'
      rw [hcone] at h1 h2
      by_cases hx : R ([], k) = ⊥
      · simp [hx]
      · simp only [Spaced.kept_bind, Spaced.peak_bind, Spaced.kept_op, Spaced.peak_op,
          Spaced.run_op, val_step, hx, ne_eq, not_false_eq_true, decide_true, ↓reduceIte,
          Nat.zero_add, Nat.add_zero, max_le_iff]
        omega)
  simp only [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul] at hloop
  simp only [budgetNetworksS, Spaced.peak_withAlloc, Spaced.peak_forList]
  have : (m + 1) * (t.nodes.card + 1) = (m + 1) + (m + 1) * t.nodes.card := by ring
  have : t.nodes.card * (2 * t.nodes.card + 3) =
      t.nodes.card * (2 * t.nodes.card + 2) + t.nodes.card := by ring
  omega

/-- **Section 2.4 with backtracking** (`camusBudgetNetworks`), with its memory. -/
def camusBudgetNetworksS (t : PhyloTree) (Q : Multiset Quartet) (m : ℕ) :
    Spaced (ℕ → List (Address × Address)) := do
  let P ← preprocessS t
  let S ← enumerateS P.1 Q P.2
  let order ← Spaced.build List.length (reverseList P.2)
  let R ← budgetFillS P.1 S.1 S.2 m order
  let N ← Spaced.op (forList (fun c _ => step (c + 1)) P.2 0)
  budgetNetworksS P.1 S.1 S.2 R N m

/-- The program of `camusBudgetNetworksS` is `camusBudgetNetworks`: same result, same running
time. -/
theorem run_camusBudgetNetworksS (t : PhyloTree) (Q : Multiset Quartet) (m : ℕ) :
    (camusBudgetNetworksS t Q m).run = camusBudgetNetworks t Q m := by
  simp only [camusBudgetNetworksS, camusBudgetNetworks, Spaced.run_bind, run_preprocessS,
    run_enumerateS, Spaced.run_build, run_budgetFillS, Spaced.run_op, run_budgetNetworksS]

/-- **Section 2.4 with backtracking: the memory.** A run of `camusBudgetNetworks`, which computes
the matrix with the budget columns `0, …, m` and backtracks the networks `N_k` for every `k ≤ m`,
holds, besides its input, at most `5 |V(T)|² + 3 m |V(T)| + 14 |V(T)| + 4 m + 3` cells at every
step. -/
theorem peak_camusBudgetNetworksS (t : PhyloTree) (Q : Multiset Quartet) (m : ℕ) :
    (camusBudgetNetworksS t Q m).peak ≤ 5 * t.nodes.card ^ 2 + 3 * (m * t.nodes.card) +
      14 * t.nodes.card + 4 * m + 3 := by
  have hT := preprocess_correct t
  have hpre := preprocess_order t
  obtain ⟨hB, -⟩ := enumerate_buckets hT Q
  obtain ⟨hk1, hp1⟩ := preprocessS_memory t
  have hP : (preprocessS t).run.val = (preprocess t).val := by rw [run_preprocessS]
  obtain ⟨hk2, hp2⟩ := enumerateS_memory (preprocessS t).run.val.1 Q (preprocessS t).run.val.2
  rw [hP, hpre, PhyloTree.preorder_length] at hk2 hp2
  obtain ⟨hk4, hp4⟩ := budgetFillS_memory hT (fun v e => (hB v).2 e)
    (enumerate (preprocess t).val.1 Q t.preorder).val.2 m t.preorder.reverse
  rw [List.length_reverse, PhyloTree.preorder_length] at hk4 hp4
  have hp5 := budgetNetworksS_memory hT (fun v e => (hB v).2 e)
    (enumerate (preprocess t).val.1 Q t.preorder).val.2
    (budgetFill (preprocess t).val.1 (enumerate (preprocess t).val.1 Q t.preorder).val.1
      (enumerate (preprocess t).val.1 Q t.preorder).val.2 m t.preorder.reverse).val m
  simp only [camusBudgetNetworksS, Spaced.peak_bind, Spaced.kept_build, Spaced.peak_build,
    Spaced.run_build, run_enumerateS, hP, hpre, val_reverseList, List.length_reverse,
    PhyloTree.preorder_length, Spaced.kept_op, Spaced.peak_op, Spaced.run_op, run_budgetFillS,
    count_eq_length, max_le_iff]
  unfold tableCells at hk1 hp1
  unfold budgetTransient at hp5
  have e1 : (m + 1) * t.nodes.card = m * t.nodes.card + t.nodes.card := by ring
  have e2 : (m + 1) * (t.nodes.card + 1) = m * t.nodes.card + m + t.nodes.card + 1 := by ring
  have e3 : t.nodes.card * (2 * t.nodes.card + 3) = 2 * t.nodes.card ^ 2 + 3 * t.nodes.card := by
    ring
  have e4 : (t.nodes.card + 1) * (m + 1) = m * t.nodes.card + m + t.nodes.card + 1 := by ring
  omega

/-- **Section 2.4 with backtracking: the memory `O(n⁴ + m n)`.** For a well-labelled tree `T` with
`n` leaves and a multiset `Q` whose quartets are on taxa of `T`, the input of `camusBudgetNetworks`
and the cells that a run holds at any step number at most `85 n⁴ + 6 m n + 4 m`; for
`m ≤ n − 1`, the budgets with networks, `O(n⁴)`. The paper does not bound the memory of
Section 2.4. -/
theorem camusBudgetNetworks_memory {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet)
    (hQ : ∀ q ∈ Q.toFinset, q.taxa ⊆ t.taxa) (m : ℕ) :
    inputCells t Q + (camusBudgetNetworksS t Q m).peak ≤
      85 * t.taxa.card ^ 4 + 6 * (m * t.taxa.card) + 4 * m := by
  have h := peak_camusBudgetNetworksS t Q m
  have hq := observedQuartets_bound t Q hQ
  have hnodes := t.nodes_count
  have htaxa : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  have hn := t.labels_nonempty
  unfold inputCells
  rw [htaxa] at hq ⊢
  set n := t.labels.length
  have hN : t.nodes.card ≤ 2 * n := by omega
  have hN2 : t.nodes.card ^ 2 ≤ 4 * n ^ 2 := by
    have := Nat.mul_le_mul hN hN
    nlinarith
  have hmN : m * t.nodes.card ≤ 2 * (m * n) := by
    have := Nat.mul_le_mul_left m hN
    linarith
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hn4 : n ^ 2 ≤ n ^ 4 := by nlinarith
  omega

/-- **Section 2.4 with backtracking**, for the program with its memory. For a well-labelled tree
`T` with `n` leaves, a multiset `Q` with `|Q|` distinct quartets, all on taxa of `T`, the budget
columns `0, …, m` for some `m ≥ 1`, and a solution `A` of the recurrence with the weights of
Equation (1), the program of `camusBudgetNetworksS` returns, for every `k ≤ m` whose row at the
root is nonempty, a backtracking trace from the root with budget `k` (`camusBudgetNetworks_trace`),
whose network is the network `N_k` (`camusBudgetNetworks_networks`); it performs at most
`2100 n² (|Q| + m³ n)` operations (`camusBudgetNetworks_time`); and its input and the cells that it
holds at any step number at most `85 n⁴ + 6 m n + 4 m` (`camusBudgetNetworks_memory`). -/
theorem camusBudgetNetworksS_section24 {t : PhyloTree} (ht : t.WellLabelled)
    (Q : Multiset Quartet) (hQ : ∀ q ∈ Q.toFinset, q.taxa ⊆ t.taxa) {m : ℕ} (hm : 1 ≤ m)
    {A : Address → ℕ → Finset ℕ} (hA : BudgetDP.Array t (edgeWeight t Q) A) :
    (∀ k ≤ m, (A [] k).Nonempty → BudgetDP.Trace t (edgeWeight t Q) A [] k
        ((camusBudgetNetworksS t Q m).run.val k).toFinset) ∧
      (camusBudgetNetworksS t Q m).run.time ≤
        2100 * t.taxa.card ^ 2 * (Q.toFinset.card + m ^ 3 * t.taxa.card) ∧
      inputCells t Q + (camusBudgetNetworksS t Q m).peak ≤
        85 * t.taxa.card ^ 4 + 6 * (m * t.taxa.card) + 4 * m := by
  rw [run_camusBudgetNetworksS]
  exact ⟨fun k hk hrow => camusBudgetNetworks_trace ht Q m hA hk hrow,
    camusBudgetNetworks_time ht Q hm, camusBudgetNetworks_memory ht Q hQ m⟩

end Camus.Complexity
