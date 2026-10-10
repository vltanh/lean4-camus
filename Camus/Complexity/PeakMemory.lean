module

public import Camus.Complexity.Space
public import Camus.Complexity.Memory
public import Camus.Complexity.Backtracking

/-!
# Section 2.3: the peak memory of CAMUS

Section 2.3 of the paper states: "We can represent Q in O(n⁴) space, since we consider integers to
require O(1) memory. All other data structures needed for the algorithm, such as the precomputed
LCAs, etc., can be stored in O(n²); hence the total memory usage is O(n⁴)." This file writes the
program `Complexity.camus` of `Camus/Complexity/Program.lean` with its memory, in the semantics of
`Camus/Complexity/Space.lean` (`Complexity.camusS`, whose program is `camus`:
`Complexity.run_camusS`), and proves both claims for the peak of a run: at every step, the program
holds at most `9 |V(T)| + 3 |V(T)|² ≤ 48 n²` cells besides its input (`Complexity.peak_camusS`,
`Complexity.peak_camusS_le`), and with the input, `T` and the `|Q|` distinct quartets of `Q` with
their multiplicities, at most `68 n⁴` cells (`Complexity.camus_memory`). The same holds with the
backtracking of Section 2.2 (`Complexity.camusNetworkS`, `Complexity.peak_camusNetworkS`):
`11 |V(T)| + 4 |V(T)|²` cells.

What is charged, in cells (`Camus/Complexity/Space.lean`):

* the preprocessing (`Complexity.preprocessS`): the list of the entries of the traversal, one cell
  per vertex, and a frame per call of the traversal; the tables of parents, depths and kinds, of
  the leaves (at most one per vertex) and of the lowest common ancestors, arrays of
  `4 |V(T)| + |V(T)|²` cells (`Complexity.tableCells`), into which the entries are then written in
  place; and the list of the vertices in preorder. The list of entries is released at the end of
  the preprocessing;
* the enumeration (`Complexity.enumerateS`): the heads of the buckets, one per vertex, and the
  weights `s_e`, an array over the pairs of vertices, `|V(T)| + |V(T)|²` cells, and one cell per
  pair put in a bucket;
* the reverse of the preorder, one cell per vertex;
* the fill (`Complexity.fillS`): the array `M`, one cell per vertex, and for each pair of a bucket
  the list of the subtrees hanging off its cycle, released once `s_e + s_dp` is computed;
* the backtracking (`Complexity.backtrackS`): a frame per call, one cell per pair found, and, in a
  call that adds an edge, the list of the subtrees hanging off its cycle, held while the
  backtracking continues there.

The tables are written where the program writes them: `Complexity.preprocess_support`,
`Complexity.enumerate_support` and `Complexity.fill_support` (`Camus/Complexity/Memory.lean`) show
that their entries are at the keys of these arrays.

## Main results

* `Complexity.camusS`: `camus` with its memory; `Complexity.run_camusS`: its program is `camus`.
* `Complexity.peak_camusS`: at most `9 |V(T)| + 3 |V(T)|²` cells at every step.
* `Complexity.peak_camusS_le`: at most `48 n²`, the paper's "O(n²)".
* `Complexity.camus_memory`: with the input, at most `68 n⁴`, the paper's "O(n⁴)".
* `Complexity.camusS_section23`: the array, the running time and the memory of Section 2.3
  together.
* `Complexity.camusNetworkS`, `Complexity.peak_camusNetworkS`: with backtracking, at most
  `11 |V(T)| + 4 |V(T)|²` cells besides the input.

## Proof (the paper's)

The preprocessing tables take `O(n²)` cells (`Complexity.preprocessS_memory`), the buckets and the
weights `O(n²)` (`Complexity.enumerateS_memory`), and the fill `O(n)` (`Complexity.fillS_memory`):
the data structures besides `Q` take `O(n²)` cells (`Complexity.peak_camusS`). The input `Q` has
at most `3 n⁴` distinct quartets (`Complexity.observedQuartets_bound`), so the total is `O(n⁴)`
(`Complexity.camus_memory`). The paper does not discuss the memory of backtracking: each of its at
most `|V(T)|` levels of calls holds a frame, a pair and a list of at most `|V(T)|` hanging
subtrees (`Complexity.backtrackS_memory`).
-/

@[expose] public section

namespace Camus.Complexity

open Timed DynamicProgramming

/-! ### The preprocessing -/

/-- The traversal `visit`, with its memory: one cell per entry it lists, and a frame per call. -/
def visitS : PhyloTree → Address → Address → ℕ → List Entry → Spaced (List Entry)
  | .leaf a, p, par, d, acc =>
      Spaced.frame (Spaced.withAlloc 1 (Spaced.op (step (⟨p, par, d, .leaf a⟩ :: acc))))
  | .fork l r, p, par, d, acc => Spaced.frame (do
      let pl ← Spaced.op (step (p ++ [false]))
      let pr ← Spaced.op (step (p ++ [true]))
      let d' ← Spaced.op (step (d + 1))
      let acc ← visitS r pr p d' acc
      let acc ← visitS l pl p d' acc
      Spaced.withAlloc 1 (Spaced.op (step (⟨p, par, d, .fork pl pr⟩ :: acc))))

/-- The program of `visitS` is `visit`. -/
theorem run_visitS : ∀ (sub : PhyloTree) (p par : Address) (d : ℕ) (acc : List Entry),
    (visitS sub p par d acc).run = visit sub p par d acc
  | .leaf a, p, par, d, acc => rfl
  | .fork l r, p, par, d, acc => by
    simp only [visitS, visit, Spaced.run_frame, Spaced.run_bind, Spaced.run_op,
      Spaced.run_withAlloc, run_visitS l, run_visitS r]

/-- The traversal of a subtree with `N` vertices keeps its `N` entries and holds at most `2 N`
cells: the entries and the frames of the calls along a path. -/
theorem visitS_memory : ∀ (sub : PhyloTree) (p par : Address) (d : ℕ) (acc : List Entry),
    (visitS sub p par d acc).kept = sub.nodes.card ∧
      (visitS sub p par d acc).peak ≤ 2 * sub.nodes.card
  | .leaf a, p, par, d, acc => by simp [visitS, PhyloTree.nodes]
  | .fork l r, p, par, d, acc => by
    have hl := fun p par d acc => visitS_memory l p par d acc
    have hr := fun p par d acc => visitS_memory r p par d acc
    simp only [visitS, Spaced.kept_frame, Spaced.peak_frame, Spaced.kept_bind,
      Spaced.peak_bind, Spaced.kept_op, Spaced.peak_op, Spaced.kept_withAlloc,
      Spaced.peak_withAlloc, Spaced.run_op, PhyloTree.nodes_card_fork]
    obtain ⟨hrk, hrp⟩ := hr (p ++ [true]) p (d + 1) acc
    obtain ⟨hlk, hlp⟩ := hl (p ++ [false]) p (d + 1) (visitS r (p ++ [true]) p (d + 1) acc).run.val
    simp only [val_step] at hrk hrp hlk hlp ⊢
    omega

/-- The cells of the preprocessing tables of a tree with `N` vertices, as arrays: the parent, the
depth and the kind of each vertex, the leaf of each taxon (at most one per vertex), and the lowest
common ancestor of each pair of vertices. -/
def tableCells (N : ℕ) : ℕ := 4 * N + N ^ 2

/-- The preprocessing (`preprocess`), with its memory: the list of entries of the traversal, the
tables, allocated as arrays (`tableCells`) and written in place, and the list of the vertices in
preorder. At its end it keeps the tables and the list. -/
def preprocessS (t : PhyloTree) : Spaced (Tables × List Address) :=
  Spaced.scope (fun P => tableCells P.2.length + P.2.length) (do
    let es ← visitS t [] [] 0 []
    let T ← Spaced.withAlloc (tableCells es.length) (Spaced.op (forList record es Tables.empty))
    let pre ← Spaced.build List.length (mapList (fun x => pure x.addr) es)
    let T ← Spaced.op (lcaTable pre T)
    pure (T, pre))

/-- The program of `preprocessS` is `preprocess`. -/
theorem run_preprocessS (t : PhyloTree) : (preprocessS t).run = preprocess t := by
  simp only [preprocessS, preprocess, Spaced.run_scope, Spaced.run_bind, run_visitS,
    Spaced.run_withAlloc, Spaced.run_op, Spaced.run_build, Spaced.run_pure]

/-- The preprocessing of a tree with `N` vertices keeps the tables and the preorder,
`tableCells N + N` cells, and holds at most `tableCells N + 2 N` cells. -/
theorem preprocessS_memory (t : PhyloTree) :
    (preprocessS t).kept = tableCells t.nodes.card + t.nodes.card ∧
      (preprocessS t).peak ≤ tableCells t.nodes.card + 2 * t.nodes.card := by
  obtain ⟨hk, hp⟩ := visitS_memory t [] [] 0 []
  have hlen : (visit t [] [] 0 []).val.length = t.nodes.card := by
    rw [val_visit_root, List.length_map, PhyloTree.preorder_length]
  simp only [preprocessS, Spaced.kept_scope, Spaced.peak_scope, Spaced.peak_bind,
    Spaced.run_bind, run_visitS, Spaced.kept_withAlloc, Spaced.peak_withAlloc,
    Spaced.run_withAlloc, Spaced.kept_op, Spaced.peak_op, Spaced.run_op, Spaced.kept_build,
    Spaced.peak_build, Spaced.run_build, Spaced.peak_pure, Spaced.run_pure, val_bind, val_pure,
    val_mapList, List.length_map, hlen, true_and]
  omega

/-! ### The enumeration of the candidate pairs -/

/-- One pair of the enumeration (`visitPair`), with its memory: a pair put in a bucket takes one
cell; the bucket heads and the weights are written in place. -/
def visitPairS (T : Tables) (Q : Multiset Quartet) (S : Buckets) (e : Address × Address) :
    Spaced Buckets := do
  let ok ← Spaced.op (admissibleTest T e)
  if ok then do
    let s ← Spaced.op (weightScan T Q e)
    let v ← Spaced.op (step (T.lca e))
    let b ← Spaced.op (step (S.1 v))
    let B ← Spaced.withAlloc 1 (Spaced.op (step (Function.update S.1 v (e :: b))))
    let W ← Spaced.op (step (Function.update S.2 e s))
    pure (B, W)
  else pure S

/-- The program of `visitPairS` is `visitPair`. -/
theorem run_visitPairS (T : Tables) (Q : Multiset Quartet) (S : Buckets) (e : Address × Address) :
    (visitPairS T Q S e).run = visitPair T Q S e := by
  unfold visitPairS visitPair
  simp only [Spaced.run_bind, Spaced.run_op]
  congr 1
  funext ok
  cases ok <;> rfl

/-- A pair of the enumeration keeps at most one cell, and holds no more than it keeps. -/
theorem visitPairS_memory (T : Tables) (Q : Multiset Quartet) (S : Buckets)
    (e : Address × Address) :
    (visitPairS T Q S e).kept ≤ 1 ∧ (visitPairS T Q S e).peak ≤ (visitPairS T Q S e).kept := by
  unfold visitPairS
  cases h : (admissibleTest T e).val <;> simp [h]

/-- The enumeration (`enumerate`), with its memory: the heads of the buckets, one per vertex, and
the weights, an array over the pairs of vertices, allocated first; then one cell per pair put in a
bucket. -/
def enumerateS (T : Tables) (Q : Multiset Quartet) (pre : List Address) : Spaced Buckets :=
  Spaced.withAlloc (pre.length + pre.length ^ 2)
    (Spaced.forList (visitPairS T Q) (pairList pre) (fun _ => [], fun _ => 0))

/-- The program of `enumerateS` is `enumerate`. -/
theorem run_enumerateS (T : Tables) (Q : Multiset Quartet) (pre : List Address) :
    (enumerateS T Q pre).run = enumerate T Q pre := by
  simp only [enumerateS, enumerate, Spaced.run_withAlloc, Spaced.run_forList, run_visitPairS]

/-- There are `N²` pairs of `N` vertices. -/
theorem length_pairList (l : List Address) : (pairList l).length = l.length ^ 2 := by
  simp only [pairList, List.length_flatMap, List.length_map, List.map_const', List.sum_replicate,
    smul_eq_mul]
  ring

/-- The enumeration over `N` vertices keeps and holds at most `N + 2 N²` cells: the bucket heads,
the weights, and at most one cell per pair of vertices. -/
theorem enumerateS_memory (T : Tables) (Q : Multiset Quartet) (pre : List Address) :
    (enumerateS T Q pre).kept ≤ pre.length + 2 * pre.length ^ 2 ∧
      (enumerateS T Q pre).peak ≤ pre.length + 2 * pre.length ^ 2 := by
  have hk := Spaced.loopKept_le (visitPairS T Q) 1 (pairList pre) (fun _ => [], fun _ => 0)
    (fun S e _ => (visitPairS_memory T Q S e).1)
  have hp := Spaced.loopPeak_le_kept_add (visitPairS T Q) 0 (pairList pre)
    (fun _ => [], fun _ => 0) (fun S e _ => (visitPairS_memory T Q S e).2)
  rw [length_pairList] at hk
  simp only [enumerateS, Spaced.kept_withAlloc, Spaced.peak_withAlloc, Spaced.kept_forList,
    Spaced.peak_forList]
  omega

/-! ### The fill of `M` -/

/-- `s_e + s_dp` for one pair (`pairValue`), with its memory: the list of the subtrees hanging off
the cycle, released once the value is computed. -/
def pairValueS (T : Tables) (W : Address × Address → ℕ) (M : Address → ℕ)
    (e : Address × Address) : Spaced ℕ :=
  Spaced.scope (fun _ => 0) (do
    let s ← Spaced.op (step (W e))
    let L ← Spaced.build List.length (hangingList T e)
    let d ← Spaced.op (sumList (fun r => step (M r)) L)
    Spaced.op (step (s + d)))

/-- `s(v)` (`sValue`), with its memory. -/
def sValueS (T : Tables) (B : Address → List (Address × Address)) (W : Address × Address → ℕ)
    (M : Address → ℕ) (v : Address) : Spaced ℕ := do
  let b ← Spaced.op (step (B v))
  Spaced.maxList (pairValueS T W M) b

/-- Equation (2) at the vertex `v` (`solveVertex`), with its memory: `M` is written in place. -/
def solveVertexS (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (M : Address → ℕ) (v : Address) : Spaced (Address → ℕ) := do
  let k ← Spaced.op (step (T.kind v))
  match k with
  | .leaf _ => Spaced.op (step (Function.update M v 0))
  | .fork l r => do
      let a ← Spaced.op (step (M l))
      let b ← Spaced.op (step (M r))
      let sv ← sValueS T B W M v
      let x ← Spaced.op (steps 2 (max (a + b) sv))
      Spaced.op (step (Function.update M v x))

/-- The fill of `M` (`fill`), with its memory: the array `M`, one cell per vertex of `order`,
allocated first. -/
def fillS (T : Tables) (B : Address → List (Address × Address)) (W : Address × Address → ℕ)
    (order : List Address) : Spaced (Address → ℕ) :=
  Spaced.withAlloc order.length (Spaced.forList (solveVertexS T B W) order (fun _ => 0))

/-- The program of `solveVertexS` is `solveVertex`. -/
theorem run_solveVertexS (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (M : Address → ℕ) (v : Address) :
    (solveVertexS T B W M v).run = solveVertex T B W M v := by
  unfold solveVertexS solveVertex
  simp only [Spaced.run_bind, Spaced.run_op]
  congr 1
  funext k
  cases k <;> rfl

/-- The program of `fillS` is `fill`. -/
theorem run_fillS (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (order : List Address) :
    (fillS T B W order).run = fill T B W order := by
  simp only [fillS, fill, Spaced.run_withAlloc, Spaced.run_forList, run_solveVertexS]

/-- With correct tables, a pair of a bucket holds at most `|V(T)|` cells: its hanging subtrees. -/
theorem pairValueS_memory {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {e : Address × Address} (he : EdgeAbove.Admissible t e) (W : Address × Address → ℕ)
    (M : Address → ℕ) :
    (pairValueS T W M e).kept = 0 ∧ (pairValueS T W M e).peak ≤ t.nodes.card := by
  have hL := length_hangingList hT he
  simp only [pairValueS, Spaced.kept_scope, Spaced.peak_scope, Spaced.peak_bind, Spaced.kept_op,
    Spaced.peak_op, Spaced.kept_build, Spaced.peak_build, true_and]
  omega

/-- With correct tables and buckets, solving the subproblem at a vertex keeps nothing and holds at
most `|V(T)|` cells. -/
theorem solveVertexS_memory {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    (W : Address × Address → ℕ) (M : Address → ℕ) (v : Address) :
    (solveVertexS T B W M v).kept = 0 ∧ (solveVertexS T B W M v).peak ≤ t.nodes.card := by
  have hs : (sValueS T B W M v).kept = 0 ∧ (sValueS T B W M v).peak ≤ t.nodes.card := by
    have hpair : ∀ e ∈ B v, (pairValueS T W M e).kept = 0 ∧
        (pairValueS T W M e).peak ≤ t.nodes.card := fun e he =>
      pairValueS_memory hT (Finset.mem_filter.mp (Finset.mem_filter.mp ((hB v e).mp he)).1).2 W M
    have hk : Spaced.loopKept (fun acc a => do
        let x ← pairValueS T W M a
        Spaced.op (step (max acc x))) (B v) 0 = 0 := by
      have := Spaced.loopKept_le (fun acc a => do
        let x ← pairValueS T W M a
        Spaced.op (step (max acc x))) 0 (B v) 0 (fun acc e he => by
          simp [(hpair e he).1])
      omega
    have hp := Spaced.loopPeak_le (fun acc a => do
        let x ← pairValueS T W M a
        Spaced.op (step (max acc x))) t.nodes.card (B v) 0
      (fun acc e he => by simp [(hpair e he).1])
      (fun acc e he => by simp [(hpair e he).1, (hpair e he).2])
    simp only [sValueS, Spaced.maxList, Spaced.kept_bind, Spaced.peak_bind, Spaced.kept_op,
      Spaced.peak_op, Spaced.kept_forList, Spaced.peak_forList, Spaced.run_op, val_step]
    omega
  unfold solveVertexS
  cases T.kind v with
  | leaf a => simp
  | fork l r =>
    simp only [Spaced.kept_bind, Spaced.peak_bind, Spaced.kept_op, Spaced.peak_op, Spaced.run_op,
      val_step]
    have := hs.1
    have := hs.2
    omega

/-- With correct tables and buckets, the fill over the `N` vertices of `T` keeps the array `M`,
`N` cells, and holds at most `2 N` cells. -/
theorem fillS_memory {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    (W : Address × Address → ℕ) (order : List Address) :
    (fillS T B W order).kept = order.length ∧
      (fillS T B W order).peak ≤ order.length + t.nodes.card := by
  have hk := Spaced.loopKept_le (solveVertexS T B W) 0 order (fun _ => 0)
    (fun M v _ => by rw [(solveVertexS_memory hT hB W M v).1])
  have hp := Spaced.loopPeak_le (solveVertexS T B W) t.nodes.card order (fun _ => 0)
    (fun M v _ => (solveVertexS_memory hT hB W M v).1)
    (fun M v _ => (solveVertexS_memory hT hB W M v).2)
  simp only [fillS, Spaced.kept_withAlloc, Spaced.peak_withAlloc, Spaced.kept_forList,
    Spaced.peak_forList]
  simp only [Nat.mul_zero, Nat.le_zero] at hk
  omega

/-! ### CAMUS -/

/-- **CAMUS** (`camus`), with its memory: the preprocessing, the enumeration of the candidate
pairs with their weights, the reverse of the preorder, and the fill of `M`. -/
def camusS (t : PhyloTree) (Q : Multiset Quartet) : Spaced (Address → ℕ) := do
  let P ← preprocessS t
  let S ← enumerateS P.1 Q P.2
  let order ← Spaced.build List.length (reverseList P.2)
  fillS P.1 S.1 S.2 order

/-- The program of `camusS` is `camus`: same result, same running time. -/
theorem run_camusS (t : PhyloTree) (Q : Multiset Quartet) : (camusS t Q).run = camus t Q := by
  simp only [camusS, camus, Spaced.run_bind, run_preprocessS, run_enumerateS, Spaced.run_build,
    run_fillS]

/-- **Section 2.3: the data structures take `O(n²)` cells.** A run of `camus` on a tree `T` holds,
besides its input, at most `9 |V(T)| + 3 |V(T)|²` cells at every step. -/
theorem peak_camusS (t : PhyloTree) (Q : Multiset Quartet) :
    (camusS t Q).peak ≤ 9 * t.nodes.card + 3 * t.nodes.card ^ 2 := by
  have hT := preprocess_correct t
  have hpre := preprocess_order t
  obtain ⟨hB, -⟩ := enumerate_buckets hT Q
  -- the preprocessing tables: `O(n²)` cells
  obtain ⟨hk1, hp1⟩ := preprocessS_memory t
  have hP : (preprocessS t).run.val = (preprocess t).val := by rw [run_preprocessS]
  -- the buckets and the weights: `O(n²)` cells
  obtain ⟨hk2, hp2⟩ := enumerateS_memory (preprocessS t).run.val.1 Q (preprocessS t).run.val.2
  rw [hP, hpre, PhyloTree.preorder_length] at hk2 hp2
  -- the array `M` and the hanging subtrees of one pair: `O(n)` cells
  obtain ⟨hk4, hp4⟩ := fillS_memory hT (fun v e => (hB v).2 e)
    (enumerate (preprocess t).val.1 Q t.preorder).val.2 t.preorder.reverse
  rw [List.length_reverse, PhyloTree.preorder_length] at hk4 hp4
  simp only [camusS, Spaced.peak_bind, Spaced.kept_build, Spaced.peak_build, Spaced.run_build,
    run_enumerateS, hP, hpre, val_reverseList, List.length_reverse, PhyloTree.preorder_length]
  unfold tableCells at hk1 hp1
  omega

/-- **Section 2.3: the data structures take `O(n²)` cells.** For a well-labelled tree `T` with `n`
leaves, a run of `camus` holds, besides its input, at most `48 n²` cells at every step: "All other
data structures needed for the algorithm, such as the precomputed LCAs, etc., can be stored in
O(n²)". -/
theorem peak_camusS_le {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet) :
    (camusS t Q).peak ≤ 48 * t.taxa.card ^ 2 := by
  have h := peak_camusS t Q
  have hnodes := t.nodes_count
  have htaxa : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  have hn := t.labels_nonempty
  rw [htaxa]
  have hN : t.nodes.card ≤ 2 * t.labels.length := by omega
  have hN2 : t.nodes.card ^ 2 ≤ 4 * t.labels.length ^ 2 := by
    have := Nat.mul_le_mul hN hN
    nlinarith
  have hn2 : t.labels.length ≤ t.labels.length ^ 2 := by nlinarith
  omega

/-- The cells of the input: one per vertex of `T`, and six per distinct quartet of `Q` (its four
taxa, its split and its multiplicity, `Q` being read as a weighted set as Section 2.3 allows). -/
noncomputable def inputCells (t : PhyloTree) (Q : Multiset Quartet) : ℕ :=
  t.nodes.card + 6 * Q.toFinset.card

/-- **Section 2.3: the memory `O(n⁴)`.** For a well-labelled tree `T` with `n` leaves and a
multiset `Q` whose quartets are on taxa of `T`, the input of `camus` and the cells that a run
holds at any step number at most `68 n⁴`: "We can represent Q in O(n⁴) space ... hence the total
memory usage is O(n⁴)". -/
theorem camus_memory {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet)
    (hQ : ∀ q ∈ Q.toFinset, q.taxa ⊆ t.taxa) :
    inputCells t Q + (camusS t Q).peak ≤ 68 * t.taxa.card ^ 4 := by
  -- the data structures: `O(n²)` cells
  have h := peak_camusS_le ht Q
  -- `Q`: at most `3 n⁴` distinct quartets, six cells each
  have hq := observedQuartets_bound t Q hQ
  have hnodes := t.nodes_count
  have htaxa : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  have hn := t.labels_nonempty
  unfold inputCells
  rw [htaxa] at h hq ⊢
  have hN : t.nodes.card ≤ 2 * t.labels.length := by omega
  have hn2 : t.labels.length ≤ t.labels.length ^ 2 := by nlinarith
  have hn4 : t.labels.length ^ 2 ≤ t.labels.length ^ 4 := by nlinarith
  omega

/-- **Section 2.3**, for the program with its memory. For a well-labelled tree `T` with `n` leaves
and a multiset `Q` with `|Q|` distinct quartets, all on taxa of `T`, the program of `camusS`
computes the array of Section 2.2 (`camus_array`), in at most `600 n² (|Q| + n)` operations
(`camus_time`), and its input and the cells that it holds at any step number at most `68 n⁴`
(`camus_memory`). -/
theorem camusS_section23 {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet)
    (hQ : ∀ q ∈ Q.toFinset, q.taxa ⊆ t.taxa) :
    DynamicProgramming.Array t (edgeWeight t Q) (camusS t Q).run.val ∧
      (camusS t Q).run.time ≤ 600 * t.taxa.card ^ 2 * (Q.toFinset.card + t.taxa.card) ∧
      inputCells t Q + (camusS t Q).peak ≤ 68 * t.taxa.card ^ 4 := by
  rw [run_camusS]
  exact ⟨camus_array ht Q, camus_time ht Q, camus_memory ht Q hQ⟩

/-! ### Backtracking (Section 2.2) -/

/-- The search of the bucket for a pair (`findPair`), with its memory: the value of each pair
examined is computed in its own scope (`pairValueS`). -/
def findPairS (T : Tables) (W : Address × Address → ℕ) (M : Address → ℕ) (target : ℕ) :
    List (Address × Address) → Spaced (Option (Address × Address))
  | [] => pure none
  | e :: es => do
      Spaced.op tick
      let x ← pairValueS T W M e
      let ok ← Spaced.op (step (decide (x = target)))
      if ok then pure (some e) else findPairS T W M target es

/-- The program of `findPairS` is `findPair`. -/
theorem run_findPairS (T : Tables) (W : Address × Address → ℕ) (M : Address → ℕ)
    (target : ℕ) : ∀ (l : List (Address × Address)),
      (findPairS T W M target l).run = findPair T W M target l
  | [] => rfl
  | e :: es => by
    simp only [findPairS, findPair, Spaced.run_bind, Spaced.run_op, Spaced.run_ite,
      Spaced.run_pure, run_findPairS T W M target es]
    rfl

/-- With correct tables, the search of a bucket of admissible pairs keeps nothing and holds at
most `|V(T)|` cells. -/
theorem findPairS_memory {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    (W : Address × Address → ℕ) (M : Address → ℕ) (target : ℕ) :
    ∀ (l : List (Address × Address)), (∀ e ∈ l, EdgeAbove.Admissible t e) →
      (findPairS T W M target l).kept = 0 ∧ (findPairS T W M target l).peak ≤ t.nodes.card
  | [], _ => by simp [findPairS]
  | e :: es, h => by
    obtain ⟨hk, hp⟩ := pairValueS_memory hT (h e (by simp)) W M
    obtain ⟨hk', hp'⟩ := findPairS_memory hT W M target es (fun f hf => h f (by simp [hf]))
    simp only [findPairS, Spaced.kept_bind, Spaced.peak_bind, Spaced.kept_op, Spaced.peak_op,
      Spaced.kept_ite, Spaced.peak_ite, Spaced.kept_pure, Spaced.peak_pure, hk', hk]
    split_ifs <;> omega

/-- Backtracking (`backtrack`, Section 2.2), with its memory: each call holds its frame, and the
call at a vertex where an edge is added holds the list of the subtrees hanging off its cycle while
it continues there; the pairs found are kept, one cell each, and the rest is released at the end
of the call. -/
def backtrackS (T : Tables) (B : Address → List (Address × Address)) (W : Address × Address → ℕ)
    (M : Address → ℕ) : ℕ → Address → List (Address × Address) →
      Spaced (List (Address × Address))
  | 0, _, acc => pure acc
  | n + 1, v, acc => Spaced.frame (Spaced.scope (fun res => res.length - acc.length) (do
      let k ← Spaced.op (step (T.kind v))
      match k with
      | .leaf _ => pure acc
      | .fork l r => do
          let a ← Spaced.op (step (M l))
          let b ← Spaced.op (step (M r))
          let mv ← Spaced.op (step (M v))
          let split ← Spaced.op (steps 2 (decide (a + b = mv)))
          if split then do
            let acc ← backtrackS T B W M n l acc
            backtrackS T B W M n r acc
          else do
            let bucket ← Spaced.op (step (B v))
            let found ← findPairS T W M mv bucket
            match found with
            | none => pure acc
            | some e => do
                let L ← Spaced.build List.length (hangingList T e)
                Spaced.withAlloc 1
                  (Spaced.forList (fun acc r => backtrackS T B W M n r acc) L (e :: acc))))

/-- The program of `backtrackS` is `backtrack`. -/
theorem run_backtrackS (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (M : Address → ℕ) :
    ∀ (n : ℕ) (v : Address) (acc : List (Address × Address)),
      (backtrackS T B W M n v acc).run = backtrack T B W M n v acc := by
  intro n
  induction n with
  | zero => intro v acc; rfl
  | succ n ih =>
    intro v acc
    have hfun : (fun acc r => (backtrackS T B W M n r acc).run) =
        fun acc r => backtrack T B W M n r acc := by
      funext acc r
      exact ih r acc
    simp only [backtrackS, backtrack, Spaced.run_frame, Spaced.run_scope, Spaced.run_bind,
      Spaced.run_op]
    congr 1
    funext k
    cases k with
    | leaf a => rfl
    | fork l r =>
      simp only [Spaced.run_bind, Spaced.run_op, Spaced.run_ite, ih, run_findPairS]
      congr 1; funext a; congr 1; funext b; congr 1; funext mv; congr 1; funext split
      split_ifs
      · rfl
      · congr 1; funext bucket; congr 1; funext found
        cases found with
        | none => rfl
        | some e =>
          simp only [Spaced.run_bind, Spaced.run_build, Spaced.run_withAlloc, Spaced.run_forList,
            hfun]

/-- The length of a list grown by prepending in a loop. -/
theorem length_foldl_prepend {α β : Type} (f : α → List β) (L : List α) (a : List β) :
    (L.foldl (fun acc r => f r ++ acc) a).length =
      a.length + (L.map fun r => (f r).length).sum := by
  induction L generalizing a with
  | nil => simp
  | cons r L ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.map_cons, List.sum_cons]
    omega

/-- With correct tables and buckets, the backtracking from `v` finds at most one pair per vertex
of `T_v`. -/
theorem length_backtrack {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    (W : Address × Address → ℕ) (M : Address → ℕ) :
    ∀ (n : ℕ) (v : Address), v ∈ t.nodes →
      (backtrack T B W M n v []).val.length ≤ (cone t v).card := by
  intro n
  induction n with
  | zero => intro v _; simp [backtrack]
  | succ n ih =>
    intro v hv
    have hvc : v ∈ cone t v := mem_cone.mpr ⟨hv, List.prefix_refl v⟩
    have hcard := Finset.card_erase_add_one hvc
    obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff v).mp hv
    have hk := hT.kind v hv
    cases sub with
    | leaf a =>
      have hk' : T.kind v = .leaf a := by rw [hk]; simp [kindAt, hsub]
      simp [backtrack, hk']
    | fork l r =>
      have hk' : T.kind v = .fork (v ++ [false]) (v ++ [true]) := by
        rw [hk]; simp [kindAt, hsub]
      have hl := PhyloTree.child_mem_nodes hsub false
      have hr := PhyloTree.child_mem_nodes hsub true
      by_cases hs : M (v ++ [false]) + M (v ++ [true]) = M v
      · -- the two children: disjoint subtrees below `v`
        obtain ⟨hdisj, hsubset⟩ := cone_children (t := t) (v := v)
        have hc := Finset.card_le_card hsubset
        rw [Finset.card_union_of_disjoint hdisj] at hc
        have h1 := ih _ hl
        have h2 := ih _ hr
        simp only [backtrack, val_bind, val_step, hk', val_steps, hs, decide_true, ↓reduceIte]
        rw [backtrack_acc, List.length_append]
        omega
      · cases hf : (findPair T W M (M v) (B v)).val with
        | none => simp [backtrack, hk', hs, hf]
        | some e =>
          -- one pair, and the subtrees hanging off its cycle: disjoint, below `v`
          obtain ⟨heB, -⟩ := findPair_sound T W M (M v) (B v) e hf
          have he := (hB v e).mp heB
          obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp he
          have hae := (Finset.mem_filter.mp hc).2
          obtain ⟨hnd, hmem⟩ := hangingList_spec hT hae
          obtain ⟨hpd, hsub'⟩ := cone_hanging hae
          rw [htarget] at hsub'
          have hfun : (fun (acc : List (Address × Address)) r =>
              (backtrack T B W M n r acc).val) =
              fun acc r => (backtrack T B W M n r []).val ++ acc := by
            funext acc r
            exact backtrack_acc T B W M n r acc
          simp only [backtrack, val_bind, val_step, hk', val_steps, hs, decide_false,
            Bool.false_eq_true, ↓reduceIte, hf, val_forList, hfun]
          rw [length_foldl_prepend]
          have hsum : ((hangingList T e).val.map
              fun r => (backtrack T B W M n r []).val.length).sum ≤
                ((cone t v).erase v).card := by
            calc
              _ ≤ ((hangingList T e).val.map fun r => (cone t r).card).sum :=
                List.sum_le_sum fun r hr =>
                  ih r (Finset.mem_filter.mp ((hmem r).mp hr)).1
              _ = ∑ r ∈ hanging t e, (cone t r).card := by
                rw [← List.sum_toFinset _ hnd]
                congr 1
                ext r
                simp [hmem]
              _ = ((hanging t e).biUnion (cone t)).card := (Finset.card_biUnion hpd).symm
              _ ≤ _ := Finset.card_le_card hsub'
          simp only [List.length_singleton]
          omega

/-- With correct tables and buckets, the backtracking from `v` with fuel `n` keeps at most one cell
per vertex of `T_v`, the pairs it finds, and holds at most `|T_v| + n (|V(T)| + 2)` cells: at each
of at most `n` levels of calls, a frame, a pair and the list of the subtrees hanging off a cycle. -/
theorem backtrackS_memory {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    (W : Address × Address → ℕ) (M : Address → ℕ) :
    ∀ (n : ℕ) (v : Address) (acc : List (Address × Address)), v ∈ t.nodes →
      (backtrackS T B W M n v acc).kept ≤ (cone t v).card ∧
        (backtrackS T B W M n v acc).peak ≤ (cone t v).card + n * (t.nodes.card + 2) := by
  intro n
  induction n with
  | zero => intro v acc _; simp [backtrackS]
  | succ n ih =>
    intro v acc hv
    set N := t.nodes.card with hN
    have hvc : v ∈ cone t v := mem_cone.mpr ⟨hv, List.prefix_refl v⟩
    have hcard := Finset.card_erase_add_one hvc
    -- the pairs kept: those found
    have hkept : (backtrackS T B W M (n + 1) v acc).kept ≤ (cone t v).card := by
      have := length_backtrack hT hB W M (n + 1) v hv
      have hkeq : (backtrackS T B W M (n + 1) v acc).kept =
          (backtrackS T B W M (n + 1) v acc).run.val.length - acc.length := rfl
      rw [hkeq, run_backtrackS, backtrack_acc, List.length_append]
      omega
    refine ⟨hkept, ?_⟩
    have hkept' := hkept
    simp only [backtrackS, Spaced.kept_frame, Spaced.kept_scope] at hkept'
    simp only [backtrackS, Spaced.peak_frame, Spaced.peak_scope]
    suffices hin : (do
        let k ← Spaced.op (step (T.kind v))
        match k with
        | .leaf _ => pure acc
        | .fork l r => do
            let a ← Spaced.op (step (M l))
            let b ← Spaced.op (step (M r))
            let mv ← Spaced.op (step (M v))
            let split ← Spaced.op (steps 2 (decide (a + b = mv)))
            if split then do
              let acc ← backtrackS T B W M n l acc
              backtrackS T B W M n r acc
            else do
              let bucket ← Spaced.op (step (B v))
              let found ← findPairS T W M mv bucket
              match found with
              | none => pure acc
              | some e => do
                  let L ← Spaced.build List.length (hangingList T e)
                  Spaced.withAlloc 1 (Spaced.forList (fun acc r => backtrackS T B W M n r acc)
                    L (e :: acc)) : Spaced (List (Address × Address))).peak ≤
          (cone t v).card + N + n * (N + 2) by
      have : n * (N + 2) + (N + 2) = (n + 1) * (N + 2) := by ring
      omega
    obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff v).mp hv
    have hk := hT.kind v hv
    cases sub with
    | leaf a =>
      have hk' : T.kind v = .leaf a := by rw [hk]; simp [kindAt, hsub]
      simp [hk']
    | fork l r =>
      have hk' : T.kind v = .fork (v ++ [false]) (v ++ [true]) := by
        rw [hk]; simp [kindAt, hsub]
      have hl := PhyloTree.child_mem_nodes hsub false
      have hr := PhyloTree.child_mem_nodes hsub true
      simp only [Spaced.peak_bind, Spaced.kept_op, Spaced.peak_op, Spaced.run_op, val_step,
        val_steps, hk', Nat.zero_add]
      by_cases hs : M (v ++ [false]) + M (v ++ [true]) = M v
      · -- the two children
        obtain ⟨hdisj, hsubset⟩ := cone_children (t := t) (v := v)
        have hc := Finset.card_le_card hsubset
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hvc] at hc
        obtain ⟨h1k, h1p⟩ := ih (v ++ [false]) acc hl
        obtain ⟨h2k, h2p⟩ := ih (v ++ [true])
          (backtrackS T B W M n (v ++ [false]) acc).run.val hr
        simp only [hs, decide_true, ↓reduceIte, Spaced.peak_bind]
        omega
      · simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte, Spaced.peak_bind,
          Spaced.kept_op, Spaced.peak_op, Spaced.run_op, val_step, Nat.zero_add]
        have hadm : ∀ e ∈ B v, EdgeAbove.Admissible t e := fun e he =>
          (Finset.mem_filter.mp (Finset.mem_filter.mp ((hB v e).mp he)).1).2
        obtain ⟨hfk, hfp⟩ := findPairS_memory hT W M (M v) (B v) hadm
        rw [hfk, Nat.zero_add]
        cases hf : (findPairS T W M (M v) (B v)).run.val with
        | none =>
          simp only [Spaced.peak_pure]
          omega
        | some e =>
          rw [run_findPairS] at hf
          obtain ⟨heB, -⟩ := findPair_sound T W M (M v) (B v) e hf
          have he := (hB v e).mp heB
          obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp he
          have hae := (Finset.mem_filter.mp hc).2
          obtain ⟨hnd, hmem⟩ := hangingList_spec hT hae
          obtain ⟨hpd, hsub'⟩ := cone_hanging hae
          rw [htarget] at hsub'
          have hL := length_hangingList hT hae
          -- the recursive calls at the hanging subtrees
          have hloop := Spaced.loopPeak_le_sum (fun acc r => backtrackS T B W M n r acc)
            (fun r => (cone t r).card) (n * (N + 2)) (hangingList T e).val (e :: acc)
            (fun acc' r hr => ih r acc' (Finset.mem_filter.mp ((hmem r).mp hr)).1)
          have hsum : ((hangingList T e).val.map fun r => (cone t r).card).sum ≤
              ((cone t v).erase v).card := by
            calc
              _ = ∑ r ∈ hanging t e, (cone t r).card := by
                rw [← List.sum_toFinset _ hnd]
                congr 1
                ext r
                simp [hmem]
              _ = ((hanging t e).biUnion (cone t)).card := (Finset.card_biUnion hpd).symm
              _ ≤ _ := Finset.card_le_card hsub'
          rw [Finset.card_erase_of_mem hvc] at hsum
          simp only [Spaced.peak_bind, Spaced.kept_build, Spaced.peak_build, Spaced.run_build,
            Spaced.peak_withAlloc, Spaced.peak_forList]
          omega

/-- **CAMUS with backtracking** (`camusNetwork`), with its memory. -/
def camusNetworkS (t : PhyloTree) (Q : Multiset Quartet) : Spaced (List (Address × Address)) := do
  let P ← preprocessS t
  let S ← enumerateS P.1 Q P.2
  let order ← Spaced.build List.length (reverseList P.2)
  let M ← fillS P.1 S.1 S.2 order
  let N ← Spaced.op (forList (fun c _ => step (c + 1)) P.2 0)
  backtrackS P.1 S.1 S.2 M N [] []

/-- The program of `camusNetworkS` is `camusNetwork`: same result, same running time. -/
theorem run_camusNetworkS (t : PhyloTree) (Q : Multiset Quartet) :
    (camusNetworkS t Q).run = camusNetwork t Q := by
  simp only [camusNetworkS, camusNetwork, Spaced.run_bind, run_preprocessS, run_enumerateS,
    Spaced.run_build, run_fillS, Spaced.run_op, run_backtrackS]

/-- **Section 2.2 and 2.3: the memory of backtracking.** A run of `camusNetwork`, which computes
the array and backtracks the network, holds, besides its input, at most `11 |V(T)| + 4 |V(T)|²`
cells at every step: the backtracking adds at most `|V(T)|² + 3 |V(T)|` cells to the
`8 |V(T)| + 3 |V(T)|²` that the tables keep. -/
theorem peak_camusNetworkS (t : PhyloTree) (Q : Multiset Quartet) :
    (camusNetworkS t Q).peak ≤ 11 * t.nodes.card + 4 * t.nodes.card ^ 2 := by
  have hT := preprocess_correct t
  have hpre := preprocess_order t
  obtain ⟨hB, -⟩ := enumerate_buckets hT Q
  obtain ⟨hk1, hp1⟩ := preprocessS_memory t
  have hP : (preprocessS t).run.val = (preprocess t).val := by rw [run_preprocessS]
  obtain ⟨hk2, hp2⟩ := enumerateS_memory (preprocessS t).run.val.1 Q (preprocessS t).run.val.2
  rw [hP, hpre, PhyloTree.preorder_length] at hk2 hp2
  obtain ⟨hk4, hp4⟩ := fillS_memory hT (fun v e => (hB v).2 e)
    (enumerate (preprocess t).val.1 Q t.preorder).val.2 t.preorder.reverse
  rw [List.length_reverse, PhyloTree.preorder_length] at hk4 hp4
  obtain ⟨-, hp5⟩ := backtrackS_memory hT (fun v e => (hB v).2 e)
    (enumerate (preprocess t).val.1 Q t.preorder).val.2
    (fill (preprocess t).val.1 (enumerate (preprocess t).val.1 Q t.preorder).val.1
      (enumerate (preprocess t).val.1 Q t.preorder).val.2 t.preorder.reverse).val
    t.nodes.card [] [] (PhyloTree.root_mem_nodes t)
  have hcone : (cone t []).card = t.nodes.card := by
    congr 1
    ext x
    simp [mem_cone]
  rw [hcone] at hp5
  simp only [camusNetworkS, Spaced.peak_bind, Spaced.kept_build, Spaced.peak_build,
    Spaced.run_build, run_enumerateS, hP, hpre, val_reverseList, List.length_reverse,
    PhyloTree.preorder_length, Spaced.kept_op, Spaced.peak_op, Spaced.run_op, run_fillS,
    count_eq_length]
  unfold tableCells at hk1 hp1
  have : t.nodes.card * (t.nodes.card + 2) = t.nodes.card ^ 2 + 2 * t.nodes.card := by ring
  omega

end Camus.Complexity
