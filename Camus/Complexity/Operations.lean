module

public import Camus.Network.Reticulations
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.Prod

/-!
# Section 2.3: operation and storage counts

Section 2.3 of the paper bounds the running time of CAMUS by `O(n²(|Q| + n))` and its memory by
`O(n⁴)`, where `n` is the number of leaves of `T`, `|Q|` is the number of distinct quartet
topologies of `Q` (each stored once, with its multiplicity as weight) and an integer takes `O(1)`
memory. Section 2.4 gives `O(n²(|Q| + m³n))` for the version that computes networks with
`1, …, m` reticulations.

The formalization does not model an implementation. It defines explicit counts, under unit cost:
sums of the sizes of the tables and loops that the paper's analysis lists, and bounds them with
explicit constants. This is an accounting of the paper's analysis, not a cost semantics of a
program. `scalarOperations` counts the preprocessing tables (all-pairs LCA, the leaves below each
vertex, depths), the array `M`, one quartet test per candidate pair `(u, w)` and distinct quartet
(`δ_T(q, (u, w))` of Definition 4, an abstract oracle `DeltaOracle`), one read of `M[r]` per subtree
`r` hanging off each cycle `γ(u, w)` (Equations (4) and (5)) and one comparison per candidate pair
(Equation (3)). Each pair is a candidate at exactly one target (`candidate_visits`): this is the
paper's remark that "no edge is ever considered in the s(·) function more than once over all
subproblems". `budgetOperations` adds the budget loops of Section 2.4, and `scalarSpace` counts the
stored integers.

## Main results

* `Complexity.scalarOperations_bound`: `scalarOperations ≤ 32 n² (|Q| + n)`.
* `Complexity.budgetOperations_bound`: `budgetOperations ≤ 100 n² (|Q| + m³ n)` for `m ≥ 1`.
* `Complexity.scalarSpace_bound`: `scalarSpace ≤ 32 n⁴` when every quartet of `Q` uses taxa of `T`.
* `Complexity.candidate_visits`: each candidate pair is examined at exactly one target.

The oracle scan is related to Equation (1) in `Camus/Complexity/Oracle.lean`.
-/

@[expose] public section

namespace Camus

namespace PhyloTree

/-- The vertices of `(l, r)` are its root and the vertices of `l` and of `r`. -/
theorem nodes_card_fork (l r : PhyloTree) :
    (PhyloTree.fork l r).nodes.card = l.nodes.card + r.nodes.card + 1 := by
  classical
  have hdis : Disjoint (l.nodes.image (false :: ·)) (r.nodes.image (true :: ·)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨x,hx,hxp⟩ := Finset.mem_image.mp hp
    obtain ⟨y,hy,hyp⟩ := Finset.mem_image.mp hq
    exact Bool.false_ne_true (List.cons.inj (hxp.trans hyp.symm)).1
  have hn : [] ∉ l.nodes.image (false :: ·) ∪ r.nodes.image (true :: ·) := by simp
  simp only [nodes,Finset.card_insert_of_notMem hn,Finset.card_union_of_disjoint hdis]
  rw [Finset.card_image_of_injective _ (fun p q h => (List.cons.inj h).2),
    Finset.card_image_of_injective _ (fun p q h => (List.cons.inj h).2)]

/-- A rooted binary tree with `n` leaves has `2n − 1` vertices. -/
theorem nodes_count (t : PhyloTree) : t.nodes.card + 1 = 2 * t.labels.length := by
  induction t with
  | leaf a => simp [nodes,labels]
  | fork l r ihl ihr =>
    rw [nodes_card_fork]
    simp only [labels,List.length_append]
    omega

end PhyloTree

namespace Complexity

open DynamicProgramming

/-- Section 2.3: the quartet test, as an abstract oracle. For a candidate pair `e = (u, w)` and a
distinct quartet `q` of `Q`, `test e q` says whether `q` is satisfied by the edge added above
`(u, w)`: displayed by `T + e` and not by `T` (Definition 4). The paper evaluates this in `O(1)`
time after preprocessing LCAs, leaf sets and depths; here only the answers are specified
(`correct`), and each query counts as one operation in `scalarOperations`. -/
structure DeltaOracle (t : PhyloTree) (Q : Multiset Quartet) where
  test : Pair → Quartet → Bool
  correct : ∀ e ∈ EdgeAbove.candidates t, ∀ q ∈ Q.toFinset,
    test e q = true ↔ q ∈ novel t Q (Realization.graph t {e})

/-- The weight `s_e(u, w)` of Equation (1) computed with the oracle: one scan of the distinct
quartets of `Q`, adding the multiplicity of each quartet that the test accepts. `Q` is given as a
weighted set, as in Section 2.3. -/
noncomputable def oracleWeight {t : PhyloTree} {Q : Multiset Quartet}
    (D : DeltaOracle t Q) (e : Pair) : ℕ :=
  ∑ q ∈ Q.toFinset, if D.test e q = true then Q.count q else 0

/-- The oracle scan computes Equation (1): `oracleWeight D e = edgeWeight t Q e` for every
candidate pair `e`. -/
theorem oracleWeight_eq {t : PhyloTree} {Q : Multiset Quartet}
    (D : DeltaOracle t Q) {e : Pair} (he : e ∈ EdgeAbove.candidates t) :
    oracleWeight D e = edgeWeight t Q e := by
  unfold oracleWeight edgeWeight
  apply Finset.sum_congr rfl
  intro q hq
  simp only [D.correct e he q hq]

/-- Section 2.3: summing `|Pairs(v)|` over the vertices `v` of `T` counts every candidate pair once,
since a pair `(u, w)` has the single target `lca(u, w)`. This is the paper's remark that no edge is
considered in `s(·)` more than once over all subproblems. -/
theorem candidate_visits (t : PhyloTree) :
    ∑ v ∈ t.nodes, (pairsAt t v).card = (EdgeAbove.candidates t).card := by
  classical
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro e he
  exact EdgeAbove.target_mem_nodes (Finset.mem_filter.mp he).2

/-- There are at most `|V(T)|²` candidate pairs. -/
theorem candidates_bound (t : PhyloTree) :
    (EdgeAbove.candidates t).card ≤ t.nodes.card ^ 2 := by
  unfold EdgeAbove.candidates
  calc
    _ ≤ (t.nodes ×ˢ t.nodes).card := Finset.card_filter_le _ _
    _ = _ := by simp [pow_two]

/-- At most `|V(T)|` subtrees hang off a cycle `γ(u, w)`. -/
theorem hanging_bound (t : PhyloTree) (e : Pair) :
    (hanging t e).card ≤ t.nodes.card := Finset.card_filter_le _ _

/-- The number of reads of `M` when Equations (4) and (5) are evaluated at every candidate pair
`(u, w)`: one per subtree hanging off the cycle `γ(u, w)`, since both equations sum `M` over these
subtrees (`DynamicProgramming.hanging_score`). -/
noncomputable def hangingReads (t : PhyloTree) : ℕ :=
  ∑ e ∈ EdgeAbove.candidates t, (hanging t e).card

/-- `hangingReads t ≤ |candidates| · |V(T)|`. -/
theorem hangingReads_bound (t : PhyloTree) :
    hangingReads t ≤ (EdgeAbove.candidates t).card * t.nodes.card := by
  unfold hangingReads
  calc
    _ ≤ ∑ _e ∈ EdgeAbove.candidates t, t.nodes.card :=
      Finset.sum_le_sum (fun e _ => hanging_bound t e)
    _ = _ := by simp

/-- Section 2.3: the operations counted for CAMUS, one unit each: the all-pairs LCA table
(`|V(T)|²` entries), the table of leaves below each vertex (`|V(T)| · n` entries), the depth array
and the array `M` (`|V(T)|` entries each), one quartet test per candidate pair and distinct quartet
of `Q`, one read of `M` per subtree hanging off the cycle of each candidate pair (`hangingReads`),
and one comparison per candidate pair in the maximum of Equation (3). Each counted operation stands
for a constant amount of work. -/
noncomputable def scalarOperations (t : PhyloTree) (Q : Multiset Quartet) : ℕ :=
  (t.nodes ×ˢ t.nodes).card + (t.nodes ×ˢ t.taxa).card + 2 * t.nodes.card +
    (EdgeAbove.candidates t ×ˢ Q.toFinset).card + hangingReads t +
    (EdgeAbove.candidates t).card

/-- Section 2.4: the operations counted for the version restricted to `m` budget columns, one unit
each: the preprocessing and quartet tests of `scalarOperations`; for every hanging-subtree read of
`hangingReads`, every budget column `k` and every pair `(i, j)` of partial budgets with
`i, j ≤ m`, one lookup (the knapsack over the hanging subtrees, `BudgetDP.forest`); for every
vertex, budget column and pair `(i, j)`, one lookup (the convolution of the children's rows); and
one comparison per candidate pair and budget column. All pairs `(i, j)` are counted, whatever their
sum, so this covers the work of the recurrence `BudgetDP.cases`. -/
noncomputable def budgetOperations (t : PhyloTree) (Q : Multiset Quartet) (m : ℕ) : ℕ :=
  (t.nodes ×ˢ t.nodes).card + (t.nodes ×ˢ t.taxa).card + 2 * t.nodes.card +
    (EdgeAbove.candidates t ×ˢ Q.toFinset).card +
    hangingReads t * (Finset.range m ×ˢ (Finset.range (m+1) ×ˢ Finset.range (m+1))).card +
    (t.nodes ×ˢ (Finset.range m ×ˢ (Finset.range (m+1) ×ˢ Finset.range (m+1)))).card +
    (EdgeAbove.candidates t ×ˢ Finset.range m).card

/-- Section 2.3: the running time `O(n²(|Q| + n))`. For a tree `T` with `n` distinct leaf labels,
`scalarOperations t Q ≤ 32 n² (|Q| + n)`, where `|Q|` is the number of distinct quartets of `Q`. -/
theorem scalarOperations_bound {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet) :
    scalarOperations t Q ≤ 32 * t.taxa.card ^ 2 * (Q.toFinset.card + t.taxa.card) := by
  have hn := t.labels_nonempty
  have hnodes := t.nodes_count
  have htaxa : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  have hc := candidates_bound t
  have hh := hangingReads_bound t
  simp only [scalarOperations,Finset.card_product]
  rw [htaxa] at *
  have hcN : (EdgeAbove.candidates t).card ≤ 4*t.labels.length^2 := by nlinarith
  have hreads : hangingReads t ≤ 8*t.labels.length^3 := by
    nlinarith only [hh,hnodes,Nat.mul_le_mul_right t.nodes.card hcN]
  have hn2 : t.labels.length ≤ t.labels.length^2 := by nlinarith
  have hn3 : t.labels.length^2 ≤ t.labels.length^3 := by
    nlinarith [Nat.mul_le_mul_right t.labels.length hn2]
  nlinarith [Nat.mul_le_mul_right Q.toFinset.card hcN]

/-- Section 2.4: the running time `O(n²(|Q| + m³n))` of the restricted version. For a tree `T` with
`n` distinct leaf labels and `m ≥ 1`, `budgetOperations t Q m ≤ 100 n² (|Q| + m³ n)`. The paper
also has `m ≤ n − 1` (`RootedNetwork.anchored_reticulation_bound`); the bound does not need it. -/
theorem budgetOperations_bound {t : PhyloTree} (ht : t.WellLabelled)
    (Q : Multiset Quartet) {m : ℕ} (hm : 1 ≤ m) :
    budgetOperations t Q m ≤
      100 * t.taxa.card ^ 2 * (Q.toFinset.card + m ^ 3 * t.taxa.card) := by
  have hn := t.labels_nonempty
  have hnodes := t.nodes_count
  have htaxa : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  have hc := candidates_bound t
  have hh := hangingReads_bound t
  unfold budgetOperations
  simp only [Finset.card_product,Finset.card_range]
  rw [htaxa] at *
  have hcN : (EdgeAbove.candidates t).card ≤ 4*t.labels.length^2 := by nlinarith
  have hindex : m * ((m+1)*(m+1)) ≤ 4*m^3 := by
    have hb : m+1 ≤ 2*m := by omega
    have hs := Nat.mul_le_mul hb hb
    nlinarith only [Nat.mul_le_mul_left m hs]
  have hreads : hangingReads t ≤ 8*t.labels.length^3 := by
    nlinarith only [hh,hnodes,Nat.mul_le_mul_right t.nodes.card hcN]
  have hm2 : m ≤ m^2 := by nlinarith
  have hm3 : m ≤ m^3 := by nlinarith [Nat.mul_le_mul_right m hm2]
  have hmone : 1 ≤ m^3 := by omega
  have hn2 : t.labels.length ≤ t.labels.length^2 := by nlinarith
  have hn3 : t.labels.length^2 ≤ t.labels.length^3 := by
    nlinarith [Nat.mul_le_mul_right t.labels.length hn2]
  have hn13 : t.labels.length ≤ t.labels.length^3 := hn2.trans hn3
  have hpre : t.nodes.card*t.nodes.card + t.nodes.card*t.labels.length + 2*t.nodes.card ≤
      10*t.labels.length^3*m^3 := by
    nlinarith only [hnodes,hn2,hn3,Nat.mul_le_mul_right (t.labels.length^3) hmone]
  have hbranch : t.nodes.card*(m*((m+1)*(m+1))) ≤ 8*t.labels.length^3*m^3 := by
    nlinarith only [Nat.mul_le_mul (show t.nodes.card ≤ 2*t.labels.length by omega) hindex,
      Nat.mul_le_mul_right (m^3) hn13]
  have hcBudget : (EdgeAbove.candidates t).card*m ≤ 4*t.labels.length^3*m^3 := by
    nlinarith only [Nat.mul_le_mul hcN hm3,Nat.mul_le_mul_right (m^3) hn3]
  nlinarith only [hpre,hbranch,hcBudget,Nat.mul_le_mul hreads hindex,
    Nat.mul_le_mul_right Q.toFinset.card hcN]

/-- A quartet as the tuple of its four labels and its split index. -/
def quartetKey (q : Quartet) : ℕ × (ℕ × (ℕ × (ℕ × Fin 3))) :=
  (q.a,q.b,q.c,q.d,q.split)

/-- A quartet is determined by its four labels and its split. -/
theorem quartetKey_injective : Function.Injective quartetKey := by
  intro q r h
  cases q
  cases r
  simp only [quartetKey,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl,rfl,rfl⟩
  rfl

/-- Section 2.3: if every quartet of `Q` uses only taxa of `T`, then `Q` has at most `3n⁴` distinct
quartets (four labels and one of three splits), so `Q` is stored in `O(n⁴)` space. -/
theorem observedQuartets_bound (t : PhyloTree) (Q : Multiset Quartet)
    (hQ : ∀ q ∈ Q.toFinset, q.taxa ⊆ t.taxa) :
    Q.toFinset.card ≤ 3*t.taxa.card^4 := by
  classical
  let slots := t.taxa ×ˢ (t.taxa ×ˢ (t.taxa ×ˢ (t.taxa ×ˢ (Finset.univ : Finset (Fin 3)))))
  have hs : Q.toFinset.image quartetKey ⊆ slots := by
    intro k hk
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hk
    have h := hQ q hq
    have ha := h (show q.a ∈ q.taxa by simp [Quartet.taxa])
    have hb := h (show q.b ∈ q.taxa by simp [Quartet.taxa])
    have hc := h (show q.c ∈ q.taxa by simp [Quartet.taxa])
    have hd := h (show q.d ∈ q.taxa by simp [Quartet.taxa])
    simp [slots,quartetKey,ha,hb,hc,hd]
  have hcard := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ quartetKey_injective] at hcard
  have hslots : slots.card = 3*t.taxa.card^4 := by
    simp only [slots,Finset.card_product,Finset.card_univ,Fintype.card_fin]
    ring
  rw [hslots] at hcard
  exact hcard

/-- Section 2.3: the integers stored by CAMUS, each of unit size: six per distinct quartet of `Q`
(four labels, the split and the multiplicity), one weight `s_e(u, w)` per candidate pair, the
all-pairs LCA table, the table of leaves below each vertex, the depth array and the array `M`. -/
noncomputable def scalarSpace (t : PhyloTree) (Q : Multiset Quartet) : ℕ :=
  6*Q.toFinset.card + (EdgeAbove.candidates t).card + (t.nodes ×ˢ t.nodes).card +
    (t.nodes ×ˢ t.taxa).card + 2*t.nodes.card

/-- Section 2.3: the memory `O(n⁴)`. For a tree `T` with `n` distinct leaf labels, if every quartet
of `Q` uses only taxa of `T`, then `scalarSpace t Q ≤ 32 n⁴`. -/
theorem scalarSpace_bound {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet)
    (hQ : ∀ q ∈ Q.toFinset, q.taxa ⊆ t.taxa) : scalarSpace t Q ≤ 32*t.taxa.card^4 := by
  have hn := t.labels_nonempty
  have hnodes := t.nodes_count
  have htaxa : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  have hc := candidates_bound t
  have hq := observedQuartets_bound t Q hQ
  unfold scalarSpace
  simp only [Finset.card_product]
  rw [htaxa] at *
  have hn2 : t.labels.length ≤ t.labels.length^2 := by nlinarith
  have hn4 : t.labels.length^2 ≤ t.labels.length^4 := by nlinarith
  nlinarith

end Complexity
end Camus
