module

public import Camus.Network.Reticulations
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.Prod

/-!
# Section 2.3: counting lemmas and memory

The counts that the bounds of Sections 2.3 and 2.4 use. A tree with `n` leaves has `2n − 1`
vertices (`PhyloTree.nodes_count`); it has at most `|V(T)|²` candidate pairs
(`Complexity.candidates_bound`), each examined at exactly one target
(`Complexity.candidate_visits`: the paper's remark that "no edge is ever considered in the s(·)
function more than once over all subproblems"); at most `|V(T)|` subtrees hang off a cycle
(`Complexity.hanging_bound`); and a multiset of quartets on the taxa of `T` has at most `3n⁴`
distinct quartets (`Complexity.observedQuartets_bound`). The running time is bounded in
`Camus/Complexity/Program.lean` and `Camus/Complexity/BudgetProgram.lean`.

Memory: `Complexity.scalarSpace` counts the integers that CAMUS stores, under the paper's convention
that an integer takes `O(1)` memory (six per distinct quartet of `Q`, one weight per candidate pair,
the tables of the preprocessing and the array `M`), and `Complexity.scalarSpace_bound` bounds it by
`32 n⁴`, the memory `O(n⁴)` of Section 2.3. The program of `Camus/Complexity/Program.lean` writes
at most three times as many entries (`Complexity.storedIntegers_le`, in
`Camus/Complexity/Memory.lean`).

## Main results

* `PhyloTree.nodes_count`: `|V(T)| + 1 = 2n`.
* `Complexity.candidate_visits`: each candidate pair is examined at exactly one target.
* `Complexity.candidates_bound`, `Complexity.hanging_bound`: the sizes of the loops.
* `Complexity.scalarSpace_bound`: `scalarSpace ≤ 32 n⁴` when every quartet of `Q` uses taxa of `T`.
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
