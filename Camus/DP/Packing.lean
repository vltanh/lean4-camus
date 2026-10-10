module

public import Camus.Defs
public import Camus.Network.Code
public import Camus.Score

/-!
# Feasible families of pairs: combining and splitting

The proof of Theorem 1 works with families of pairs `(u, w)` (edges added above `(u, w)`) instead
of networks. A family `E` is feasible below a vertex `v` of `T`
(`DynamicProgramming.FeasibleBelow t v E`) if it is cycle-separated (admissible pairs whose cycles
share no vertex of `T`) and all its targets lie in `T_v`; its canonical network
`Realization.graph t E` is then a level-1 network built on `T` (`Realization.levelOne`). This file
proves the tree geometry of feasible families used in the proof of Theorem 1
(`Camus/DP/Correctness.lean`).

* Part (a) of the proof, that the output is a level-1 network: the families below the two children
  of `v` combine (`DynamicProgramming.fork_feasible`), and so do an edge `e` with target `v` and
  families below the roots of the subtrees hanging off its cycle `γ(e)`
  (`DynamicProgramming.gall_feasible`). These are the two cases of the backtracking.
* Part (c), the induction: if no edge of a feasible family `E` has target `v`, `E` splits into
  families below the two children (`DynamicProgramming.fork_partition`); if `e ∈ E` has target `v`,
  the other edges split into families below the roots of the subtrees hanging off `γ(e)`
  (`DynamicProgramming.gall_partition`, by `DynamicProgramming.competitor_in_hanging`, which uses
  Lemma 2). The induction is on `DynamicProgramming.remainingDepth`.

The hanging roots of `γ(e)` are `DynamicProgramming.hanging t e`, the vertices of `T` not on `γ(e)`
whose parent is on `γ(e)` (the frontier of `EdgeAbove.footprint t e`).

## Main results

* `DynamicProgramming.fork_feasible`, `DynamicProgramming.gall_feasible`: feasibility of the two
  cases of the backtracking.
* `DynamicProgramming.fork_partition`, `DynamicProgramming.gall_partition`: the two cases of the
  induction.
* `DynamicProgramming.competitor_in_hanging`: in the second case, every other edge has its target
  below exactly one hanging root.
* `DynamicProgramming.value_gall`: the value of `e` with families below the hanging roots is the
  weight of `e` plus their values.
* `DynamicProgramming.remainingDepth`, `DynamicProgramming.remainingDepth_lt`: the induction
  measure.
* `DynamicProgramming.feasible_leaf_empty`: the base case.
-/

@[expose] public section

namespace Camus

namespace PhyloTree

/-- The subtree at the address `p ++ q` is the subtree at `q` of the subtree at `p`. -/
theorem nodeAt_append (t : PhyloTree) (p q : Address) :
    t.nodeAt (p ++ q) = (t.nodeAt p).bind (fun s => s.nodeAt q) := by
  induction p generalizing t with
  | nil => simp [nodeAt]
  | cons b p ih =>
    cases t with
    | leaf a => simp [nodeAt]
    | fork l r => cases b <;> simp [nodeAt, ih]

/-- A leaf of `T` has no proper descendant in `T`. -/
theorem leaf_no_descendant {t : PhyloTree} {p q : Address} {a : ℕ}
    (hp : t.nodeAt p = some (.leaf a)) (hq : q ∈ t.nodes) (hpq : p <+: q) : p = q := by
  obtain ⟨s, rfl⟩ := hpq
  obtain ⟨u, hu⟩ := (mem_nodes_iff _ _).mp hq
  rw [nodeAt_append, hp] at hu
  cases s with
  | nil => simp
  | cons b s => simp [nodeAt] at hu

/-- Both children `p ++ [false]` and `p ++ [true]` of an internal vertex `p` are vertices of `T`. -/
theorem child_mem_nodes {t l r : PhyloTree} {p : Address}
    (hp : t.nodeAt p = some (.fork l r)) (b : Bool) : p ++ [b] ∈ t.nodes := by
  rw [mem_nodes_iff, nodeAt_append, hp]
  cases b <;> simp [nodeAt]

end PhyloTree

/-- A proper descendant of `p` is below the left child or below the right child of `p`. -/
theorem prefix_child_cases {p q : Address} (hpq : p <+: q) (hne : p ≠ q) :
    p ++ [false] <+: q ∨ p ++ [true] <+: q := by
  obtain ⟨s, rfl⟩ := hpq
  cases s with
  | nil => simp at hne
  | cons b s =>
    cases b
    · exact Or.inl ⟨s, by simp⟩
    · exact Or.inr ⟨s, by simp⟩

/-- No address is below both children of `p`. -/
theorem child_cones_disjoint (p : Address) :
    ¬ ∃ q : Address, p ++ [false] <+: q ∧ p ++ [true] <+: q := by
  rintro ⟨q, hl, hr⟩
  rcases List.prefix_or_prefix_of_prefix hl hr with h | h
  all_goals simp at h

namespace EdgeAbove

/-- The target `lca(u, w)` of an admissible pair `(u, w)` is a vertex of `T`. -/
theorem target_mem_nodes {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) : target e ∈ t.nodes :=
  t.nodes_prefix_closed he.1 (lca_prefix_left _ _)

/-- The vertices of `T` on the cycle `γ(u, w)` lie below the target `lca(u, w)`. -/
theorem footprint_below {t : PhyloTree} {e : Address × Address} {x : Address}
    (hx : x ∈ footprint t e) : target e <+: x := (Finset.mem_filter.mp hx).2.1

/-- A subfamily of a cycle-separated family is cycle-separated. -/
theorem separated_subset {t : PhyloTree} {E F : Finset (Address × Address)}
    (hE : CycleSeparated t E) (hF : F ⊆ E) : CycleSeparated t F := by
  exact ⟨fun _ hf => hE.1 (hF hf), fun _ he _ hf hne => hE.2 (hF he) (hF hf) hne⟩

end EdgeAbove

namespace DynamicProgramming

/-- The measure of the strong induction in the proof of Theorem 1: the height of `T` minus the
depth of `v`. It decreases from `v` to each proper descendant (`remainingDepth_lt`), as does the
number of leaves below `v`, the paper's measure. -/
def remainingDepth (t : PhyloTree) (v : Address) : ℕ :=
  t.nodes.sup List.length - v.length

/-- `remainingDepth` decreases strictly from `v` to each proper descendant `r` in `T`. -/
theorem remainingDepth_lt {t : PhyloTree} {v r : Address}
    (hr : r ∈ t.nodes) (hvr : v <+: r) (hne : v ≠ r) :
    remainingDepth t r < remainingDepth t v := by
  have hle : r.length ≤ t.nodes.sup List.length := Finset.le_sup hr
  have hlt : v.length < r.length := by
    by_contra hn
    exact hne (hvr.eq_of_length_le (by omega))
  unfold remainingDepth
  omega

/-- The empty family is feasible below every vertex. -/
theorem feasible_empty (t : PhyloTree) (v : Address) : FeasibleBelow t v ∅ := by
  simp [FeasibleBelow, EdgeAbove.CycleSeparated, Set.Pairwise]

/-- A subfamily of a family feasible below `v` is feasible below `v`. -/
theorem feasible_subset {t : PhyloTree} {v : Address} {E F : Finset Pair}
    (hE : FeasibleBelow t v E) (hF : F ⊆ E) : FeasibleBelow t v F :=
  ⟨EdgeAbove.separated_subset hE.1 hF, fun e he => hE.2 e (hF he)⟩

/-- A family feasible below `v` is feasible below every ancestor of `v`. -/
theorem feasible_ancestor {t : PhyloTree} {u v : Address} {E : Finset Pair}
    (hE : FeasibleBelow t v E) (huv : u <+: v) : FeasibleBelow t u E :=
  ⟨hE.1, fun e he => huv.trans (hE.2 e he)⟩

/-- Base case of the induction in the proof of Theorem 1: the only family feasible below a leaf `v`
is empty. Both ends of a pair with target in `T_v` would be `v`, and the ends of an admissible pair
are distinct. -/
theorem feasible_leaf_empty {t : PhyloTree} {v : Address} {a : ℕ} {E : Finset Pair}
    (hv : t.nodeAt v = some (.leaf a)) (hE : FeasibleBelow t v E) : E = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have ha := (Finset.mem_filter.mp (hE.1.1 he)).2
  have hve := hE.2 e he
  have hvu := hve.trans (lca_prefix_left _ _)
  have hvw := hve.trans (lca_prefix_right _ _)
  have hu := PhyloTree.leaf_no_descendant hv ha.1 hvu
  have hw := PhyloTree.leaf_no_descendant hv ha.2.1 hvw
  exact ha.2.2.2.2 (hw.symm.trans hu ▸ List.prefix_refl _)

/-- Case 2 of the induction in the proof of Theorem 1. Let `E` be feasible below `v` and `e ∈ E`
with target `v`. Every other `f ∈ E` has its target below exactly one root of a subtree hanging off
`γ(e)` (`hanging t e`). Indeed the target of `f` is not `v`, by Lemma 2
(`EdgeAbove.target_unique`); it lies on the cycle of `f`, hence not on `γ(e)`; and it lies below
`v`. -/
theorem competitor_in_hanging {t : PhyloTree} {v : Address} {E : Finset Pair}
    (hE : FeasibleBelow t v E) {e f : Pair} (he : e ∈ E) (hf : f ∈ E)
    (hroot : EdgeAbove.target e = v) (hne : f ≠ e) :
    ∃! r, r ∈ hanging t e ∧ r <+: EdgeAbove.target f := by
  have hae := (Finset.mem_filter.mp (hE.1.1 he)).2
  have haf := (Finset.mem_filter.mp (hE.1.1 hf)).2
  by_cases hsame : EdgeAbove.target f = EdgeAbove.target e
  · exact (hne (EdgeAbove.target_unique t E hE.1 hf he hsame)).elim
  have htf := EdgeAbove.target_mem_footprint t f haf
  have hnot : EdgeAbove.target f ∉ EdgeAbove.footprint t e := by
    intro h
    exact Finset.disjoint_left.mp (hE.1.2 hf he hne) htf h
  apply exists_unique_frontier (EdgeAbove.footprint_region t e hae)
    (EdgeAbove.target_mem_nodes haf) (hroot ▸ hE.2 f hf) hnot

/-- Two frontier vertices of a tree region that are both ancestors of the same vertex are equal. -/
theorem frontier_prefix_unique {t : PhyloTree} {p : Address} {S : Finset Address}
    (hS : TreeRegion t p S) {r s x : Address}
    (hr : r ∈ frontier t S) (hs : s ∈ frontier t S)
    (hrx : r <+: x) (hsx : s <+: x) : r = s := by
  rcases List.prefix_or_prefix_of_prefix hrx hsx with h | h
  · exact frontier_antichain hS hr hs h
  · exact (frontier_antichain hS hs hr h).symm

/-- Families feasible below distinct frontier vertices of a tree region are disjoint. -/
theorem forest_disjoint {t : PhyloTree} {p : Address} {S : Finset Address}
    (hS : TreeRegion t p S) (F : Address → Finset Pair)
    (hF : ∀ r ∈ frontier t S, FeasibleBelow t r (F r)) :
    (frontier t S : Set Address).Pairwise (fun r s => Disjoint (F r) (F s)) := by
  intro r hr s hs hne
  apply Finset.disjoint_left.mpr
  intro e her hes
  exact hne (frontier_prefix_unique hS hr hs ((hF r hr).2 e her) ((hF s hs).2 e hes))

/-- Let `S` be a tree region with top `p` (a connected set of vertices below `p`). The union of
families `F r` feasible below the frontier vertices `r` of `S` is feasible below `p`: the cycles of
families below distinct frontier vertices lie in disjoint subtrees. -/
theorem forest_feasible {t : PhyloTree} {p : Address} {S : Finset Address}
    (hS : TreeRegion t p S) (F : Address → Finset Pair)
    (hF : ∀ r ∈ frontier t S, FeasibleBelow t r (F r)) :
    FeasibleBelow t p ((frontier t S).biUnion F) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro e he
    obtain ⟨r, hr, her⟩ := Finset.mem_biUnion.mp he
    exact (hF r hr).1.1 her
  · intro e he f hf hne
    obtain ⟨r, hr, her⟩ := Finset.mem_biUnion.mp he
    obtain ⟨s, hs, hfs⟩ := Finset.mem_biUnion.mp hf
    by_cases hrs : r = s
    · subst s
      exact (hF r hr).1.2 her hfs hne
    · apply Finset.disjoint_left.mpr
      intro x hxe hxf
      have hrx := ((hF r hr).2 e her).trans (EdgeAbove.footprint_below hxe)
      have hsx := ((hF s hs).2 f hfs).trans (EdgeAbove.footprint_below hxf)
      exact hrs (frontier_prefix_unique hS hr hs hrx hsx)
  · intro e he
    obtain ⟨r, hr, her⟩ := Finset.mem_biUnion.mp he
    exact (frontier_below hS hr).1.trans ((hF r hr).2 e her)

/-- The cycles of a family feasible below a frontier vertex of a tree region `S` avoid `S`. -/
theorem forest_avoids_region {t : PhyloTree} {p : Address} {S : Finset Address}
    (hS : TreeRegion t p S) (F : Address → Finset Pair)
    (hF : ∀ r ∈ frontier t S, FeasibleBelow t r (F r))
    {e : Pair} (he : e ∈ (frontier t S).biUnion F) :
    Disjoint (EdgeAbove.footprint t e) S := by
  obtain ⟨r, hr, her⟩ := Finset.mem_biUnion.mp he
  apply Finset.disjoint_left.mpr
  intro x hx hxs
  exact frontier_cone_disjoint hS hr
    (((hF r hr).2 e her).trans (EdgeAbove.footprint_below hx)) hxs

/-- Part (a) of the proof of Theorem 1, for an edge with target `v`: an admissible pair `e`,
together with families feasible below the roots of the subtrees hanging off `γ(e)`, is feasible
below the target of `e`. The cycles of the hanging families avoid `γ(e)` and each other; this is
how Equations (4)–(5) keep cycles with targets in relation disjoint. -/
theorem gall_feasible {t : PhyloTree} {e : Pair}
    (he : EdgeAbove.Admissible t e) (F : Address → Finset Pair)
    (hF : ∀ r ∈ hanging t e, FeasibleBelow t r (F r)) :
    FeasibleBelow t (EdgeAbove.target e) (insert e ((hanging t e).biUnion F)) := by
  have hS := EdgeAbove.footprint_region t e he
  have hforest := forest_feasible hS F hF
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he.1, he.2.1⟩, he⟩
    · exact hforest.1.1 hf
  · intro f hf g hg hne
    rcases Finset.mem_insert.mp hf with rfl | hf
    · rcases Finset.mem_insert.mp hg with rfl | hg
      · exact (hne rfl).elim
      · exact (forest_avoids_region hS F hF hg).symm
    · rcases Finset.mem_insert.mp hg with rfl | hg
      · exact forest_avoids_region hS F hF hf
      · exact hforest.1.2 hf hg hne
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact List.prefix_refl _
    · exact hforest.2 f hf

/-- The pair `e` belongs to no family feasible below a root of a subtree hanging off `γ(e)`. -/
theorem gall_not_mem_forest {t : PhyloTree} {e : Pair}
    (he : EdgeAbove.Admissible t e) (F : Address → Finset Pair)
    (hF : ∀ r ∈ hanging t e, FeasibleBelow t r (F r)) :
    e ∉ (hanging t e).biUnion F := by
  intro h
  have hd := forest_avoids_region (EdgeAbove.footprint_region t e he) F hF h
  have hm := EdgeAbove.target_mem_footprint t e he
  exact Finset.disjoint_left.mp hd hm hm

/-- The pairs of `E` whose target lies in `T_r`. -/
def restrictBelow (r : Address) (E : Finset Pair) : Finset Pair :=
  E.filter (fun e => r <+: EdgeAbove.target e)

/-- The restriction of a feasible family below any vertex `r` is feasible below `r`. -/
theorem restrict_feasible {t : PhyloTree} {v r : Address} {E : Finset Pair}
    (hE : FeasibleBelow t v E) : FeasibleBelow t r (restrictBelow r E) := by
  exact ⟨EdgeAbove.separated_subset hE.1 (Finset.filter_subset _ _),
    fun _ he => (Finset.mem_filter.mp he).2⟩

/-- Families feasible below the two children of `v` are disjoint. -/
theorem fork_disjoint {t : PhyloTree} {v : Address} {L R : Finset Pair}
    (hL : FeasibleBelow t (v ++ [false]) L)
    (hR : FeasibleBelow t (v ++ [true]) R) : Disjoint L R := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact child_cones_disjoint v ⟨EdgeAbove.target e, hL.2 e he, hR.2 e hf⟩

/-- Part (a) of the proof of Theorem 1, for the first term of Equation (2): the union of families
feasible below the two children of `v` is feasible below `v`. Their targets are not in relation,
and their cycles lie in the two disjoint subtrees. -/
theorem fork_feasible {t : PhyloTree} {v : Address} {L R : Finset Pair}
    (hL : FeasibleBelow t (v ++ [false]) L)
    (hR : FeasibleBelow t (v ++ [true]) R) : FeasibleBelow t v (L ∪ R) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hL.1.1 he
    · exact hR.1.1 he
  · intro e he f hf hne
    rcases Finset.mem_union.mp he with he | he
    · rcases Finset.mem_union.mp hf with hf | hf
      · exact hL.1.2 he hf hne
      · apply Finset.disjoint_left.mpr
        intro x hx hy
        exact child_cones_disjoint v ⟨x,
          (hL.2 e he).trans (EdgeAbove.footprint_below hx),
          (hR.2 f hf).trans (EdgeAbove.footprint_below hy)⟩
    · rcases Finset.mem_union.mp hf with hf | hf
      · apply Finset.disjoint_left.mpr
        intro x hx hy
        exact child_cones_disjoint v ⟨x,
          (hL.2 f hf).trans (EdgeAbove.footprint_below hy),
          (hR.2 e he).trans (EdgeAbove.footprint_below hx)⟩
      · exact hR.1.2 he hf hne
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact (List.prefix_append _ _).trans (hL.2 e he)
    · exact (List.prefix_append _ _).trans (hR.2 e he)

/-- Case 1 of the induction in the proof of Theorem 1: if no pair of a family `E` feasible below `v`
has target `v`, then `E` is the union of its restrictions below the two children of `v`. -/
theorem fork_partition {t : PhyloTree} {v : Address} {E : Finset Pair}
    (hE : FeasibleBelow t v E) (hroot : ∀ e ∈ E, EdgeAbove.target e ≠ v) :
    E = restrictBelow (v ++ [false]) E ∪ restrictBelow (v ++ [true]) E := by
  ext e
  simp only [restrictBelow, Finset.mem_union, Finset.mem_filter]
  constructor
  · intro he
    rcases prefix_child_cases (hE.2 e he) (Ne.symm (hroot e he)) with h | h
    · exact Or.inl ⟨he, h⟩
    · exact Or.inr ⟨he, h⟩
  · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he

/-- Case 2 of the induction in the proof of Theorem 1: if `e` is a pair with target `v` in a family
`E` feasible below `v`, then `E` is `e` together with the restrictions of `E \ {e}` below the roots
of the subtrees hanging off `γ(e)` (`competitor_in_hanging`). -/
theorem gall_partition {t : PhyloTree} {v : Address} {E : Finset Pair}
    (hE : FeasibleBelow t v E) {e : Pair} (he : e ∈ E)
    (hroot : EdgeAbove.target e = v) :
    E = insert e ((hanging t e).biUnion (fun r => restrictBelow r (E.erase e))) := by
  ext f
  simp only [Finset.mem_insert, Finset.mem_biUnion, restrictBelow,
    Finset.mem_filter, Finset.mem_erase]
  constructor
  · intro hf
    by_cases hfe : f = e
    · exact Or.inl hfe
    · obtain ⟨r, hr, _⟩ := competitor_in_hanging hE he hf hroot hfe
      exact Or.inr ⟨r, hr.1, ⟨hfe, hf⟩, hr.2⟩
  · rintro (rfl | ⟨r, _, ⟨_, hf⟩, _⟩)
    · exact he
    · exact hf

/-- The value (total weight) of a union of families feasible below the frontier vertices of a tree
region is the sum of their values. -/
theorem value_forest {t : PhyloTree} {p : Address} {S : Finset Address}
    (hS : TreeRegion t p S) (weight : Pair → ℕ) (F : Address → Finset Pair)
    (hF : ∀ r ∈ frontier t S, FeasibleBelow t r (F r)) :
    value weight ((frontier t S).biUnion F) = ∑ r ∈ frontier t S, value weight (F r) := by
  exact Finset.sum_biUnion (forest_disjoint hS F hF)

/-- The value of `e` together with families feasible below the roots of the subtrees hanging off
`γ(e)` is the weight of `e` plus the sum of their values. -/
theorem value_gall {t : PhyloTree} {e : Pair}
    (he : EdgeAbove.Admissible t e) (weight : Pair → ℕ) (F : Address → Finset Pair)
    (hF : ∀ r ∈ hanging t e, FeasibleBelow t r (F r)) :
    value weight (insert e ((hanging t e).biUnion F)) =
      weight e + ∑ r ∈ hanging t e, value weight (F r) := by
  rw [value, Finset.sum_insert (gall_not_mem_forest he F hF)]
  congr 1
  exact value_forest (EdgeAbove.footprint_region t e he) weight F hF

end DynamicProgramming
end Camus
