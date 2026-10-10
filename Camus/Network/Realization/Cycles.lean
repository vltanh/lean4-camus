module

public import Camus.Network.Realization.Binary
public import Camus.Network.Completeness.Tree

/-!
# The canonical network of an edge family: the cycle of an added edge

Definition 3 and the caption of Figure 1 say that adding the edge `u′ → w′` creates a cycle
`γ(u, w)`. This file builds it in `Realization.graph t E`, for `(u, w)` in a cycle-separated
family `E`. The support of the network, as an undirected graph, is a tree: it is connected
through the root and acyclic (`Realization.support_acyclic`), so two vertices are joined by a
unique path in it (`Realization.support_existsUnique_path`). The fundamental cycle of `(u, w)`
(`Realization.fundamentalCycle`) is the added edge `u′ → w′` followed by the support path from
`w′` back to `u′` (`Realization.cycleSupportPath`). Acyclicity of the support uses the rank of a
vertex, its number of strict ancestors (`RootedNetwork.dagRank`), which increases along every
edge: on an undirected cycle of support edges, both cycle edges at a vertex of maximal rank
would end at that vertex, where only one support edge ends.

## Main results

* `Realization.support_acyclic`: the support, as an undirected graph, is acyclic.
* `Realization.cycleSupportPath`: the support path from `w′` to `u′`.
* `Realization.fundamentalCycle`, `Realization.fundamentalCycle_isCycle`: the cycle `γ(u, w)`.
-/

@[expose] public section

namespace Camus.Realization

/-- For a cycle-separated family, the rank (the number of strict ancestors,
`RootedNetwork.dagRank`) increases strictly along every edge of `Realization.graph t E`. -/
theorem graph_rank_lt {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {u v : ℕ} (he : (u,v) ∈ (graph t E).edges) :
    (graph t E).dagRank u < (graph t E).dagRank v := by
  classical
  unfold RootedNetwork.dagRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_exists_subset_erase.mpr
  refine ⟨u, Finset.mem_filter.mpr ⟨(graph_edge_endpoints t E hE.1 he).1,
    Relation.TransGen.single he⟩, ?_⟩
  intro w hw
  obtain ⟨hw, hwu⟩ := Finset.mem_filter.mp hw
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr
    ⟨hw, hwu.trans (Relation.TransGen.single he)⟩⟩
  intro hwu'
  subst w
  exact graph_dag t E hE u hwu

/-- For a cycle-separated family `E`, the support of `Realization.graph t E`, as an undirected
graph, is acyclic. On a cycle, the two neighbours of a vertex `m` of maximal rank have rank at
most that of `m`, so both cycle edges at `m` are support edges ending at `m`; as only one support
edge ends at `m`, the two neighbours coincide, which a cycle does not allow. -/
theorem support_acyclic (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) :
    ({graph t E with edges := supportEdges t E}).underlying.IsAcyclic := by
  classical
  intro v c hc
  have hn : c.support.toFinset.Nonempty :=
    ⟨v, List.mem_toFinset.mpr c.start_mem_support⟩
  -- Rotate the cycle to start at a vertex `m` of maximal rank.
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image c.support.toFinset (graph t E).dagRank hn
  have hmc : m ∈ c.support := List.mem_toFinset.mp hm
  let d := c.rotate m hmc
  have hd : d.IsCycle := hc.rotate hmc
  have hs : (graph t E).dagRank d.snd ≤ (graph t E).dagRank m := hmax _
    (List.mem_toFinset.mpr ((c.mem_support_rotate_iff m hmc).mp
      (List.mem_of_mem_tail (d.snd_mem_tail_support hd.not_nil))))
  have hp : (graph t E).dagRank d.penultimate ≤ (graph t E).dagRank m := hmax _
    (List.mem_toFinset.mpr ((c.mem_support_rotate_iff m hmc).mp
      (List.mem_of_mem_dropLast (d.penultimate_mem_dropLast_support hd.not_nil))))
  have hsa := d.adj_snd hd.not_nil
  have hpa := d.adj_penultimate hd.not_nil
  -- Both cycle edges at `m` are support edges ending at `m`, as the rank increases along edges.
  have hin₁ : (d.snd,m) ∈ supportEdges t E := by
    rcases hsa.2 with hout | hin
    · exact False.elim ((not_lt_of_ge hs) (graph_rank_lt hE (Finset.mem_union_left _ hout)))
    · exact hin
  have hin₂ : (d.penultimate,m) ∈ supportEdges t E := by
    rcases hpa.2 with hin | hout
    · exact hin
    · exact False.elim ((not_lt_of_ge hp) (graph_rank_lt hE (Finset.mem_union_left _ hout)))
  -- Only one support edge ends at `m`, so the two neighbours of `m` on the cycle coincide.
  exact hd.snd_ne_penultimate (support_incoming_unique t E hE.1 hin₁ hin₂)

/-- For a cycle-separated family, `Realization.graph t E` has no loop. -/
theorem graph_edge_ne {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {u v : ℕ} (he : (u,v) ∈ (graph t E).edges) : u ≠ v := by
  intro huv
  subst v
  exact graph_dag t E hE u (Relation.TransGen.single he)

/-- For a cycle-separated family, if `u → v` is an edge of `Realization.graph t E`, then
`v → u` is not. -/
theorem graph_edge_reverse_not_mem {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {u v : ℕ}
    (he : (u,v) ∈ (graph t E).edges) : (v,u) ∉ (graph t E).edges := by
  intro hr
  exact graph_dag t E hE u ((Relation.TransGen.single he).trans
    (Relation.TransGen.single hr))

/-- The undirected support graph is a subgraph of the underlying undirected graph of
`Realization.graph t E`. -/
theorem support_underlying_le (t : PhyloTree) (E : Finset Pair) :
    ({graph t E with edges := supportEdges t E}).underlying ≤ (graph t E).underlying := by
  intro u v h
  exact ⟨h.1, h.2.imp (Finset.mem_union_left _) (Finset.mem_union_left _)⟩

/-- For a cycle-separated family, any two vertices of `Realization.graph t E` are connected in
the undirected support graph. -/
theorem support_connected_vertices {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {u v : ℕ}
    (hu : u ∈ (graph t E).vertices) (hv : v ∈ (graph t E).vertices) :
    ({graph t E with edges := supportEdges t E}).underlying.Reachable u v := by
  have rootpath : ∀ w ∈ (graph t E).vertices,
      ({graph t E with edges := supportEdges t E}).underlying.Reachable (graph t E).root w := by
    intro w hw
    apply (SimpleGraph.reachable_iff_reflTransGen _ _).mpr
    apply Relation.ReflTransGen.mono ?_ _ _ (support_reaches t E hE.1 hw)
    intro a b hab
    exact ⟨graph_edge_ne hE (Finset.mem_union_left _ hab), Or.inl hab⟩
  exact (rootpath u hu).symm.trans (rootpath v hv)

/-- For a cycle-separated family, any two vertices of `Realization.graph t E` are joined by a
unique path in the undirected support graph. -/
theorem support_existsUnique_path {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {u v : ℕ}
    (hu : u ∈ (graph t E).vertices) (hv : v ∈ (graph t E).vertices) :
    ∃! p : ({graph t E with edges := supportEdges t E}).underlying.Walk u v, p.IsPath := by
  classical
  let p := (support_connected_vertices hE hu hv).some.toPath
  refine ⟨p, p.isPath, ?_⟩
  intro q hq
  exact Subtype.mk.inj ((support_acyclic t E hE).subsingleton_path u v |>.elim ⟨q,hq⟩ p)

/-- For `(u, w)` in a cycle-separated family `E`, the path from `w′` to `u′` in the undirected
support graph of `Realization.graph t E` (it is unique). -/
noncomputable def cycleSupportPath (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) (e : Pair) (he : e ∈ E) :
    ({graph t E with edges := supportEdges t E}).underlying.Path (recipient t e) (donor t e) :=
  ⟨Classical.choose (support_existsUnique_path hE
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, by simp⟩))
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, by simp⟩))),
    (Classical.choose_spec (support_existsUnique_path hE
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, by simp⟩))
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, by simp⟩)))).1⟩

/-- The cycle `γ(u, w)` of Definition 3 in `Realization.graph t E`, for `(u, w)` in a
cycle-separated family `E`: the closed walk at `u′` along the added edge `u′ → w′` and back along
the support path from `w′` to `u′` (`Realization.cycleSupportPath`). -/
noncomputable def fundamentalCycle (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) (e : Pair) (he : e ∈ E) :
    (graph t E).underlying.Walk (donor t e) (donor t e) :=
  .cons ⟨donor_ne_recipient t e e,
      Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩))⟩
    ((cycleSupportPath t E hE e he).val.mapLe (support_underlying_le t E))

/-- The fundamental cycle of `(u, w)` is a cycle: the support path does not use the edge
between `u′` and `w′`, which is a support edge in neither direction. -/
theorem fundamentalCycle_isCycle (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) (e : Pair) (he : e ∈ E) :
    (fundamentalCycle t E hE e he).IsCycle := by
  classical
  apply SimpleGraph.Walk.cons_isCycle_iff _ _ |>.mpr
  refine ⟨(cycleSupportPath t E hE e he).isPath.mapLe _, ?_⟩
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  intro hmem
  have hadj := (cycleSupportPath t E hE e he).val.edges_subset_edgeSet hmem
  rcases hadj.2 with hs | hr
  · exact added_edge_not_support hE.1 he hs
  · exact graph_edge_reverse_not_mem hE
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩))
      (Finset.mem_union_left _ hr)

end Camus.Realization
