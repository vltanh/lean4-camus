module

public import Camus.Network.Realization.CycleFootprint
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# The canonical network of an edge family: every cycle is a fundamental cycle

This file proves the level-1 condition for `Realization.graph t E`, `E` cycle-separated: two
cycles with distinct edge sets are vertex-disjoint (`Realization.cycles_disjoint`). First, every
edge of a cycle lies on a fundamental cycle (`Realization.cycle_edge_in_fundamental`).
Otherwise it is a support edge whose ends stay connected, through the rest of the cycle, once it
is removed. Replacing each added edge `u′ → w′` of that connection by the support path between
`w′` and `u′`, which lies on the fundamental cycle of `(u, w)` and so avoids the removed edge,
gives a cycle of the support tree, which is acyclic. So every cycle lies in the union of the
fundamental cycles (`Realization.cyclicGraph`). These are vertex-disjoint
(`Realization.fundamentalCycles_disjoint`), so in their union every non-isolated vertex has
degree `2` (`Realization.cyclicGraph_isCycles`), and in such a graph two cycles through a common
vertex have the same edges (`Realization.isCycles_cycle_edges_eq`). Hence every cycle of the
network has the edges of a fundamental cycle, and cycles with distinct edge sets are
vertex-disjoint.

## Main results

* `Realization.cycle_edge_in_fundamental`: every edge of a cycle lies on a fundamental cycle.
* `Realization.cyclicGraph_isCycles`: in the union of the fundamental cycles, every non-isolated
  vertex has degree `2`.
* `Realization.isCycles_cycle_edges_eq`: in such a graph, two cycles through a common vertex
  have the same edges.
* `Realization.cycles_disjoint`: cycles of `Realization.graph t E` with distinct edge sets are
  vertex-disjoint.
-/

@[expose] public section

namespace Camus.Realization

/-- Let `r` be an edge on no fundamental cycle. Two vertices adjacent in the network minus `r`
are connected in the support graph minus `r`: a support edge is kept, and an added edge between
`u′` and `w′` is replaced by the support path between `w′` and `u′`, which lies on the
fundamental cycle of `(u, w)`. -/
theorem full_deleted_edge_replace {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) (r : Sym2 ℕ)
    (hr : ∀ e (he : e ∈ E), r ∉ (fundamentalCycle t E hE e he).edges)
    {u v : ℕ} (huv : ((graph t E).underlying.deleteEdges {r}).Adj u v) :
    (({graph t E with edges := supportEdges t E}).underlying.deleteEdges {r}).Reachable u v := by
  classical
  have hadj := (SimpleGraph.deleteEdges_adj.mp huv).1
  have hne := (SimpleGraph.deleteEdges_adj.mp huv).2
  have hs : ((u,v) ∈ supportEdges t E ∨ (v,u) ∈ supportEdges t E) ∨
      ((u,v) ∈ E.image (fun e => (donor t e,recipient t e)) ∨
        (v,u) ∈ E.image (fun e => (donor t e,recipient t e))) := by
    rcases hadj.2 with hf | hb <;> rcases Finset.mem_union.mp ‹_› with hs | ha
    · exact Or.inl (Or.inl hs)
    · exact Or.inr (Or.inl ha)
    · exact Or.inl (Or.inr hs)
    · exact Or.inr (Or.inr ha)
  rcases hs with hs | ha
  · exact SimpleGraph.Adj.reachable (SimpleGraph.deleteEdges_adj.mpr ⟨⟨hadj.1,hs⟩,hne⟩)
  · have hpath : ∀ e (he : e ∈ E), r ∉ (cycleSupportPath t E hE e he).val.edges := by
      intro e he hmem
      apply hr e he
      change r ∈ s(donor t e,recipient t e) ::
        ((cycleSupportPath t E hE e he).val.mapLe (support_underlying_le t E)).edges
      exact List.mem_cons_of_mem _ (by simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using hmem)
    rcases ha with hf | hb
    · obtain ⟨e,he,hpair⟩ := Finset.mem_image.mp hf
      have hu : u = donor t e := (congrArg Prod.fst hpair).symm
      have hv : v = recipient t e := (congrArg Prod.snd hpair).symm
      rw [hu,hv]
      exact ((cycleSupportPath t E hE e he).val.toDeleteEdge r (hpath e he)).reachable.symm
    · obtain ⟨e,he,hpair⟩ := Finset.mem_image.mp hb
      have hv : v = donor t e := (congrArg Prod.fst hpair).symm
      have hu : u = recipient t e := (congrArg Prod.snd hpair).symm
      rw [hu,hv]
      exact ((cycleSupportPath t E hE e he).val.toDeleteEdge r (hpath e he)).reachable

private theorem walk_replace_reachable {G H : SimpleGraph ℕ}
    (hreplace : ∀ u v, G.Adj u v → H.Reachable u v) {u v : ℕ} (p : G.Walk u v) :
    H.Reachable u v := by
  induction p with
  | nil => rfl
  | cons hadj p ih => exact (hreplace _ _ hadj).trans ih

/-- For a cycle-separated family `E`, every edge of a cycle of `Realization.graph t E` lies on
the fundamental cycle of some pair of `E`. -/
theorem cycle_edge_in_fundamental {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {v : ℕ} (c : (graph t E).underlying.Walk v v)
    (hc : c.IsCycle) {r : Sym2 ℕ} (hr : r ∈ c.edges) :
    ∃ e, ∃ he : e ∈ E, r ∈ (fundamentalCycle t E hE e he).edges := by
  classical
  -- Suppose that the edge `r` of `c` lies on no fundamental cycle.
  by_contra hnone
  have havoid : ∀ e (he : e ∈ E), r ∉ (fundamentalCycle t E hE e he).edges := by
    intro e he hmem
    exact hnone ⟨e,he,hmem⟩
  obtain ⟨u,w⟩ := r
  have hadj := c.adj_of_mem_edges hr
  -- Its ends stay connected once `r` is removed, through the rest of `c`.
  have hfull := (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle).mpr ⟨v,c,hc,hr⟩
  -- `r` is a support edge, since an added edge lies on its own fundamental cycle.
  have hsupport : ({graph t E with edges := supportEdges t E}).underlying.Adj u w := by
    refine ⟨hadj.1,?_⟩
    rcases hadj.2 with hfw | hbw <;> rcases Finset.mem_union.mp ‹_› with hs | ha
    · exact Or.inl hs
    · obtain ⟨e,he,hpair⟩ := Finset.mem_image.mp ha
      have hu : u = donor t e := (congrArg Prod.fst hpair).symm
      have hw : w = recipient t e := (congrArg Prod.snd hpair).symm
      apply False.elim
      apply havoid e he
      change s(u,w) ∈ s(donor t e,recipient t e) :: _
      simp [hu,hw]
    · exact Or.inr hs
    · obtain ⟨e,he,hpair⟩ := Finset.mem_image.mp ha
      have hw : w = donor t e := (congrArg Prod.fst hpair).symm
      have hu : u = recipient t e := (congrArg Prod.snd hpair).symm
      apply False.elim
      apply havoid e he
      change s(u,w) ∈ s(donor t e,recipient t e) :: _
      simp [hu,hw,Sym2.eq_swap]
  -- Replace the added edges of that connection by support paths, which avoid `r`.
  have hreplaced := walk_replace_reachable (fun u v hadj => full_deleted_edge_replace hE _ havoid hadj)
    hfull.2.some
  -- So `r` lies on a cycle of the support, which is acyclic.
  have hscycle := SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp
    ⟨hsupport,hreplaced⟩
  obtain ⟨z,d,hd,_⟩ := hscycle
  exact support_acyclic t E hE d hd

/-- The union of the fundamental cycles of the pairs of a cycle-separated family `E`, as a
simple graph: two vertices are adjacent iff they are joined by an edge of some fundamental
cycle. -/
noncomputable def cyclicGraph (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) : SimpleGraph ℕ where
  Adj u v := ∃ e, ∃ he : e ∈ E, (fundamentalCycle t E hE e he).toSubgraph.Adj u v
  symm := ⟨by intro u v ⟨e,he,hadj⟩; exact ⟨e,he,hadj.symm⟩⟩
  loopless := ⟨by
    intro u ⟨e,he,hadj⟩
    exact ((fundamentalCycle t E hE e he).adj_of_mem_edges
      (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hadj)).ne rfl⟩

/-- The union of the fundamental cycles is a subgraph of the underlying undirected graph of
`Realization.graph t E`. -/
theorem cyclicGraph_le (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) : cyclicGraph t E hE ≤ (graph t E).underlying := by
  intro u v ⟨e,he,hadj⟩
  exact (fundamentalCycle t E hE e he).adj_of_mem_edges
    (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hadj)

/-- At a vertex of the fundamental cycle of `e`, the edges of the union of the fundamental
cycles are those of this cycle, since the fundamental cycles are vertex-disjoint. -/
theorem cyclicGraph_adj_at_cycle {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) {v : ℕ}
    (hv : v ∈ (fundamentalCycle t E hE e he).support) (w : ℕ) :
    (cyclicGraph t E hE).Adj v w ↔ (fundamentalCycle t E hE e he).toSubgraph.Adj v w := by
  constructor
  · rintro ⟨f,hf,hadj⟩
    have hfv := SimpleGraph.Walk.mem_support_of_adj_toSubgraph hadj
    have hef : e = f := by
      by_contra hne
      exact Finset.disjoint_left.mp (fundamentalCycles_disjoint hE he hf hne)
        (List.mem_toFinset.mpr hv) (List.mem_toFinset.mpr hfv)
    subst f
    exact hadj
  · intro hadj
    exact ⟨e,he,hadj⟩

/-- In the union of the fundamental cycles, every non-isolated vertex has degree `2`
(`SimpleGraph.IsCycles`). -/
theorem cyclicGraph_isCycles (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) : (cyclicGraph t E hE).IsCycles := by
  intro v hv
  obtain ⟨w,hw⟩ := hv
  obtain ⟨e,he,hadj⟩ := hw
  have hmem := SimpleGraph.Walk.mem_support_of_adj_toSubgraph hadj
  have hneigh : (cyclicGraph t E hE).neighborSet v =
      (fundamentalCycle t E hE e he).toSubgraph.neighborSet v := by
    ext w
    exact cyclicGraph_adj_at_cycle hE he hmem w
  rw [hneigh]
  exact (fundamentalCycle_isCycle t E hE e he).ncard_neighborSet_toSubgraph_eq_two
    hmem

/-- The union of the fundamental cycles is locally finite: the neighbours of a vertex are
vertices of `Realization.graph t E`. -/
@[instance_reducible] noncomputable def cyclicGraphLocallyFinite (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) : (cyclicGraph t E hE).LocallyFinite := by
  intro v
  apply Set.Finite.fintype
  apply (graph t E).vertices.finite_toSet.subset
  intro w hw
  have hadj := cyclicGraph_le t E hE hw
  rcases hadj.2 with hf | hb
  · exact (graph_edge_endpoints t E hE.1 hf).2
  · exact (graph_edge_endpoints t E hE.1 hb).1

private theorem isCycles_walk_support_subset {G : SimpleGraph ℕ} [G.LocallyFinite]
    (hG : G.IsCycles) {z : ℕ} (d : G.Walk z z) (hd : d.IsCycle)
    {u v : ℕ} (p : G.Walk u v) (hu : u ∈ d.support) : p.support ⊆ d.support := by
  induction p with
  | nil =>
    intro w hw
    exact List.mem_singleton.mp hw ▸ hu
  | cons hadj p ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl | htail
    · exact hu
    · have hdadj := (hd.adj_toSubgraph_iff_of_isCycles hG (d.mem_verts_toSubgraph.mpr hu) _).mpr hadj
      have hnext := SimpleGraph.Walk.mem_support_of_adj_toSubgraph hdadj.symm
      exact ih hnext htail

private theorem isCycles_walk_edges_subset {G : SimpleGraph ℕ} [G.LocallyFinite]
    (hG : G.IsCycles) {z : ℕ} (d : G.Walk z z) (hd : d.IsCycle)
    {u v : ℕ} (p : G.Walk u v) (hu : u ∈ d.support) : p.edges ⊆ d.edges := by
  intro r hr
  obtain ⟨a,b⟩ := r
  have hamem := p.fst_mem_support_of_mem_edges hr
  have hadj := p.adj_of_mem_edges hr
  have ha := isCycles_walk_support_subset hG d hd p hu hamem
  exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp
    ((hd.adj_toSubgraph_iff_of_isCycles hG (d.mem_verts_toSubgraph.mpr ha) _).mpr hadj)

/-- In a locally finite graph whose non-isolated vertices all have degree `2`, two cycles
through a common vertex have the same edges. -/
theorem isCycles_cycle_edges_eq {G : SimpleGraph ℕ} [G.LocallyFinite]
    (hG : G.IsCycles) {u v x : ℕ} (c : G.Walk u u) (d : G.Walk v v)
    (hc : c.IsCycle) (hd : d.IsCycle) (hxc : x ∈ c.support) (hxd : x ∈ d.support) :
    c.edges.toFinset = d.edges.toFinset := by
  have hcsub : c.edges ⊆ d.edges := by
    intro r hr
    apply isCycles_walk_edges_subset hG d hd (c.rotate x hxc) hxd
    exact (c.rotate_edges x hxc).mem_iff.mpr hr
  have hdsub : d.edges ⊆ c.edges := by
    intro r hr
    apply isCycles_walk_edges_subset hG c hc (d.rotate x hxd) hxc
    exact (d.rotate_edges x hxd).mem_iff.mpr hr
  apply Finset.Subset.antisymm
  · intro r hr
    exact List.mem_toFinset.mpr (hcsub (List.mem_toFinset.mp hr))
  · intro r hr
    exact List.mem_toFinset.mpr (hdsub (List.mem_toFinset.mp hr))

/-- The level-1 condition for the canonical network: for a cycle-separated family `E`, two
cycles of `Realization.graph t E` with distinct edge sets are vertex-disjoint. Both cycles lie in
the union of the fundamental cycles, where two cycles through a common vertex have the same
edges. -/
theorem cycles_disjoint (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) (u v : ℕ)
    (c : (graph t E).underlying.Walk u u) (d : (graph t E).underlying.Walk v v)
    (hc : c.IsCycle) (hd : d.IsCycle) (hne : c.edges.toFinset ≠ d.edges.toFinset) :
    Disjoint c.support.toFinset d.support.toFinset := by
  classical
  let := cyclicGraphLocallyFinite t E hE
  -- Both cycles lie in the union of the fundamental cycles.
  have hcEdges : ∀ r, r ∈ c.edges → r ∈ (cyclicGraph t E hE).edgeSet := by
    intro r hr
    obtain ⟨e,he,hfund⟩ := cycle_edge_in_fundamental hE c hc hr
    obtain ⟨a,b⟩ := r
    change (cyclicGraph t E hE).Adj a b
    exact ⟨e,he,SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr hfund⟩
  have hdEdges : ∀ r, r ∈ d.edges → r ∈ (cyclicGraph t E hE).edgeSet := by
    intro r hr
    obtain ⟨e,he,hfund⟩ := cycle_edge_in_fundamental hE d hd hr
    obtain ⟨a,b⟩ := r
    change (cyclicGraph t E hE).Adj a b
    exact ⟨e,he,SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr hfund⟩
  rw [Finset.disjoint_left]
  intro x hxc hxd
  let cK := c.transfer (cyclicGraph t E hE) hcEdges
  let dK := d.transfer (cyclicGraph t E hE) hdEdges
  have hcK : cK.IsCycle := hc.transfer hcEdges
  have hdK : dK.IsCycle := hd.transfer hdEdges
  have hxcK : x ∈ cK.support := by simpa only [cK,SimpleGraph.Walk.support_transfer] using List.mem_toFinset.mp hxc
  have hxdK : x ∈ dK.support := by simpa only [dK,SimpleGraph.Walk.support_transfer] using List.mem_toFinset.mp hxd
  -- There, two cycles through the common vertex `x` have the same edges.
  have heq := isCycles_cycle_edges_eq (cyclicGraph_isCycles t E hE) cK dK hcK hdK hxcK hxdK
  exact hne (by simpa only [cK,dK,SimpleGraph.Walk.edges_transfer] using heq)

end Camus.Realization
