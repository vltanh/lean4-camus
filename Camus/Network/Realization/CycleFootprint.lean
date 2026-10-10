module

public import Camus.Network.Realization.CycleWires

/-!
# The canonical network of an edge family: vertices of the cycles

For `(u, w)` in a cycle-separated family `E`, every vertex of the fundamental cycle `γ(u, w)` is
a vertex of `T` in the footprint of `(u, w)`, or `u′`, or `w′`: it is in
`Realization.cycleVertices t (u, w)` (`Realization.fundamentalCycle_support_subset`). The proof
restricts the undirected support graph to these vertices (`Realization.cycleSupportGraph`),
joins `w′` and `u′` through `lca(u, w)` in the restriction, along the support edges found in
`Camus/Network/Realization/CycleWires.lean`, and concludes by uniqueness of paths in the support
tree. Since the footprints of distinct pairs are disjoint and distinct pairs have distinct fresh
vertices, the cycles of distinct pairs are vertex-disjoint
(`Realization.fundamentalCycles_disjoint`).

## Main results

* `Realization.fundamentalCycle_support_subset`: the vertices of `γ(u, w)` are in the footprint
  of `(u, w)` or are `u′` or `w′`.
* `Realization.cycleVertices_disjoint`: these vertex sets are disjoint for distinct pairs.
* `Realization.fundamentalCycles_disjoint`: the fundamental cycles of distinct pairs are
  vertex-disjoint.
-/

@[expose] public section

namespace Camus.Realization

/-- The undirected support graph of `Realization.graph t E` restricted to
`Realization.cycleVertices t e`: the footprint of `e = (u, w)` together with `u′` and `w′`. -/
noncomputable def cycleSupportGraph (t : PhyloTree) (E : Finset Pair) (e : Pair) : SimpleGraph ℕ
    where
  Adj u v := ({graph t E with edges := supportEdges t E}).underlying.Adj u v ∧
    u ∈ cycleVertices t e ∧ v ∈ cycleVertices t e
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro v h; exact h.1.1 rfl⟩

/-- The restricted support graph is a subgraph of the support graph. -/
theorem cycleSupportGraph_le (t : PhyloTree) (E : Finset Pair) (e : Pair) :
    cycleSupportGraph t E e ≤ ({graph t E with edges := supportEdges t E}).underlying :=
  fun _ _ h => h.1

/-- A vertex of the footprint of `e` is in `Realization.cycleVertices t e`. -/
theorem code_mem_cycleVertices_of_footprint {t : PhyloTree} {e : Pair} {p : Address}
    (hp : p ∈ EdgeAbove.footprint t e) : Address.code p ∈ cycleVertices t e :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩)

/-- For a cycle-separated family, a support edge between two vertices of
`Realization.cycleVertices t e` is an edge of the restricted support graph. -/
theorem cycleSupportGraph_adj_of_support {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} {u v : ℕ}
    (huv : (u,v) ∈ supportEdges t E) (hu : u ∈ cycleVertices t e) (hv : v ∈ cycleVertices t e) :
    (cycleSupportGraph t E e).Adj u v :=
  ⟨⟨graph_edge_ne hE (Finset.mem_union_left _ huv),Or.inl huv⟩,hu,hv⟩

/-- For `(u, w)` in a cycle-separated family, every vertex of the footprint is joined to
`lca(u, w)` in the restricted support graph, by edges `parent(q) → q`, `q` in the footprint. -/
theorem original_cycle_connected {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) {p : Address}
    (hp : p ∈ EdgeAbove.footprint t e) :
    (cycleSupportGraph t E e).Reachable (Address.code (EdgeAbove.target e)) (Address.code p) := by
  have ha := (Finset.mem_filter.mp (hE.1 he)).2
  have hall : ∀ n, ∀ p : Address, p.length = n → p ∈ EdgeAbove.footprint t e →
      (cycleSupportGraph t E e).Reachable (Address.code (EdgeAbove.target e)) (Address.code p) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hlen hp
      by_cases hp0 : p = EdgeAbove.target e
      · rw [hp0]
      · have hnonroot : p ≠ [] := by
          intro h
          have hprefix := (Finset.mem_filter.mp hp).2.1
          have hzero : (EdgeAbove.target e).length = 0 := by simpa [h] using hprefix.length_le
          have ht := List.length_eq_zero_iff.mp hzero
          exact hp0 (h.trans ht.symm)
        have hparent : parent p ∈ EdgeAbove.footprint t e :=
          ((EdgeAbove.footprint_region t e ha).2.2 p hp).2 (parent p)
            (prefix_parent_of_ne (Finset.mem_filter.mp hp).2.1 (Ne.symm hp0)) (parent_prefix p)
        have hplen : (parent p).length < n := by
          have hpos := List.length_pos_iff.mpr hnonroot
          simp only [parent,List.length_take]
          omega
        have hreach := ih _ hplen (parent p) rfl hparent
        exact hreach.trans (SimpleGraph.Adj.reachable
          (cycleSupportGraph_adj_of_support hE (internal_cycle_parent_edge hE he hp hp0)
            (code_mem_cycleVertices_of_footprint hparent) (code_mem_cycleVertices_of_footprint hp)))
  exact hall p.length p rfl hp

/-- For `(u, w)` in a cycle-separated family, `u′` is joined to `lca(u, w)` in the restricted
support graph: by the edge `u′ → u` if `u = lca(u, w)`, through `parent(u)` otherwise. -/
theorem donor_cycle_connected {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) :
    (cycleSupportGraph t E e).Reachable (Address.code (EdgeAbove.target e)) (donor t e) := by
  classical
  have ha := (Finset.mem_filter.mp (hE.1 he)).2
  have hd : donor t e ∈ cycleVertices t e := by simp [cycleVertices]
  by_cases hghost : EdgeAbove.target e = e.1
  · have hroot : Address.code e.1 ∈ cycleVertices t e :=
      code_mem_cycleVertices_of_footprint (hghost ▸ EdgeAbove.target_mem_footprint t e ha)
    rw [hghost]
    exact (SimpleGraph.Adj.reachable
      (cycleSupportGraph_adj_of_support hE (ghost_boundary_edge hE he hghost) hd hroot)).symm
  · have hparent := donor_parent_mem_footprint ha hghost
    exact (original_cycle_connected hE he hparent).trans (SimpleGraph.Adj.reachable
      (cycleSupportGraph_adj_of_support hE (donor_boundary_edge hE he hghost)
        (code_mem_cycleVertices_of_footprint hparent) hd))

/-- For `(u, w)` in a cycle-separated family, `w′` is joined to `lca(u, w)` in the restricted
support graph, through `parent(w)`. -/
theorem recipient_cycle_connected {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) :
    (cycleSupportGraph t E e).Reachable (Address.code (EdgeAbove.target e)) (recipient t e) := by
  classical
  have ha := (Finset.mem_filter.mp (hE.1 he)).2
  have hparent := recipient_parent_mem_footprint ha
  have hr : recipient t e ∈ cycleVertices t e := by simp [cycleVertices]
  exact (original_cycle_connected hE he hparent).trans (SimpleGraph.Adj.reachable
    (cycleSupportGraph_adj_of_support hE (recipient_boundary_edge hE he)
      (code_mem_cycleVertices_of_footprint hparent) hr))

/-- A walk of the restricted support graph that starts in `Realization.cycleVertices t e`
stays in it. -/
theorem cycleSupportGraph_walk_support {t : PhyloTree} {E : Finset Pair} {e : Pair}
    {u v : ℕ} (p : (cycleSupportGraph t E e).Walk u v)
    (hu : u ∈ cycleVertices t e) : p.support.toFinset ⊆ cycleVertices t e := by
  intro w hw
  have hw := List.mem_toFinset.mp hw
  induction p with
  | nil => exact List.mem_singleton.mp hw ▸ hu
  | cons hadj p ih =>
    rcases List.mem_cons.mp hw with rfl | htail
    · exact hu
    · exact ih hadj.2.2 (List.mem_toFinset.mpr htail) htail

/-- For `(u, w)` in a cycle-separated family, the support path from `w′` to `u′` stays in
`Realization.cycleVertices t (u, w)`: there is such a path in the restricted support graph, and
paths in the support tree are unique. -/
theorem cycleSupportPath_support_subset (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) (e : Pair) (he : e ∈ E) :
    (cycleSupportPath t E hE e he).val.support.toFinset ⊆ cycleVertices t e := by
  classical
  let p := ((recipient_cycle_connected hE he).symm.trans (donor_cycle_connected hE he)).some.toPath
  let pS := p.val.mapLe (cycleSupportGraph_le t E e)
  have hPS : pS.IsPath := p.isPath.mapLe _
  have heq : pS = (cycleSupportPath t E hE e he).val :=
    Subtype.mk.inj ((support_acyclic t E hE).subsingleton_path _ _ |>.elim
      ⟨pS,hPS⟩ (cycleSupportPath t E hE e he))
  rw [←heq, SimpleGraph.Walk.support_mapLe_eq_support]
  exact cycleSupportGraph_walk_support p.val (by simp [cycleVertices])

/-- For `(u, w)` in a cycle-separated family `E`, every vertex of the fundamental cycle
`γ(u, w)` is in `Realization.cycleVertices t (u, w)`: it is a vertex of the footprint of
`(u, w)`, or `u′`, or `w′`. -/
theorem fundamentalCycle_support_subset (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) (e : Pair) (he : e ∈ E) :
    (fundamentalCycle t E hE e he).support.toFinset ⊆ cycleVertices t e := by
  intro v hv
  change v ∈ (donor t e ::
    ((cycleSupportPath t E hE e he).val.mapLe (support_underlying_le t E)).support).toFinset at hv
  have hmem : v = donor t e ∨ v ∈ (cycleSupportPath t E hE e he).val.support := by
    simpa only [SimpleGraph.Walk.support_mapLe_eq_support, List.mem_toFinset, List.mem_cons] using
        hv
  rcases hmem with rfl | hmem
  · simp [cycleVertices]
  · exact cycleSupportPath_support_subset t E hE e he (List.mem_toFinset.mpr hmem)

/-- For distinct pairs `e ≠ f` of a cycle-separated family, `Realization.cycleVertices t e` and
`Realization.cycleVertices t f` are disjoint. -/
theorem cycleVertices_disjoint {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e f : Pair} (he : e ∈ E) (hf : f ∈ E) (hef : e ≠ f) :
    Disjoint (cycleVertices t e) (cycleVertices t f) := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hw
  simp only [cycleVertices, Finset.mem_union, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton] at hv hw
  rcases hv with ⟨p,hp,hpc⟩ | hd | hr <;> rcases hw with ⟨q,hq,hqc⟩ | hd' | hr'
  · have hpq := Address.code_injective (hpc.trans hqc.symm)
    exact Finset.disjoint_left.mp (hE.2 he hf hef) hp (hpq.symm ▸ hq)
  · exact donor_ne_code f (Finset.mem_filter.mp hp).1 (hd'.symm.trans hpc.symm)
  · exact recipient_ne_code f (Finset.mem_filter.mp hp).1 (hr'.symm.trans hpc.symm)
  · exact donor_ne_code e (Finset.mem_filter.mp hq).1 (hd.symm.trans hqc.symm)
  · exact hef (donor_injective t (hE.1 he) (hE.1 hf) (hd.symm.trans hd'))
  · exact donor_ne_recipient t e f (hd.symm.trans hr')
  · exact recipient_ne_code e (Finset.mem_filter.mp hq).1 (hr.symm.trans hqc.symm)
  · exact donor_ne_recipient t f e (hd'.symm.trans hr)
  · exact hef (recipient_injective t (hE.1 he) (hE.1 hf) (hr.symm.trans hr'))

/-- For distinct pairs `e ≠ f` of a cycle-separated family `E`, the fundamental cycles of `e`
and of `f` in `Realization.graph t E` are vertex-disjoint. -/
theorem fundamentalCycles_disjoint {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e f : Pair} (he : e ∈ E) (hf : f ∈ E) (hef : e ≠ f) :
    Disjoint (fundamentalCycle t E hE e he).support.toFinset
      (fundamentalCycle t E hE f hf).support.toFinset :=
  Finset.disjoint_of_subset_left (fundamentalCycle_support_subset t E hE e he)
    (Finset.disjoint_of_subset_right (fundamentalCycle_support_subset t E hE f hf)
      (cycleVertices_disjoint hE he hf hef))

end Camus.Realization
