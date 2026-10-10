module

public import Camus.Network.Baseline.Main
public import Camus.Network.Completeness.Reachability
public import Camus.Network.Realization.Construction
public import Camus.Network.SingleEdge

/-!
# The clades of the support switching

The canonical network `Realization.graph t E` of a cycle-separated family `E` has the switching
`Realization.supportEdges t E` that keeps the subdivided edges of `T` and leaves out the added
edges. Its clades are those of `T`: the clade below the vertex `p` of `T`, or below a fresh vertex
on the edge above `p`, is the clade of `p` in `T` (`Realization.cladeBelow_support_code`,
`Realization.cladeBelow_support_interior`). The cone below `p` is closed under the support edges
(`Realization.below_support_closed`), and `p` reaches the leaves of its subtree along them
(`SupportSubdivision.original_reachable_of_prefix`).

## Main results

* `Realization.cladeBelow_support_code`: the clade below a vertex of `T`.
* `Realization.cladeBelow_support_interior`: the clade below a fresh vertex.
* `Realization.taxaAt_mem_clades`: the clade of a vertex of `T` is a clade of `T`.
-/

@[expose] public section

namespace Camus

namespace Realization

variable {t : PhyloTree} {E : Finset Pair}

/-- In the support switching of `Realization.graph t E`, the clade below the vertex `p` of `T` is
the clade of `p` in `T`. -/
theorem cladeBelow_support_code (ht : t.WellLabelled) (hE : EdgeAbove.CycleSeparated t E)
    {p : Address} (hp : p ∈ t.nodes) :
    (graph t E).cladeBelow (supportEdges t E) (Address.code p) = t.taxaAt p := by
  classical
  obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff p).mp hp
  ext a
  simp only [RootedNetwork.cladeBelow, Finset.mem_filter, PhyloTree.taxaAt, hsub]
  change a ∈ t.taxa ∧ Relation.ReflTransGen (fun u v => (u, v) ∈ supportEdges t E)
      (Address.code p) (Address.code (leafAddress t a)) ↔ a ∈ sub.taxa
  constructor
  · rintro ⟨ha, hreach⟩
    -- the cone below `p` is closed under the support edges
    have hcone : ∀ w, Relation.ReflTransGen (fun u v => (u, v) ∈ supportEdges t E)
        (Address.code p) w → Below t E p w := by
      intro w hw
      induction hw with
      | refl => exact (below_code_iff hp).mpr (List.prefix_refl p)
      | tail _ hstep ih => exact below_support_closed hE.1 ih hstep
    have hbelow := hcone _ hreach
    rw [below_code_iff (leafAddress_mem_nodes ha)] at hbelow
    exact (PhyloTree.subtree_taxa_iff_prefix ht hsub ha).mpr hbelow
  · intro ha
    have hat : a ∈ t.taxa := PhyloTree.subtree_taxa_subset hsub ha
    exact ⟨hat, (support t ht E hE).original_reachable_of_prefix (leafAddress_mem_nodes hat)
      ((PhyloTree.subtree_taxa_iff_prefix ht hsub hat).mp ha)⟩

/-- In the support switching of `Realization.graph t E`, the clade below a fresh vertex on the
edge above the vertex `q` of `T` is the clade of `q` in `T`. -/
theorem cladeBelow_support_interior (ht : t.WellLabelled) (hE : EdgeAbove.CycleSeparated t E)
    {q : Address} (hq : q ∈ t.nodes) (hq0 : q ≠ []) {v : ℕ}
    (hv : v ∈ wireInterior (wire t E q)) :
    (graph t E).cladeBelow (supportEdges t E) v = t.taxaAt q := by
  classical
  rw [← cladeBelow_support_code ht hE hq]
  ext a
  simp only [RootedNetwork.cladeBelow, Finset.mem_filter]
  refine and_congr_right fun ha => ?_
  change Relation.ReflTransGen (fun u w => (u, w) ∈ supportEdges t E) v
      (Address.code (leafAddress t a)) ↔
    Relation.ReflTransGen (fun u w => (u, w) ∈ supportEdges t E) (Address.code q)
      (Address.code (leafAddress t a))
  constructor
  · intro hreach
    have hcone : ∀ w, Relation.ReflTransGen (fun u v => (u, v) ∈ supportEdges t E) v w →
        Below t E q w := by
      intro w hw
      induction hw with
      | refl => exact (below_interior_iff hE.1 hv).mpr (List.prefix_refl q)
      | tail _ hstep ih => exact below_support_closed hE.1 ih hstep
    have hbelow := hcone _ hreach
    rw [below_code_iff (leafAddress_mem_nodes ha)] at hbelow
    exact (support t ht E hE).original_reachable_of_prefix (leafAddress_mem_nodes ha) hbelow
  · -- the fresh vertex reaches the end of its wire, `q`
    intro hreach
    exact ((support t ht E hE).wire_reachable_to_last hq hq0
      (mem_wire.mpr (Or.inr (Or.inl hv)))).trans hreach

/-- The clade of a vertex of `T` is a clade of `T`. -/
theorem taxaAt_mem_clades {p : Address} (hp : p ∈ t.nodes) : t.taxaAt p ∈ t.clades := by
  obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff p).mp hp
  rw [PhyloTree.clades_mem_iff]
  exact ⟨p, sub, hsub, by simp [PhyloTree.taxaAt, hsub]⟩

end Realization

end Camus
