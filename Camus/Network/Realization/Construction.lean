module

public import Camus.Network.Realization.Cactus
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The canonical network of an edge family: construction

Definition 3 adds an edge above a pair `(u, w)` of vertices of `T`: a vertex `u′` is placed on
the edge above `u`, a vertex `w′` on the edge above `w`, and the edge `u′ → w′` is added. The
canonical network `Realization.graph t E` (defined in `Camus/Defs.lean`) does this for all pairs
of a family `E` at once: the edge above each vertex `p` of `T` becomes a directed path, the wire
above `p`, through the fresh vertices placed on it. This file assembles the proof that the
construction gives a valid network. Let `T` be well-labelled, and let `E` be a family of
admissible pairs whose cycle footprints are pairwise disjoint (`EdgeAbove.CycleSeparated t E`).
Then `Realization.graph t E` is a rooted binary level-1 network; `T` is a root-preserving
support subdivision of it, so that the network is built on `T`; and the pairs read off its
non-tree edges are the pairs of `E`.

## Main results

* `Realization.levelOne`: `Realization.graph t E` is a rooted binary level-1 network.
* `Realization.support`: `T` is a root-preserving support subdivision of `Realization.graph t E`:
  the vertex `p` of `T` is `Address.code p`, the edge above `p` is replaced by the wire above
  `p`, and the wire edges form a switching of the network. With `Realization.levelOne`, the
  network is built on `T` (`RootedNetwork.AnchoredExtension`).
* `Realization.extracted_eq`: the pairs extracted through this subdivision (for each non-tree
  edge, the vertices of `T` just below its two ends, as in Procedure ASSIGN of Definition 2) are
  the pairs of `E`.

Conversely, every network built on `T` is isomorphic to the canonical network of its extracted
pairs (`SupportSubdivision.canonical_iso`).
-/

@[expose] public section

namespace Camus

namespace Realization

/-- For a well-labelled `T` and a cycle-separated family `E`, `T` is a root-preserving support
subdivision of `Realization.graph t E` with switching `Realization.supportEdges t E`: the vertex
`p` of `T` is `Address.code p`, and the edge above `p` is replaced by the wire
`Realization.wire t E p`. -/
noncomputable def support (t : PhyloTree) (ht : t.WellLabelled)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    SupportSubdivision t (graph t E) (supportEdges t E) := by
  classical
  refine
    { original := Address.code
      wire := wire t E
      original_injective := Address.code_injective.injOn
      root_preserved := rfl
      taxa_preserved := rfl
      leaves_preserved := ?_
      wire_laws := ?_
      interiors_disjoint := ?_
      vertices_covered := vertices_covered t E hE.1
      edges_covered := rfl
      switching := support_switching t E hE.1 }
  · intro p hp a hleaf
    change Address.code p = Address.code (leafAddress t a)
    rw [leafAddress_eq ht hleaf]
  · intro p hp hp0
    exact ⟨wire_length t E p, wire_nodup t E hE.1 hp hp0,
      wire_head t E p, wire_last t E p, wireInterior_disjoint_original t E p⟩
  · intro p hp q hq hpq
    exact interiors_disjoint t E hE.1 hpq

/-- Definition 3 gives a valid network: for a well-labelled `T` and a cycle-separated family
`E`, `Realization.graph t E` is a rooted binary level-1 network. -/
theorem levelOne (t : PhyloTree) (ht : t.WellLabelled)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    (graph t E).RootedBinaryLevelOne :=
  levelOne_of_cycle_disjoint t ht E hE (cycles_disjoint t E hE)

/-- For a well-labelled `T` and a cycle-separated family `E`, the pairs extracted from
`Realization.graph t E` through the subdivision `Realization.support` are the pairs of `E`: the
non-tree edges are the added edges `u′ → w′`, and `u′` and `w′` are inside the wires above `u`
and above `w`. -/
theorem extracted_eq (t : PhyloTree) (ht : t.WellLabelled)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    (support t ht E hE).extracted = E := by
  classical
  -- The added edge `u′ → w′` of `(u, w)` has the anchors `u` and `w`.
  have hpair : ∀ e ∈ E,
      (support t ht E hE).pairOf (donor t e, recipient t e) = e := by
    intro e he
    have ha := (Finset.mem_filter.mp (hE.1 he)).2
    have hd := (support t ht E hE).anchor_eq ha.1 ha.2.2.1
      ((donor_mem_wireInterior_iff hE.1 he).mpr rfl)
    have hr := (support t ht E hE).anchor_eq ha.2.1 ha.2.2.2.1
      ((recipient_mem_wireInterior_iff hE.1 he).mpr rfl)
    exact Prod.ext hd hr
  -- The non-tree edges are the added edges.
  unfold SupportSubdivision.extracted
  rw [nonSupportEdges t E hE.1, Finset.image_image]
  calc
    _ = E.image id := Finset.image_congr hpair
    _ = E := Finset.image_id


end Realization

end Camus
