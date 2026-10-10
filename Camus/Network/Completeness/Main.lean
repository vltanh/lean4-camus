module

public import Camus.Network.Realization.Construction
public import Camus.Network.Baseline.Main
public import Camus.Network.Completeness.Footprints
public import Camus.Network.Completeness.Iso
public import Camus.Network.Completeness.Reduction
public import Camus.Network.Realization.Refinement
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Completeness: every network built on T is canonical

Adding an edge above each pair of a cycle-separated family `E` (Definition 3) gives a rooted
binary level-1 network built on `T`, the canonical network `Realization.graph t E`
(`Realization.levelOne`, `Realization.support`). This file proves the converse. Let `N` be a
rooted binary level-1 network and `H` a support subdivision of `T` in `N` with switching `S`. A
non-tree edge `d = (u', w')` gives the pair `H.pairOf d = (u, w)` of Definition 2, where `u` and
`w` are the vertices of `T` directly below `u'` and `w'`. The family `H.extracted` of these pairs
is cycle-separated, distinct non-tree edges give distinct pairs, and `N` is isomorphic to
`Realization.graph t H.extracted`. So every level-1 network built on `T` arises by adding edges
above pairs; the proof of Theorem 1 relies on this when it says that an added edge of an optimal
network "is added above the pair `(a, b)`". The file also makes the network `T + e` of
Section 2.1 precise. Theorem 1, Lemmas 1 and 2, and Section 2.4 use these results.

## Main results

* `SupportSubdivision.extracted_separated`: the extracted family is cycle-separated.
* `SupportSubdivision.pairOf_injective`: distinct non-tree edges give distinct pairs.
* `SupportSubdivision.canonical_iso`: `N` is isomorphic to `Realization.graph t H.extracted`.
* `SupportSubdivision.single_edge_reduction`: for a non-tree edge `d`, `N` without the other
  non-tree edges is a subdivision of `Realization.graph t {H.pairOf d}`, so `T + d` is this
  canonical network.

## Proof outline

1. A switching is a spanning tree of `N` (`RootedNetwork.switching_existsUnique_path`). Each
   non-tree edge closes a cycle with it, and the cycles of distinct non-tree edges are disjoint
   since `N` is level-1 (`RootedNetwork.fundamentalCycles_disjoint`).
2. Degree counting puts both endpoints of a non-tree edge inside wires
   (`SupportSubdivision.deleted_source_anchor_spec`,
   `SupportSubdivision.deleted_target_anchor_spec`), and their anchors form an admissible pair
   (`SupportSubdivision.deleted_pair_admissible`).
3. The footprint of the pair lies on the cycle of the edge
   (`SupportSubdivision.footprint_mem_fundamentalCycle`). So the footprints of distinct pairs are
   disjoint, and distinct non-tree edges give distinct pairs.
4. The encoding of the vertices of `N` (`SupportSubdivision.vertexEquiv`) maps each wire of `N`
   to the canonical wire, with the endpoints in the same order
   (`SupportSubdivision.map_wire_eq`), so it is an isomorphism (`SupportSubdivision.canonicalIso`).
5. For `T + d`, the support of `Realization.graph t H.extracted` is a subdivision of the support
   of `Realization.graph t {H.pairOf d}` (`Realization.singletonSupportSubdivision`). Adding the
   edge of `H.pairOf d` to both and decoding shows that `N` restricted to the edges `S ∪ {d}` is
   a subdivision of `Realization.graph t {H.pairOf d}`
   (`SupportSubdivision.transport_single_refinement`).
-/

@[expose] public section

namespace Camus

namespace SupportSubdivision

/-- The extracted family `H.extracted` of a rooted binary level-1 network `N` is cycle-separated
(`EdgeAbove.CycleSeparated`): its pairs are admissible, and distinct pairs have disjoint
footprints. Each footprint lies on the cycle of its non-tree edge, and these cycles are
disjoint. -/
theorem extracted_separated {t : PhyloTree}
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) :
    EdgeAbove.CycleSeparated t H.extracted := by
  classical
  refine ⟨H.extracted_subset_candidates hN, ?_⟩
  intro p hp q hq hpq
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
  have hef : e ≠ f := by
    intro hef
    subst f
    exact hpq rfl
  apply Finset.disjoint_left.mpr
  intro x hxe hxf
  exact Finset.disjoint_left.mp
    (RootedNetwork.fundamentalCycles_disjoint hN H.switching he hf hef)
    (List.mem_toFinset.mpr (H.footprint_mem_fundamentalCycle hN he hxe))
    (List.mem_toFinset.mpr (H.footprint_mem_fundamentalCycle hN hf hxf))

/-- Distinct non-tree edges of `N` have distinct pairs `(u, w)` (Definition 2). The target
`lca(u, w)` lies on `γ(u, w)`, hence on the cycle of every non-tree edge with pair `(u, w)`, and
the cycles of distinct non-tree edges are disjoint. -/
theorem pairOf_injective {t : PhyloTree}
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) :
    Set.InjOn H.pairOf (N.edges \ S) := by
  classical
  intro e he f hf hpair
  have he' : e ∈ (N.edges \ S : Finset (ℕ × ℕ)) := by simpa using he
  have hf' : f ∈ (N.edges \ S : Finset (ℕ × ℕ)) := by simpa using hf
  by_contra hef
  have hmem := EdgeAbove.target_mem_footprint t (H.pairOf e)
    (H.deleted_pair_admissible hN he')
  have hmem' : EdgeAbove.target (H.pairOf e) ∈ EdgeAbove.footprint t (H.pairOf f) := by
    rw [← hpair]
    exact hmem
  exact Finset.disjoint_left.mp
    (RootedNetwork.fundamentalCycles_disjoint hN H.switching he' hf' hef)
    (List.mem_toFinset.mpr (H.footprint_mem_fundamentalCycle hN he' hmem))
    (List.mem_toFinset.mpr (H.footprint_mem_fundamentalCycle hN hf' hmem'))

/-- A rooted binary level-1 network `N` with a support subdivision `H` of `T` is isomorphic, as a
rooted network with labelled leaves, to the canonical network `Realization.graph t H.extracted`
of its extracted pairs. With `SupportSubdivision.extracted_separated`, this shows that every
network built on `T` is obtained, up to isomorphism, by adding edges above the pairs of a
cycle-separated family (Definition 3). -/
theorem canonical_iso {t : PhyloTree}
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) :
    Nonempty (N.Iso (Realization.graph t H.extracted)) := by
  have hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)) := by
    simpa using pairOf_injective hN H
  exact ⟨H.canonicalIso hN hpairs (extracted_separated hN H)⟩

/-- Section 2.1: the network `T + d`, for a non-tree edge `d`. Removing the other non-tree edges
from `N` gives the network on the vertices of `N` with edges `S ∪ {d}`. It is a subdivision of
the canonical network `Realization.graph t {H.pairOf d}` of the single pair `H.pairOf d`:
suppressing the interior vertices of its wires, which are its vertices of indegree and outdegree
one, gives back `Realization.graph t {H.pairOf d}`. So `T + d` is this canonical network. -/
theorem single_edge_reduction {t : PhyloTree}
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S)
    {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    Nonempty (GraphSubdivision (Realization.graph t {H.pairOf e})
      {N with edges := insert e S}) := by
  classical
  have hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)) := by
    simpa using pairOf_injective hN H
  have hsep := extracted_separated hN H
  have hpair : H.pairOf e ∈ H.extracted := Finset.mem_image.mpr ⟨e,he,rfl⟩
  exact H.transport_single_refinement hN hpairs hsep he
    (Realization.singletonSupportSubdivision hsep hpair)
    (Realization.singletonSupportSubdivision_original hsep hpair)

end SupportSubdivision

end Camus
