module

public import Camus.Network.Subdivision.Cuts
public import Camus.Network.Baseline.Clades

/-!
# Subdividing edges does not change the displayed quartets

Section 2.1 defines `T + e` as the subnetwork of `N` obtained by removing all other non-tree edges
and then suppressing the vertices of indegree and outdegree one. This file shows that the
suppression does not change the displayed quartets. If `N` is obtained from a rooted binary level-1
network `P` by subdividing edges (`GraphSubdivision P N`: each edge of `P` becomes a directed path,
its wire, through fresh vertices; root and labelled leaves are kept), then `N` and `P` display the
same quartets. The theorem is applied, mainly in the proof of Lemma 1, to subnetworks of a network
built on `T` that are subdivisions of `T + e` (`SupportSubdivision.single_edge_reduction`) or of `T`
itself (`SupportSubdivision.baseline_subdivision`).

## Main results

* `GraphSubdivision.displays_iff`: a subdivision of `P` displays the same quartets as `P`.

## Proof outline

Call an edge of `P` active for a set `B` of arcs of `N` if its whole wire lies in `B`.

1. For a switching `B` of `N`, the active edges form a switching of `P`
   (`GraphSubdivision.active_switching`). Conversely, every switching `R` of `P` is the set of
   active edges of a switching of `N`, its lift (`GraphSubdivision.lift_switching`,
   `GraphSubdivision.active_lift`).
2. Deleting from `B` an arc on the wire of an edge `e` of `P` separates the same quartets as
   deleting `e` from the active edges (`GraphSubdivision.separates_cut_iff`). This step uses that
   `P` is acyclic; see `SubdivisionCounterexample.antiparallel_cut_counterexample`.
3. If `N` displays `q` through a switching `B` and the deletion of an arc on the wire of `e`, then
   `e` is active: otherwise deleting `e` changes nothing, and the switching of `P` formed by the
   active edges is connected (`RootedNetwork.switching_connected_vertices`), so it separates no
   quartet. If `P` displays `q` through a switching `R` and the deletion of `e ∈ R`, then `N`
   displays `q` through the lift of `R` and the deletion of the terminal arc of the wire of `e`.
-/

@[expose] public section

namespace Camus

/-- Subdividing edges does not change the displayed quartets. Let `P` be a rooted binary level-1
network and `N` a subdivision of `P` (`GraphSubdivision P N`). Then `N` displays a quartet `q` if
and only if `P` displays `q`. This makes the suppression of the vertices of indegree and outdegree
one in the paper's `T + e` (Section 2.1) harmless. -/
theorem GraphSubdivision.displays_iff {P N : RootedNetwork}
    (hP : P.RootedBinaryLevelOne) (H : GraphSubdivision P N) (q : Quartet) :
    N.DisplaysQuartet q ↔ P.DisplaysQuartet q := by
  classical
  constructor
  -- `N` displays `q`: the active edges of the switching, cut at the edge of `P` whose wire carries
  -- the deleted arc, display `q` in `P`
  · rintro ⟨hq, B, hB, edge, hedge, hsep⟩
    rw [H.taxa_preserved] at hq
    obtain ⟨arc, harcB, heq⟩ := edgeSet_arc_exists {N with edges := B} hedge
    have harcN := hB.1 harcB
    rw [H.edges_covered] at harcN
    obtain ⟨e, he, harc⟩ := Finset.mem_biUnion.mp harcN
    have hR := H.active_switching hB
    have hsepP : P.Separates (({P with edges := H.active B}).underlying.deleteEdges {s(e.1,e.2)}) q := by
      apply (H.separates_cut_iff hP hB.1 he harc q hq).mp
      simpa only [heq] using hsep
    -- the cut edge `e` is active: otherwise the cut leaves the connected switching of `P` intact
    have heR : e ∈ H.active B := by
      by_contra hnot
      have hgraph : ({P with edges := H.active B}).underlying.deleteEdges {s(e.1,e.2)} =
          ({P with edges := H.active B}).underlying := by
        rw [underlying_eraseArc, source_eraseArc hP hR.1 he, Finset.erase_eq_of_notMem hnot]
      rw [hgraph] at hsepP
      obtain ⟨a, ha⟩ := q.sides_nonempty.1
      obtain ⟨b, hb⟩ := q.sides_nonempty.2
      have haP := hq (q.sides_subset_taxa.1 ha)
      have hbP := hq (q.sides_subset_taxa.2 hb)
      exact hsepP.2.2 a ha b hb (RootedNetwork.switching_connected_vertices hP hR
        (H.leaves_left a haP) (H.leaves_left b hbP))
    refine ⟨hq, H.active B, hR, s(e.1,e.2), ?_, hsepP⟩
    exact ⟨RootedNetwork.edge_ne hP he, Or.inl heR⟩
  -- `P` displays `q`: lift the switching to `N` and cut the terminal arc of the cut edge's wire
  · rintro ⟨hq, R, hR, edge, hedge, hsep⟩
    obtain ⟨e, heR, heq⟩ := edgeSet_arc_exists {P with edges := R} hedge
    have he := hR.1 heR
    let B := H.liftSwitching R
    have hB : N.Switching B := H.lift_switching hR
    have hactive : H.active B = R := H.active_lift hR
    have hterm := H.terminal_spec he
    have htermB : H.terminal e ∈ B := (H.terminal_mem_lift hR.1 he).mpr heR
    have hneq : (H.terminal e).1 ≠ (H.terminal e).2 := by
      intro h
      have hidx := wire_edge_idxOf (H.wire_laws e he).2.1 hterm.1
      rw [h] at hidx
      omega
    refine ⟨by simpa only [H.taxa_preserved] using hq, B, hB,
      s((H.terminal e).1,(H.terminal e).2), ⟨hneq, Or.inl htermB⟩, ?_⟩
    apply (H.separates_cut_iff hP hB.1 he hterm.1 q hq).mpr
    simpa only [hactive, heq] using hsep

end Camus
