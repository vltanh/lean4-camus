module

public import Camus.GraphSubdivisionCuts
public import Camus.GraphBaselineClades

@[expose] public section

namespace Camus

theorem GraphSubdivision.displays_iff {P N : RootedNetwork}
    (hP : P.RootedBinaryLevelOne) (H : GraphSubdivision P N) (q : Quartet) :
    N.DisplaysQuartet q ↔ P.DisplaysQuartet q := by
  classical
  constructor
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
