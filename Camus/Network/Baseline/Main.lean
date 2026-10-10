module

public import Camus.Network.Baseline.Clades

@[expose] public section

namespace Camus.Realization

theorem baseline_displays_iff (t : PhyloTree) (ht : t.WellLabelled) (q : Quartet) :
    (graph t ∅).DisplaysQuartet q ↔ q.induced t = true := by
  classical
  simp only [Quartet.induced, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  constructor
  · rintro ⟨hq, S, hS, edge, hedge, hsep⟩
    have hSeq := baseline_switching_unique t ht hS
    subst S
    change edge ∈ (graph t ∅).underlying.edgeSet at hedge
    obtain ⟨p, hp, hpnil, heq⟩ := (baseline_edgeSet t edge).mp hedge
    obtain ⟨sub, hnode⟩ := (PhyloTree.mem_nodes_iff _ _).mp hp
    refine ⟨hq, sub.taxa, (PhyloTree.clades_mem_iff t _).mpr ⟨p, sub, hnode, rfl⟩, ?_⟩
    apply (baselineCut_separates_iff ht hnode q hq).mp
    simpa only [baselineCutGraph, heq] using hsep
  · rintro ⟨hq, S, hclade, hcut⟩
    obtain ⟨p, sub, hnode, htaxa⟩ := (PhyloTree.clades_mem_iff t S).mp hclade
    have hpnil : p ≠ [] := by
      intro h
      subst p
      simp only [PhyloTree.nodeAt, Option.some.injEq] at hnode
      subst sub
      exact q.cutBy_not_whole S (htaxa ▸ hq) hcut
    have hp := (PhyloTree.mem_nodes_iff t p).mpr ⟨sub, hnode⟩
    have hempty : EdgeAbove.CycleSeparated t ∅ := by simp [EdgeAbove.CycleSeparated, Set.Pairwise]
    have htotal : (graph t ∅).Switching (graph t ∅).edges := by
      simpa only [graph, Finset.image_empty, Finset.union_empty] using (support t ht ∅ hempty).switching
    refine ⟨hq, (graph t ∅).edges, htotal, baselineCut p, ?_, ?_⟩
    · change baselineCut p ∈ (graph t ∅).underlying.edgeSet
      exact (baseline_edgeSet t _).mpr ⟨p, hp, hpnil, rfl⟩
    · apply (baselineCut_separates_iff ht hnode q hq).mpr
      simpa only [htaxa] using hcut


end Camus.Realization
