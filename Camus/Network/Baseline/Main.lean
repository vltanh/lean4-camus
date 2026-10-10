module

public import Camus.Network.Baseline.Clades

/-!
# The quartets displayed by `T` are `Q(T)`

Definition 1 defines the quartets `Q(t)` induced in a tree `t`, and the quartets `Q(N_r)` of a
network through its displayed trees. The formalization describes them in two ways: through
switchings and edge cuts for networks (`RootedNetwork.DisplaysQuartet`), and through clades for
trees (`Quartet.induced`: some clade of `t` contains one pair of the quartet and avoids the other).
This file shows that the two agree on `T`, viewed as the canonical network of the empty family,
`Realization.graph t ∅`. So `Q(T)` is the set of quartets displayed by `T`, and a quartet satisfied
by a network built on `T` (`q ∈ Q(N_r) \ Q(T)`) is one that the network displays and `T` does not
induce.

## Main results

* `Realization.baseline_displays_iff`: `Realization.graph t ∅` displays `q` if and only if `q` is
  induced in `t`.

## Proof outline

The only switching of `T` is `T` itself (`Realization.baseline_switching_unique`), its edges are the
edges above its non-root vertices (`Realization.baseline_edgeSet`), and deleting the edge above `p`
separates `q` if and only if the clade of `T_p` induces the split of `q`
(`Realization.baselineCut_separates_iff`). The root has no edge above it, and its clade, the whole
taxon set, induces no quartet (`Quartet.cutBy_not_whole`).
-/

@[expose] public section

namespace Camus.Realization

/-- The quartets displayed by `T`. For a well-labelled tree `t`, the canonical network of the empty
family, `Realization.graph t ∅`, displays a quartet `q` if and only if `q` is induced in `t`
(`Quartet.induced`), that is, `q ∈ Q(t)` (Definition 1). -/
theorem baseline_displays_iff (t : PhyloTree) (ht : t.WellLabelled) (q : Quartet) :
    (graph t ∅).DisplaysQuartet q ↔ q.induced t = true := by
  classical
  simp only [Quartet.induced, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  constructor
  -- a displaying switching is `T` itself, and its cut edge lies above some vertex `p`; the clade of
  -- `T_p` induces `q`
  · rintro ⟨hq, S, hS, edge, hedge, hsep⟩
    have hSeq := baseline_switching_unique t ht hS
    subst S
    change edge ∈ (graph t ∅).underlying.edgeSet at hedge
    obtain ⟨p, hp, hpnil, heq⟩ := (baseline_edgeSet t edge).mp hedge
    obtain ⟨sub, hnode⟩ := (PhyloTree.mem_nodes_iff _ _).mp hp
    refine ⟨hq, sub.taxa, (PhyloTree.clades_mem_iff t _).mpr ⟨p, sub, hnode, rfl⟩, ?_⟩
    apply (baselineCut_separates_iff ht hnode q hq).mp
    simpa only [baselineCutGraph, heq] using hsep
  -- a clade inducing `q` is that of some `T_p` with `p` not the root; cut `T` above `p`
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
      simpa only [graph, Finset.image_empty, Finset.union_empty] using (support t ht ∅
          hempty).switching
    refine ⟨hq, (graph t ∅).edges, htotal, baselineCut p, ?_, ?_⟩
    · change baselineCut p ∈ (graph t ∅).underlying.edgeSet
      exact (baseline_edgeSet t _).mpr ⟨p, hp, hpnil, rfl⟩
    · apply (baselineCut_separates_iff ht hnode q hq).mpr
      simpa only [htaxa] using hcut


end Camus.Realization
