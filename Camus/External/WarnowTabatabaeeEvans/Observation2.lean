module

public import Camus.Network.Cuts
public import Camus.Network.Isomorphism.Rename

/-!
# Observation 2 of Warnow, Tabatabaee and Evans

The paper's Lemma 1 "follows directly from Observation 2 in Warnow et al. (2025)". Warnow,
Tabatabaee and Evans state the observation without proof ("The following observation is
straightforward and the proof is omitted"): "For every level-1 phylogenetic network N, ab | cd ∈
Q(N_r) if and only if a, b is separated from c, d as the result of deleting either a cut edge in N or
deleting two edges from a cycle, where one of the edges is incident with the bottom node of the
cycle." This file states it (`WarnowTabatabaeeEvansObservation2`) and proves it
(`External.observation2`).

## Main results

* `External.observation2_forward`: a displayed quartet is separated by a cut edge or by a cut of
  two edges of one cycle, one of them entering the cycle's reticulation.
* `External.observation2_backward`: the converse.
* `External.observation2`: Observation 2.

## Proof

A switching `S` of `N`, which keeps one incoming edge at every vertex other than the root, is a
spanning tree of `N`. Each edge `d` that it leaves out closes a cycle with the path of `S` between
its ends (`RootedNetwork.fundamentalCycle`), and its head is a reticulation
(`RootedNetwork.indegree_eq_two_of_deleted`).

* Forward. Let `S` display `q` through an edge `e`. If `e` is a cut edge of `N`, deleting it
  leaves the same components in `N` as in `S` (`RootedNetwork.bridge_cut_reachable_iff`).
  Otherwise `e` lies on a cycle of `N`; since `S` has no cycle, this cycle uses an edge `d` that
  `S` leaves out, and since distinct cycles of `N` are vertex-disjoint, it is the cycle of `d`.
  Deleting `e` and `d` from `N` leaves the same components as deleting `e` from `S`, because the
  other left-out edges have their ends joined by paths that avoid this cycle
  (`RootedNetwork.cycle_cut_reachable_iff`, `RootedNetwork.switching_cut_graph`). The head of `d`
  is the cycle's reticulation.
* Backward. A cut edge lies in every switching (`RootedNetwork.bridge_mem_switching`), which has
  the same components after its deletion. For a cut of two edges of a cycle, one of them entering
  the reticulation `r`, the cycle is that of the edge `d` into `r` left out by any switching
  (`RootedNetwork.cycle_eq_fundamental_of_reticulation`), and keeping `d` instead of the cut edge
  at `r` gives a switching that displays `q` (`RootedNetwork.fundamental_cycle_cut_displays_raw`).

## The Lean statement

Display (`RootedNetwork.DisplaysQuartet`) is membership in `Q(N_r)`: some switching has an edge
whose deletion separates the two pairs of `q`, each pair staying connected; this is the
definition of `Q(T)` for the trees in `N` of Warnow, Tabatabaee and Evans (Definitions 4–6), whose
unary vertices and unlabelled leaves change no split. The networks are those of
`RootedNetwork.RootedBinaryLevelOne`, the binary level-1 networks of the source. The source's
"bottom node" of a cycle is its vertex of indegree 2, and the cycles are those of the underlying
undirected graph; in a level-1 network every cycle through a reticulation contains both its
incoming edges, so the two readings agree.
-/

@[expose] public section

namespace Camus.External

/-- The statement of Observation 2 of Tandy Warnow, Yasamin Tabatabaee and Steven N. Evans,
"Advances in Estimating Level-1 Phylogenetic Networks from Unrooted SNPs", J. Comput. Biol.
32(1):3–27, 2025, doi:10.1089/cmb.2024.0710. Let `N` be a rooted binary level-1 network and `q` a
quartet whose taxa are taxa of `N`. Then `N` displays `q` (q ∈ Q(N_r)) if and only if the two sides
of `q` are separated by deleting either one cut edge of `N` (`RootedNetwork.CutEdgeSeparates`) or
two distinct edges of one cycle of `N`, at least one of them incident to the reticulation of that
cycle, its vertex of indegree 2 (`RootedNetwork.CycleSeparates`). It is proved by
`External.observation2`. -/
def WarnowTabatabaeeEvansObservation2 : Prop :=
  ∀ N : RootedNetwork, N.RootedBinaryLevelOne →
    ∀ q : Quartet, q.taxa ⊆ N.taxa →
      (N.DisplaysQuartet q ↔ N.CutEdgeSeparates q ∨ N.CycleSeparates q)

open RootedNetwork SimpleGraph

/-- **Observation 2** of Warnow, Tabatabaee and Evans, forward direction: a quartet displayed by
a rooted binary level-1 network is separated by removing a bridge, or by removing two edges of one
cycle, one of them an incoming edge of the cycle's reticulation. -/
theorem observation2_forward {N : RootedNetwork} (hN : N.RootedBinaryLevelOne) (q : Quartet)
    (hq : N.DisplaysQuartet q) : N.CutEdgeSeparates q ∨ N.CycleSeparates q := by
  classical
  obtain ⟨-, R, hR, e, he, hsep⟩ := hq
  have heN : e ∈ N.underlying.edgeSet := edgeSet_mono (switching_underlying_le hR) he
  by_cases hb : N.underlying.IsBridge e
  · -- the bridge is an edge of the switching, and leaves the same two components
    left
    refine ⟨e, heN, hb, ?_⟩
    obtain ⟨h1, h2, h3⟩ := hsep
    exact ⟨fun x hx y hy => (bridge_cut_reachable_iff hN hR e hb _ _).mpr (h1 x hx y hy),
      fun x hx y hy => (bridge_cut_reachable_iff hN hR e hb _ _).mpr (h2 x hx y hy),
      fun x hx y hy h => h3 x hx y hy ((bridge_cut_reachable_iff hN hR e hb _ _).mp h)⟩
  · right
    -- `e` lies on a cycle of `N`
    obtain ⟨u, p, hp, hep⟩ : ∃ u, ∃ p : N.underlying.Walk u u, p.IsCycle ∧ e ∈ p.edges := by
      by_contra hno
      push Not at hno
      exact hb ((isBridge_iff_forall_cycle_notMem heN).mpr fun u p hp hep => hno u p hp hep)
    -- the cycle uses an edge `d` that the switching leaves out, since the switching is a tree
    obtain ⟨b, hbp, hbR⟩ : ∃ b ∈ p.edges, b ∉ ({N with edges := R}).underlying.edgeSet := by
      by_contra hall
      push Not at hall
      exact switching_acyclic hN hR _ (hp.transfer hall)
    obtain ⟨d, hdN, hdb⟩ : ∃ d ∈ N.edges, s(d.1, d.2) = b := by
      have hbN := p.edges_subset_edgeSet hbp
      induction b using Sym2.inductionOn with
      | _ x y =>
        rcases hbN.2 with hxy | hyx
        · exact ⟨(x, y), hxy, rfl⟩
        · exact ⟨(y, x), hyx, Sym2.eq_swap⟩
    have hdR : d ∉ R := by
      intro hdR
      apply hbR
      rw [← hdb]
      exact ⟨edge_ne hN hdN, Or.inl hdR⟩
    have hd : d ∈ N.edges \ R := Finset.mem_sdiff.mpr ⟨hdN, hdR⟩
    -- by level-1 disjointness, the cycle is the fundamental cycle of `d`
    have hceq : p.edges.toFinset = (fundamentalCycle hN hR hd).edges.toFinset := by
      by_contra hne
      have hdis := hN.2.2.2.2.2.2.2.2.2.2 u d.1 p (fundamentalCycle hN hR hd) hp
        (fundamentalCycle_isCycle hN hR hd) hne
      have hd1p : d.1 ∈ p.support := by
        rw [← hdb] at hbp
        exact p.fst_mem_support_of_mem_edges hbp
      exact Finset.disjoint_left.mp hdis (List.mem_toFinset.mpr hd1p)
        (List.mem_toFinset.mpr (fundamentalCycle_source_mem hN hR hd))
    have heF : e ∈ (fundamentalCycle hN hR hd).edges := by
      apply List.mem_toFinset.mp
      rw [← hceq]
      exact List.mem_toFinset.mpr hep
    have hdF := fundamentalCycle_mem_edges hN hR hd
    have hne : e ≠ s(d.1, d.2) := by
      intro h
      exact deleted_edge_not_switching_edgeSet hN hR hd (h ▸ he)
    -- removing `e` and `d` from `N` leaves the components of the switching without `e`
    have hB : ∀ c ∈ ({e, s(d.1, d.2)} : Set (Sym2 ℕ)), c ∈ (fundamentalCycle hN hR hd).edges := by
      intro c hc
      rcases Set.mem_insert_iff.mp hc with rfl | hc
      · exact heF
      · exact Set.mem_singleton_iff.mp hc ▸ hdF
    have hreach (x y : ℕ) :
        (N.underlying.deleteEdges {e, s(d.1, d.2)}).Reachable x y ↔
          (({N with edges := R}).underlying.deleteEdges {e}).Reachable x y := by
      rw [cycle_cut_reachable_iff hN hR hd _ hB x y, switching_cut_graph hN hR hd e]
    obtain ⟨h1, h2, h3⟩ := hsep
    refine ⟨d.1, fundamentalCycle hN hR hd, fundamentalCycle_isCycle hN hR hd, d.2,
      fundamentalCycle_target_mem hN hR hd, indegree_eq_two_of_deleted hN hR hd,
      e, heF, s(d.1, d.2), hdF, hne, Or.inr (Sym2.mem_mk_right _ _), ?_⟩
    exact ⟨fun x hx y hy => (hreach _ _).mpr (h1 x hx y hy),
      fun x hx y hy => (hreach _ _).mpr (h2 x hx y hy),
      fun x hx y hy h => h3 x hx y hy ((hreach _ _).mp h)⟩

/-- **Observation 2** of Warnow, Tabatabaee and Evans, backward direction: a quartet on four taxa
of a rooted binary level-1 network that is separated by removing a bridge, or by removing two
edges of one cycle one of which is incident to the cycle's reticulation, is displayed. -/
theorem observation2_backward {N : RootedNetwork} (hN : N.RootedBinaryLevelOne) (q : Quartet)
    (hqt : q.taxa ⊆ N.taxa) (h : N.CutEdgeSeparates q ∨ N.CycleSeparates q) :
    N.DisplaysQuartet q := by
  classical
  obtain ⟨R, hR⟩ := exists_switching hN
  rcases h with ⟨b, hbN, hb, hsep⟩ | ⟨v, c, hc, r, hr, hret, e, he, f, hf, hef, hrc, hsep⟩
  · -- every switching keeps the bridge, with the same two components
    obtain ⟨h1, h2, h3⟩ := hsep
    refine ⟨hqt, R, hR, b, bridge_mem_switching hN hR hbN hb, ?_⟩
    exact ⟨fun x hx y hy => (bridge_cut_reachable_iff hN hR b hb _ _).mp (h1 x hx y hy),
      fun x hx y hy => (bridge_cut_reachable_iff hN hR b hb _ _).mp (h2 x hx y hy),
      fun x hx y hy h => h3 x hx y hy ((bridge_cut_reachable_iff hN hR b hb _ _).mpr h)⟩
  · -- the cycle is the fundamental cycle of the edge into `r` that `R` leaves out
    obtain ⟨d, hd, hdr⟩ := deleted_incoming_of_reticulation hN hR r hret
    have hceq := cycle_eq_fundamental_of_reticulation hN hR c hc hr hd hdr
    have hmem {x : Sym2 ℕ} (hx : x ∈ c.edges) : x ∈ (fundamentalCycle hN hR hd).edges := by
      apply List.mem_toFinset.mp
      rw [← hceq]
      exact List.mem_toFinset.mpr hx
    have hraw : ({N with edges := insert d R}).DisplaysQuartet q := by
      rcases hrc with hre | hrf
      · exact fundamental_cycle_cut_displays_raw hN hR hd q hqt e f (hmem he) (hmem hf) hef
          (hdr.symm ▸ hre) hsep
      · exact fundamental_cycle_cut_displays_raw hN hR hd q hqt f e (hmem hf) (hmem he)
          hef.symm (hdr.symm ▸ hrf) (by simpa only [Set.pair_comm] using hsep)
    exact displays_of_edges_subset
      (Finset.insert_subset (Finset.mem_sdiff.mp hd).1 hR.1) q hraw

/-- **Observation 2** of Warnow, Tabatabaee and Evans (2025): in a rooted binary level-1 network, a
quartet on four of its taxa is displayed if and only if deleting a cut edge, or two edges of one
cycle one of which is incident to the cycle's reticulation, separates its two pairs. -/
theorem observation2 : WarnowTabatabaeeEvansObservation2 :=
  fun _ hN q hqt => ⟨observation2_forward hN q, observation2_backward hN q hqt⟩

end Camus.External
