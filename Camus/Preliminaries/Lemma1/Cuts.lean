module

public import Camus.Network.Cuts
public import Camus.Network.Completeness.Baseline
public import Camus.Network.Realization.Construction
public import Camus.Network.Baseline.Main
public import Camus.Network.Completeness.Main
public import Camus.Network.Isomorphism.Invariance
public import Camus.Network.Subdivision.Invariance
public import Camus.External.WarnowTabatabaeeEvans.Observation2

/-!
# Lemma 1, existence: from Observation 2 to one non-tree edge

This file proves the existence part of Lemma 1 (`RootedNetwork.novel_edge_exists`): if a rooted
binary level-1 network `N` built on `T` displays a quartet `q` that `T` does not induce, then
`T + d` displays `q` for some non-tree edge `d`. It uses Observation 2 of Warnow, Tabatabaee and
Evans (2025), proved in `Camus/External/WarnowTabatabaeeEvans/Observation2.lean`.

Throughout, `S` is a switching of `N`; its edges form a spanning tree of the underlying graph of
`N`, and in the main results they are the edges of the subdivided `T`. The non-tree edges are those
of `N.edges \ S`, and `{N with edges := R}` is `N` with edge set `R`. The cycle of a non-tree edge
`d` (`RootedNetwork.fundamentalCycle`) is `d` followed by the path of `S` joining its ends
(`RootedNetwork.supportPath`); it is the cycle `γ(u, w)` created by `d`. Since `N` is level-1, the
cycles of distinct non-tree edges are vertex-disjoint.

## Main results

* `RootedNetwork.novel_edge_exists`: existence in Lemma 1.
* `RootedNetwork.cutEdgeSeparates_baseline`: a quartet separated by deleting a cut edge of `N` is
  induced by `T`.
* `RootedNetwork.cycle_eq_fundamental_of_reticulation`: a cycle through the head of a non-tree edge
  `d` is the cycle of `d`.
* `RootedNetwork.fundamental_cycle_cut_displays_raw`: if deleting two edges of the cycle of `d`, one
  of them entering the head of `d`, separates `q` in `N`, then `N` with the other non-tree edges
  deleted displays `q`.

## Proof (the paper's)

The paper derives Lemma 1 from Observation 2. The existence part follows this route.

1. By Observation 2, `q` is separated in `N` by deleting a cut edge, or by deleting two edges of a
   cycle, one of them at the reticulation of the cycle.
2. A cut edge of `N` lies in every switching (`RootedNetwork.bridge_mem_switching`), and deleting
   it leaves the same components in `N` as in the subdivided `T`
   (`RootedNetwork.bridge_cut_reachable_iff`). So in the first case `T` induces `q`
   (`RootedNetwork.cutEdgeSeparates_baseline`), which is excluded.
3. In the second case the reticulation is the head of a non-tree edge `d`
   (`RootedNetwork.deleted_incoming_of_reticulation`), and the cycle is the cycle of `d`
   (`RootedNetwork.cycle_eq_fundamental_of_reticulation`).
4. Deleting edges of the cycle of `d` leaves the same components after the other non-tree edges are
   deleted, since their cycles are disjoint from that of `d`
   (`RootedNetwork.cycle_cut_reachable_iff`). Deleting the cut edge at the reticulation leaves a
   switching, so `N` with the other non-tree edges deleted displays `q`
   (`RootedNetwork.fundamental_cycle_cut_displays_raw`).
5. That network is a subdivision of `T + d` (`SupportSubdivision.single_edge_reduction`), and
   subdivision preserves display (`GraphSubdivision.displays_iff`), so `T + d` displays `q`.
-/

@[expose] public section

namespace Camus.RootedNetwork

/-- The cut-edge case of Observation 2: if deleting a cut edge of `N` separates `q`, then `T`
induces `q`. So a quartet satisfied by `N` is separated by a cycle. -/
theorem cutEdgeSeparates_baseline {t : PhyloTree} (ht : t.WellLabelled)
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S)
    (q : Quartet) (hqt : q.taxa ⊆ N.taxa) (hq : N.CutEdgeSeparates q) :
    q.induced t = true := by
  classical
  obtain ⟨b,hb,hbridge,hsep⟩ := hq
  have hsepS : ({N with edges := S}).Separates
      (({N with edges := S}).underlying.deleteEdges {b}) q := by
    obtain ⟨h1,h2,h3⟩ := hsep
    refine ⟨?_,?_,?_⟩
    · intro a ha c hc
      exact (bridge_cut_reachable_iff hN H.switching b hbridge _ _).mp (h1 a ha c hc)
    · intro a ha c hc
      exact (bridge_cut_reachable_iff hN H.switching b hbridge _ _).mp (h2 a ha c hc)
    · intro a ha c hc h
      exact h3 a ha c hc ((bridge_cut_reachable_iff hN H.switching b hbridge _ _).mpr h)
  have hraw : ({N with edges := S}).DisplaysQuartet q :=
    ⟨hqt,S,⟨Finset.Subset.refl _,H.switching.2⟩,b,
      bridge_mem_switching hN H.switching hb hbridge,hsepS⟩
  have hbase : EdgeAbove.CycleSeparated t ∅ := by simp [EdgeAbove.CycleSeparated]
  have hbq := (H.baseline_subdivision.displays_iff
    (Realization.levelOne t ht ∅ hbase) q).mp hraw
  exact (Realization.baseline_displays_iff t ht q).mp hbq

/-- Existence in Lemma 1. Let `N` be a rooted binary level-1 network built on a well-labelled
tree `T`, with support subdivision `H` whose edges are `S`. If `N` displays `q` and `T` does not
induce `q`, then `T + d` (`Realization.graph t {H.pairOf d}`) displays `q` for some non-tree edge
`d ∈ N.edges \ S`. -/
theorem novel_edge_exists
    {t : PhyloTree} (ht : t.WellLabelled) {N : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)}
    (H : SupportSubdivision t N S) (q : Quartet)
    (hq : N.DisplaysQuartet q) (hnot : q.induced t ≠ true) :
    ∃ d, d ∈ N.edges \ S ∧
      (Realization.graph t {H.pairOf d}).DisplaysQuartet q := by
  classical
  -- Observation 2: `q` is separated by a cut edge or by a two-edge cut of a cycle.
  rcases (External.observation2 N hN q hq.1).mp hq with hcut | hcycle
  -- A cut edge would make `q` induced by `T`.
  · exact False.elim (hnot (cutEdgeSeparates_baseline ht hN H q hq.1 hcut))
  -- The cycle is the cycle of the non-tree edge `d` entering its reticulation.
  · obtain ⟨v,c,hc,r,hr,hret,e,he,f,hf,hef,hrcut,hsep⟩ := hcycle
    obtain ⟨d,hd,hdr⟩ := deleted_incoming_of_reticulation hN H.switching r hret
    have hceq := cycle_eq_fundamental_of_reticulation hN H.switching c hc hr hd hdr
    have heF : e ∈ (fundamentalCycle hN H.switching hd).edges := by
      apply List.mem_toFinset.mp
      rw [← hceq]
      exact List.mem_toFinset.mpr he
    have hfF : f ∈ (fundamentalCycle hN H.switching hd).edges := by
      apply List.mem_toFinset.mp
      rw [← hceq]
      exact List.mem_toFinset.mpr hf
    -- The cut still separates `q` once the other non-tree edges are deleted.
    have hraw : ({N with edges := insert d S}).DisplaysQuartet q := by
      rcases hrcut with hre | hrf
      · exact fundamental_cycle_cut_displays_raw hN H.switching hd q hq.1 e f heF hfF hef
          (hdr.symm ▸ hre) hsep
      · exact fundamental_cycle_cut_displays_raw hN H.switching hd q hq.1 f e hfF heF hef.symm
          (hdr.symm ▸ hrf) (by simpa only [Set.pair_comm] using hsep)
    -- That network is a subdivision of `T + d`, which therefore displays `q`.
    have hExtract := H.extracted_separated hN
    have hm : H.pairOf d ∈ H.extracted := Finset.mem_image.mpr ⟨d,hd,rfl⟩
    have hsing : EdgeAbove.CycleSeparated t {H.pairOf d} := by
      refine ⟨Finset.singleton_subset_iff.mpr (hExtract.1 hm),?_⟩
      simp
    obtain ⟨D⟩ := H.single_edge_reduction hN hd
    exact ⟨d,hd,(D.displays_iff (Realization.levelOne t ht _ hsing) q).mp hraw⟩

end Camus.RootedNetwork
