module

public import Camus.Network.Realization.Construction
public import Camus.Network.Baseline.Main
public import Camus.Network.Completeness.Main
public import Camus.Network.Isomorphism.Invariance
public import Camus.Network.Subdivision.Invariance
public import Camus.External.WarnowTabatabaeeEvans.Observation2
public import Camus.Network.Realization.Subdivision
public import Camus.Defs
public import Camus.Network.Code
public import Camus.Score
public import Camus.Preliminaries.Lemma1.Unique

/-!
# Lemmas 1 and 2: attributing satisfied quartets to non-tree edges

This file states Lemma 1 and Lemma 2 of Section 2.1. In both, `N` is a rooted binary level-1
network built on a tree `T` (well-labelled, in Lemma 1), given with a support subdivision
`H : SupportSubdivision t N S`: the edges `S` of `N` form a subdivision of `T`, the edges of
`N.edges \ S` are the non-tree edges, and `H.pairOf d` is the pair `(u, w)` of vertices of `T`
directly below the two ends of the non-tree edge `d` (Definition 2). The network `T + d` of the
paper is the canonical network `Realization.graph t {H.pairOf d}`, obtained from `T` by adding an
edge above `(u, w)` (Definition 3). A quartet is satisfied by a network if the network displays it
and `T` does not induce it. The proof of Lemma 1 uses Observation 2 of Warnow, Tabatabaee and Evans
(2025), proved in `Camus/External/WarnowTabatabaeeEvans/Observation2.lean` (`External.observation2`).

## Main results

* `lemma1`: Lemma 1, first sentence: a quartet satisfied by `N` is displayed by `T + d` for exactly
  one non-tree edge `d`.
* `DynamicProgramming.novel_disjoint_union`: Lemma 1, second sentence, for the canonical network
  `Realization.graph t E` of a cycle-separated family `E` of pairs: the quartets of `Q` that it
  satisfies are the disjoint union of those satisfied by the networks `Realization.graph t {e}`,
  `e ∈ E`.
* `lemma2`: Lemma 2: two non-tree edges of `N` with the same target are equal.
* `DynamicProgramming.mem_novel_iff`: `DynamicProgramming.novel t Q N` is the set of quartets of
  `Q` satisfied by `N`.
* `DynamicProgramming.baseline_subset`: a quartet displayed by `T` is displayed by every
  `Realization.graph t E`.

## Proof (the paper's)

The paper proves Lemma 1 in one sentence: it "follows directly from Observation 2 in Warnow et al.
(2025)". The formal proof of `lemma1` has two parts, and only the first uses Observation 2.

* Existence (`RootedNetwork.novel_edge_exists`, in `Preliminaries/Lemma1/Cuts.lean`). By
  Observation 2, `q` is separated in `N` by deleting a cut edge, or by deleting two edges of a
  cycle, one of them at the reticulation of the cycle. A cut edge would separate `q` in `T` as
  well, and `T` does not induce `q` (`RootedNetwork.cutEdgeSeparates_baseline`). So a cycle
  separates `q`; it is the cycle of the non-tree edge `d` entering its reticulation
  (`RootedNetwork.cycle_eq_fundamental_of_reticulation`). The same two edges separate `q` after the
  other non-tree edges are deleted (`RootedNetwork.fundamental_cycle_cut_displays_raw`), and the
  network so obtained is a subdivision of `T + d` (`SupportSubdivision.single_edge_reduction`),
  which therefore displays `q` (`GraphSubdivision.displays_iff`).
* Uniqueness (`RootedNetwork.novel_edge_unique`, in `Preliminaries/Lemma1/Unique.lean`) uses that
  the cycles of `N` are vertex-disjoint, and not Observation 2. Write `q = ab|cd`. In the subdivided
  `T`, the path from `a` to `b` and the path from `c` to `d` meet: otherwise an edge of `T` would
  separate the two pairs and `T` would induce `q`
  (`RootedNetwork.nonbaseline_pair_paths_intersect`). A common vertex of the two paths lies on the
  cycle of every non-tree edge `d` such that `T + d` displays `q`
  (`RootedNetwork.single_novel_pair_vertex_on_cycle`). Two such edges would have cycles sharing this
  vertex, so there is only one.

The second sentence of Lemma 1 (`DynamicProgramming.novel_disjoint_union`) applies `lemma1` to
`N = Realization.graph t E`: existence gives the inclusion into the union, uniqueness gives
disjointness, and the reverse inclusion holds because a switching of `T + e` is a switching of `N`
(`Realization.single_displays_full`).

The paper proves Lemma 2 by observing that two non-tree edges with target `v` would give two cycles
through `v`. Formally, the pairs of the non-tree edges of `N` form a cycle-separated family
(`SupportSubdivision.extracted_separated`); for such a family this argument is
`EdgeAbove.target_unique`, and distinct non-tree edges have distinct pairs
(`SupportSubdivision.pairOf_injective`).

## Implementation notes

The paper obtains `T + d` from `N` by deleting the other non-tree edges and suppressing the vertices
of indegree and outdegree one. `SupportSubdivision.single_edge_reduction` proves that `N` with the
other non-tree edges deleted (`{N with edges := insert d S}`) is a subdivision of
`Realization.graph t {H.pairOf d}`. Its proof matches the subdivided tree edges of `N` with those of
the canonical network of the family of pairs of `N` (`SupportSubdivision.map_wire_eq`). There, the
edge of `T` above a vertex `p` is subdivided by at most one ghost donor, the donor end of an edge
added above a pair `(p, w)` with target `p` (`Realization.ghostEndpoints_mem_unique`): two would
belong to two non-tree edges with target `p`, which Lemma 2 (`EdgeAbove.target_unique`) excludes.
The proof that canonical networks are level-1 (`Realization.levelOne`) uses Lemma 2 in the same way.
These uses of Lemma 2 belong to the construction of `T + d`, not to the attribution argument.
-/

@[expose] public section

namespace Camus

namespace Realization

/-- Let `E` be a cycle-separated family of pairs and `e ∈ E`. If `T + e`
(`Realization.graph t {e}`) displays `q`, so does `Realization.graph t E`: the network
`Realization.graph t E` with the other added edges deleted is a subdivision of `T + e`, and its
switchings are switchings of `Realization.graph t E`. This is the inclusion of the union in the
second sentence of Lemma 1. -/
theorem single_displays_full (t : PhyloTree) (ht : t.WellLabelled)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) {e : Pair}
    (he : e ∈ E) (q : Quartet)
    (hq : (graph t {e}).DisplaysQuartet q) : (graph t E).DisplaysQuartet q := by
  classical
  let N := graph t E
  let S := supportEdges t E
  let H := support t ht E hE
  have hN : N.RootedBinaryLevelOne := levelOne t ht E hE
  have hExtract : H.extracted = E := extracted_eq t ht E hE
  have hx : e ∈ (N.edges \ S).image H.pairOf := by
    change e ∈ H.extracted
    rw [hExtract]
    exact he
  obtain ⟨d,hd,hde⟩ := Finset.mem_image.mp hx
  obtain ⟨D⟩ := H.single_edge_reduction hN hd
  rw [hde] at D
  have hsing : EdgeAbove.CycleSeparated t {e} := by
    refine ⟨Finset.singleton_subset_iff.mpr (hE.1 he), ?_⟩
    simp
  have hraw := (D.displays_iff (levelOne t ht {e} hsing) q).mpr hq
  apply RootedNetwork.displays_of_edges_subset (N := N) (S := insert d S) _ q hraw
  exact Finset.insert_subset (Finset.mem_sdiff.mp hd).1 H.switching.1

end Realization

/-- **Lemma 1** (`mthst2`), first sentence. Let `T` be a well-labelled tree and `N` a rooted
binary level-1 network built on `T`, given by a support subdivision `H` of `T` in `N` whose edges
are `S`. If `N` displays a quartet `q` that `T` does not induce (`q` is satisfied by `N`), then
there is a unique non-tree edge `d ∈ N.edges \ S` such that `T + d` displays `q`. Here `T + d` is
the canonical network `Realization.graph t {H.pairOf d}` of the pair of `d` (Definition 3).

Departure from the paper: the paper derives the whole lemma from Observation 2. The formal proof
uses Observation 2 for existence (`RootedNetwork.novel_edge_exists`) and proves uniqueness from the
vertex-disjointness of the cycles of `N` (`RootedNetwork.novel_edge_unique`). Observation 2 gives,
for one network, a cycle whose cut separates `q`; it does not say that this cycle is unique, so
uniqueness needs its own argument. -/
theorem lemma1
    (t : PhyloTree) (ht : t.WellLabelled) (N : RootedNetwork)
    (hN : N.RootedBinaryLevelOne) (S : Finset (ℕ × ℕ))
    (H : SupportSubdivision t N S) (q : Quartet)
    (hq : N.DisplaysQuartet q) (hnot : q.induced t ≠ true) :
    ∃! e, e ∈ N.edges \ S ∧
      (Realization.graph t {H.pairOf e}).DisplaysQuartet q := by
  -- Existence, from Observation 2.
  obtain ⟨e,he,hqe⟩ := RootedNetwork.novel_edge_exists ht hN H q hq hnot
  refine ⟨e,⟨he,hqe⟩,?_⟩
  -- Uniqueness, from the vertex-disjointness of the cycles of `N`.
  intro f hf
  exact RootedNetwork.novel_edge_unique ht hN H q hnot hf.1 he hf.2 hqe

/-- **Lemma 2** (`mthst4`). Let `N` be a rooted binary level-1 network built on `T`, given by a
support subdivision `H` of `T` in `N` whose edges are `S`. Two non-tree edges `e, f ∈ N.edges \ S`
with the same target (`EdgeAbove.target` of their pairs `H.pairOf e`, `H.pairOf f`, Definition 2)
are equal.

Proof: the target of each pair lies on its cycle, and the cycles of distinct pairs share no vertex
(`EdgeAbove.target_unique`, applied to the cycle-separated family `H.extracted`); distinct non-tree
edges have distinct pairs (`SupportSubdivision.pairOf_injective`). -/
theorem lemma2 (t : PhyloTree) (N : RootedNetwork)
    (hN : N.RootedBinaryLevelOne) (S : Finset (ℕ × ℕ))
    (H : SupportSubdivision t N S) {e f : ℕ × ℕ}
    (he : e ∈ N.edges \ S) (hf : f ∈ N.edges \ S)
    (htarget : EdgeAbove.target (H.pairOf e) = EdgeAbove.target (H.pairOf f)) : e = f := by
  -- Distinct non-tree edges have distinct pairs.
  apply H.pairOf_injective hN (by simpa using he) (by simpa using hf)
  -- Two pairs with the same target have cycles through that target, so they are equal.
  apply EdgeAbove.target_unique t H.extracted (H.extracted_separated hN)
  · exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  · exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
  · exact htarget

namespace DynamicProgramming

/-- For a well-labelled `T`, a quartet `q` is in `novel t Q N` iff `q` occurs in `Q`, `N` displays
`q`, and `T` does not induce `q`: `novel t Q N` is the set of quartets of `Q` satisfied by `N`. -/
theorem mem_novel_iff (t : PhyloTree) (ht : t.WellLabelled)
    (Q : Multiset Quartet) (N : RootedNetwork) (q : Quartet) :
    q ∈ novel t Q N ↔ q ∈ Q.toFinset ∧ N.DisplaysQuartet q ∧ ¬q.induced t = true := by
  classical
  simp only [novel, repertoire, Finset.mem_sdiff, Finset.mem_filter,
    Realization.baseline_displays_iff t ht q]
  tauto

/-- **Lemma 1** (`mthst2`), second sentence, for a network given by its family of added edges. Let
`E` be a cycle-separated family of pairs and `N = Realization.graph t E`. The set of quartets of `Q`
satisfied by `N` is the union of the sets of quartets of `Q` satisfied by the single-edge networks
`T + e = Realization.graph t {e}`, `e ∈ E`, and these sets are pairwise disjoint. The proof applies
`lemma1` to `N`. -/
theorem novel_disjoint_union
    (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    novel t Q (Realization.graph t E) =
        E.biUnion (fun e => novel t Q (Realization.graph t {e})) ∧
      (E : Set Pair).Pairwise (fun e f =>
        Disjoint (novel t Q (Realization.graph t {e}))
          (novel t Q (Realization.graph t {f}))) := by
  classical
  let N := Realization.graph t E
  let S := Realization.supportEdges t E
  let H := Realization.support t ht E hE
  have hN : N.RootedBinaryLevelOne := Realization.levelOne t ht E hE
  have hExtract : H.extracted = E := Realization.extracted_eq t ht E hE
  have hpair (d : ℕ × ℕ) (hd : d ∈ N.edges \ S) : H.pairOf d ∈ E := by
    have hm : H.pairOf d ∈ H.extracted := Finset.mem_image.mpr ⟨d,hd,rfl⟩
    simpa only [hExtract] using hm
  have hindex (e : Pair) (he : e ∈ E) :
      ∃ d, d ∈ N.edges \ S ∧ H.pairOf d = e := by
    have hx : e ∈ (N.edges \ S).image H.pairOf := by
      change e ∈ H.extracted
      rw [hExtract]
      exact he
    exact Finset.mem_image.mp hx
  constructor
  · ext q
    constructor
    -- A quartet satisfied by `N` is satisfied by `T + e` for some `e ∈ E` (existence in Lemma 1).
    · intro hq
      obtain ⟨hQ,hdisplay,hnot⟩ := (mem_novel_iff t ht Q N q).mp hq
      obtain ⟨d,hd,_⟩ := lemma1 t ht N hN S H q hdisplay hnot
      exact Finset.mem_biUnion.mpr ⟨H.pairOf d,hpair d hd.1,
        (mem_novel_iff t ht Q _ q).mpr ⟨hQ,hd.2,hnot⟩⟩
    -- A quartet satisfied by `T + e` is satisfied by `N`.
    · intro hq
      obtain ⟨e,he,hqe⟩ := Finset.mem_biUnion.mp hq
      obtain ⟨hQ,hdisplay,hnot⟩ := (mem_novel_iff t ht Q _ q).mp hqe
      exact (mem_novel_iff t ht Q N q).mpr ⟨hQ,
        Realization.single_displays_full t ht E hE he q hdisplay,hnot⟩
  -- Disjointness: the edge given by Lemma 1 is unique.
  · intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro q hqe hqf
    obtain ⟨_,heDisplay,hnot⟩ := (mem_novel_iff t ht Q _ q).mp hqe
    obtain ⟨_,hfDisplay,_⟩ := (mem_novel_iff t ht Q _ q).mp hqf
    have hdisplay := Realization.single_displays_full t ht E hE he q heDisplay
    obtain ⟨d,_,hunique⟩ := lemma1 t ht N hN S H q hdisplay hnot
    obtain ⟨de,hde,hpe⟩ := hindex e he
    obtain ⟨df,hdf,hpf⟩ := hindex f hf
    have hdeq : de = d := hunique de ⟨hde,by rw [hpe]; exact heDisplay⟩
    have hdfq : df = d := hunique df ⟨hdf,by rw [hpf]; exact hfDisplay⟩
    apply hef
    calc
      e = H.pairOf de := hpe.symm
      _ = H.pairOf df := congrArg H.pairOf (hdeq.trans hdfq.symm)
      _ = f := hpf

/-- Every quartet of `Q` displayed by `T` (the network `Realization.graph t ∅`) is displayed by
`Realization.graph t E`, for every cycle-separated family `E`. -/
theorem baseline_subset (t : PhyloTree) (ht : t.WellLabelled)
    (Q : Multiset Quartet) (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    repertoire Q (Realization.graph t ∅) ⊆ repertoire Q (Realization.graph t E) := by
  classical
  intro q hq
  obtain ⟨hQ,hdisplay⟩ := Finset.mem_filter.mp hq
  have hbase : EdgeAbove.CycleSeparated t ∅ := by simp [EdgeAbove.CycleSeparated]
  have D := Realization.supportGraphSubdivision t E hE.1
  have hraw := (D.displays_iff (Realization.levelOne t ht ∅ hbase) q).mpr hdisplay
  have hS := (Realization.support t ht E hE).switching.1
  exact Finset.mem_filter.mpr ⟨hQ, RootedNetwork.displays_of_edges_subset hS q hraw⟩

end DynamicProgramming
namespace SupportSubdivision

/-- Let `N` be a rooted binary level-1 network built on a well-labelled tree `T`, with support
subdivision `H`, and `d` a non-tree edge of `N`. A quartet displayed by `T + d` (the canonical
network `Realization.graph t {H.pairOf d}`) is displayed by `N`: deleting the other non-tree edges
of `N` gives a subdivision of `T + d`, whose switchings are switchings of `N`. -/
theorem single_displays {t : PhyloTree} (ht : t.WellLabelled) {N : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S)
    {d : ℕ × ℕ} (hd : d ∈ N.edges \ S) (q : Quartet)
    (hq : (Realization.graph t {H.pairOf d}).DisplaysQuartet q) : N.DisplaysQuartet q := by
  classical
  obtain ⟨D⟩ := H.single_edge_reduction hN hd
  have hsing : EdgeAbove.CycleSeparated t {H.pairOf d} := by
    refine ⟨Finset.singleton_subset_iff.mpr ((H.extracted_separated hN).1 ?_), by simp⟩
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hraw := (D.displays_iff (Realization.levelOne t ht {H.pairOf d} hsing) q).mpr hq
  exact RootedNetwork.displays_of_edges_subset
    (Finset.insert_subset (Finset.mem_sdiff.mp hd).1 H.switching.1) q hraw

end SupportSubdivision

open DynamicProgramming in
/-- **Lemma 1** (`mthst2`), second sentence. Let `T` be a well-labelled tree and `N` a rooted
binary level-1 network built on `T`, with support subdivision `H` whose edges are `S`. For every
multiset `Q`, the quartets of `Q` satisfied by `N` are the disjoint union, over the non-tree edges
`d ∈ N.edges \ S`, of the quartets of `Q` satisfied by `T + d`
(`Realization.graph t {H.pairOf d}`). -/
theorem lemma1_union (t : PhyloTree) (ht : t.WellLabelled) (N : RootedNetwork)
    (hN : N.RootedBinaryLevelOne) (S : Finset (ℕ × ℕ)) (H : SupportSubdivision t N S)
    (Q : Multiset Quartet) :
    novel t Q N = (N.edges \ S).biUnion (fun d => novel t Q (Realization.graph t {H.pairOf d})) ∧
      ((N.edges \ S : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).Pairwise (fun d d' =>
        Disjoint (novel t Q (Realization.graph t {H.pairOf d}))
          (novel t Q (Realization.graph t {H.pairOf d'}))) := by
  classical
  constructor
  · ext q
    constructor
    · -- a satisfied quartet is satisfied by `T + d` for the edge `d` of the first sentence
      intro hq
      obtain ⟨hQ, hdisplay, hnot⟩ := (mem_novel_iff t ht Q N q).mp hq
      obtain ⟨d, hd, _⟩ := lemma1 t ht N hN S H q hdisplay hnot
      exact Finset.mem_biUnion.mpr ⟨d, hd.1, (mem_novel_iff t ht Q _ q).mpr ⟨hQ, hd.2, hnot⟩⟩
    · -- a quartet satisfied by some `T + d` is displayed, hence satisfied, by `N`
      intro hq
      obtain ⟨d, hd, hqd⟩ := Finset.mem_biUnion.mp hq
      obtain ⟨hQ, hdisplay, hnot⟩ := (mem_novel_iff t ht Q _ q).mp hqd
      exact (mem_novel_iff t ht Q N q).mpr ⟨hQ, H.single_displays ht hN hd q hdisplay, hnot⟩
  · -- the union is disjoint by the uniqueness in the first sentence
    intro d hd d' hd' hne
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    obtain ⟨_, hdisplay, hnot⟩ := (mem_novel_iff t ht Q _ q).mp hq
    obtain ⟨_, hdisplay', _⟩ := (mem_novel_iff t ht Q _ q).mp hq'
    obtain ⟨_, _, hunique⟩ := lemma1 t ht N hN S H q
      (H.single_displays ht hN hd q hdisplay) hnot
    exact hne ((hunique d ⟨hd, hdisplay⟩).trans (hunique d' ⟨hd', hdisplay'⟩).symm)

end Camus
