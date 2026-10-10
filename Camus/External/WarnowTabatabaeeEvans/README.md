# Observation 2 of Warnow, Tabatabaee and Evans

**Source.** Tandy Warnow, Yasamin Tabatabaee and Steven N. Evans, *Advances in estimating
level-1 phylogenetic networks from unrooted SNPs*, Journal of Computational Biology 32(1) (2025)
3–27, <https://doi.org/10.1089/cmb.2024.0710>, Section 2.1, Observation 2 (published online on
25 November 2024; the bioRxiv preprint of July 2024 does not contain it).

**Statement.** "The following observation is straightforward and the proof is omitted.
Observation 2. For every level-1 phylogenetic network N, ab | cd ∈ Q(N_r) if and only if a, b is
separated from c, d as the result of deleting either a cut edge in N or deleting two edges from a
cycle, where one of the edges is incident with the bottom node of the cycle." Here `Q(N_r)` is the
set of quartet trees of the trees contained in `N`, those obtained by deleting one incoming edge
of each reticulation (Definitions 5 and 6 of the source), and the networks are binary.

**How the paper uses it.** The proof of Lemma 1 is the sentence "This lemma follows directly from
Observation 2 in Warnow et al. (2025)." The formalization uses it for the existence half of
Lemma 1 ([`RootedNetwork.novel_edge_exists`](../../Preliminaries/Lemma1/Cuts.lean#L95)); the uniqueness half needs another argument
(the report's E1).

**The Lean statement.** [`External.WarnowTabatabaeeEvansObservation2`](Observation2.lean#L69), in
[`Camus/External/WarnowTabatabaeeEvans/Observation2.lean`](Observation2.lean): for every rooted binary level-1 network `N`
([`RootedNetwork.RootedBinaryLevelOne`](../../../Challenge.lean#L317)) and every quartet `q` on four of its taxa, `N` displays `q`
([`RootedNetwork.DisplaysQuartet`](../../../Challenge.lean#L358): some switching of `N`, which keeps one incoming edge at every
vertex other than the root, has an edge whose deletion separates the two pairs of `q`, each pair
staying connected) if and only if deleting a cut edge of the underlying undirected graph
separates them ([`RootedNetwork.CutEdgeSeparates`](../../Defs.lean#L749)), or deleting two edges of one cycle, at least one
of them incident to a vertex of indegree 2 on that cycle, does ([`RootedNetwork.CycleSeparates`](../../Defs.lean#L757)).
This is the source's statement: a switching is a tree contained in `N`, and its unary vertices and
unlabelled leaves change no split; a vertex of indegree 2 on a cycle of a level-1 network is the
cycle's bottom node; and deleting both edges into the bottom node separates the same pairs as
deleting the edge below it.

**The proof.** [`External.observation2`](Observation2.lean#L186), from [`External.observation2_forward`](Observation2.lean#L79) and
[`External.observation2_backward`](Observation2.lean#L155). A switching is a spanning tree of the network, and every edge
`d` that it leaves out closes a cycle with the path of the switching between its ends; the head of
`d` is the cycle's reticulation. If a switching displays `q` through an edge `e`, either `e` is a
cut edge of `N`, and deleting it leaves the same two components in `N` as in the switching, or `e`
lies on a cycle of `N`, which is then the cycle of a left-out edge `d`, and deleting `e` and `d`
from `N` leaves the same two components, because the other left-out edges have their ends joined by
paths that avoid this cycle (the cycles of a level-1 network are vertex-disjoint). The converse runs
the same argument from a switching that keeps every cut edge, or that leaves out the cut edge at the
reticulation. The general facts about switchings are in
[`Camus/Network/Cuts.lean`](../../Network/Cuts.lean),
[`Camus/Network/Completeness/Tree.lean`](../../Network/Completeness/Tree.lean) and
[`Camus/Network/Completeness/Cycles.lean`](../../Network/Completeness/Cycles.lean).
