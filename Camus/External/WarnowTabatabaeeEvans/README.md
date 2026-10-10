# Results of Warnow, Tabatabaee and Evans

Two results of Warnow, Tabatabaee and Evans that the paper uses: Observation 2, in the proof of
Lemma 1, and the convergence of the quartets of SNPs to the quartets of the network under their
site model, in the consistency argument of Section 3.2.

## Observation 2

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
([`RootedNetwork.RootedBinaryLevelOne`](../../../Challenge.lean#L270)) and every quartet `q` on four of its taxa, `N` displays `q`
([`RootedNetwork.DisplaysQuartet`](../../../Challenge.lean#L311): some switching of `N`, which keeps one incoming edge at every
vertex other than the root, has an edge whose deletion separates the two pairs of `q`, each pair
staying connected) if and only if deleting a cut edge of the underlying undirected graph
separates them ([`RootedNetwork.CutEdgeSeparates`](../../Defs.lean#L882)), or deleting two edges of one cycle, at least one
of them incident to a vertex of indegree 2 on that cycle, does ([`RootedNetwork.CycleSeparates`](../../Defs.lean#L890)).
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

## The site model and the quartets of SNPs (Theorem 6)

**Source.** The same article, Section 4.2 (the single site model) and the proof of Theorem 6
(Section 4.3.2).

**Statement.** Each site picks a tree contained in `N`, each reticulation inheriting from one of
its parents with a transmission probability `κ(e)` (`0 < κ(e) < 1`, summing to 1 at each
reticulation), and evolves down it under a substitution model with a positive distribution at the
root, `p(e, s, s') > 0` for `s ≠ s'` on the tree edges and no change on the reticulation edges. An
Oracle selects the SNPs, the sites that change state exactly once. Theorem 6 states that
Gusfield-Estimate-Rooted is statistically consistent, and its proof shows that every clade of a
tree contained in `N` is the clade of an SNP with positive probability: "It is easy to see that the
probability that c changes on e and no other edge in T is strictly positive."

**How the paper uses it.** Section 3.2: "According to the theory given in Warnow et al. (2025), as
the number of gene trees increases, this multiset will be identical to Q(N_r) (when considered as a
set), with probability converging to 1." Here the multiset is that of the quartets `ab|cd` of the
SNPs, `a`, `b` in one state and `c`, `d` in the other, and "gene trees" means sites (the report's
E9).

**The Lean statement.** The model is [`External.SiteModel`](SiteModel.lean#L303) in
[`Camus/External/WarnowTabatabaeeEvans/SiteModel.lean`](SiteModel.lean) (its parameters, with the constraints of
Section 4.2, are [`External.SiteParameters`](SiteModel.lean#L282)), and the convergence is [`External.support_tendsto`](Sampling.lean#L99) in
[`Camus/External/WarnowTabatabaeeEvans/Sampling.lean`](Sampling.lean): for independent sites with the law of the
model, the probability that the support of the multiset of the quartets of the SNPs among the first
`m` sites is the set of quartets displayed by `N` tends to 1. Sequences of independent sites with
this law exist ([`External.SiteModel.sites`](Sampling.lean#L250)).

**A missing hypothesis.** The constraints of Section 4.2 do not make `p(e, s, s)` positive on the
tree edges, and the step "it is easy to see" needs it: if the state must change on a tree edge `f`,
no site that changes only on another edge exists. For the tree `(((A,B),C),D)` with the state always
changing on the edge above `((A,B),C)`, which meets every constraint of Section 4.2, no SNP of
positive probability has the clade `{A, B}`, and the quartet `AB|CD` of the tree is never observed
([`External.theorem6_step_needs_stay`](Theorem6.lean#L183), in [`Camus/External/WarnowTabatabaeeEvans/Theorem6.lean`](Theorem6.lean)).
Theorem 6 then fails for this network. Their Theorem 7 assumes `0 < p_on ≤ p(e, s, s)`, and so does
[`External.SiteModel`](SiteModel.lean#L303) (its field `stay_pos`). Substitution probabilities of a continuous-time Markov
chain, as in the standard models, satisfy it.

**The proof.** WTE's, for quartets in place of clades. If `N` displays `q`, some switching has an
edge into a vertex of indegree 1 whose clade cuts `q` ([`RootedNetwork.displays_iff_treeEdge_cladeBelow`](../../Network/Clades.lean#L205)).
The history that follows this switching and changes state on that edge alone has positive
probability ([`External.SiteModel.exists_snp`](SiteModel.lean#L1028), [`External.SiteModel.quartetProb_pos`](SiteModel.lean#L1043)), and every
quartet of an SNP is displayed by `N` ([`External.SiteHistory.displays_of_mem_quartets`](SiteModel.lean#L892)). With
finitely many quartets, a union bound with `(1 − p)^m → 0` gives the convergence.

