# Audit of the paper and the formalization

Paper: James Willson and Tandy Warnow, *CAMUS: scalable phylogenetic network estimation*,
Bioinformatics 42, Supplement 1 (2026), btag245, <https://doi.org/10.1093/bioinformatics/btag245>
(ISMB 2026; received 10 April 2026, accepted 16 April 2026, published 7 July 2026; CC BY 4.0). No
TeX source is public. The audit was made against the publisher's JATS XML, as distributed by
[Europe PMC (PMC13340232)](https://www.ebi.ac.uk/europepmc/webservices/rest/PMC13340232/fullTextXML),
whose identifiers serve as labels: Definition 1 is `mthst1`, Lemma 1 `mthst2`, Definition 2
`mthst3`, Lemma 2 `mthst4`, Definitions 3–5 `mthst6`–`mthst8`, Theorem 1 `mthst9`, and Equations
(1)–(5) `E1`–`E5` (these labels are written in code spans; the findings of this report are E1–E7).
Section, result and equation numbers are the published version's. The earlier versions, bioRxiv
[10.64898/2026.02.01.703143](https://doi.org/10.64898/2026.02.01.703143) v1 (4 February 2026) and
v2 (5 February 2026), differ in places noted below (Section 10).

Status of the formalization:

- **Proved:** Lemma 1 (both sentences, for every network built on the constraint tree), Lemma 2,
  Theorem 1, the four properties of the networks of Section 2.4, the bound of `n − 1`
  reticulations, the operation counts of Sections 2.3 and 2.4 in a unit-cost accounting, and
  Algorithm 1's test, each by the paper's argument where the paper gives one. Two claims of the
  paper are refuted (E5, E6), and the closest correct statements are proved.
- **Cited results:** the paper's proofs use one result from the literature, Observation 2 of
  Warnow, Tabatabaee and Evans (2025), which its source states without proof. It is proved here
  ([`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L186), Section 2). The formalization is unconditional: nothing is assumed.
- **Build:** `lake build` succeeds; the only `sorry`s are the ten in [`Challenge.lean`](Challenge.lean), by
  design. There is no `axiom`. [`scripts/Audit.lean`](scripts/Audit.lean) checks that every declaration of the library depends only
  on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- **Challenge and Comparator:** [`Challenge.lean`](Challenge.lean) states Theorem 1, the claim of Section 2.4, the
  refutations of E5 and E6, the corrected recovery of Section 3.2, and five theorems that tie the
  definitions to known objects or show that the hypotheses can be met, in Lean and Mathlib with its
  own copy of the definitions; Comparator accepts [`Solution.lean`](Solution.lean) against it, under Lean's kernel
  and NanoDa.
- **Statements:** Theorem 1 and the lemmas are stated as in the paper. Two definitions are read
  precisely (Equation (1) over distinct quartets, E3; `Pairs(v)` restricted to pairs that give a
  network, E4), and two claims are corrected (E5, E6), with the author of the formalization.
- **Proofs:** every proof follows the paper's, except one step: the uniqueness in Lemma 1, which
  the paper derives from Observation 2 and which needs another argument (E1, Section 7).

## 1. Summary

- **Errors.** Two claims are false. Section 2.4 says that the score "will never decrease as the
  number of reticulations increases"; with exactly `k` reticulations, as the section computes the
  networks, it can (E5). Section 3.2 says that the true network is the unique network satisfying
  all its quartets, hence the unique optimum; a network with more reticulations that displays more
  quartets ties it, and CAMUS itself can return it (E6). Neither affects Theorem 1.
- **Gaps.** The proof of Lemma 1 derives uniqueness from Observation 2, which gives only existence;
  uniqueness follows from the vertex-disjointness of the cycles (E1). Section 2.2 calls `M[r]` the
  score of the best network, which counts the quartets of `Q` displayed, while `M[r]` counts those
  satisfied; they differ by a constant (E2).
- **Definitions read precisely.** Summing `δ` over the multiset `Q`, as Equation (1) is written,
  makes a quartet's multiplicity enter twice (`m²` instead of `m`); Section 2.3's weighted-set reading is meant (E3).
  `Pairs(v)`, read literally, contains pairs that give no network and make the recurrence circular
  (E4).
- **Missing hypotheses.** The corrected Section 3.2 needs the true network to be identifiable under
  inclusion and ties to be broken toward the fewest reticulations (Section 4).
- **Redundant hypotheses.** None.
- **Use of cited results.** Observation 2 is used correctly for the existence half of Lemma 1, and
  is proved here; it does not give the uniqueness half (E1).
- **Typos.** A few, in Definition 3, Figure 1, Sections 2.2, 3.2 and 3.4, and the references (E7).

## 2. Results from prior work and how the paper uses them

### Proved in `External/`

| Result | Where the paper uses it | Source | Theorem in `External/` |
| --- | --- | --- | --- |
| Observation 2: for every binary level-1 network `N`, `ab\|cd ∈ Q(N_r)` if and only if `a, b` is separated from `c, d` by deleting a cut edge of `N`, or two edges of a cycle one of which is incident with the cycle's bottom node | Proof of Lemma 1 (Section 2.1): "This lemma follows directly from Observation 2 in Warnow et al. (2025)" | T. Warnow, Y. Tabatabaee, S. N. Evans, *Advances in estimating level-1 phylogenetic networks from unrooted SNPs*, J. Comput. Biol. 32 (2025) 3–27, [doi:10.1089/cmb.2024.0710](https://doi.org/10.1089/cmb.2024.0710), Section 2.1: "The following observation is straightforward and the proof is omitted." | [`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L186), with [`External.observation2_forward`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L79) and [`External.observation2_backward`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L155) ([`Camus/External/WarnowTabatabaeeEvans/`](Camus/External/WarnowTabatabaeeEvans)) |

The Lean statement ([`External.WarnowTabatabaeeEvansObservation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L69)) is the source's: a switching
of `N`, which keeps one incoming edge of every vertex other than the root, is a tree contained in
`N` (the source's Definition 5), whose unary vertices and unlabelled leaves change no split; a
vertex of indegree 2 on a cycle is the cycle's bottom node; and the "two edges ... one of which"
is read as at least one, since deleting both edges into the bottom node separates the same pairs as
deleting the edge below it. The proof uses that a switching is a spanning tree that leaves out
exactly one edge into each cycle's bottom, so that, the cycles being vertex-disjoint, deleting a
cut edge, or an edge of a cycle together with the left-out one, leaves the same components in the
network as in the switching ([`Camus/External/WarnowTabatabaeeEvans/README.md`](Camus/External/WarnowTabatabaeeEvans/README.md)).

### Assumed

Nothing.

### Standard facts used without citation

| Fact | Where the paper uses it | In the formalization |
| --- | --- | --- |
| Deleting one incoming edge of each reticulation leaves a spanning tree | Definition 1 | [`RootedNetwork.switching_existsUnique_path`](Camus/Network/Completeness/Tree.lean#L143), [`RootedNetwork.exists_switching`](Camus/Network/Cuts.lean#L43) |
| In a tree, a quartet `ab\|cd` is induced if and only if an edge separates `{a, b}` from `{c, d}`, i.e. some clade contains one pair and no taxon of the other | Definition 1, and `Q(T)` | [`Realization.baseline_displays_iff`](Camus/Network/Baseline/Main.lean#L38) |
| Suppressing vertices of indegree and outdegree 1 changes no displayed quartet | The definition of `T + e` (Section 2.1) | [`GraphSubdivision.displays_iff`](Camus/Network/Subdivision/Invariance.lean#L48), [`SupportSubdivision.single_edge_reduction`](Camus/Network/Completeness/Main.lean#L127) |
| Isomorphic networks display the same quartets | Throughout | [`RootedNetwork.Iso.displays_iff`](Camus/Network/Isomorphism/Invariance.lean#L31) |
| Adding edges above pairs whose cycles share no vertex gives a rooted binary level-1 network built on `T` | Proof of Theorem 1: "By design, the solution that CAMUS outputs is a level-1 phylogenetic network N that extends T" | [`Realization.levelOne`](Camus/Network/Realization/Construction.lean#L72), [`Realization.support`](Camus/Network/Realization/Construction.lean#L45) |
| Every level-1 network built on `T` is obtained so, from the pairs of its non-tree edges | Sections 2.2 and the proof of Theorem 1, which treat a network as its set of added edges | [`SupportSubdivision.canonical_iso`](Camus/Network/Completeness/Main.lean#L114), [`SupportSubdivision.extracted_separated`](Camus/Network/Completeness/Main.lean#L67) |
| A level-1 network on `n` leaves has at most `n − 1` reticulations | Section 2.4: "it is known that a level-1 phylogenetic network on n leaves will not have more than n−1 reticulations" | [`RootedNetwork.anchored_reticulation_bound`](Camus/Network/Reticulations.lean#L227), for networks built on `T`, which is the case the section needs |

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Observation 2 (Warnow, Tabatabaee and Evans 2025) | Proof of Lemma 1 | Applied correctly for existence; it does not give uniqueness, which needs the vertex-disjointness of the cycles (E1) |

The other citations give context, or support the pipelines and the experiments, which are not
formalized: the statistical consistency of ASTRAL (Mirarab et al. 2014) in Sections 3.1 and 3.2 and of
quartet-based methods under the model of Warnow et al. (2025) in Section 3.2, the constant-time computation of `δ` in
Section 2.3 (Warnow et al. 2025; Gambette et al. 2012), ghost lineages (Tricou et al. 2025), and the
methods, simulators and data of Sections 1, 3 and 4.

## 3. Errors and gaps in the paper

**E1. Proof of Lemma 1 (Section 2.1, `mthst2`): uniqueness.** The proof is one sentence: "This
lemma follows directly from Observation 2 in Warnow et al. (2025)." Observation 2 gives the
existence of the non-tree edge. If `q` is satisfied by `N`, it is displayed and not in `Q(T)`, so it
is not separated by a cut edge of `N` (a cut edge of a network built on `T` is an edge of `T` and
separates only quartets of `T`), and hence by two edges of one cycle `C`, one of them at its bottom
node; the same cut separates `q` in `T + e`, for `e` the non-tree edge of `C`. Observation 2 does not
say that this cycle is unique. Uniqueness follows from the vertex-disjointness of the cycles. Since
`q = ab|cd` is not in `Q(T)`, the paths of `T` from `a` to `b` and from `c` to `d` meet in a vertex
`z` (Warnow et al.'s Definition 4 states this form of `Q(T)`). If `T + e` displays `q`, the two edges
whose deletion separates the pairs lie on the cycle of `e`; a path of `T` meets that cycle in one
subpath, so if `z` were off the cycle it would stay joined to `a` or `b`, and to `c` or `d`, and the
pairs would not be separated. So `z` lies on the cycle of `e`, and two edges satisfying `q` would give
two cycles through `z`. The lemma holds. The formalization proves existence from Observation 2
([`RootedNetwork.novel_edge_exists`](Camus/Preliminaries/Lemma1/Cuts.lean#L95)) and uniqueness by this argument ([`RootedNetwork.novel_edge_unique`](Camus/Preliminaries/Lemma1/Unique.lean#L202),
[`RootedNetwork.nonbaseline_pair_paths_intersect`](Camus/Preliminaries/Lemma1/Unique.lean#L85)). The bioRxiv versions gave another proof, by
contradiction ("Let v be the LCA of the roots of the two cycles. Then v is in a cycle that contains
the roots of both cycles, and N is not level-1"), whose last step does not follow: the paths
of the tree from that common ancestor to the two cycles form no cycle, and two vertex-disjoint cycles
are allowed in a level-1 network.

**E2. Section 2.2: the score and `M[r]`.** The section defines the score of `N` as "the number of
quartet trees in Q that also appear in Q(N_r)", and its second paragraph ends: "Thus, M[r] is the
score of the best level-1 network possible built on T". But `M[r]` counts the quartets satisfied by
the network, those in `Q(N_r) \ Q(T)`, as the proof of Theorem 1 says ("M[r] is the number of
quartet trees in Q that are satisfied by N and not by T"). The two numbers differ by the number of
quartets of `Q` (with multiplicity) in `Q(T)`, the same for every network built on `T`, so they have
the same optimal networks. The formalization proves both: the output satisfies `M[r]` quartets, and
no network built on `T` satisfies more or displays more ([`theorem1`](Camus/DP/Theorem1.lean#L109)). The definition of the score and this
sentence appear only in the published version.

**E3. Definition 4 and Equation (1): a quartet's multiplicity enters twice.** "... let Q be a
multiset of quartet trees. We define δ_T(q,(u,w)) to be the number of times q appears in Q if q is satisfied
by an edge e added above (u,w); otherwise, the value is 0", and `s_e(u,w) = Σ_{q∈Q} δ_T(q,(u,w))`,
"the number of quartets in Q satisfied by the edge e added above (u,w)". If the sum runs over the
elements of the multiset, a quartet that appears `m` times contributes `m²`, not `m`: for
`Q = {q, q}` the sum is 4 and the number of satisfied quartets 2
([`Counterexamples.squared_multiplicity_counterexample`](Camus/Galled/Counterexamples.lean#L135)). Section 2.3 gives the intended reading: "Q
can be equivalently represented as a weighted set, where the weight of an element is the number of
times the element appears in Q". The formalization sums over the distinct quartets of `Q`
([`DynamicProgramming.edgeWeight`](Challenge.lean#L665), [`Camus.equation1`](Camus/Score.lean#L50)). The algorithm and its results are unaffected.

**E4. Section 2.2: `Pairs(v)` contains pairs that give no network.** "[W]hen v≠r, we let Pairs(v)
denote the set of all ordered pairs of nodes (u,w) in T such that lca_T(u,w)=v; note that this
allows u=v with w below v". Read literally, this also contains `(u, v)` with `u` below `v`, and
`(v, v)`. Adding an edge from above `u` to above an ancestor of `u` creates a directed cycle, and
`(v, v)` subdivides one edge twice, so these pairs give no phylogenetic network. They also make the
recurrence circular: for `(v, v)` the cycle contains no vertex of `T`, and Equation (5) gives
`s_dp(v, v, v) = M[v]`, so that `M[v]` appears on both sides of Equation (2). The section's own
description excludes them ("a set of ordered pair (u,w) of nodes in T so that the triplet (u,w,v)
would be assigned to a non-tree edge we would add to T"), and at the root the paper's set already
excludes `u = r` and `w = r`. The formalization takes `Pairs(v)` to be the pairs with target `v`,
ends other than the root, and recipient `w` not an ancestor of (or equal to) the donor `u`
([`EdgeAbove.Admissible`](Challenge.lean#L234), [`DynamicProgramming.pairsAt`](Challenge.lean#L575)); at the root this is the paper's set, and no
pair that gives a network is lost. Ghost lineages (`u = v`) are kept. Theorem 1 holds with this
reading.

**E5. Section 2.4: the best score with exactly `k` reticulations can decrease as `k` grows.** "By
design, the score (the number of quartets in Q that are satisfied) will never decrease as the
number of reticulations increases". The section then computes, for each `k`, a network `N_k` that
"contains exactly k non-tree edges" and maximizes the score among such networks, and adds columns
"until we no longer get an improvement in score". For exact numbers of reticulations the claim is
false. Take `T = (A,(B,(D,C)))` and `Q = {AC|BD}`. A network built on `T` with two reticulations, a
triangle at the root and an edge from above `(B,(D,C))` to above `C`, displays `AC|BD`. With three
reticulations, the most that a tree with four leaves allows, the cycles have vertex-disjoint
footprints on the three internal vertices of `T`, so each is a triangle on one vertex, and triangles
change no displayed quartet: every such network displays only the quartet `AB|CD` of `T`
([`not_exactCountMonotone`](Camus/Restriction/Monotonicity.lean#L37), from [`Counterexamples.graph_exact_budget_nonmonotone`](Camus/Restriction/Witness.lean#L410)). For "at most `k`"
reticulations the claim holds, trivially, since the networks allowed only grow with `k`
([`Camus.atMostScore_mono`](Camus/Score.lean#L172), for an abstract finite family of networks). A drop requires every internal vertex of `T` to lie on a cycle of every
optimal network with `k` reticulations, since otherwise a triangle at a free vertex gives `k + 1`
reticulations and the same score; here it happens at `k = n − 1`, past the point where the stopping
rule stops. The four properties of the networks `N_k` that the section asks for hold
([`BudgetDP.reticulation_restriction`](Camus/Restriction/Main.lean#L61)).

**E6. Section 3.2: the true network need not be the unique optimum, and CAMUS need not return
it.** "When Q is a multi-set version of Q(N_r), then CAMUS will add the correct reticulations and
return N, since this is the unique network that can satisfy all the quartets in Q(N_r), and hence N
will be the unique solution to CAMUS' optimization problem." The objective counts the quartets of
`Q` that a network displays, so a network built on `t` that displays a superset of `Q(N_r)` ties
with `N`. Take for `N` and for `t` the tree `(O,((B,A),(D,C)))`, and for `Q` its five quartets. The
network obtained by adding an edge above `(A, C)` is built on `t`, has a five-vertex cycle that
keeps the outgroup outside, and displays the five quartets; it is optimal too, with one reticulation
against none ([`not_uniqueOptimum`](Camus/Pipelines/Uniqueness.lean#L49)). On this input every weight of Equation (1) is 0, and a valid
backtracking trace of the dynamic program adds that edge ([`camus_may_add_edge`](Camus/Pipelines/Uniqueness.lean#L134)), so CAMUS may return
it. Adding a triangle at an internal vertex of `t` that lies on no cycle of the true network gives the
same failure, and
excluding small cycles does not help, since the cycle here has five vertices. The claim holds under
two more hypotheses (Section 4): the true network is identifiable under inclusion, and ties are
broken toward the fewest reticulations ([`recovery`](Camus/Pipelines/Uniqueness.lean#L151)); a tree is identifiable under inclusion
([`tree_identifiable`](Camus/Pipelines/Uniqueness.lean#L190)). The statistical consistency argued in the rest of the section rests on this
step and on the models of Warnow et al. (2025), which are not formalized. The bioRxiv versions already claimed the
consistency of this pipeline; the uniqueness sentence, its justification, appears only in the
published version.

**E7. Typos.**

- Definition 3: "let T be a rooted tree and u and w be nodes in N" should be "nodes in T".
- Figure 1, caption: "it is satisfied by the added edge from u′ to v′" should be "from u′ to w′".
- Section 2.2, first sentence: "CAMUS seeks to add edges to N" should be "to T".
- Section 3.2: "any tree t ∈ Q(N_r) can be used as the basis for N" and "suppose that there is some
  t ∈ Q(N_r)" mean a displayed tree, `t ∈ 𝒯` of Definition 1, not a quartet tree; and "as the
  number of gene trees increases", in the pipeline for SNPs, means sites.
- Lemma 2: "Let N be a level-1 phylogenetic network N extending T" repeats `N`; Figure 1's caption
  says "the rooted trees (A,((D,E),G))" for one tree.
- References: NANUQ is *Algorithms Mol Biol* 14:24, not 14:25; and "NANUQ+ (Allman et al. 2019)", in
  the introduction and the conclusion, cites the 2019 paper on NANUQ, while NANUQ+ is Allman, Baños,
  Rhodes and Wicke, *Algorithms Mol Biol* 20 (2025) 14.

## 4. Missing hypotheses

| Where | Missing hypothesis | Counterexample without it | In the formalization |
| --- | --- | --- | --- |
| Section 3.2: "N will be the unique solution to CAMUS' optimization problem" | The true network `N` is identifiable under inclusion: every network built on `t` that displays all the quartets of `N`, with no more reticulations, is isomorphic to `N`; and ties are broken toward the fewest reticulations | E6: the tree `(O,((B,A),(D,C)))` and the network with one added edge above `(A, C)` both display all five quartets | Hypotheses `identifiable` and `fewest` of [`recovery`](Camus/Pipelines/Uniqueness.lean#L151); [`tree_identifiable`](Camus/Pipelines/Uniqueness.lean#L190) shows that every tree satisfies the first |
| Section 3.4: "for t small enough (specifically, t<(f2−f3)/(f2+f3)), then we will include q2" | `f2 + f3 > 0` | For `f2 = f3 = 0` the ratio is undefined (the test `f2 − f3 > t·(f2+f3)` then keeps no second quartet) | Hypothesis `0 < f₂ + f₃` of [`retainSecond_iff_ratio`](Camus/Pipelines/Filtering.lean#L34) |

No other statement of the paper needs a hypothesis that it leaves unstated. The trees are
phylogenetic trees, with distinct leaf labels, which the statements assume
([`PhyloTree.WellLabelled`](Challenge.lean#L138)). The restriction of `Pairs(v)` (E4) is part of a definition.

## 5. Redundant hypotheses

None. Every hypothesis of the formal statements of Lemmas 1 and 2, Theorem 1 and Section 2.4 is used
by its proof.

## 6. How the formalization reads the paper

- **Trees, quartets and display.** A tree is a full binary tree with labelled leaves ([`PhyloTree`](Challenge.lean#L125));
  its vertices are addressed by their paths from the root. A quartet is written with its four taxa
  in increasing order and one of three splits ([`Quartet`](Challenge.lean#L158)). Definition 1's trees of a network are its
  switchings: one incoming edge kept at every vertex other than the root
  ([`RootedNetwork.Switching`](Challenge.lean#L342)), which in a binary network is one incoming edge kept at each
  reticulation. A quartet is displayed, `q ∈ Q(N_r)`, when some switching has an edge whose removal
  separates its two pairs ([`RootedNetwork.DisplaysQuartet`](Challenge.lean#L358)). This is the paper's notion: in a tree,
  a quartet is induced exactly when an edge separates its pairs, whatever unary vertices and
  unlabelled leaves remain. For the constraint tree it agrees with the clades of `T`
  ([`Realization.baseline_displays_iff`](Camus/Network/Baseline/Main.lean#L38), in the Challenge as [`Challenge.tree_displays_iff`](Challenge.lean#L789)).
- **Networks.** A rooted binary level-1 phylogenetic network is a finite directed graph with the laws
  of [`RootedNetwork.RootedBinaryLevelOne`](Challenge.lean#L317): acyclic, every vertex reachable from the root, the root
  of indegree 0 and outdegree 0 or 2, the other vertices leaves (1, 0), tree vertices (1, 2) or
  reticulations (2, 1), the leaves labelled bijectively, and any two distinct cycles of the
  underlying undirected graph vertex-disjoint ("level-1", as in the paper). Triangles are allowed, as
  in CAMUS.
- **Built on `T`.** "N is built on T" is read as: `T`, with its edges subdivided, is a switching of `N`
  with the same root and the same labelled leaves ([`RootedNetwork.AnchoredExtension`](Challenge.lean#L417),
  [`SupportSubdivision`](Challenge.lean#L390)). These are the networks obtained by adding edges to `T`, as CAMUS does: an
  added edge never starts above the root ("we cannot add an edge to T that begins above the root of
  T"), and cannot end above it (it would close a directed cycle). Definition 1's "built on t" also
  allows a network whose root is the tail of an edge into a reticulation, with `t` the displayed tree
  left after suppressing the root. Such networks are not in the formal class. They do not change the
  optimum, since moving that edge's tail onto the edge from the root of `T` to its child on the other
  side of the cycle gives a network built on `T` that displays the same quartets; this is not formalized, and Theorem 1 is stated for the
  root-preserving class, over which the paper's dynamic program optimizes.
- **Added edges and `T + e`.** An added edge is a pair `(u, w)` of vertices of `T`; the network
  obtained by adding the edges of a family `E` is `Realization.graph t E`. Every network built on `T`
  is isomorphic to `Realization.graph t E` for the family of pairs of its non-tree edges
  ([`SupportSubdivision.canonical_iso`](Camus/Network/Completeness/Main.lean#L114)), and deleting the other non-tree edges of `N` leaves a subdivision of
  the canonical network of the single pair of `e` ([`SupportSubdivision.single_edge_reduction`](Camus/Network/Completeness/Main.lean#L127)), so
  that `T + e` (Section 2.1: delete the other non-tree edges and suppress) is that canonical network,
  with the same displayed quartets ([`GraphSubdivision.displays_iff`](Camus/Network/Subdivision/Invariance.lean#L48)). On an edge of `T` that carries ends of two added edges, the end
  of the outer cycle comes before a ghost donor ([`Realization.outerEndpoints`](Challenge.lean#L481),
  [`Realization.ghostEndpoints`](Challenge.lean#L488)); in every network built on `T` this order is forced
  ([`SupportSubdivision.no_ghost_before_endpoint`](Camus/Network/Completeness/Order.lean#L33)).
- **The recurrence.** Definition 5's children are children in the network `T + e`, as the
  definition says: at the parent of `u` (or of `w`), whose edge to `u` carries an end of `e`, the
  child on the cycle is the new vertex ([`Realization.child`](Challenge.lean#L535), [`Realization.offChild`](Challenge.lean#L543)). With the
  children in `T`, Equations (4) and (5) would count `M[u]` (or `M[w]`) twice, and drop the subtree of
  its sibling, whenever `u` (or `w`) is the left child of a vertex of the cycle other than the target. The equations'
  condition is `l(x) ∉ γ(u,w)`; in the JATS source the membership symbol is struck through, which a
  plain-text extraction loses. Equation (1) is read over the distinct quartets of `Q` (E3), and
  `Pairs(v)` with the restriction of E4. [`DynamicProgramming.Array`](Challenge.lean#L618) states the recurrence; it
  determines `M` on the vertices of `T`, and a solution and a backtracking trace exist
  ([`DynamicProgramming.exists_array_trace`](Camus/DP/Correctness.lean#L401)). [`DynamicProgramming.Trace`](Challenge.lean#L631) allows any maximizing branch,
  so Theorem 1 covers every way of breaking ties.
- **Theorem 1.** It is stated for every array satisfying the recurrence and every backtracking
  trace, against every network built on `T`. Its score is the number of quartets of `Q` satisfied,
  counted with multiplicity, and it also states the optimality of the number displayed (E2). The
  paper's induction on the number of leaves below a vertex is an induction on the measure
  [`DynamicProgramming.remainingDepth`](Camus/DP/Packing.lean#L121) (the height of `T` minus the depth of the vertex), which also
  decreases from a vertex to its descendants: the same induction over subtrees.
- **Section 2.4.** The paper describes the modified dynamic program by the meaning of its entries
  `M[v, k]` ("the solution found for subtree T_v of the network limited to allowing k non-tree
  edges") and gives no recurrence. The formalization's recurrence ([`BudgetDP.Array`](Challenge.lean#L722)) has that
  meaning: a row `M v k` is empty when no family of `k` added edges below `v` is feasible, and
  otherwise holds the best value; the fork case convolves the children's rows, and the case of an
  edge with target `v` distributes the remaining budget over the subtrees hanging off its cycle, by
  a knapsack that keeps the maximum after each convolution. The networks `N_k` are given by
  existence: the value of each nonempty row is attained by a network with exactly `k` reticulations,
  not computed by backtracking. The number of reticulations is the number of vertices of indegree 2
  ([`RootedNetwork.reticulationCount`](Challenge.lean#L676)), which for a network built on `T` is its number of non-tree
  edges. The stopping rule is not formalized.
- **Section 2.3.** The formalization does not model an implementation. It defines counts of the
  operations that the paper's analysis lists ([`Complexity.scalarOperations`](Camus/Complexity/Operations.lean#L146),
  [`Complexity.budgetOperations`](Camus/Complexity/Operations.lean#L158), [`Complexity.scalarSpace`](Camus/Complexity/Operations.lean#L264): the tables of lowest common ancestors,
  leaf sets and depths, one quartet test per candidate pair and distinct quartet, one read per
  subtree hanging off each candidate cycle, the comparisons) and bounds them by `32 n² (|Q| + n)`,
  `100 n² (|Q| + m³ n)` for `m ≥ 1`, and `32 n⁴` when the quartets of `Q` are on taxa of `T`, with
  `|Q|` the number of distinct quartets, as in the paper. The quartet test is a unit-cost oracle
  ([`Complexity.DeltaOracle`](Camus/Complexity/Operations.lean#L80)) whose answers give Equation (1)'s weights; its constant-time
  implementation after an `O(n²)` preprocessing, which the paper takes from Warnow et al. (2025) and
  Gambette et al. (2012), is assumed by the cost model, not proved.
- **Section 3.4.** Algorithm 1 is applied to the numbers of copies of the three topologies rather
  than to their relative frequencies, which gives the same test, since its inequality is
  homogeneous; ties are broken by a fixed order of the three topologies, where the paper's "without
  loss of generality" leaves them open ([`Algorithm1.rank`](Camus/Pipelines/Algorithm1.lean#L78)).

**Corrections.** Two claims of the paper are false (E5, E6). The formalization proves the closest
correct statements, chosen with the author of the formalization:

- Section 2.4's monotonicity, for "at most `k`" reticulations: immediate for networks built on `T`,
  since a network with at most `j ≤ k` reticulations has at most `k`, and proved for an abstract
  finite family of networks ([`Camus.atMostScore_mono`](Camus/Score.lean#L172)); the section's four properties of the networks
  `N_k` hold for exact numbers ([`BudgetDP.reticulation_restriction`](Camus/Restriction/Main.lean#L61)).
- Section 3.2's recovery, under identifiability under inclusion and the tie-break toward the fewest
  reticulations ([`recovery`](Camus/Pipelines/Uniqueness.lean#L151)); for an abstract finite family of candidate networks, also along a
  sequence of inputs and in probability ([`correctedConsistency`](Camus/Pipelines/Recovery.lean#L68), [`correctedEventualConsistency`](Camus/Pipelines/Recovery.lean#L99),
  [`correctedStatisticalConsistency`](Camus/Pipelines/Statistical.lean#L43)).

## 7. Departures from the paper's proofs

| Result | The paper's argument | The formalization's | Why it is necessary | E-item |
| --- | --- | --- | --- | --- |
| Lemma 1, uniqueness | "This lemma follows directly from Observation 2" | Existence from Observation 2 ([`RootedNetwork.novel_edge_exists`](Camus/Preliminaries/Lemma1/Cuts.lean#L95)); uniqueness from the vertex-disjointness of the cycles: the paths of `T` joining the two pairs of `q` meet, and their meeting vertex lies on the cycle of every edge that satisfies `q` ([`RootedNetwork.novel_edge_unique`](Camus/Preliminaries/Lemma1/Unique.lean#L202)) | Observation 2 gives existence, not uniqueness: the paper's step has a gap that cannot be filled from Observation 2 alone | E1 |

Every other proof follows the paper's: Lemma 2 by the two cycles through the target; Theorem 1 by
the paper's induction, with its two cases, Lemma 2 for the edge with target `y`, the subtrees hanging
off its cycle as the subproblems of Equations (4) and (5), Equation (2), and Lemma 1 for the
additivity of the score. The formal proof of Theorem 1 applies Lemma 1 outside the induction, to the output and to the family
of each competing network, to equate the number of satisfied quartets with the total weight of the
added edges, where the paper invokes it inside the induction; and it reduces every competing network to its family of added edges, which the paper
identifies with the network. The recurrence of Section 2.4 and Observation 2 have no proof in the
paper to follow.

## 8. What each result depends on

A summary of the output of [`scripts/Audit.lean`](scripts/Audit.lean), which also checks that every declaration of the library depends only
on Lean's three standard axioms.

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| Lemma 1 | [`Camus.lemma1`](Camus/Preliminaries/Lemmas.lean#L138), [`Camus.lemma1_union`](Camus/Preliminaries/Lemmas.lean#L289) | [`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L186) |
| Lemma 2 | [`Camus.lemma2`](Camus/Preliminaries/Lemmas.lean#L160), [`EdgeAbove.target_unique`](Camus/Tree/Geometry.lean#L161) | – |
| Equations (1)–(5) | [`Camus.equation1`](Camus/Score.lean#L50), [`DynamicProgramming.Array`](Challenge.lean#L618), [`DynamicProgramming.s`](Challenge.lean#L610), [`DynamicProgramming.equation4`](Camus/DP/Correctness.lean#L77), [`DynamicProgramming.equation5`](Camus/DP/Correctness.lean#L87) | – |
| Theorem 1 | [`Camus.theorem1`](Camus/DP/Theorem1.lean#L109) | [`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L186) |
| Section 2.3 | [`Complexity.scalarOperations_bound`](Camus/Complexity/Operations.lean#L167), [`Complexity.scalarSpace_bound`](Camus/Complexity/Operations.lean#L270) | – |
| Section 2.4, the networks `N_k` | [`BudgetDP.reticulation_restriction`](Camus/Restriction/Main.lean#L61) | [`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L186) |
| Section 2.4, `m ≤ n − 1` | [`RootedNetwork.anchored_reticulation_bound`](Camus/Network/Reticulations.lean#L227) | – |
| Section 2.4, the operations | [`Complexity.budgetOperations_bound`](Camus/Complexity/Operations.lean#L187) | – |
| Section 2.4, monotonicity (E5) | [`not_exactCountMonotone`](Camus/Restriction/Monotonicity.lean#L37); [`Camus.atMostScore_mono`](Camus/Score.lean#L172) | [`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L186); – |
| Section 3.2, uniqueness (E6) | [`not_uniqueOptimum`](Camus/Pipelines/Uniqueness.lean#L49), [`camus_may_add_edge`](Camus/Pipelines/Uniqueness.lean#L134) | – |
| Section 3.2, corrected | [`Camus.recovery`](Camus/Pipelines/Uniqueness.lean#L151), [`Camus.tree_identifiable`](Camus/Pipelines/Uniqueness.lean#L190), [`correctedStatisticalConsistency`](Camus/Pipelines/Statistical.lean#L43) | – |
| Section 3.4 | [`retainSecond_iff_ratio`](Camus/Pipelines/Filtering.lean#L34), [`Algorithm1.filterQuartets_mono`](Camus/Pipelines/Algorithm1.lean#L191) | – |

The route check ([`scripts/route_check.py`](scripts/route_check.py), run in CI) compares the results that each formal proof uses
with those that the paper's proof cites ([`docs/paper_routes.tsv`](docs/paper_routes.tsv), written by hand from the published version).
Every proof uses the results that the paper's proof cites, and uses three more, recorded in
[`docs/route_differences.tsv`](docs/route_differences.tsv), each with its reason: Lemma 1 reaches Lemma 2 through the construction
of `T + e`, not through its argument, and Theorem 1 uses `s_e` and `s(y)`, which its proof names
without citing Equations (1) and (3).

## 9. Not formalized

- The pipelines' statistics (Section 3): the models of Warnow et al. (2025) and of the network
  multispecies coalescent, the statistical consistency of ASTRAL and of the SNP pipeline beyond its
  deterministic step (E6), and Algorithm 1's motivation from the multispecies coalescent.
- The stopping rule of Section 2.4 ("until we no longer get an improvement in score"), and
  backtracking in the modified dynamic program.
- The running time and memory of an implementation (Section 2.3), beyond the accounting described in
  Section 6, and the constant-time computation of `δ`.
- Definition 1's networks whose root lies above the root of `T` (Section 6).
- The experiments (Sections 4 and 5), the software, and the supplement, which contains no
  mathematics.

## 10. The paper in the literature

The search was made on 10 October 2026, in the publisher's and Europe PMC's records, PubMed, Crossref,
bioRxiv, arXiv, Semantic Scholar and OpenAlex (the papers that CAMUS cites and those that cite it),
the CAMUS repository, the authors' pages, GitHub, the Palomar registry, formal-conjectures, the
Archive of Formal Proofs and the public archive of the Lean Zulip. The works below are the closest to
CAMUS's question, adding edges to a fixed tree to explain quartets, and every work that cites it.

**Versions.** The bioRxiv versions v1 (4 February 2026) and v2 (5 February 2026) differ only in a
date, a typo and layout. The published version (7 July 2026) keeps Lemma 2, Theorem 1 and its proof,
Equations (1)–(5), `Pairs(v)` and Section 2.4. It changes Lemma 1's proof (E1), and adds Definition
1's sentences on networks built on a tree, the definition of the score and the sentence on `M[r]`
(E2), the weighted-set reading of `Q` and the memory bound in Section 2.3 (E3), the uniqueness
sentence of Section 3.2 (E6), a section on ASTRAL and the avian experiment. No erratum or later version was found. The software's release 1.0.2 (15 September 2026,
<https://github.com/jsdoublel/camus/releases>) fixes "issue #28 that could cause some output networks
to fail to be level-1 (due improper placement of branches attaching to the same edge in the
constraint tree)" and a non-optimality "in some cases with high values of k" (the exact-`k` code omitted the
subtree off the cycle at `v` in the case `u = v`, which Equation (5) includes). These concern the
implementation, not the paper; both points are explicit in the formalization (Section 6, and
[`DynamicProgramming.sdpGhost`](Challenge.lean#L599)).

### Before the paper

- **Two-phase methods.** T-REX (Makarenkov, *Bioinformatics* 17 (2001) 664–668,
  [doi](https://doi.org/10.1093/bioinformatics/17.7.664)) adds reticulations to a distance tree; Cao,
  Zhu and Nakhleh (WABI 2019, LIPIcs 143:21, [doi](https://doi.org/10.4230/LIPIcs.WABI.2019.21)) study
  augmenting a species tree into a network and find the augmentation step the weak point. CAMUS
  belongs to this family; its contribution is an exact polynomial algorithm for its objective.
- **Level-1 networks from quartets and triplets.** Gusfield's galled trees (*J. Comput. Syst. Sci.* 70
  (2005) 381–398, [doi](https://doi.org/10.1016/j.jcss.2004.12.009)); Gambette and Huber on encodings by
  triplets (*J. Math. Biol.* 65 (2012) 157–180, [doi](https://doi.org/10.1007/s00285-011-0456-y));
  Gambette, Berry and Paul (*J. Bioinform. Comput. Biol.* 10 (2012) 1250004,
  [doi](https://doi.org/10.1142/S0219720012500047)) and Keijsper and Pendavingh (*Bull. Math. Biol.* 76
  (2014) 2517–2541, [doi](https://doi.org/10.1007/s11538-014-0022-z)) reconstruct level-1 networks from
  their quartets in the sense of two vertex-disjoint paths. Without a fixed tree, van Iersel, Kelk
  and Mnich show that maximizing the number of triplets consistent with a level-`k` network is
  NP-hard, and give an exact exponential-time algorithm for level 1 (*J. Bioinform. Comput. Biol.* 7
  (2009) 597–623, [doi](https://doi.org/10.1142/S0219720009004308)). No exact algorithm for CAMUS's problem, with the
  tree fixed, was found before the paper.
- **The cited result.** Warnow, Tabatabaee and Evans (*J. Comput. Biol.* 32 (2025) 3–27,
  [doi](https://doi.org/10.1089/cmb.2024.0710)) estimate level-1 networks from unrooted SNPs; they
  state Observation 2 without proof (Section 2), and their Theorem 5 shows that `Q(N_r)` determines
  the unrooted topology of a level-1 network all of whose cycles have length at least five, and the
  bottom node of each cycle. This is identifiability by equality of quartet sets; E6 concerns
  inclusion.
- **Other level-1 methods.** NANUQ (Allman, Baños and Rhodes, *Algorithms Mol. Biol.* 14 (2019) 24,
  [doi](https://doi.org/10.1186/s13015-019-0159-2)) and NANUQ+ (2025,
  [doi](https://doi.org/10.1186/s13015-025-00274-w)) work from quartet concordance factors under the
  coalescent; Squirrel (Holtgrefe et al., *Mol. Biol. Evol.* 42 (2025) msaf067,
  [doi](https://doi.org/10.1093/molbev/msaf067)) from quarnets or sequence alignments; and the
  pseudolikelihood methods PhyloNet-MPL and SNaQ, which the paper compares with, from gene trees. Dinh and Baños (*Mol. Biol. Evol.* 42 (2025)
  msaf049, [doi](https://doi.org/10.1093/molbev/msaf049)) show that ASTRAL can return a tree not
  displayed by the network, even in non-anomalous settings, which bears on the pipelines' first step.

### Concurrent work

No work with the same result was found. Around the paper's first version: TriMouNet (Mao and
Grünewald, bioRxiv preprint, 17 February 2026, [doi](https://doi.org/10.64898/2026.02.14.705539)),
which assembles level-1 networks from trinets inferred from gene trees and which the paper names for
future comparison; InPhyNet (Kolbow, Kong and Solís-Lemus, bioRxiv preprint, May 2025,
[doi](https://doi.org/10.1101/2025.05.05.652278)), which merges level-1 subnetworks; SNaQ.jl (Kolbow et
al., *Bioinformatics* 42 (2026) btag289, [doi](https://doi.org/10.1093/bioinformatics/btag289)); and
the estimation of trees of blobs by quartet methods (Dai, Han and Molloy, *Genome Res.* 2026,
[doi](https://doi.org/10.1101/gr.282203.126)). These address related questions by other methods.

### Since the paper

- NetCS (Dai and Molloy, WABI 2026, LIPIcs 390:1, [doi](https://doi.org/10.4230/LIPIcs.WABI.2026.1))
  reconstructs level-1 blobs under the network multispecies coalescent, with consistency under its
  model; it notes that CAMUS "does not currently have statistical guarantees" under that model and "can be
  statistically inconsistent when ASTRAL-IV is used to construct the base tree", and benchmarks it on
  the paper's data.
- BROOQS (Arasti and Mirarab, bioRxiv preprint, September 2026, quoted from its version of
  9 September 2026, [doi](https://doi.org/10.64898/2026.08.31.748319)) reports that it "consistently outperforms CAMUS"
  and that "CAMUS tends to substantially overestimate the number of reticulations with its default
  criterion", the selection of the number of reticulations of Section 2.4.
- Holtgrefe, Huber, van Iersel and Moulton (arXiv preprint 2610.07855, 2026) and Kadereit et al.
  (*Am. J. Bot.* 2026, [doi](https://doi.org/10.1002/ajb2.70252), an empirical use) cite CAMUS without
  bearing on its results.
- No work correcting or extending the paper's theorems was found.

### Formalizations

No other formalization of CAMUS, of its Theorem 1, or of Observation 2 was found. Formalizations of
nearby phylogenetics exist in Lean: Allman, Degnan and Rhodes's identifiability of species trees
(<https://github.com/vltanh/lean4-adr11>, by the maintainer of this project, registered on
Palomar), trees, splits, quartets, consensus and the consistency of quartet-based species-tree methods
(<https://github.com/chaoszhang/lean4phylo>, October 2026), and partial modules on rooted networks for
NANUQ in an AI-agent research repository (<https://github.com/Sodelin/Research-Commons>); none treats
CAMUS. This work consulted none of them.

## 11. What's next

### Open directions

- **Identifiability under inclusion.** The corrected Section 3.2 ([`recovery`](Camus/Pipelines/Uniqueness.lean#L151)) needs the true network
  to be identifiable under inclusion among the networks built on `t` with no more reticulations. A
  tree is ([`tree_identifiable`](Camus/Pipelines/Uniqueness.lean#L190)), and a network of triangles is not. The natural conjecture, after
  Warnow et al.'s Theorem 5, is that a level-1 network whose cycles have length at least five is:
  a network built on `t` that displays all its quartets, with no more reticulations, is isomorphic to
  it. Proving it would give the deterministic step of Section 3.2 for such networks, and with the
  convergence of the observed quartets (Warnow et al. 2025) the statistical consistency of the SNP
  pipeline under the tie-break.
- **The tie-break and the stopping rule.** The tie-break toward the fewest reticulations is
  computable with the paper's own tools: run the dynamic program of Section 2.4 and keep the least `k`
  whose row attains the unrestricted optimum `M[r]`. For the selection of `k` in Section 2.4, E5 shows
  that the exact scores need not increase; the running maxima of the rows do, and the drop needs every
  internal vertex of `T` to be covered by the cycles of every optimal network with `k` reticulations.
  A characterization of when the exact scores are monotone, or a stopping rule with a guarantee, is
  open.
- **Definition 1's class.** Theorem 1 is stated for networks whose root is the root of `T`; extending
  it to every network of which `T` is a displayed tree, by the argument of Section 6, would match
  Definition 1 exactly.

### Simpler proofs

- **Theorem 1 splits into Lemma 1 and a packing problem.** Section 2.2 already observes that, by
  Lemma 1, the number of quartets satisfied by a network built on `T` is the sum, over its added
  edges, of the weights `s_e`. The proof of Theorem 1 can use this once, before the induction: the
  theorem is then the statement that the recurrence computes a maximum-weight family of pairs whose
  cycles share no vertex of `T`, a packing of paths in a tree, whose proof by induction over subtrees
  involves no quartet and no double counting. The paper's proof instead invokes Lemma 1 inside the
  induction. The formal proof is organized this way ([`DynamicProgramming.trace_correct`](Camus/DP/Correctness.lean#L123) and
  [`DynamicProgramming.array_upper`](Camus/DP/Correctness.lean#L164) work with abstract weights), checked in Lean.

### The formalization

The items of Section 9 are what remains: the statistical models of Section 3, the stopping rule and
backtracking of Section 2.4, a cost semantics for Section 2.3, and Definition 1's wider class of
networks. The general facts proved here about directed graphs, switchings, subdivisions and cycle
cuts ([`Camus/Network/`](Camus/Network)) could serve other formalizations of phylogenetic networks.
