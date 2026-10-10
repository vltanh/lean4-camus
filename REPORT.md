# Audit of the paper and the formalization

Paper: James Willson and Tandy Warnow, *CAMUS: scalable phylogenetic network estimation*,
Bioinformatics 42, Supplement 1 (2026), btag245, <https://doi.org/10.1093/bioinformatics/btag245>
(ISMB 2026; received 10 April 2026, accepted 16 April 2026, published 7 July 2026; CC BY 4.0). No
TeX source is public. The audit was made against the publisher's JATS XML, as distributed by
[Europe PMC (PMC13340232)](https://www.ebi.ac.uk/europepmc/webservices/rest/PMC13340232/fullTextXML),
whose identifiers serve as labels: Definition 1 is `mthst1`, Lemma 1 `mthst2`, Definition 2
`mthst3`, Lemma 2 `mthst4`, Definitions 3–5 `mthst6`–`mthst8`, Theorem 1 `mthst9`, and Equations
(1)–(5) `E1`–`E5` (these labels are written in code spans; the findings of this report are E1–E10).
Section, result and equation numbers are the published version's. The earlier versions, bioRxiv
[10.64898/2026.02.01.703143](https://doi.org/10.64898/2026.02.01.703143) v1 (4 February 2026) and
v2 (5 February 2026), differ in places noted below (Section 10).

Status of the formalization:

- **Proved:** Lemma 1 (both sentences, for every network built on the constraint tree), Lemma 2,
  Theorem 1 against every network built on `T` in the sense of Definition 1, that every level-1
  network is built on one of its trees, with at most `n − 1` reticulations, the running time and
  the peak memory of Section 2.3 for CAMUS written as a program in a cost semantics, the four
  properties of the networks of Section 2.4 for the networks returned by backtracking, with the
  running time and memory of the program that computes them, Algorithm 1's test, Section 3.2's
  argument as one statement about the SNP pipeline inside the site model of Warnow et al. (2025),
  and Quartet Filtering under the multispecies coalescent and the network multispecies coalescent,
  each by the paper's argument where the paper gives one. Four claims of the paper are refuted
  (E5–E8), and the closest correct statements are proved; one assumption of its design of Quartet
  Filtering fails under the network coalescent (E9).
- **Cited results:** the paper's proofs use Observation 2 of Warnow, Tabatabaee and Evans (2025),
  which its source states without proof, and Section 3.2 their site model and the convergence of
  the observed quartets. Both are proved here ([`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L187), [`External.support_tendsto`](Camus/External/WarnowTabatabaeeEvans/Sampling.lean#L99),
  Section 2), the second under a hypothesis that their model omits (Section 4). The quartet
  probabilities under the multispecies coalescent come from the Lean formalization of Allman,
  Degnan and Rhodes (2011), and the network coalescent from the maintainer's formalization of BROOQS
  (copied into [`Camus/External/NMSC/`](Camus/External/NMSC)). The formalization is unconditional: nothing is assumed.
- **Build:** `lake build` succeeds; the only `sorry`s are the fifteen in [`Challenge.lean`](Challenge.lean), by
  design. There is no `axiom`. [`scripts/Audit.lean`](scripts/Audit.lean) checks that every declaration of the library
  depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- **Challenge and Comparator:** [`Challenge.lean`](Challenge.lean) states Theorem 1, against Definition 1's class;
  the reduction of that class to the networks obtained by adding edges to `T`; the claim of
  Section 2.4, for the networks returned by backtracking; the refutations of E5 to E8; the
  corrected recovery of Section 3.2, and a counterexample showing its hypothesis necessary; and
  theorems that tie the definitions to known objects or show that the hypotheses can be met. They
  are written in Lean and Mathlib with the Challenge's own copy of the definitions, and Comparator
  accepts [`Solution.lean`](Solution.lean) against it, under Lean's kernel and NanoDa. The cost semantics,
  tree-basedness, the probabilistic statements and the coalescent models are in the library only.
- **Statements:** Theorem 1 and the lemmas are stated as in the paper. Two definitions are read
  precisely (Equation (1) over distinct quartets, E3; `Pairs(v)` restricted to pairs that give a
  network, E4), and four claims are refuted (E5–E8), with corrected statements chosen with the
  author of the formalization.
- **Proofs:** every proof follows the paper's, except at two steps (Section 7): the uniqueness in
  Lemma 1, which the paper derives from Observation 2 and which needs another argument (E1); and,
  for Theorem 1 over Definition 1's class, the networks whose root lies above the root of `T`, which
  the paper's proof does not treat and which are reduced to the others first (E8).

## 1. Summary

- **Errors.** Four claims are false. Section 2.4 says that the score "will never decrease as the
  number of reticulations increases"; with exactly `k` reticulations, as the section computes the
  networks, it can (E5). Its stopping rule, "until we no longer get an improvement in score", can
  stop before a better score, also when the scores never decrease (E6). Section 3.2 says that the
  true network is the unique network satisfying all its quartets, hence the unique optimum and
  CAMUS's output. A network with more reticulations, or with as many and a deeper donor, ties it,
  and CAMUS itself can return it; inside the site model of Warnow et al., such a tie with the fewest
  reticulations occurs with probability tending to 1, under every hypothesis of the section's
  argument, an outgroup included (E7). Section 3.2 also
  says that any tree of `N` can serve as a basis for `N`, which fails when the root of `N` lies on a
  cycle (E8). None affects Theorem 1.
- **A failing assumption.** Sections 3.3 and 3.4 design Quartet Filtering to keep the quartets of
  `Q(N_r)` and only them, which needs the displayed quartets to be the most frequent. Under the
  network multispecies coalescent they are, except in the anomalous configuration of Ané, Fogg,
  Allman, Baños and Rhodes (2024), whom the paper cites for ASTRAL: there the filter drops the
  quartet of `Q(N_r)` and keeps one outside it, for every threshold (E9).
- **Gaps.** The proof of Lemma 1 derives uniqueness from Observation 2, which gives only existence;
  uniqueness follows from the vertex-disjointness of the cycles (E1). Section 2.2 calls `M[r]` the
  score of the best network, which counts the quartets of `Q` displayed, while `M[r]` counts those
  satisfied; they differ by a constant (E2). The proof of Theorem 1 treats the networks obtained by
  adding edges to `T`, not the networks of Definition 1 whose root lies above the root of `T`; these
  display the quartets of networks of the first kind (E8).
- **Definitions read precisely.** Summing `δ` over the multiset `Q`, as Equation (1) is written,
  makes a quartet's multiplicity enter twice (`m²` instead of `m`); Section 2.3's weighted-set reading is meant (E3).
  `Pairs(v)`, read literally, contains pairs that give no network and make the recurrence circular
  (E4).
- **Missing hypotheses.** The corrected Section 3.2 needs the true network to be identifiable under
  inclusion, which fails even when every cycle has at least five vertices, and ties to be broken
  toward the fewest reticulations. The convergence of the observed quartets that Section 3.2 takes
  from Warnow et al. needs the substitution probabilities `p(e, s, s)` to be positive, which their
  model does not require. The motivation of Algorithm 1 needs a positive threshold (Section 4).
- **Redundant hypotheses.** None.
- **Use of cited results.** Observation 2 is used correctly for the existence half of Lemma 1, and
  is proved here; it does not give the uniqueness half (E1). Warnow et al.'s convergence of the
  observed quartets holds under the hypothesis above, and is proved here. The pattern of the quartet
  probabilities under the multispecies coalescent that motivates Algorithm 1 is correct.
- **Typos.** A few, in Definition 3, Lemma 2, Figure 1, Sections 2.2 and 3.2, and the references (E10).

## 2. Results from prior work and how the paper uses them

### Proved in `External/`

| Result | Where the paper uses it | Source | Theorem in `External/` |
| --- | --- | --- | --- |
| Observation 2: for every binary level-1 network `N`, `ab\|cd ∈ Q(N_r)` if and only if `a, b` is separated from `c, d` by deleting a cut edge of `N`, or two edges of a cycle one of which is incident with the cycle's bottom node | Proof of Lemma 1 (Section 2.1): "This lemma follows directly from Observation 2 in Warnow et al. (2025)" | T. Warnow, Y. Tabatabaee, S. N. Evans, *Advances in estimating level-1 phylogenetic networks from unrooted SNPs*, J. Comput. Biol. 32 (2025) 3–27, [doi:10.1089/cmb.2024.0710](https://doi.org/10.1089/cmb.2024.0710), Section 2.1: "The following observation is straightforward and the proof is omitted." | [`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L187), with [`External.observation2_forward`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L80) and [`External.observation2_backward`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L156) ([`Camus/External/WarnowTabatabaeeEvans/`](Camus/External/WarnowTabatabaeeEvans)) |
| The quartets of the SNPs converge to `Q(N_r)`: under the single site model of Warnow et al., with `p(e, s, s) > 0` on the tree edges, every quartet displayed by `N` is a quartet of an SNP with positive probability (the step of the proof of their Theorem 6, for clades), and every quartet of an SNP is displayed | Section 3.2: "According to the theory given in Warnow et al. (2025), as the number of gene trees increases, this multiset will be identical to Q(N_r) (when considered as a set), with probability converging to 1" | The same article, Section 4.2 and the proof of Theorem 6 | [`External.support_tendsto`](Camus/External/WarnowTabatabaeeEvans/Sampling.lean#L99), from [`External.SiteModel.exists_snp`](Camus/External/WarnowTabatabaeeEvans/SiteModel.lean#L1041) and [`External.SiteHistory.displays_of_mem_quartets`](Camus/External/WarnowTabatabaeeEvans/SiteModel.lean#L905) (the model: [`External.SiteModel`](Camus/External/WarnowTabatabaeeEvans/SiteModel.lean#L316)) |
| The quartet concordance factors of four components of a cycle of a level-1 network under the network multispecies coalescent are those of the induced metric quarnet | Sections 3.3 and 3.4: the distributions of quartet trees under the NMSC that motivate Quartet Filtering | H. Baños, *Identifying species network features from gene tree quartets under the coalescent model*, Bull. Math. Biol. 81 (2019) 494–534, through the maintainer's formalization of BROOQS (Arasti and Mirarab, bioRxiv 2026), copied into [`Camus/External/NMSC/`](Camus/External/NMSC) | [`Brooqs.nmsc_quartetCF`](Camus/External/NMSC/Cycle.lean#L743), with [`Brooqs.Net.weakPattern`](Camus/External/NMSC/Pattern.lean#L880) for every four taxa |
| A 3-cycle above two taxa can make the displayed quartet the least probable (an anomalous network) | Section 3.3: "ASTRAL can be provably inaccurate at estimating an underlying tree within the network under some conditions (Solís-Lemus et al. 2016, Ané et al. 2024, Dinh and Baños 2025)" | C. Ané, J. Fogg, E. S. Allman, H. Baños, J. A. Rhodes, *Anomalous networks under the multispecies coalescent: theory and prevalence*, J. Math. Biol. 88 (2024) 29 | [`Brooqs.net32_anomaly`](Camus/External/NMSC/ThreeCycle.lean#L581) |

The Lean statement ([`External.WarnowTabatabaeeEvansObservation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L70)) is the source's: a switching
of `N`, which keeps one incoming edge of every vertex other than the root, is a tree contained in
`N` (the source's Definition 5), whose unary vertices and unlabelled leaves change no split; a
vertex of indegree 2 on a cycle is the cycle's bottom node; and "two edges from a cycle, where one
of the edges is incident with the bottom node" is read as at least one, since deleting both edges into the bottom node separates the same pairs as
deleting the edge below it. The proof uses that a switching is a spanning tree that leaves out
exactly one edge into each cycle's bottom, so that, the cycles being vertex-disjoint, deleting a
cut edge, or an edge of a cycle together with the left-out one, leaves the same components in the
network as in the switching ([`Camus/External/WarnowTabatabaeeEvans/README.md`](Camus/External/WarnowTabatabaeeEvans/README.md)).

The site model ([`External.SiteParameters`](Camus/External/WarnowTabatabaeeEvans/SiteModel.lean#L290), [`External.SiteModel`](Camus/External/WarnowTabatabaeeEvans/SiteModel.lean#L316)) has the parameters and the
constraints of Warnow et al.'s Section 4.2, with their designation of reticulation edges (at least
one of the two edges into each reticulation, with no substitution on it; the other may be a tree
edge), and also requires `p(e, s, s) > 0` on the tree edges, which their argument needs and their
list omits (Section 4). A site is a switching of `N` and a
state at every vertex, with the product of the transmission, root and substitution probabilities;
these sum to 1 ([`External.SiteParameters.weight_sum`](Camus/External/WarnowTabatabaeeEvans/SiteModel.lean#L596)), and sequences of independent sites with this
law exist ([`External.SiteModel.sites`](Camus/External/WarnowTabatabaeeEvans/Sampling.lean#L250)). The quartets of an SNP are those cut by the clade below the
edge where its state changes, which are the quartets `ab|cd` with `a`, `b` in one state and `c`, `d`
in the other that the pipeline adds to `Q` ([`External.SiteHistory.quartets_eq_pattern`](Camus/External/WarnowTabatabaeeEvans/SiteModel.lean#L863)). The
convergence follows from the positivity by a union bound
([`Camus/External/WarnowTabatabaeeEvans/README.md`](Camus/External/WarnowTabatabaeeEvans/README.md)).

### Proved in another library

| Result | Where the paper uses it | Source | In the formalization |
| --- | --- | --- | --- |
| Under the multispecies coalescent on a rooted binary species tree, the quartet gene tree that matches the species tree on four taxa has probability `1 − (2/3)e^{−x}`, and each of the other two `(1/3)e^{−x}`, where `x > 0` is the length of the internal edge of the species tree on those taxa | Section 3.3, the motivation of Algorithm 1: "the multi-species coalescent (MSC) model (Takahata 1989) under which, for every four species, the most probable quartet tree matches the species tree and the other two quartet trees have the same lower probability" | E. S. Allman, J. H. Degnan, J. A. Rhodes, *Identifying the rooted species tree from the distribution of unrooted gene trees under the coalescent*, J. Math. Biol. 62 (2011) 833–862, [doi:10.1007/s00285-010-0355-7](https://doi.org/10.1007/s00285-010-0355-7), Section 4.1 and Lemma 5; the paper cites Takahata (1989) | The formalization <https://github.com/vltanh/lean4-adr11> (a dependency of this project): its four-taxon distributions (`ADR11.four_unrootedDist_of_mem`, `ADR11.four_unrootedDist_of_ne_of_isBinary`) and its restriction of the coalescent to four taxa, applied in [`Coalescent.quartetProb_species`](Camus/Pipelines/Coalescent/Quartets.lean#L448), [`Coalescent.quartetProb_other`](Camus/Pipelines/Coalescent/Quartets.lean#L459) and [`Coalescent.msc_pattern`](Camus/Pipelines/Coalescent/Quartets.lean#L496) |

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
| A level-1 network on `n` leaves has at most `n − 1` reticulations | Section 2.4: "it is known that a level-1 phylogenetic network on n leaves will not have more than n−1 reticulations" | [`RootedNetwork.anchored_reticulation_bound`](Camus/Network/Reticulations.lean#L228), for networks built on `T`, which is the case the section needs |
| In a rooted binary tree, every four taxa carry exactly one induced quartet | Section 3.2: "the quartet support score of t will be larger than the score of any other tree" | [`PhyloTree.induced_existsUnique`](Camus/Pipelines/Astral.lean#L298) |
| The lowest common ancestors of all pairs of vertices and the depths of a tree can be tabulated in `O(n²)` time, and membership in a leaf set read off them | Section 2.3 | [`Complexity.preprocess_time`](Camus/Complexity/Tables.lean#L658), from the recurrence [`Complexity.lca_recurrence`](Camus/Complexity/Tables.lean#L169) |
| Every rooted binary level-1 network is built on one of its trees, and has at most `n − 1` reticulations | Section 2.1: "N can be constructed by taking one of the trees t∈T and adding reticulations"; Section 3.2: "Recall that the network N is tree-based (which follows directly from being level-1)"; Section 2.4: "it is known that a level-1 phylogenetic network on n leaves will not have more than n−1 reticulations" | [`RootedNetwork.treeBased`](Camus/Network/TreeBased/Main.lean#L136), [`RootedNetwork.exists_canonical`](Camus/Network/TreeBased/Root.lean#L261), [`RootedNetwork.reticulationCount_le`](Camus/Network/TreeBased/Main.lean#L146) |
| The quartets of a binary tree determine it (Steel 1992) | Section 3.2: "ASTRAL will return t since it solves its optimization problem exactly" | [`PhyloTree.rootedIso_of_induced_eq`](Camus/Pipelines/AstralTree.lean#L562), from lean4-adr11's `ADR11.mem_unroot_iff_quartets` |
| The strong law of large numbers | Sections 3.2 and 3.4: "the most frequently observed quartet tree will be the most probable quartet tree with probability converging to 1"; "the gap between f2 and f3 will approach 0" | `ProbabilityTheory.strong_law_ae_real` (Mathlib) |

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Observation 2 (Warnow, Tabatabaee and Evans 2025) | Proof of Lemma 1 | Applied correctly for existence; it does not give uniqueness, which needs the vertex-disjointness of the cycles (E1) |
| The model and the proof of Theorem 6 of Warnow, Tabatabaee and Evans (2025) | Section 3.2, the convergence of the observed quartets | Correct once `p(e, s, s) > 0` on the tree edges is added to the model, as their Theorem 7 assumes; without it the step fails (Section 4). The conclusion that the paper draws, that CAMUS then returns the true network, is false (E7) |
| Warnow et al. (2025) and Gambette et al. (2012): quartets "determined by the nodes they attach to in the cycle" | Section 2.3, `δ_T` in `O(1)` time | Correct: the quartets satisfied by an added edge are those of `Q` that `T` does not induce and that a clade of the tree `T'` displayed through the edge cuts ([`Realization.mem_novel_single_iff`](Camus/Network/SingleEdge.lean#L398)), which a constant number of table reads decides ([`Complexity.delta`](Camus/Complexity/Delta.lean#L732), at most 130 operations) |
| Takahata (1989): the multispecies coalescent | Section 3.3 | Correct ([`Coalescent.msc_pattern`](Camus/Pipelines/Coalescent/Quartets.lean#L496), from Allman, Degnan and Rhodes) |
| Solís-Lemus et al. (2016), Ané et al. (2024), Dinh and Baños (2025): ASTRAL can be inaccurate under the network coalescent | Section 3.3 | Correct; an explicit instance is [`Camus.NMSC.anomaly_astral`](Camus/Pipelines/NMSC/Anomaly.lean#L282). The same anomaly defeats Quartet Filtering, which the paper does not say (E9) |
| Mirarab et al. (2014): ASTRAL solves its problem exactly | Section 3.2 | Taken as the definition of ASTRAL's output: the formalization proves the section's claim about the exact maximizers of the quartet support score ([`astral_maximizer_tendsto`](Camus/Pipelines/Astral.lean#L546)) |

The other citations give context, or support the pipelines and the experiments, which are not
formalized: the statistical consistency of ASTRAL under the multispecies coalescent (Mirarab et al.
2014) in Section 3.1, ghost lineages (Tricou et al. 2025), and the methods, simulators and data of
Sections 1, 3 and 4.

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
([`DynamicProgramming.edgeWeight`](Challenge.lean#L662), [`Camus.equation1`](Camus/Score.lean#L50)). The algorithm and its results are unaffected.

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
([`EdgeAbove.Admissible`](Challenge.lean#L187), [`DynamicProgramming.pairsAt`](Challenge.lean#L572)); at the root this is the paper's set, and no
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
([`not_exactCountMonotone`](Camus/Restriction/Monotonicity.lean#L37), from [`Counterexamples.graph_exact_budget_nonmonotone`](Camus/Restriction/Witness.lean#L427)). For "at most `k`"
reticulations the claim holds, trivially, since the networks allowed only grow with `k`
([`Camus.atMostScore_mono`](Camus/Score.lean#L172), for an abstract finite family of networks). A drop requires every internal vertex of `T` to lie on a cycle of every
optimal network with `k` reticulations, since otherwise a triangle at a free vertex gives `k + 1`
reticulations and the same score; here it happens at `k = n − 1`. The stopping rule can also stop
too early without any drop (E6). The four properties of the networks `N_k` that the section asks for
hold, for the networks returned by backtracking through the modified array
([`BudgetDP.backtracking_networks`](Camus/Restriction/Backtracking.lean#L499), [`BudgetDP.reticulation_restriction`](Camus/Restriction/Main.lean#L61)).

**E6. Section 2.4: the stopping rule can stop before a better score.** The section computes the
columns of `M[v, k]` "in order of increasing k, dynamically adding new columns to our matrix, until we
no longer get an improvement in score", and calls `m` "the number of reticulations after which the
score does not improve". The rule can stop where a larger number of reticulations gives a better
score, with exactly `k` reticulations and with at most `k`. Take the caterpillar
`T = (A,(B,(C,(D,(E,(F,(G,H)))))))` and `Q = {AF|CG, AF|CG, AC|BD, AE|DF, AH|FG}`. The best numbers
of quartets of `Q` displayed by a network built on `T` with exactly, or at most, 0, 1, 2 and 3
reticulations are 0, 2, 2 and 3 ([`Counterexamples.caterpillar_scores`](Camus/Restriction/StoppingRule.lean#L345)). One edge, above `(A, F)`,
satisfies both copies of `AF|CG`. Two edges with vertex-disjoint cycles satisfy at most two quartets
of `Q`: the cycle of every edge that satisfies a quartet of `Q` passes through one of three vertices
of `T`, and the cycle of an edge that satisfies two passes through all three. Three edges, above
`(A, C)`, `((D,(E,(F,(G,H)))), E)` and `((F,(G,H)), H)`, satisfy `AC|BD`, `AE|DF` and `AH|FG`. So the
rule stops at `m = 1`, with score 2, while three reticulations give 3, the best score of any network
built on `T` ([`not_exactStoppingRule`](Camus/Restriction/StoppingRule.lean#L462), [`not_atMostStoppingRule`](Camus/Restriction/StoppingRule.lean#L481)); every array of the recurrence has
the root rows `{0}`, `{2}`, `{2}`, `{3}`, and the rule applied to them stops at `m = 1`
([`Counterexamples.caterpillar_root_rows`](Camus/Restriction/StoppingRule.lean#L422), [`Counterexamples.caterpillar_array_stops`](Camus/Restriction/StoppingRule.lean#L444)). Unlike E5, the
scores do not decrease here. Eight leaves are needed for this pattern: an argument (an optimal family
of `k + 2` edges has only edges of positive weight, whose cycles have at least two vertices of `T`)
and an exhaustive search on seven leaves show it, without a formal proof. The rule decides which
columns, and so which networks `N_k`, are computed; choosing among them "where the score stops
improving substantially" is a separate, informal step. The point is that the computed networks need
not include one with the best score.

**E7. Section 3.2: the true network need not be the unique optimum, and CAMUS need not return
it.** "When Q is a multi-set version of Q(N_r), then CAMUS will add the correct reticulations and
return N, since this is the unique network that can satisfy all the quartets in Q(N_r), and hence N
will be the unique solution to CAMUS' optimization problem." The objective counts the quartets of
`Q` that a network displays, so a network built on `t` that displays a superset of `Q(N_r)` ties
with `N`. Take for `N` and for `t` the tree `(O,((B,A),(D,C)))`, and for `Q` its five quartets. The
network obtained by adding an edge above `(A, C)` is built on `t`, has a five-vertex cycle that
keeps the outgroup outside, and displays the five quartets; it is optimal too, with one reticulation
against none ([`not_uniqueOptimum`](Camus/Pipelines/Uniqueness.lean#L50)). On this input every weight of Equation (1) is 0, and a valid
backtracking trace of the dynamic program adds that edge ([`camus_may_add_edge`](Camus/Pipelines/Uniqueness.lean#L135)), so CAMUS may return
it. Adding a triangle at an internal vertex of `t` that lies on no cycle of the true network gives the
same failure, and
excluding small cycles does not help, since the cycle here has five vertices. The claim holds under
two more hypotheses (Section 4): the true network is identifiable under inclusion, and ties are
broken toward the fewest reticulations ([`recovery`](Camus/Pipelines/Uniqueness.lean#L152)); a tree is identifiable under inclusion
([`tree_identifiable`](Camus/Pipelines/Uniqueness.lean#L191)). The tie-break toward the fewest reticulations does not restore uniqueness, and excluding small
cycles does not help either. Take `t = ((A,B),(C,(F,(D,E))))` and for `N` the network obtained by
adding an edge from above the cherry `(D,E)` to above `A`; its cycle has six vertices. Moving the
donor down, to above `D`, gives a network `P` built on `t`, with one reticulation and a seven-vertex
cycle, that displays the 22 quartets of `N` and three more, `AD|BE`, `AD|CE` and `AD|EF`
([`Counterexamples.shallow_subset_deep`](Camus/Pipelines/Inclusion.lean#L134), [`Counterexamples.mem_shallowQuartets`](Camus/Pipelines/Inclusion.lean#L276),
[`Counterexamples.mem_deepQuartets`](Camus/Pipelines/Inclusion.lean#L299)). If `Q` is a multiset version of `Q(N_r)`, then `P` is optimal
with the fewest reticulations among the optimal networks, and is not isomorphic to `N`
([`Counterexamples.deepNet_optimal_fewest`](Camus/Pipelines/Inclusion.lean#L169), [`Counterexamples.deep_not_iso_shallow`](Camus/Pipelines/Inclusion.lean#L151)); a backtracking
trace of the dynamic program returns it ([`Counterexamples.camus_may_return_deep`](Camus/Pipelines/Inclusion.lean#L374)); and `N` is not
identifiable under inclusion ([`Counterexamples.shallow_not_identifiable`](Camus/Pipelines/Inclusion.lean#L219); in the Challenge,
[`Challenge.recovery_needs_identifiable`](Challenge.lean#L980)). The example is an instance of a general fact. If the donor `u` of an
added edge is not an ancestor of its recipient `w`, moving the donor to any vertex below `u` keeps
every quartet that the edge satisfies ([`Realization.deeper_donor_displays`](Camus/Network/SingleEdge/Deeper.lean#L49)): every clade of the
tree that the edge displays is a clade of the tree displayed after the move, or a clade of `t`. So a
network with one such edge, whose donor is not a leaf, is identifiable under inclusion only if the
move adds no quartet ([`Realization.deeper_donor_not_identifiable`](Camus/Network/SingleEdge/Deeper.lean#L131)). For a ghost donor, an ancestor of
the recipient, the move can lose quartets ([`Counterexamples.ghost_deeper_donor`](Camus/Pipelines/Inclusion.lean#L243)).

The failure persists inside the model of Warnow et al. (2025) on which the section's argument rests
(Section 2). For every site model on `N` with at least two states, the probability that `P` is
optimal for the observed quartets, with the fewest reticulations among the optimal networks built
on `t`, tends to 1 as the number of sites grows ([`snp_deeperDonor_tendsto`](Camus/Pipelines/SNP.lean#L169)), since the observed
quartets have support `Q(N_r)` with probability tending to 1. The same holds with an outgroup, which
the section assumes ("provided we have an outgroup"; the tree "will be rooted using the
outgroup"): on `(O,((A,B),(C,(F,(D,E)))))`, the edges above `((D,E), A)` and `(D, A)` give networks
with cycles of six and seven vertices, neither through the root, that display 51 and 55 quartets,
the second adding `AD|BE`, `AD|CE`, `AD|EF` and `AD|EO` ([`Counterexamples.outgroup_subset_deep`](Camus/Pipelines/InclusionOutgroup.lean#L223),
[`Counterexamples.outgroup_root_not_on_cycle`](Camus/Pipelines/InclusionOutgroup.lean#L200), [`snp_outgroup_tendsto`](Camus/Pipelines/InclusionOutgroup.lean#L279)). For this network, some site
model also meets the condition of the section's ASTRAL step, that `t` induces the most probable
quartet on every four taxa, so the counterexample meets every hypothesis of the argument
([`Counterexamples.deeperDonor_meets_hypotheses`](Camus/Pipelines/SNPCondition.lean#L321)). The section's conclusion, that CAMUS returns `N`,
then holds only if CAMUS happens to break the tie between `N` and `P` in favour of `N`. With
identifiability under inclusion and the tie-break, the conclusion holds in probability
([`snp_recovery_tendsto`](Camus/Pipelines/SNP.lean#L81), [`snp_output_tendsto`](Camus/Pipelines/SNP.lean#L111), [`snp_correctedStatisticalConsistency`](Camus/Pipelines/SNP.lean#L139)). The bioRxiv versions already claimed the consistency of this
pipeline; the uniqueness sentence, its justification, appears only in the published version.

**E8. Sections 2.1 and 3.2: a tree of `N` need not be a basis for `N`.** Section 2.1 says that `N`
"can be constructed by taking one of the trees t∈T and adding reticulations (edges) to t", and
that `N` is then built on `t`; Section 3.2 says that "any tree t∈Q(N_r) can be used as the basis for
N (i.e. N can be obtained by adding reticulate edges to t)". The first holds, the second fails when
the root of `N` lies on a cycle. If the root of `N` has the root of `t` and a reticulation as
children, deleting the edge into the reticulation leaves a root with one child, which the clean-up
of Definition 1 suppresses, so `t` is a tree of `N`; but adding edges to `t` (Definition 3) never
creates a vertex above its root. For `t = ((A,B),C)` and the network whose root has as children the
root of `t` and a reticulation above `B`, no network obtained by adding edges to `t`, and so no
output of CAMUS on `t`, is isomorphic to it ([`Counterexamples.camus_output_not_rootAboveNet`](Camus/Network/RootAbove/Example.lean#L414),
[`Counterexamples.builtOn_not_anchored`](Camus/Network/RootAbove/Example.lean#L389)). The proof of Theorem 1, which compares the output with "any
level-1 phylogenetic network that extends T", treats a network as `T` with added edges, each with a
target in `T`, and so leaves these networks out. The gap is harmless: moving the tail of the edge
from the root below the root of `t` gives a network obtained by adding edges to `t`, with the same
reticulations and the same displayed quartets ([`RootedNetwork.BuiltOn.exists_anchored`](Camus/Network/RootAbove/Main.lean#L64)), so
Theorem 1 and the optimality of the networks of Section 2.4 hold over Definition 1's class
([`theorem1_builtOn`](Camus/DP/Definition1.lean#L76), [`BudgetDP.exact_graph_optimal_builtOn`](Camus/DP/Definition1.lean#L114); in the Challenge, [`Challenge.theorem1`](Challenge.lean#L852) and
[`Challenge.reticulation_restriction`](Challenge.lean#L903)). In Section 3.2 the tree is rooted at an outgroup, a child of the root
of `N`, and then every tree of `N` is a basis for it ([`RootedNetwork.BuiltOn.anchored_of_outgroup`](Camus/Network/TreeBased/Root.lean#L347)).

**E9. Sections 3.3 and 3.4: under the network coalescent, Quartet Filtering can keep the wrong
quartets.** The pipeline for gene trees keeps, on each four taxa, the most frequent quartet tree,
and the second when its frequency stands far enough above the third's (Algorithm 1): "The motivation
for this approach is that we do not want to include quartet trees that are not in Q(Nr). On the
other hand, we do not want to eliminate these quartet trees." This needs the quartets that `N`
displays to be the most frequent. Under the network multispecies coalescent they usually are: on four
taxa a level-1 network displays one or two quartet trees; when one, the other two have equal
probabilities, and when two, the third is strictly the least probable ([`Brooqs.Net.weakPattern`](Camus/External/NMSC/Pattern.lean#L880)).
Outside the anomalous configuration of Ané, Fogg, Allman, Baños and Rhodes (2024), two of the four
taxa below the reticulation of a cycle whose smallest subnetwork holds three of them, the displayed
quartets are strictly the most probable ([`Brooqs.Net.regularOn_of_not_anomalous`](Camus/External/NMSC/Pattern.lean#L871)), and for every
threshold below a positive bound, almost surely, for all large numbers of gene trees, the output of
Quartet Filtering has support `Q(N_r)` ([`Camus.NMSC.nmsc_filterQuartets_support`](Camus/Pipelines/NMSC/Recovery.lean#L100); a network whose
reticulations have at most one leaf below them has no anomalous configuration,
[`Camus.NMSC.noAnomaly_of_below`](Camus/Pipelines/NMSC/Filtering.lean#L243)). In the anomalous configuration this fails. For a 3-cycle with `x`
and `y` below its reticulation, `z` on one side and `w` outside, with inheritance probability 1/2,
edges of length 1/20 at the reticulation and an edge of length 3 along which the lineages of `z` and
of one of `x`, `y` can coalesce, the network displays only `xy|zw`, whose probability is about
0.231, against about 0.385 for each of the two others ([`Brooqs.net32_anomaly`](Camus/External/NMSC/ThreeCycle.lean#L581)). Then, for every
threshold, almost surely, for all large numbers of gene trees, Quartet Filtering drops `xy|zw`, the
only quartet of `Q(N_r)` on these taxa, and keeps one that is not in `Q(N_r)`
([`Camus.NMSC.anomaly_filterQuartets`](Camus/Pipelines/NMSC/Anomaly.lean#L224)); and no tree of maximum quartet support is a displayed tree of
`N` ([`Camus.NMSC.anomaly_astral`](Camus/Pipelines/NMSC/Anomaly.lean#L282)), an explicit instance of the section's remark on ASTRAL. The paper
cites Ané et al. (2024) for ASTRAL, not for its filter. Outside the anomaly, CAMUS on the filtered
quartets is in the situation of Section 3.2: the recovery of E7 holds under identifiability under
inclusion and the tie-break ([`Camus.NMSC.nmsc_recovery_graph`](Camus/Pipelines/NMSC/Recovery.lean#L198)), and fails without it
([`Camus.NMSC.nmsc_uniqueness_counterexample`](Camus/Pipelines/NMSC/Uniqueness.lean#L84)).

**E10. Typos.**

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
| Section 3.2: "N will be the unique solution to CAMUS' optimization problem" | The true network `N` is identifiable under inclusion: every network built on `t` that displays all the quartets of `N`, with no more reticulations, is isomorphic to `N`; and ties are broken toward the fewest reticulations | E7: the tree `(O,((B,A),(D,C)))` and the network with one added edge above `(A, C)` both display all five quartets; with the tie-break, the networks of the deeper donor, whose cycles have six and seven vertices ([`Challenge.recovery_needs_identifiable`](Challenge.lean#L980)), also with an outgroup ([`Counterexamples.outgroupDeep_optimal_fewest`](Camus/Pipelines/InclusionOutgroup.lean#L254)) | Hypotheses `identifiable` and `fewest` of [`recovery`](Camus/Pipelines/Uniqueness.lean#L152), and of [`snp_output_tendsto`](Camus/Pipelines/SNP.lean#L111) in the site model; [`tree_identifiable`](Camus/Pipelines/Uniqueness.lean#L191) shows that every tree satisfies the first |
| Section 3.2: "According to the theory given in Warnow et al. (2025), as the number of gene trees increases, this multiset will be identical to Q(N_r)" | The substitution probabilities `p(e, s, s)` are positive on the tree edges, which Warnow et al.'s Section 4.2 does not require (their Theorem 7 assumes it, as `p_on`) | The tree `(((A,B),C),D)`, with the state always changing on the edge above `((A,B),C)`: no SNP of positive probability has the clade `{A, B}`, and the quartet `AB\|CD` is never observed ([`External.theorem6_step_needs_stay`](Camus/External/WarnowTabatabaeeEvans/Theorem6.lean#L186)) | Field `stay_pos` of [`External.SiteModel`](Camus/External/WarnowTabatabaeeEvans/SiteModel.lean#L316) |
| Section 3.3: Quartet Filtering keeps the quartets of `Q(N_r)` ("we do not want to include quartet trees that are not in Q(Nr). On the other hand, we do not want to eliminate these quartet trees") | No four taxa are in the anomalous configuration of Ané et al. (2024) | E9: a 3-cycle above two taxa ([`Camus.NMSC.anomaly_filterQuartets`](Camus/Pipelines/NMSC/Anomaly.lean#L224)) | Hypothesis `NoAnomaly` of [`Camus.NMSC.nmsc_filterQuartets_of_noAnomaly`](Camus/Pipelines/NMSC/Filtering.lean#L298) |
| Section 3.4: "for t small enough (specifically, t<(f2−f3)/(f2+f3)), then we will include q2" | `f2 + f3 > 0` | For `f2 = f3 = 0` the ratio is undefined (the test `f2 − f3 > t·(f2+f3)` then keeps no second quartet) | Hypothesis `0 < f₂ + f₃` of [`retainSecond_iff_ratio`](Camus/Pipelines/Filtering.lean#L34) |
| Section 3.4: under the multispecies coalescent "the gap between f2 and f3 will approach 0", so that Quartet Filtering keeps only the most frequent quartet | The threshold `t` is positive (the algorithm allows `t ∈ [0, 1]`) | For `t = 0`, the second quartet is kept whenever `f2 > f3` ([`retainSecond_zero`](Camus/Pipelines/Filtering.lean#L61)), which the convergence of the frequencies does not exclude | Hypothesis `0 < t` of [`Coalescent.msc_filterBlock`](Camus/Pipelines/Coalescent.lean#L221) and [`Coalescent.msc_filterQuartets`](Camus/Pipelines/Coalescent.lean#L250) |

No other statement of the paper needs a hypothesis that it leaves unstated. The trees are
phylogenetic trees, with distinct leaf labels, which the statements assume
([`PhyloTree.WellLabelled`](Challenge.lean#L91)). The restriction of `Pairs(v)` (E4) is part of a definition. Section
3.2's "the most probable quartet tree" is read as strictly more probable than the other two, which
the definite article says (Section 6).

## 5. Redundant hypotheses

None. Every hypothesis of the formal statements of Lemmas 1 and 2, Theorem 1 and Section 2.4 is used
by its proof. Of the hypotheses added in Section 4, identifiability and `p(e, s, s) > 0` cannot be
dropped (Section 4's counterexamples); for the threshold of Algorithm 1, Section 4 gives the
reason.

## 6. How the formalization reads the paper

- **Trees, quartets and display.** A tree is a full binary tree with labelled leaves ([`PhyloTree`](Challenge.lean#L78));
  its vertices are addressed by their paths from the root. A quartet is written with its four taxa
  in increasing order and one of three splits ([`Quartet`](Challenge.lean#L111)). Definition 1's trees of a network are its
  switchings: one incoming edge kept at every vertex other than the root
  ([`RootedNetwork.Switching`](Challenge.lean#L295)), which in a binary network is one incoming edge kept at each
  reticulation. A quartet is displayed, `q ∈ Q(N_r)`, when some switching has an edge whose removal
  separates its two pairs ([`RootedNetwork.DisplaysQuartet`](Challenge.lean#L311)). This is the paper's notion: in a tree,
  a quartet is induced exactly when an edge separates its pairs, whatever unary vertices and
  unlabelled leaves remain. For the constraint tree it agrees with the clades of `T`
  ([`Realization.baseline_displays_iff`](Camus/Network/Baseline/Main.lean#L38), in the Challenge as [`Challenge.tree_displays_iff`](Challenge.lean#L870)).
- **Networks.** A rooted binary level-1 phylogenetic network is a finite directed graph with the laws
  of [`RootedNetwork.RootedBinaryLevelOne`](Challenge.lean#L270): acyclic, every vertex reachable from the root, the root
  of indegree 0 and outdegree 0 or 2, the other vertices leaves (1, 0), tree vertices (1, 2) or
  reticulations (2, 1), the leaves labelled bijectively, and any two distinct cycles of the
  underlying undirected graph vertex-disjoint ("level-1", as in the paper). Triangles are allowed, as
  in CAMUS.
- **Built on `T`.** In this report, a network built on `T` is one obtained by adding edges to
  `T`, with the root of `T` at its root ([`RootedNetwork.AnchoredExtension`](Challenge.lean#L370)), the class over which
  CAMUS optimizes; Definition 1's wider class is always called "built on `T` in the sense of
  Definition 1". Definition 1's "N is built on t", `t` one of the trees of `N`, is
  [`RootedNetwork.BuiltOn`](Challenge.lean#L414): some switching of `N` is `T` with its edges subdivided, below a directed
  path from the root of `N` to the root of `T` ([`DisplayedSubdivision`](Challenge.lean#L382)). A switching of a rooted
  binary level-1 network leaves no unlabelled leaf ([`RootedNetwork.switching_leaf_of_childless`](Camus/Network/RootAbove/Defs.lean#L44)), so
  the clean-up of Definition 1 only suppresses vertices with one child, a root with one child
  included. The networks obtained by adding edges to `T`, as CAMUS does, are those whose root is the
  root of `T` ([`RootedNetwork.AnchoredExtension`](Challenge.lean#L370), [`SupportSubdivision`](Challenge.lean#L343)): an added edge never starts
  above the root ("we cannot add an edge to T that begins above the root of T"), and cannot end
  above it (it would close a directed cycle). Definition 1's class is larger
  ([`Counterexamples.builtOn_not_anchored`](Camus/Network/RootAbove/Example.lean#L389)): the root of `N` may have the root of `T` and a
  reticulation as children ([`DisplayedSubdivision.root_above`](Camus/Network/RootAbove/RootWire.lean#L226)). Each such network displays the
  quartets of a network obtained by adding edges to `T`, with as many reticulations
  ([`RootedNetwork.BuiltOn.exists_anchored`](Camus/Network/RootAbove/Main.lean#L64), E8). Theorem 1 and the optimality of Section 2.4's
  networks are stated against Definition 1's class; the other statements of Sections 2.4 and 3.2
  concern the networks obtained by adding edges to `T`, the class over which CAMUS optimizes. Every
  level-1 network is built on one of its trees, in the sense of Definition 1 for each of its
  switchings ([`RootedNetwork.treeBased`](Camus/Network/TreeBased/Main.lean#L136)) and with the root kept for some
  ([`RootedNetwork.exists_anchoredExtension`](Camus/Network/TreeBased/Root.lean#L251)); it is isomorphic to a canonical network
  `Realization.graph t E` ([`RootedNetwork.exists_canonical`](Camus/Network/TreeBased/Root.lean#L261)); its quartets are those of its trees,
  `Q(N_r) = ∪ Q(t)` ([`RootedNetwork.displays_iff_exists_builtOn`](Camus/Network/TreeBased/Display.lean#L351)); and with an outgroup leaf below
  its root it is built on each of its trees with the root kept
  ([`RootedNetwork.BuiltOn.anchored_of_outgroup`](Camus/Network/TreeBased/Root.lean#L347)). Figure 1's example is checked
  ([`Figure1.net_displays_iff`](Camus/Preliminaries/Figure1.lean#L103)).
- **Added edges and `T + e`.** An added edge is a pair `(u, w)` of vertices of `T`; the network
  obtained by adding the edges of a family `E` is `Realization.graph t E`. Every network built on `T`
  is isomorphic to `Realization.graph t E` for the family of pairs of its non-tree edges
  ([`SupportSubdivision.canonical_iso`](Camus/Network/Completeness/Main.lean#L114)), and deleting the other non-tree edges of `N` leaves a subdivision of
  the canonical network of the single pair of `e` ([`SupportSubdivision.single_edge_reduction`](Camus/Network/Completeness/Main.lean#L127)), so
  that `T + e` (Section 2.1: delete the other non-tree edges and suppress) is that canonical network,
  with the same displayed quartets ([`GraphSubdivision.displays_iff`](Camus/Network/Subdivision/Invariance.lean#L48)). On an edge of `T` that carries ends of two added edges, the end
  of the outer cycle comes before a ghost donor ([`Realization.outerEndpoints`](Challenge.lean#L478),
  [`Realization.ghostEndpoints`](Challenge.lean#L485)); in every network built on `T` this order is forced
  ([`SupportSubdivision.no_ghost_before_endpoint`](Camus/Network/Completeness/Order.lean#L33)).
  The quartets that `T + e` displays are those of `T` and those cut by a clade of the tree `T'`,
  `T` with the subtree at `w` pruned and regrafted above `u` ([`Realization.single_displays_iff`](Camus/Network/SingleEdge.lean#L333),
  [`EdgeAbove.switchedClades`](Camus/Network/SingleEdge.lean#L127); in general, a network displays `q` exactly when some switching has an
  edge whose clade below cuts `q`, [`RootedNetwork.displays_iff_cladeBelow`](Camus/Network/Clades.lean#L186)). So `δ_T` of
  Definition 4 and the weights of Equation (1) are computable ([`EdgeAbove.satisfies`](Camus/Network/SingleEdge.lean#L134),
  [`DynamicProgramming.edgeWeight_eq_satisfies`](Camus/Network/SingleEdge.lean#L414)), and the counterexamples about networks with one
  added edge are checked by `decide`.
- **The recurrence.** Definition 5's children are children in the network `T + e`, as the
  definition says: at the parent of `u` (or of `w`), whose edge to `u` carries an end of `e`, the
  child on the cycle is the new vertex ([`Realization.child`](Challenge.lean#L532), [`Realization.offChild`](Challenge.lean#L540)). With the
  children in `T`, Equations (4) and (5) would count `M[u]` (or `M[w]`) twice, and drop the subtree of
  its sibling, whenever `u` (or `w`) is the left child of a vertex of the cycle other than the target. The equations'
  condition is `l(x) ∉ γ(u,w)`; in the JATS source the membership symbol is struck through, which a
  plain-text extraction loses. Equation (1) is read over the distinct quartets of `Q` (E3), and
  `Pairs(v)` with the restriction of E4. [`DynamicProgramming.Array`](Challenge.lean#L615) states the recurrence; it
  determines `M` on the vertices of `T`, and a solution and a backtracking trace exist
  ([`DynamicProgramming.exists_array_trace`](Camus/DP/Correctness.lean#L401)). [`DynamicProgramming.Trace`](Challenge.lean#L628) allows any maximizing branch,
  so Theorem 1 covers every way of breaking ties.
- **Theorem 1.** It is stated for every array satisfying the recurrence and every backtracking
  trace, against every network built on `T` in the sense of Definition 1. Its score is the number of quartets of `Q` satisfied,
  counted with multiplicity, and it also states the optimality of the number displayed (E2). The
  paper's induction on the number of leaves below a vertex is an induction on the measure
  [`DynamicProgramming.remainingDepth`](Camus/DP/Packing.lean#L121) (the height of `T` minus the depth of the vertex), which also
  decreases from a vertex to its descendants: the same induction over subtrees.
- **Section 2.4.** The paper describes the modified dynamic program by the meaning of its entries
  `M[v, k]` ("the solution found for subtree T_v of the network limited to allowing k non-tree
  edges") and gives no recurrence. The formalization's recurrence ([`BudgetDP.Array`](Challenge.lean#L719)) has that
  meaning: a row `M v k` is empty when no family of `k` added edges below `v` is feasible, and
  otherwise holds the best value; the fork case convolves the children's rows, and the case of an
  edge with target `v` distributes the remaining budget over the subtrees hanging off its cycle, by
  a knapsack that keeps the maximum after each convolution. The networks `N_k` are those returned by
  backtracking through the array ([`BudgetDP.Trace`](Challenge.lean#L748), with a trace through the knapsack,
  [`BudgetDP.Knapsack`](Challenge.lean#L727)): the network of every trace from the root with budget `k` is built on `T`,
  has exactly `k` non-tree edges and as many reticulations ([`RootedNetwork.nonTree_card_eq`](Camus/Restriction/Backtracking.lean#L78)),
  satisfies the value of the row, and is optimal ([`BudgetDP.trace_graph_optimal`](Camus/Restriction/Backtracking.lean#L352),
  [`BudgetDP.backtracking_networks`](Camus/Restriction/Backtracking.lean#L499)); a trace exists for every nonempty row ([`BudgetDP.exists_trace`](Camus/Restriction/Backtracking.lean#L285)),
  and the row of `k` at the root is nonempty if and only if `k ≤ n − 1`
  ([`BudgetDP.root_row_nonempty_iff_le`](Camus/Restriction/Backtracking.lean#L442)). The number of reticulations is the number of vertices of
  indegree 2 ([`RootedNetwork.reticulationCount`](Challenge.lean#L673)). The stopping rule is read as the claim that the
  score does not improve after the column where the rule stops, for exact numbers of reticulations
  and for at most `k` ([`StopsAt`](Challenge.lean#L816), [`ExactStoppingRule`](Challenge.lean#L826), [`AtMostStoppingRule`](Challenge.lean#L834)), and refuted (E6).
  Backtracking through the array for every budget is a program too
  ([`Complexity.camusBudgetNetworks`](Camus/Complexity/BudgetBacktracking.lean#L1130)), whose output is a trace for every nonempty row
  ([`Complexity.camusBudgetNetworks_optimal`](Camus/Complexity/BudgetBacktracking.lean#L1183)); with the array it takes at most
  `2100 n² (|Q| + m³ n)` operations ([`Complexity.camusBudgetNetworks_time`](Camus/Complexity/BudgetBacktracking.lean#L1300)).
- **Section 2.3.** CAMUS is written as a program in a cost monad ([`Complexity.Timed`](Camus/Complexity/Timed.lean#L58)): a result
  with the number of elementary operations performed, one per read or write of a table entry, per
  arithmetic operation or comparison on integers, per comparison of vertex names and per loop
  iteration, as in the paper's unit-cost model ("we consider integers to require O(1) memory"). Vertices
  are named by their addresses, used only as names: parents, depths and lowest common ancestors are
  read from tables. The program ([`Complexity.camus`](Camus/Complexity/Program.lean#L950)) builds the tables of the preprocessing
  ([`Complexity.preprocess`](Camus/Complexity/Tables.lean#L315), in at most `20 |V(T)|²` operations, [`Complexity.preprocess_time`](Camus/Complexity/Tables.lean#L658)),
  enumerates the candidate pairs once into buckets by target with their weights, computed by one
  scan of the distinct quartets of `Q` with the test [`Complexity.delta`](Camus/Complexity/Delta.lean#L732), which returns `δ_T`
  ([`Complexity.val_delta`](Camus/Complexity/Delta.lean#L761)) in at most 130 operations ([`Complexity.time_delta`](Camus/Complexity/Delta.lean#L746)), and fills `M` from
  the leaves up, reading `s_dp` off the subtrees hanging off each cycle, which it lists by walking
  from `u` and `w` up to the target. It computes the array of the recurrence
  ([`Complexity.camus_array`](Camus/Complexity/Program.lean#L1090), so Theorem 1 applies, [`Complexity.camus_optimal`](Camus/Complexity/Program.lean#L1102)), in at most
  `600 n² (|Q| + n)` operations ([`Complexity.camus_time`](Camus/Complexity/Program.lean#L1193)), with `n` the number of taxa and `|Q|` the
  number of distinct quartets. With backtracking the bound is `700 n² (|Q| + n)`
  ([`Complexity.camusNetwork_time`](Camus/Complexity/Backtracking.lean#L529)). The program of Section 2.4 computes the `m + 1` columns
  `0, …, m` of the array, the rows of the recurrence for `k ≤ m` ([`Complexity.camusBudget_rows`](Camus/Complexity/BudgetProgram.lean#L563), [`Complexity.camusBudget_agrees`](Camus/Complexity/BudgetProgram.lean#L547)) in
  at most `1000 n² (|Q| + m³ n)` operations ([`Complexity.camusBudget_time`](Camus/Complexity/BudgetProgram.lean#L682)); the paper's "O(m²) time
  to find the correct DP look-ups to solve each problem" gives its total when it is read per pair,
  per hanging subtree and per column. Memory: the cost semantics has a space component
  ([`Complexity.Spaced`](Camus/Complexity/Space.lean#L74): the cells held at every step, and their peak), which charges every table at
  its declared size, one cell per list element and one frame per recursive call. CAMUS holds at most
  `48 n²` cells besides its input ([`Complexity.peak_camusS_le`](Camus/Complexity/PeakMemory.lean#L368)), the paper's `O(n²)` for "all other
  data structures", and at most `68 n⁴` with its input ([`Complexity.camus_memory`](Camus/Complexity/PeakMemory.lean#L391)), the paper's
  `O(n⁴)`; the program of Section 2.4 with backtracking holds at most `85 n⁴ + 6 m n + 4 m`
  ([`Complexity.camusBudgetNetworks_memory`](Camus/Complexity/PeakMemoryBudget.lean#L813)). The input `Q` is the weighted set of
  its distinct quartets with their multiplicities, as Section 2.3 allows, and reading a multiplicity is
  one operation; the table of the leaves is indexed by the taxa, which costs one operation per
  lookup when the taxa are the numbers `0, …, n − 1` (other labels need hashing).
- **Section 3.2.** The SNP pipeline is studied inside the site model of Warnow et al. (Section 2):
  sites are independent with the law of the model, and `Q_m` is the multiset of the quartets of the
  SNPs among the first `m` sites ([`External.sampleQuartets`](Camus/External/WarnowTabatabaeeEvans/Sampling.lean#L67)). ASTRAL's output is an exact maximizer
  of the quartet support score of Section 3.1 ([`quartetSupport`](Camus/Pipelines/Astral.lean#L68)) over the well-labelled trees on
  the taxa of `t`, compared through their sets of quartets, the trees standing for their unrooted
  forms. "The most probable quartet tree is induced by t" is read as: on every four taxa, the
  quartet that `t` induces is strictly more probable, for one site, than the other two
  ([`MostProbableQuartets`](Camus/Pipelines/Astral.lean#L465)). Under it, with probability tending to 1 every exact maximizer has the
  quartets of `t` ([`astral_maximizer_tendsto`](Camus/Pipelines/Astral.lean#L546)), by the paper's argument: the most frequent quartet
  on four taxa is eventually the most probable (the strong law), and a tree with other quartets
  scores less on some four taxa and no more on the others ([`quartetSupport_lt`](Camus/Pipelines/Astral.lean#L421)). The section's last
  step, CAMUS on `t` and `Q_m`, is proved in probability under identifiability under inclusion and
  the tie-break ([`snp_recovery_tendsto`](Camus/Pipelines/SNP.lean#L81), [`snp_output_tendsto`](Camus/Pipelines/SNP.lean#L111)), and refuted without the first (E7).
  That such a tree, rooted at the outgroup, is `t` up to the order of children is Steel's
  determination of a tree by its quartets ([`PhyloTree.rootedIso_of_induced_eq`](Camus/Pipelines/AstralTree.lean#L562), through lean4-adr11),
  and networks built on two such trees are the same ([`PhyloTree.RootedIso.anchoredExtension_iff`](Camus/Network/RootedIso.lean#L278)).
  The pipeline is one statement ([`pipeline_tendsto`](Camus/Pipelines/Pipeline.lean#L486)): with probability tending to 1, every tree of
  maximum quartet support rooted at the outgroup yields, through CAMUS with the tie-break, a network
  isomorphic to `N`, under identifiability under inclusion; on the counterexample of E7 with an
  outgroup it yields a network not isomorphic to `N` ([`pipeline_outgroup_tendsto`](Camus/Pipelines/Pipeline.lean#L632)). The paper's
  hypotheses, `t` a tree of `N` and an outgroup below its root, give the formal ones
  ([`RootedNetwork.BuiltOn.anchored_of_outgroup`](Camus/Network/TreeBased/Root.lean#L347), [`RootedNetwork.BuiltOn.rootedAt_of_outgroup`](Camus/Pipelines/Pipeline.lean#L225)), the
  pipeline always returns a network ([`pipeline_output_exists`](Camus/Pipelines/Pipeline.lean#L208)), and its hypotheses can all hold
  ([`pipeline_tendsto_tree`](Camus/Pipelines/Pipeline.lean#L594)).
- **Sections 3.3 and 3.4.** Algorithm 1 is applied to the numbers of copies of the three topologies rather
  than to their relative frequencies, which gives the same test, since its inequality is
  homogeneous; ties are broken by a fixed order of the three topologies, where the paper's "without
  loss of generality" leaves them open ([`Algorithm1.rank`](Camus/Pipelines/Algorithm1.lean#L78)). Its motivation from the multispecies
  coalescent is stated for gene trees drawn independently from the coalescent distribution of
  lean4-adr11 (`ADR11.SpeciesTree.unrootedDist`), with a bridge from its split sets to the quartets
  of CAMUS ([`Coalescent.quartetProb_eq`](Camus/Pipelines/Coalescent/Quartets.lean#L386)) and from its species trees to the trees of CAMUS
  ([`Coalescent.HasTopology`](Camus/Pipelines/Coalescent/Topology.lean#L36), [`Coalescent.msc_pattern_induced`](Camus/Pipelines/Coalescent/Topology.lean#L195); every well-labelled tree is the
  topology of a species tree, [`Coalescent.exists_hasTopology`](Camus/Pipelines/Coalescent/Sampling.lean#L183)). For every binary species tree and
  every four taxa, the quartet of the species tree is strictly the most probable and the other two have the same probability
  ([`Coalescent.msc_pattern`](Camus/Pipelines/Coalescent/Quartets.lean#L496)); for every threshold `t > 0`, almost surely, for all large numbers of
  gene trees, Quartet Filtering keeps exactly the copies of the quartets of the species tree
  ([`Coalescent.msc_filterBlock`](Camus/Pipelines/Coalescent.lean#L221), [`Coalescent.msc_filterQuartets`](Camus/Pipelines/Coalescent.lean#L250)); independent gene trees with this
  law exist, so these statements are not vacuous ([`Coalescent.genes`](Camus/Pipelines/Coalescent/Sampling.lean#L78),
  [`Coalescent.msc_filterQuartets_genes`](Camus/Pipelines/Coalescent/Sampling.lean#L198)). Conversely, for any law of gene
  trees whose two minor probabilities differ, `p2 > p3`, and `t < (p2 − p3)/(p2 + p3)`, Quartet
  Filtering eventually keeps the second quartet too ([`Coalescent.filterBlock_keeps_second`](Camus/Pipelines/Coalescent.lean#L334)): the
  signal the paper attributes to horizontal gene transfer. Under the network multispecies coalescent
  ([`Camus/External/NMSC/`](Camus/External/NMSC): networks described from the root, [`Brooqs.Net`](Camus/External/NMSC/Model.lean#L61), with Kingman's coalescent
  along their edges), Quartet Filtering is proved to return `Q(N_r)` outside the anomalous
  configuration, and to fail in it (E9). Its conclusions are stated for CAMUS's networks through a
  displayed tree of `N` that keeps its root, [`Camus.NMSC.baseTree`](Camus/Pipelines/NMSC/BaseTree.lean#L70), and the canonical network
  `Realization.graph (baseTree N) (pairs N)`, which displays exactly the quartets that `N` displays
  ([`Camus.NMSC.graph_displaysQuartet_iff`](Camus/Pipelines/NMSC/Bridge.lean#L895)).

**Corrections.** Four claims of the paper are false (E5–E8). The formalization proves the closest
correct statements, chosen with the author of the formalization:

- Section 2.4's monotonicity, for "at most `k`" reticulations: immediate for networks built on `T`,
  since a network with at most `j ≤ k` reticulations has at most `k`, and proved for an abstract
  finite family of networks ([`Camus.atMostScore_mono`](Camus/Score.lean#L172)); the section's four properties of the networks
  `N_k` hold for exact numbers, for the networks returned by backtracking
  ([`BudgetDP.reticulation_restriction`](Camus/Restriction/Main.lean#L61), [`BudgetDP.backtracking_networks`](Camus/Restriction/Backtracking.lean#L499)).
- Section 2.4's stopping rule: computing all `n − 1` columns, which the running time
  `O(n²(|Q| + m³n))` allows with `m = n − 1`, gives every `N_k` ([`BudgetDP.exists_backtracking_networks`](Camus/Restriction/Backtracking.lean#L528)).
- Section 3.2's recovery, under identifiability under inclusion and the tie-break toward the fewest
  reticulations ([`recovery`](Camus/Pipelines/Uniqueness.lean#L152)), also in probability inside the site model of Warnow et al.
  ([`snp_recovery_tendsto`](Camus/Pipelines/SNP.lean#L81), [`snp_correctedStatisticalConsistency`](Camus/Pipelines/SNP.lean#L139)), and for an abstract finite family
  of candidate networks ([`correctedConsistency`](Camus/Pipelines/Recovery.lean#L68), [`correctedEventualConsistency`](Camus/Pipelines/Recovery.lean#L99)).
- Section 3.2's basis: a network built on `T` in the sense of Definition 1 has the reticulations and
  the displayed quartets of a network obtained by adding edges to `T`
  ([`RootedNetwork.BuiltOn.exists_anchored`](Camus/Network/RootAbove/Main.lean#L64)).

## 7. Departures from the paper's proofs

| Result | The paper's argument | The formalization's | Why it is necessary | E-item |
| --- | --- | --- | --- | --- |
| Lemma 1, uniqueness | "This lemma follows directly from Observation 2" | Existence from Observation 2 ([`RootedNetwork.novel_edge_exists`](Camus/Preliminaries/Lemma1/Cuts.lean#L95)); uniqueness from the vertex-disjointness of the cycles: the paths of `T` joining the two pairs of `q` meet, and their meeting vertex lies on the cycle of every edge that satisfies `q` ([`RootedNetwork.novel_edge_unique`](Camus/Preliminaries/Lemma1/Unique.lean#L202)) | Observation 2 gives existence, not uniqueness: the paper's step has a gap that cannot be filled from Observation 2 alone | E1 |
| Theorem 1 and Section 2.4, against Definition 1's class | The proof of Theorem 1 treats a network that extends `T` as `T` with added edges, each with a target in `T` | The paper's argument for the networks whose root is the root of `T`, after a reduction of the others: an outgroup is added above the root, the network is reduced to its canonical form, the tail of the edge from the root is moved below the root of `T`, and Lemma 1 with the quartets displayed by `T + e` shows that the quartets do not change ([`RootedNetwork.BuiltOn.exists_anchored`](Camus/Network/RootAbove/Main.lean#L64), [`theorem1_builtOn`](Camus/DP/Definition1.lean#L76)) | The edge from the root of a network whose root lies above the root of `T` has no target in `T`, so the paper's argument does not apply to it | E8 |

Every other proof follows the paper's: Lemma 2 by the two cycles through the target; Theorem 1 by
the paper's induction, with its two cases, Lemma 2 for the edge with target `y`, the subtrees hanging
off its cycle as the subproblems of Equations (4) and (5), Equation (2), and Lemma 1 for the
additivity of the score. The formal proof of Theorem 1 applies Lemma 1 outside the induction, to the output and to the family
of each competing network, to equate the number of satisfied quartets with the total weight of the
added edges, where the paper invokes it inside the induction; and it reduces every competing network to its family of added edges, which the paper
identifies with the network. The running time of Section 2.3 follows the paper's four steps: the
preprocessing in `O(n²)`, `δ_T` in `O(1)`, `s(v)` in `O(|Pairs(v)| (|Q| + n))`, and each pair
considered at one target only ([`Complexity.candidate_visits`](Camus/Complexity/Counts.lean#L74)); that of Section 2.4 follows its count
of look-ups. The steps of Section 3.2 follow the paper's arguments: the strong law for the most
frequent quartets, and the argument of Warnow et al. for the support of the observed quartets, with
the hypothesis of Section 4; the motivation of Algorithm 1 follows Section 3.4's sentence on the gap
between `f2` and `f3`. The recurrence and the backtracking of Section 2.4, Observation 2 and the
counterexamples have no proof in the paper to follow.

## 8. What each result depends on

A summary of the output of [`scripts/Audit.lean`](scripts/Audit.lean), which also checks that every declaration of the library depends only
on Lean's three standard axioms.

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| Definition 1, networks built on `T` | [`RootedNetwork.BuiltOn.exists_anchored`](Camus/Network/RootAbove/Main.lean#L64), [`RootedNetwork.treeBased`](Camus/Network/TreeBased/Main.lean#L136), [`RootedNetwork.displays_iff_exists_builtOn`](Camus/Network/TreeBased/Display.lean#L351) | [`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L187) |
| Figure 1 | [`Figure1.net_displays_iff`](Camus/Preliminaries/Figure1.lean#L103) | – |
| Lemma 1 | [`Camus.lemma1`](Camus/Preliminaries/Lemmas.lean#L139), [`Camus.lemma1_union`](Camus/Preliminaries/Lemmas.lean#L290) | [`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L187) |
| Lemma 2 | [`Camus.lemma2`](Camus/Preliminaries/Lemmas.lean#L161), [`EdgeAbove.target_unique`](Camus/Tree/Geometry.lean#L161) | – |
| Definition 4, the quartets satisfied by `T + e` | [`Realization.mem_novel_single_iff`](Camus/Network/SingleEdge.lean#L398) | – |
| Equations (1)–(5) | [`Camus.equation1`](Camus/Score.lean#L50), [`DynamicProgramming.Array`](Challenge.lean#L615), [`DynamicProgramming.s`](Challenge.lean#L607), [`DynamicProgramming.equation4`](Camus/DP/Correctness.lean#L77), [`DynamicProgramming.equation5`](Camus/DP/Correctness.lean#L87) | – |
| Theorem 1 | [`Camus.theorem1`](Camus/DP/Theorem1.lean#L109), [`Camus.theorem1_builtOn`](Camus/DP/Definition1.lean#L76) | [`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L187) |
| Section 2.3, the program and its running time | [`Complexity.camus_array`](Camus/Complexity/Program.lean#L1090), [`Complexity.camus_time`](Camus/Complexity/Program.lean#L1193), with [`Complexity.preprocess_time`](Camus/Complexity/Tables.lean#L658), [`Complexity.val_delta`](Camus/Complexity/Delta.lean#L761), [`Complexity.time_delta`](Camus/Complexity/Delta.lean#L746) | – |
| Section 2.3, memory | [`Complexity.storedIntegers_bound`](Camus/Complexity/Memory.lean#L181), [`Complexity.camus_memory`](Camus/Complexity/PeakMemory.lean#L391) | – |
| Section 2.4, the networks `N_k` | [`BudgetDP.reticulation_restriction`](Camus/Restriction/Main.lean#L61), [`BudgetDP.trace_graph_optimal`](Camus/Restriction/Backtracking.lean#L352), [`BudgetDP.backtracking_networks`](Camus/Restriction/Backtracking.lean#L499), [`BudgetDP.exact_graph_optimal_builtOn`](Camus/DP/Definition1.lean#L114) | [`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L187) |
| Section 2.4, `m ≤ n − 1` | [`RootedNetwork.anchored_reticulation_bound`](Camus/Network/Reticulations.lean#L228), [`RootedNetwork.reticulationCount_le`](Camus/Network/TreeBased/Main.lean#L146) | – |
| Section 2.4, the program and its running time | [`Complexity.camusBudget_agrees`](Camus/Complexity/BudgetProgram.lean#L547), [`Complexity.camusBudget_time`](Camus/Complexity/BudgetProgram.lean#L682), [`Complexity.camusBudgetNetworks_time`](Camus/Complexity/BudgetBacktracking.lean#L1300), [`Complexity.camusBudgetNetworks_memory`](Camus/Complexity/PeakMemoryBudget.lean#L813) | – |
| Section 2.4, monotonicity (E5) | [`not_exactCountMonotone`](Camus/Restriction/Monotonicity.lean#L37); [`Camus.atMostScore_mono`](Camus/Score.lean#L172) | [`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L187); – |
| Section 2.4, the stopping rule (E6) | [`not_exactStoppingRule`](Camus/Restriction/StoppingRule.lean#L462), [`not_atMostStoppingRule`](Camus/Restriction/StoppingRule.lean#L481) | [`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L187) |
| Section 3.2, uniqueness (E7) | [`not_uniqueOptimum`](Camus/Pipelines/Uniqueness.lean#L50), [`camus_may_add_edge`](Camus/Pipelines/Uniqueness.lean#L135), [`Counterexamples.shallow_not_identifiable`](Camus/Pipelines/Inclusion.lean#L219), [`Realization.deeper_donor_displays`](Camus/Network/SingleEdge/Deeper.lean#L49), [`Counterexamples.camus_may_return_deep`](Camus/Pipelines/Inclusion.lean#L374) | – |
| Section 3.2, E7 in the site model | [`snp_deeperDonor_tendsto`](Camus/Pipelines/SNP.lean#L169), [`Counterexamples.deeperDonor_meets_hypotheses`](Camus/Pipelines/SNPCondition.lean#L321) (with an outgroup) | [`External.support_tendsto`](Camus/External/WarnowTabatabaeeEvans/Sampling.lean#L99) |
| Section 3.2, corrected | [`Camus.recovery`](Camus/Pipelines/Uniqueness.lean#L152), [`Camus.tree_identifiable`](Camus/Pipelines/Uniqueness.lean#L191), [`snp_recovery_tendsto`](Camus/Pipelines/SNP.lean#L81), [`snp_correctedStatisticalConsistency`](Camus/Pipelines/SNP.lean#L139) | –; [`External.support_tendsto`](Camus/External/WarnowTabatabaeeEvans/Sampling.lean#L99) |
| Section 3.2, the ASTRAL step | [`astral_maximizer_tendsto`](Camus/Pipelines/Astral.lean#L546), [`PhyloTree.rootedIso_of_induced_eq`](Camus/Pipelines/AstralTree.lean#L562) | – |
| Section 3.2, the pipeline | [`pipeline_output_exists`](Camus/Pipelines/Pipeline.lean#L208), [`pipeline_tendsto`](Camus/Pipelines/Pipeline.lean#L486), [`pipeline_outgroup_tendsto`](Camus/Pipelines/Pipeline.lean#L632) | [`External.support_tendsto`](Camus/External/WarnowTabatabaeeEvans/Sampling.lean#L99) |
| Section 3.2, the basis (E8) | [`Counterexamples.camus_output_not_rootAboveNet`](Camus/Network/RootAbove/Example.lean#L414) | [`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L187) |
| Sections 3.3 and 3.4, under the network coalescent (E9) | [`Brooqs.Net.weakPattern`](Camus/External/NMSC/Pattern.lean#L880), [`Camus.NMSC.nmsc_filterQuartets_support`](Camus/Pipelines/NMSC/Recovery.lean#L100), [`Camus.NMSC.anomaly_filterQuartets`](Camus/Pipelines/NMSC/Anomaly.lean#L224), [`Camus.NMSC.anomaly_astral`](Camus/Pipelines/NMSC/Anomaly.lean#L282), [`Camus.NMSC.nmsc_recovery_graph`](Camus/Pipelines/NMSC/Recovery.lean#L198) | [`Brooqs.net32_anomaly`](Camus/External/NMSC/ThreeCycle.lean#L581), [`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L187) |
| Sections 3.3 and 3.4 | [`retainSecond_iff_ratio`](Camus/Pipelines/Filtering.lean#L34), [`Algorithm1.filterQuartets_mono`](Camus/Pipelines/Algorithm1.lean#L191), [`Coalescent.msc_pattern`](Camus/Pipelines/Coalescent/Quartets.lean#L496), [`Coalescent.msc_filterQuartets`](Camus/Pipelines/Coalescent.lean#L250), [`Coalescent.msc_filterQuartets_genes`](Camus/Pipelines/Coalescent/Sampling.lean#L198), [`Coalescent.filterBlock_keeps_second`](Camus/Pipelines/Coalescent.lean#L334) | – (the quartet probabilities of lean4-adr11) |

The route check ([`scripts/route_check.py`](scripts/route_check.py), run in CI) compares the results that each formal proof uses
with those that the paper's proof cites ([`docs/paper_routes.tsv`](docs/paper_routes.tsv), written by hand from the published version).
Every proof uses the results that the paper's proof cites, and uses three more, recorded in
[`docs/route_differences.tsv`](docs/route_differences.tsv), each with its reason: Lemma 1 reaches Lemma 2 through the construction
of `T + e`, not through its argument, and Theorem 1 uses `s_e` and `s(y)`, which its proof names
without citing Equations (1) and (3).

## 9. Not formalized

- Under the network coalescent: the recovery of Section 3.2 through displayed trees of `N` other than
  [`Camus.NMSC.baseTree`](Camus/Pipelines/NMSC/BaseTree.lean#L70), the symmetry of the model under the exchange of the two sides of a cycle, and
  the parameters for which the anomalous configuration does defeat Quartet Filtering (one example is
  proved, E9).
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
sentence of Section 3.2 (E7) and its sentence on the basis of `N` (E8), a section on ASTRAL and the avian experiment. No erratum or later version was found. The software's release 1.0.2 (15 September 2026,
<https://github.com/jsdoublel/camus/releases>) fixes "issue #28 that could cause some output networks
to fail to be level-1 (due improper placement of branches attaching to the same edge in the
constraint tree)" and a non-optimality "in some cases with high values of k" (the exact-`k` code omitted the
subtree off the cycle at `v` in the case `u = v`, which Equation (5) includes). These concern the
implementation, not the paper; both points are explicit in the formalization (Section 6, and
[`DynamicProgramming.sdpGhost`](Challenge.lean#L596)).

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
  bottom node of each cycle. This is identifiability by equality of quartet sets; E7 concerns
  inclusion, which fails for such networks.
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
CAMUS. This work depends on lean4-adr11, for the quartet probabilities under the multispecies
coalescent and Steel's determination of a tree by its quartets (Section 2), and copies the network
coalescent of the maintainer's formalization of BROOQS; it consulted none of the others.

## 11. What's next

### Open directions

- **Identifiability under inclusion.** The corrected Section 3.2 ([`recovery`](Camus/Pipelines/Uniqueness.lean#L152)) needs the true network
  to be identifiable under inclusion among the networks built on `t` with no more reticulations. A
  tree is ([`tree_identifiable`](Camus/Pipelines/Uniqueness.lean#L191)), and a network of triangles is not. Networks whose cycles have
  length at least five need not be either, against the conjecture of the previous version of this
  report: moving the donor of an added edge down keeps every quartet that the edge satisfies (E7,
  [`Realization.deeper_donor_displays`](Camus/Network/SingleEdge/Deeper.lean#L49)). Warnow et al.'s Theorem 5 recovers from `Q(N_r)` the unrooted
  topology of such a network and the bottom node of each cycle, by equality of quartet sets, not by
  inclusion. A second tie-break, toward the fewest displayed quartets
  among the optimal networks with the fewest reticulations, selects the true network in E7's
  example (22 quartets against 25). Whether it recovers every network whose cycles have at least five
  vertices, and whether a dynamic program can compute it, is open; with Warnow et al.'s Theorem 5 and
  the convergence of the observed quartets ([`External.support_tendsto`](Camus/External/WarnowTabatabaeeEvans/Sampling.lean#L99)) it would give a consistent
  pipeline for SNPs.
- **The stopping rule.** E6 shows that the rule can stop before a better score, also when the scores
  never decrease. Computing all `n − 1` columns costs `O(n²(|Q| + n⁴))` time by Section 2.4's bound.
  A rule with a guarantee, or a characterization of the inputs whose best scores are concave in the
  number of reticulations, is open. The tie-break toward the fewest reticulations is computable with
  the same program: keep the least `k` whose row attains the unrestricted optimum `M[r]`.
- **The network coalescent.** E9 shows one anomalous network on which Quartet Filtering keeps the
  wrong quartets. Which parameters make the anomalous configuration defeat the filter, and whether a
  filter that tests the pattern of all three frequencies, not only the gap between the two smallest,
  avoids it, are open.

### Simpler proofs

- **Theorem 1 splits into Lemma 1 and a packing problem.** Section 2.2 already observes that, by
  Lemma 1, the number of quartets satisfied by a network built on `T` is the sum, over its added
  edges, of the weights `s_e`. The proof of Theorem 1 can use this once, before the induction: the
  theorem is then the statement that the recurrence computes a maximum-weight family of pairs whose
  cycles share no vertex of `T`, a packing of paths in a tree, whose proof by induction over subtrees
  involves no quartet and no double counting. The paper's proof instead invokes Lemma 1 inside the
  induction. The formal proof is organized this way ([`DynamicProgramming.trace_correct`](Camus/DP/Correctness.lean#L123) and
  [`DynamicProgramming.array_upper`](Camus/DP/Correctness.lean#L164) work with abstract weights), checked in Lean.
- **Display by clades.** A network displays a quartet if and only if some switching has an edge
  whose clade below cuts it ([`RootedNetwork.displays_iff_cladeBelow`](Camus/Network/Clades.lean#L186)). For `T + e` the clades are
  explicit, those of `T` and of `T'` ([`EdgeAbove.switchedClades`](Camus/Network/SingleEdge.lean#L127)), which makes every question about
  a network with one added edge a finite computation. The deeper-donor inclusion is then a comparison
  of clades ([`Realization.deeper_donor_displays`](Camus/Network/SingleEdge/Deeper.lean#L49)), and the constant-time test of Section 2.3 reads
  two lowest common ancestors in `T'` off the tables of `T` ([`Complexity.switched_cut_iff`](Camus/Complexity/Delta.lean#L525)).

### The formalization

The items of Section 9 are what remains. The general facts proved here about directed graphs,
switchings, subdivisions, cycle cuts and the clades of switchings
([`Camus/Network/`](Camus/Network)), and the cost monad of Section 2.3 ([`Camus/Complexity/Timed.lean`](Camus/Complexity/Timed.lean)), could serve
other formalizations of phylogenetic networks and of their algorithms.
