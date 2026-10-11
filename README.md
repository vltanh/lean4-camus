# CAMUS's optimality, in Lean

[![Lean Action CI](https://github.com/vltanh/lean4-camus/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-camus/actions/workflows/lean_action_ci.yml)

A Lean 4 and Mathlib formalization of James Willson and Tandy Warnow, *CAMUS: scalable
phylogenetic network estimation*, Bioinformatics 42, Supplement 1 (2026), btag245,
<https://doi.org/10.1093/bioinformatics/btag245>. CAMUS takes a rooted binary tree `T` and a
multiset `Q` of quartet trees, and adds edges to `T` to obtain a rooted level-1 phylogenetic network
that displays as many quartets of `Q` as possible. The paper's Theorem 1 says that its dynamic
program over `T` finds such a network. The formalization proves Lemmas 1 and 2 and Theorem 1, by the paper's arguments except at two steps,
Theorem 1 against every network built on `T` in the sense of Definition 1, whose root may lie above
the root of `T`; the running time and peak memory of Sections 2.3 and 2.4, for CAMUS written as a
program in a cost semantics; the claim of Section 2.4, for the networks returned by backtracking
through a recurrence of its own; and the steps of the paper's statistical arguments (Sections 3.2 to
3.4) inside the models they use, with the network multispecies coalescent for Quartet Filtering. It
is unconditional: the results from the literature that the proofs use, Observation 2 and the site
model of Warnow, Tabatabaee and Evans (2025), are proved here, the coalescent probabilities come
from a Lean formalization of Allman, Degnan and Rhodes (2011), and the network coalescent from the
maintainer's formalization of BROOQS. Four claims of the paper are false, and the formalization
refutes them: the best score with exactly `k` reticulations can decrease as `k` grows, and the
stopping rule can stop before a better score (Section 2.4); the true network need not be the unique
optimum, even with the fewest reticulations, cycles of length at least five and an outgroup, so that
the SNP pipeline can fail under every hypothesis of its consistency argument; and a tree of a
network need not be a basis for it (Section 3.2). Under the network coalescent, Quartet Filtering
can keep a quartet outside `Q(N_r)` and drop the one inside it (Sections 3.3 and 3.4); for
thresholds 0 < t < t₀(N) it almost surely ends up doing so exactly in an explicit region of the
parameters of the network.

## What is proved

- The paper's results, each by the paper's proof where it gives one: Lemma 1 ([`Camus.lemma1`](Camus/Preliminaries/Lemmas.lean#L139),
  [`Camus.lemma1_union`](Camus/Preliminaries/Lemmas.lean#L290)), Lemma 2 ([`Camus.lemma2`](Camus/Preliminaries/Lemmas.lean#L161)), Theorem 1 ([`Camus.theorem1`](Camus/DP/Theorem1.lean#L109), and over Definition
  1's class [`Camus.theorem1_builtOn`](Camus/DP/Definition1.lean#L76)), the running time `O(n²(|Q| + n))` and memory `O(n⁴)` of
  Section 2.3 for CAMUS as a program, with `δ_T` in constant time ([`Complexity.camus_array`](Camus/Complexity/Program.lean#L1090),
  [`Complexity.camus_time`](Camus/Complexity/Program.lean#L1193), [`Complexity.time_delta`](Camus/Complexity/Delta.lean#L746), [`Complexity.storedIntegers_bound`](Camus/Complexity/Memory.lean#L181), and the peak
  memory [`Complexity.camus_memory`](Camus/Complexity/PeakMemory.lean#L391), with the memory of each step declared in the program), the
  networks `N_k` of Section 2.4 returned by backtracking ([`BudgetDP.reticulation_restriction`](Camus/Restriction/Main.lean#L61),
  [`BudgetDP.backtracking_networks`](Camus/Restriction/Backtracking.lean#L499)), the running time `O(n²(|Q| + m³n))` of computing the modified
  array and backtracking ([`Complexity.camusBudget_time`](Camus/Complexity/BudgetProgram.lean#L682), [`Complexity.camusBudgetNetworks_time`](Camus/Complexity/BudgetBacktracking.lean#L1302)), and
  the bound of `n − 1` reticulations ([`RootedNetwork.anchored_reticulation_bound`](Camus/Network/Reticulations.lean#L228), and for every
  rooted binary level-1 network [`RootedNetwork.reticulationCount_le`](Camus/Network/TreeBased/Root.lean#L267)), tree-basedness
  ([`RootedNetwork.treeBased`](Camus/Network/TreeBased/Main.lean#L135)), the SNP pipeline of Section 3.2 as one statement in the site model of
  Warnow et al. ([`pipeline_tendsto`](Camus/Pipelines/Pipeline.lean#L486)), and the test of Algorithm 1 with its motivation under the
  multispecies coalescent ([`Coalescent.msc_filterQuartets`](Camus/Pipelines/Coalescent.lean#L250)) and the network coalescent
  ([`Camus.NMSC.nmsc_filterQuartets_support`](Camus/Pipelines/NMSC/Recovery.lean#L100), [`Camus.NMSC.anomaly_filterQuartets`](Camus/Pipelines/NMSC/Anomaly.lean#L238)), with recovery,
  without the anomalous configuration and for 0 < t < t₀(N), under identifiability under inclusion
  and the tie-break, through every displayed tree of the network when its root has an outgroup leaf,
  including the tree of ASTRAL when it is one of them ([`Camus.NMSC.nmsc_recovery_displayed`](Camus/Pipelines/NMSC/DisplayedTrees.lean#L1104),
  [`Camus.NMSC.nmsc_recovery_underlying`](Camus/Pipelines/NMSC/Pipeline.lean#L117)), the symmetry of the model under the exchange of the sides
  of a cycle ([`Brooqs.Net.SideSwap.geneTreeDist_eq`](Camus/External/NMSC/Swap.lean#L307)), and the exact region of the anomaly in every
  network ([`Brooqs.Net.Cycle.anomalous_iff_of_anomalous`](Camus/External/NMSC/AnomalyGeneral.lean#L890), [`Camus.NMSC.anomalous_drop_iff`](Camus/Pipelines/NMSC/AnomalyBoundary.lean#L749)). Two
  steps depart from the paper: uniqueness in Lemma 1, and the networks of Definition 1 whose root
  lies above the root of `T` (see the audit summary).
- The cited results: Observation 2 of Warnow, Tabatabaee and Evans ([`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L187)), proved
  from general facts about switchings and cycles, and the convergence of the quartets of SNPs under
  their site model ([`External.support_tendsto`](Camus/External/WarnowTabatabaeeEvans/Sampling.lean#L99)), with a hypothesis their model omits.
- The refutations ([`not_exactCountMonotone`](Camus/Restriction/Monotonicity.lean#L37), [`not_exactStoppingRule`](Camus/Restriction/StoppingRule.lean#L462), [`not_atMostStoppingRule`](Camus/Restriction/StoppingRule.lean#L481),
  [`not_uniqueOptimum`](Camus/Pipelines/Uniqueness.lean#L50), [`Counterexamples.shallow_not_identifiable`](Camus/Pipelines/Inclusion.lean#L219),
  [`Counterexamples.deeperDonor_meets_hypotheses`](Camus/Pipelines/SNPCondition.lean#L321), with an outgroup,
  [`Counterexamples.camus_output_not_rootAboveNet`](Camus/Network/RootAbove/Example.lean#L414)),
  with CAMUS itself returning the wrong network ([`camus_may_add_edge`](Camus/Pipelines/Uniqueness.lean#L135),
  [`Counterexamples.camus_may_return_deep`](Camus/Pipelines/Inclusion.lean#L374)), and the corrected Section 3.2 ([`Camus.recovery`](Camus/Pipelines/Uniqueness.lean#L152)).
- `lake build` succeeds with no `sorry` outside [`Challenge.lean`](Challenge.lean) and no `axiom`;
  `lake env lean scripts/Audit.lean` checks that every declaration depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).

## The main results

[`Challenge.lean`](Challenge.lean) states them in Lean and Mathlib, with its own copy of the definitions they need
(its module docstring explains each one):

- [`Challenge.theorem1`](Challenge.lean#L852) (Theorem 1): for every array `M` satisfying the recurrence of Equations
  (1)–(5) and every backtracking trace `E`, the network obtained by adding `E` to `T` is built on
  `T`, satisfies `M[root]` quartets of `Q`, and no network built on `T` in the sense of Definition 1
  satisfies more, or displays more quartets of `Q`.
- [`Challenge.definition1_reduction`](Challenge.lean#L883), [`Challenge.builtOn_not_anchored`](Challenge.lean#L891): every network built on `T` in
  the sense of Definition 1 has the reticulations and the quartets of a network obtained by adding
  edges to `T`, and the first class is larger.
- [`Challenge.reticulation_restriction`](Challenge.lean#L903) (Section 2.4): the modified array's row `k` at the root is
  nonempty if and only if some network built on `T` has exactly `k` reticulations, and every network
  returned by backtracking from it is built on `T`, has `k` reticulations and the best score among
  them.
- [`Challenge.not_exactCountMonotone`](Challenge.lean#L926), [`Challenge.not_exactStoppingRule`](Challenge.lean#L932),
  [`Challenge.not_atMostStoppingRule`](Challenge.lean#L937) and [`Challenge.not_uniqueOptimum`](Challenge.lean#L942): the claims of Sections 2.4
  and 3.2, stated as [`ExactCountMonotone`](Challenge.lean#L781), [`ExactStoppingRule`](Challenge.lean#L826), [`AtMostStoppingRule`](Challenge.lean#L834) and
  [`UniqueOptimum`](Challenge.lean#L792), are false.
- [`Challenge.recovery`](Challenge.lean#L950): the claim of Section 3.2 holds when the true network is identifiable under
  inclusion and ties are broken toward the fewest reticulations; [`Challenge.tree_identifiable`](Challenge.lean#L967): a
  tree is identifiable under inclusion; [`Challenge.recovery_needs_identifiable`](Challenge.lean#L980): identifiability
  cannot be dropped, even with the tie-break.
- [`Challenge.exists_array_trace`](Challenge.lean#L865) and [`Challenge.exists_budget_traces`](Challenge.lean#L920): the arrays and the traces
  exist; [`Challenge.tree_displays_iff`](Challenge.lean#L870): a tree displays exactly its own quartets;
  [`Challenge.edgeWeight_eq`](Challenge.lean#L876): the weights of Equation (1) count the quartets satisfied by one added
  edge.

The cost semantics of Sections 2.3 and 2.4, the probabilistic statements of Sections 3.2 and 3.4
and the general deeper-donor theorem are in the library only.

## Palomar

The project is packaged for the [Palomar](https://palomar-registry.org) registry:
[`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean) (which restates the Challenge's
theorems and proves them from the library), [`comparator.json`](comparator.json) and
[`formalization.yaml`](formalization.yaml). It is not submitted. To run Comparator locally (it needs
[bubblewrap](https://github.com/containers/bubblewrap)):

```sh
lake env lake comparator --config=comparator.json
```

## Audit summary

From [`REPORT.md`](REPORT.md):

- **Errors.** The best score with exactly `k` reticulations can decrease as `k` grows, contrary to
  Section 2.4 (E5), whose stopping rule can stop before a better score (E6). The true network need
  not be the unique optimal network, even with the fewest reticulations and cycles of length at
  least five, and CAMUS may return another, contrary to Section 3.2; in the site model of Warnow et
  al. such a tie occurs with probability tending to 1 under every hypothesis of the section's
  argument, an outgroup included (E7). A tree of a network need not be a basis for it, contrary to
  Section 3.2 (E8). Under the network coalescent, on a network in the anomalous configuration of Ané
  et al. (2024), with suitable edge lengths, Quartet Filtering keeps a quartet outside `Q(N_r)` and
  drops the one inside it, against the aims of Section 3.3; the region of parameters in which this
  happens is determined exactly, in every network (E9). Theorem 1 is unaffected.
- **Gaps.** Lemma 1's proof derives uniqueness from Observation 2, which gives only existence;
  uniqueness follows from the vertex-disjointness of the cycles (E1). Section 2.2 calls `M[r]` the
  score of the best network, but `M[r]` counts the satisfied quartets, a constant fewer (E2). The
  proof of Theorem 1 does not treat the networks of Definition 1 whose root lies above the root of
  `T`; they display the quartets of networks that it does treat (E8).
- **Definitions read precisely.** Equation (1) is read over distinct quartets, as Section 2.3
  allows; summed over the multiset, a quartet's multiplicity would enter twice, `m²` for `m` (E3). `Pairs(v)` is read as the
  pairs that give a network; read literally it makes the recurrence circular (E4).
- **Missing hypotheses.** The corrected Section 3.2 needs identifiability under inclusion and a
  tie-break toward the fewest reticulations; Warnow et al.'s site model needs `p(e, s, s) > 0` on
  the tree edges for the convergence of the observed quartets; the motivation of Algorithm 1 needs a
  positive threshold.
- **Redundant hypotheses.** None.
- **Use of cited results.** Observation 2 is used correctly for existence in Lemma 1, and is proved
  here; the convergence of the observed quartets holds with the hypothesis above, and is proved here.
- **Proofs.** Every proof follows the paper's, except uniqueness in Lemma 1, where the paper's step
  has the gap E1 and the formalization uses the disjointness of the cycles, and Theorem 1 over
  Definition 1's class, where the networks whose root lies above the root of `T` are first reduced
  to the others (E8).
- **Typos.** E10.

## Credits

- Formalized in six rounds, at the request of The-Anh Vu-Le, following the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure (version 2.2.0):
  first by OpenAI's `gpt-6.1-sol` in Codex CLI, with three sub-agents (8 October 2026, 1.9 hours);
  then restyled and audited again by Claude Opus 5.5 in Claude Code, which also proved Observation 2
  (10 October 2026, 1.8 hours, 9 sub-agents); then extended by Claude Opus 5.5 to the parts that the
  second round left out: the cost semantics, backtracking and the stopping rule of Sections 2.3 and
  2.4, Definition 1's class, the models of Sections 3.2 and 3.4, and the counterexamples (10 October
  2026, 2.8 hours, 10 sub-agents); then, in a fourth round, the items that remained: tree-basedness,
  the SNP pipeline as one statement, backtracking time and peak memory, and Quartet Filtering under
  the network coalescent (10 October 2026, 3.2 hours, 5 sub-agents, then a review by 4 more); then,
  in a fifth round, three items left under the network coalescent: recovery through every tree, the
  exchange of the sides of a cycle, and the region of the anomaly (10 October 2026, 1.1 hours, 3
  sub-agents); then, in a sixth round, the displayed trees of the model as the trees of the graph of
  `N`, the pipeline of Section 3.3, and the region of the anomaly in every network (10 October 2026,
  1.6 hours, 3 sub-agents).
- No person has reviewed the proofs yet; independent agents reviewed the statements, the proofs, the
  findings and the account of the literature. [`CREDITS.md`](CREDITS.md) gives the details.

## Related work

From [`REPORT.md`](REPORT.md), Section 10 (search of 10 October 2026):

- CAMUS belongs to the two-phase methods that add edges to a tree (T-REX, Makarenkov 2001; Cao, Zhu
  and Nakhleh 2019); no exact algorithm for its problem, with the tree fixed, was found before it.
  Without a fixed tree, maximizing consistent triplets over level-`k` networks is NP-hard (van
  Iersel, Kelk and Mnich 2009).
- Observation 2 comes from Warnow, Tabatabaee and Evans (2025), who state it without proof; their
  Theorem 5 shows that the quartets of a level-1 network with cycles of length at least five
  determine its unrooted topology and the bottom node of each cycle, which concerns equality of
  quartet sets, where E7 concerns inclusion. Their site model is formalized here, with a hypothesis
  that their argument needs.
- Since the paper: NetCS (Dai and Molloy, WABI 2026) and BROOQS (Arasti and Mirarab, preprint, 2026)
  compare with CAMUS; BROOQS reports that CAMUS's default criterion overestimates the number of
  reticulations. No correction of the paper was found; release 1.0.2 of the software fixes the
  placement of ends of added edges on one edge of the tree.
- No other formalization of CAMUS or Observation 2 was found. The coalescent probabilities come
  from lean4-adr11, a formalization of Allman, Degnan and Rhodes (2011) by the same maintainer.

## What's next

Identifiability under inclusion fails even for networks whose cycles have length at least five (E7);
a second tie-break toward the fewest displayed quartets selects the true network in the
counterexample, and whether it recovers every such network is open. Under the network coalescent,
the region in which the anomaly of E9 defeats Quartet Filtering is determined for every network;
whether a filter that tests all three frequencies avoids the anomaly is open. Theorem 1 splits into
Lemma 1 and a weighted packing of paths in a tree, which is how the formal proof is organized, and
display by the clades of switchings makes every question about one added edge a finite computation.
See [`REPORT.md`](REPORT.md), Section 11.

## Building

```sh
lake exe cache get            # download Mathlib's compiled files
lake build                    # builds the library, the Challenge and the Solution
lake env lean scripts/Audit.lean                       # axioms and dependencies
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
python3 scripts/sync_challenge_defs.py --check         # the Challenge's copy of the definitions
python3 scripts/linkify_docs.py                        # update the documents' links to the code
```

The toolchain is Lean `v4.35.0-rc4`, with Mathlib's tag `v4.35.0-rc4`; the library also depends
on <https://github.com/vltanh/lean4-adr11>, for the multispecies coalescent.
[`scripts/route_check.py`](scripts/route_check.py) reads `.lake/route_deps.tsv`, which the audit
writes.

## Layout

| Module | Contents |
| --- | --- |
| [`Camus/Defs.lean`](Camus/Defs.lean) | The definitions (the block copied into [`Challenge.lean`](Challenge.lean)): trees, quartets, networks and display (Definition 1), networks built on `T` (root kept, and in the sense of Definition 1), added edges (Definitions 2, 3, 5), the recurrence (Equations (1)–(5)), the modified recurrence of Section 2.4 and its backtracking, the refuted claims |
| [`Camus/Score.lean`](Camus/Score.lean) | Definition 4 and Equation (1); scores of multisets |
| [`Camus/Tree/`](Camus/Tree) | Lowest common ancestors, cycle footprints, Lemma 2 for families of added edges; hanging subtrees |
| [`Camus/Network/`](Camus/Network) | Directed networks: the canonical network of a family of added edges is level-1 and built on `T` ([`Camus/Network/Realization/`](Camus/Network/Realization)), every network built on `T` is one up to isomorphism ([`Camus/Network/Completeness/`](Camus/Network/Completeness)), display is invariant under subdivision and isomorphism ([`Camus/Network/Subdivision/`](Camus/Network/Subdivision), [`Camus/Network/Isomorphism/`](Camus/Network/Isomorphism)), a tree displays its own quartets ([`Camus/Network/Baseline/`](Camus/Network/Baseline)), switchings and cycle cuts ([`Camus/Network/Cuts.lean`](Camus/Network/Cuts.lean)), display by the clades of switchings ([`Camus/Network/Clades.lean`](Camus/Network/Clades.lean)), the quartets displayed by `T + e` and the deeper donor ([`Camus/Network/SingleEdge.lean`](Camus/Network/SingleEdge.lean), [`Camus/Network/SingleEdge/`](Camus/Network/SingleEdge)), Definition 1's networks whose root lies above the root of `T` ([`Camus/Network/RootAbove/`](Camus/Network/RootAbove)), tree-basedness ([`Camus/Network/TreeBased/`](Camus/Network/TreeBased)), trees equal up to the order of children ([`Camus/Network/RootedIso.lean`](Camus/Network/RootedIso.lean)), reticulation counts ([`Camus/Network/Reticulations.lean`](Camus/Network/Reticulations.lean)) |
| [`Camus/External/WarnowTabatabaeeEvans/`](Camus/External/WarnowTabatabaeeEvans) | Observation 2, and the site model with the convergence of the quartets of SNPs and the gap in Theorem 6, with a README on their source |
| [`Camus/External/NMSC/`](Camus/External/NMSC) | The network multispecies coalescent, copied from the maintainer's formalization of BROOQS, and files written for CAMUS: the displayed quartets, the pattern of the quartet concordance factors of every four taxa (strict outside the anomalous configuration), the anomalous configuration of E9 and its exact region in every network, the exchange of the sides of a cycle, and independent gene trees; a README gives its source |
| [`Camus/Preliminaries/`](Camus/Preliminaries) | Section 2.1: Lemmas 1 and 2 ([`Camus/Preliminaries/Lemmas.lean`](Camus/Preliminaries/Lemmas.lean)), with the steps of Lemma 1 ([`Camus/Preliminaries/Lemma1/`](Camus/Preliminaries/Lemma1)), and Figure 1 ([`Camus/Preliminaries/Figure1.lean`](Camus/Preliminaries/Figure1.lean)) |
| [`Camus/DP/`](Camus/DP) | Section 2.2: the geometry of feasible families and hanging subtrees ([`Camus/DP/Packing.lean`](Camus/DP/Packing.lean), [`Camus/DP/Frontier.lean`](Camus/DP/Frontier.lean)), the recurrence's correctness ([`Camus/DP/Correctness.lean`](Camus/DP/Correctness.lean)), Theorem 1 ([`Camus/DP/Theorem1.lean`](Camus/DP/Theorem1.lean)), over Definition 1's class ([`Camus/DP/Definition1.lean`](Camus/DP/Definition1.lean)) |
| [`Camus/Complexity/`](Camus/Complexity) | Sections 2.3 and 2.4: the cost monad ([`Camus/Complexity/Timed.lean`](Camus/Complexity/Timed.lean)), the preprocessing ([`Camus/Complexity/Tables.lean`](Camus/Complexity/Tables.lean)), `δ_T` in constant time ([`Camus/Complexity/Delta.lean`](Camus/Complexity/Delta.lean)), CAMUS as a program and its running time ([`Camus/Complexity/Program.lean`](Camus/Complexity/Program.lean), [`Camus/Complexity/Backtracking.lean`](Camus/Complexity/Backtracking.lean), [`Camus/Complexity/BudgetProgram.lean`](Camus/Complexity/BudgetProgram.lean), [`Camus/Complexity/BudgetBacktracking.lean`](Camus/Complexity/BudgetBacktracking.lean)), memory ([`Camus/Complexity/Memory.lean`](Camus/Complexity/Memory.lean), [`Camus/Complexity/Counts.lean`](Camus/Complexity/Counts.lean), and the peak in [`Camus/Complexity/Space.lean`](Camus/Complexity/Space.lean), [`Camus/Complexity/PeakMemory.lean`](Camus/Complexity/PeakMemory.lean), [`Camus/Complexity/PeakMemoryBudget.lean`](Camus/Complexity/PeakMemoryBudget.lean)) |
| [`Camus/Restriction/`](Camus/Restriction) | Section 2.4: the modified recurrence and its correctness, the networks `N_k` ([`Camus/Restriction/Main.lean`](Camus/Restriction/Main.lean)) and their backtracking ([`Camus/Restriction/Backtracking.lean`](Camus/Restriction/Backtracking.lean)), E5 ([`Camus/Restriction/Monotonicity.lean`](Camus/Restriction/Monotonicity.lean), [`Camus/Restriction/Witness.lean`](Camus/Restriction/Witness.lean), [`Camus/Restriction/Counterexample.lean`](Camus/Restriction/Counterexample.lean)) and E6 ([`Camus/Restriction/StoppingRule.lean`](Camus/Restriction/StoppingRule.lean)) |
| [`Camus/Pipelines/`](Camus/Pipelines) | Section 3: E7 and the corrected recovery ([`Camus/Pipelines/Uniqueness.lean`](Camus/Pipelines/Uniqueness.lean), [`Camus/Pipelines/Counterexample.lean`](Camus/Pipelines/Counterexample.lean), [`Camus/Pipelines/Inclusion.lean`](Camus/Pipelines/Inclusion.lean), [`Camus/Pipelines/Recovery.lean`](Camus/Pipelines/Recovery.lean), [`Camus/Pipelines/Statistical.lean`](Camus/Pipelines/Statistical.lean)), the SNP pipeline in the site model ([`Camus/Pipelines/Astral.lean`](Camus/Pipelines/Astral.lean), [`Camus/Pipelines/AstralTree.lean`](Camus/Pipelines/AstralTree.lean), [`Camus/Pipelines/SNP.lean`](Camus/Pipelines/SNP.lean), [`Camus/Pipelines/SNPCondition.lean`](Camus/Pipelines/SNPCondition.lean), [`Camus/Pipelines/Pipeline.lean`](Camus/Pipelines/Pipeline.lean)), Algorithm 1 ([`Camus/Pipelines/Algorithm1.lean`](Camus/Pipelines/Algorithm1.lean), [`Camus/Pipelines/Filtering.lean`](Camus/Pipelines/Filtering.lean)) and its motivation under the multispecies coalescent ([`Camus/Pipelines/Coalescent.lean`](Camus/Pipelines/Coalescent.lean), [`Camus/Pipelines/Coalescent/`](Camus/Pipelines/Coalescent)) and the network coalescent ([`Camus/Pipelines/NMSC/`](Camus/Pipelines/NMSC)) |
| [`Camus/Galled/`](Camus/Galled) | A block grammar of galled networks, with E3, E5 and E7 checked in it |
| [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean) | The statements of record, and their proofs from the library |
| [`scripts/`](scripts) | The audit, the route check, the Challenge's copy of the definitions, the documents' links and tables |
| [`docs/`](docs) | The routes of the paper's proofs, and the reviewed differences |

## GitHub configuration

`.github/workflows/lean_action_ci.yml` builds the project on every push and runs the audit, the route
check, and the checks of the Challenge's copy of the definitions, of the links and of the tables.
`.github/workflows/palomar_preflight.yml` runs Palomar's preflight on demand; it needs a public repository.

## License

Apache-2.0; see [`LICENSE`](LICENSE).
