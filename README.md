# CAMUS's optimality, in Lean

[![Lean Action CI](https://github.com/vltanh/lean4-camus/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-camus/actions/workflows/lean_action_ci.yml)

A Lean 4 and Mathlib formalization of James Willson and Tandy Warnow, *CAMUS: scalable
phylogenetic network estimation*, Bioinformatics 42, Supplement 1 (2026), btag245,
<https://doi.org/10.1093/bioinformatics/btag245>. CAMUS takes a rooted binary tree `T` and a
multiset `Q` of quartet trees, and adds edges to `T` to obtain a rooted level-1 phylogenetic network
that displays as many quartets of `Q` as possible. The paper's Theorem 1 says that its dynamic
program over `T` finds such a network. The formalization proves Theorem 1 and Lemmas 1 and 2, by the
paper's arguments, and the claim of Section 2.4 with a recurrence of its own, over every finite
directed rooted binary level-1 network built on `T`. It is unconditional: the one result from the literature
that the proofs use, Observation 2 of Warnow, Tabatabaee and Evans (2025), which its authors state
without proof, is proved here. Two claims of the paper are false, and the formalization refutes
them: the best score with exactly `k` reticulations can decrease as `k` grows (Section 2.4), and
the true network need not be the unique optimum (Section 3.2).

## What is proved

- The paper's results, each by the paper's proof where it gives one: Lemma 1 ([`Camus.lemma1`](Camus/Preliminaries/Lemmas.lean#L138), [`Camus.lemma1_union`](Camus/Preliminaries/Lemmas.lean#L289)),
  Lemma 2 ([`Camus.lemma2`](Camus/Preliminaries/Lemmas.lean#L160)), Theorem 1 ([`Camus.theorem1`](Camus/DP/Theorem1.lean#L109)), the networks `N_k` of Section 2.4
  ([`BudgetDP.reticulation_restriction`](Camus/Restriction/Main.lean#L61)) and their bound of `n − 1` reticulations
  ([`RootedNetwork.anchored_reticulation_bound`](Camus/Network/Reticulations.lean#L227)), the operation counts of Sections 2.3 and 2.4 in a
  unit-cost accounting, and the test of Algorithm 1 (Section 3.4). One step departs from the paper:
  uniqueness in Lemma 1 (see the audit summary).
- The cited result: Observation 2 of Warnow, Tabatabaee and Evans
  ([`External.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L186)), proved from general facts about switchings and cycles.
- The two refutations ([`not_exactCountMonotone`](Camus/Restriction/Monotonicity.lean#L37), [`not_uniqueOptimum`](Camus/Pipelines/Uniqueness.lean#L49), and [`camus_may_add_edge`](Camus/Pipelines/Uniqueness.lean#L134):
  CAMUS itself may return the wrong network), and the corrected Section 3.2 ([`Camus.recovery`](Camus/Pipelines/Uniqueness.lean#L151)).
- `lake build` succeeds with no `sorry` outside [`Challenge.lean`](Challenge.lean) and no `axiom`;
  `lake env lean scripts/Audit.lean` checks that every declaration depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).

## The main results

[`Challenge.lean`](Challenge.lean) states them in Lean and Mathlib, with its own copy of the
definitions they need (its module docstring explains each one):

- [`Challenge.theorem1`](Challenge.lean#L771) (Theorem 1): for every array `M` satisfying the recurrence of Equations
  (1)–(5) and every backtracking trace `E`, the network obtained by adding `E` to `T` is built on
  `T`, satisfies `M[root]` quartets of `Q`, and no network built on `T` satisfies more, or displays
  more quartets of `Q`.
- [`Challenge.reticulation_restriction`](Challenge.lean#L804) (Section 2.4): the modified array's row `k` at the root is
  nonempty if and only if some network built on `T` has exactly `k` reticulations, and its value is
  then the best score among them, attained.
- [`Challenge.not_exactCountMonotone`](Challenge.lean#L824) and [`Challenge.not_uniqueOptimum`](Challenge.lean#L829): the claims of Sections 2.4
  and 3.2, stated as [`ExactCountMonotone`](Challenge.lean#L739) and [`UniqueOptimum`](Challenge.lean#L750), are false.
- [`Challenge.recovery`](Challenge.lean#L837): the claim of Section 3.2 holds when the true network is identifiable under
  inclusion and ties are broken toward the fewest reticulations; [`Challenge.tree_identifiable`](Challenge.lean#L854): a
  tree is identifiable under inclusion.
- [`Challenge.exists_array_trace`](Challenge.lean#L784) and [`Challenge.exists_budgetArray`](Challenge.lean#L819): the arrays and a trace exist;
  [`Challenge.tree_displays_iff`](Challenge.lean#L789): a tree displays exactly its own quartets;
  [`Challenge.edgeWeight_eq`](Challenge.lean#L795): the weights of Equation (1) count the quartets satisfied by one added
  edge.

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
  Section 2.4 (E5); the true network need not be the unique optimal network, and CAMUS may return
  another, contrary to Section 3.2 (E6). Theorem 1 is unaffected.
- **Gaps.** Lemma 1's proof derives uniqueness from Observation 2, which gives only existence;
  uniqueness follows from the vertex-disjointness of the cycles (E1). Section 2.2 calls `M[r]` the
  score of the best network, but `M[r]` counts the satisfied quartets, a constant fewer (E2).
- **Definitions read precisely.** Equation (1) is read over distinct quartets, as Section 2.3
  allows; summed over the multiset, a quartet's multiplicity would enter twice, `m²` for `m` (E3). `Pairs(v)` is read as the
  pairs that give a network; read literally it makes the recurrence circular (E4).
- **Missing hypotheses.** The corrected Section 3.2 needs identifiability under inclusion and a
  tie-break toward the fewest reticulations.
- **Redundant hypotheses.** None.
- **Use of cited results.** Observation 2 is used correctly for existence in Lemma 1, and is proved
  here.
- **Proofs.** Every proof follows the paper's, except uniqueness in Lemma 1, where the paper's step
  has the gap E1 and the formalization uses the disjointness of the cycles.
- **Typos.** E7.

## Credits

- Formalized in two rounds, at the request of The-Anh Vu-Le, following the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure (version 2.2.0):
  first by OpenAI's `gpt-6.1-sol` in Codex CLI, with three sub-agents (8 October 2026, 1.9 hours);
  then restyled and audited again by Claude Opus 5.5 in Claude Code, which also proved
  Observation 2 (10 October 2026, 1.8 hours, 9 sub-agents).
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
  quartet sets, where E6 concerns inclusion.
- Since the paper: NetCS (Dai and Molloy, WABI 2026) and BROOQS (Arasti and Mirarab, preprint, 2026)
  compare with CAMUS; BROOQS reports that CAMUS's default criterion overestimates the number of
  reticulations. No correction of the paper was found; release 1.0.2 of the software fixes the
  placement of ends of added edges on one edge of the tree.
- No other formalization of CAMUS or Observation 2 was found.

## What's next

A level-1 network whose cycles have length at least five should be identifiable under inclusion,
which would give the deterministic step of Section 3.2 for such networks; and the tie-break toward
the fewest reticulations is computable with Section 2.4's own dynamic program. Theorem 1 splits into
Lemma 1 and a weighted packing of paths in a tree, which is how the formal proof is organized. See
[`REPORT.md`](REPORT.md), Section 11.

## Building

```sh
lake exe cache get            # download Mathlib's compiled files
lake build                    # builds the library, the Challenge and the Solution
lake env lean scripts/Audit.lean                       # axioms and dependencies
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
python3 scripts/sync_challenge_defs.py --check         # the Challenge's copy of the definitions
python3 scripts/linkify_docs.py                        # update the documents' links to the code
```

The toolchain is Lean `v4.35.0-rc4`, with Mathlib's tag `v4.35.0-rc4`.
[`scripts/route_check.py`](scripts/route_check.py) reads `.lake/route_deps.tsv`, which the audit
writes.

## Layout

| Module | Contents |
| --- | --- |
| [`Camus/Defs.lean`](Camus/Defs.lean) | The definitions (the block copied into [`Challenge.lean`](Challenge.lean)): trees, quartets, networks and display (Definition 1), networks built on `T`, added edges (Definitions 2, 3, 5), the recurrence (Equations (1)–(5)), the modified recurrence of Section 2.4, the two refuted claims |
| [`Camus/Score.lean`](Camus/Score.lean) | Definition 4 and Equation (1); scores of multisets |
| [`Camus/Tree/`](Camus/Tree) | Lowest common ancestors, cycle footprints, Lemma 2 for families of added edges; hanging subtrees |
| [`Camus/Network/`](Camus/Network) | Directed networks: the canonical network of a family of added edges is level-1 and built on `T` ([`Camus/Network/Realization/`](Camus/Network/Realization)), every network built on `T` is one up to isomorphism ([`Camus/Network/Completeness/`](Camus/Network/Completeness)), display is invariant under subdivision and isomorphism ([`Camus/Network/Subdivision/`](Camus/Network/Subdivision), [`Camus/Network/Isomorphism/`](Camus/Network/Isomorphism)), a tree displays its own quartets ([`Camus/Network/Baseline/`](Camus/Network/Baseline)), switchings and cycle cuts ([`Camus/Network/Cuts.lean`](Camus/Network/Cuts.lean)), reticulation counts ([`Camus/Network/Reticulations.lean`](Camus/Network/Reticulations.lean)) |
| [`Camus/External/WarnowTabatabaeeEvans/`](Camus/External/WarnowTabatabaeeEvans) | Observation 2, stated and proved, with a README on its source |
| [`Camus/Preliminaries/`](Camus/Preliminaries) | Section 2.1: Lemmas 1 and 2 ([`Camus/Preliminaries/Lemmas.lean`](Camus/Preliminaries/Lemmas.lean)), with the steps of Lemma 1 ([`Camus/Preliminaries/Lemma1/`](Camus/Preliminaries/Lemma1)) |
| [`Camus/DP/`](Camus/DP) | Section 2.2: the geometry of feasible families and hanging subtrees ([`Camus/DP/Packing.lean`](Camus/DP/Packing.lean), [`Camus/DP/Frontier.lean`](Camus/DP/Frontier.lean)), the recurrence's correctness ([`Camus/DP/Correctness.lean`](Camus/DP/Correctness.lean)), Theorem 1 ([`Camus/DP/Theorem1.lean`](Camus/DP/Theorem1.lean)) |
| [`Camus/Complexity/`](Camus/Complexity) | Section 2.3: the operation and memory counts |
| [`Camus/Restriction/`](Camus/Restriction) | Section 2.4: the modified recurrence and its correctness, the networks `N_k` ([`Camus/Restriction/Main.lean`](Camus/Restriction/Main.lean)), and E5 ([`Camus/Restriction/Monotonicity.lean`](Camus/Restriction/Monotonicity.lean), [`Camus/Restriction/Witness.lean`](Camus/Restriction/Witness.lean), [`Camus/Restriction/Counterexample.lean`](Camus/Restriction/Counterexample.lean)) |
| [`Camus/Pipelines/`](Camus/Pipelines) | Section 3: E6 and the corrected recovery ([`Camus/Pipelines/Uniqueness.lean`](Camus/Pipelines/Uniqueness.lean), [`Camus/Pipelines/Counterexample.lean`](Camus/Pipelines/Counterexample.lean), [`Camus/Pipelines/Recovery.lean`](Camus/Pipelines/Recovery.lean), [`Camus/Pipelines/Statistical.lean`](Camus/Pipelines/Statistical.lean)), Algorithm 1 ([`Camus/Pipelines/Algorithm1.lean`](Camus/Pipelines/Algorithm1.lean), [`Camus/Pipelines/Filtering.lean`](Camus/Pipelines/Filtering.lean)) |
| [`Camus/Galled/`](Camus/Galled) | A block grammar of galled networks, with E3, E5 and E6 checked in it |
| [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean) | The statements of record, and their proofs from the library |
| [`scripts/`](scripts) | The audit, the route check, the Challenge's copy of the definitions, the documents' links and tables |
| [`docs/`](docs) | The routes of the paper's proofs, and the reviewed differences |

## GitHub configuration

`.github/workflows/lean_action_ci.yml` builds the project on every push and runs the audit, the route
check, and the checks of the Challenge's copy of the definitions, of the links and of the tables.
`.github/workflows/palomar_preflight.yml` runs Palomar's preflight on demand; it needs a public repository.

## License

Apache-2.0; see [`LICENSE`](LICENSE).
