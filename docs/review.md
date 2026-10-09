# Independent proof and source review

Reviewer: the source-review agent, independently reviewing the implementation groups. Source: published JATS `sources/paper.xml`, accession PMC13340232. Original publisher TeX was unavailable. This review is not a substitute for the final project build, axiom audit, Comparator or dependency-route checks.

## Dynamic program and baseline

The mathematical statements and proof routes of `PackingGeometry`, `CycleFrontier`, `PackingTheorem` and `GraphBaselineCuts`/`GraphBaselineClades`/`GraphBaseline` pass review against §2.2. In particular:

- `array_upper` follows the source's two-case strong induction. The finite remaining-depth measure replaces leafset cardinality only as a termination measure; every hanging subproblem is strictly below its target.
- The equal-target contradiction in `competitor_in_hanging` invokes geometric Lemma 2, `EdgeAbove.target_unique`. This is the paper's reason that a target can carry at most one reticulation.
- `hanging_score` explicitly invokes both `equation4` and `equation5`. Their off-cycle child test uses children in the actual subdivided single-edge network, as Definition 5 requires. An original endpoint's parent can have a new subdivision vertex as its on-cycle child; testing only membership of the original child in an original-node footprint would be wrong.
- `Trace` contains recurrence and branch-choice laws, not feasibility or optimality assumptions. These conclusions are proved by `trace_correct` and `array_upper`. `exists_array_trace` constructs an array and trace, so the main premise is inhabited.
- Baseline display is proved from actual graph switching and cut reachability. It is not a defining field of the support representation.

The source's phrase “satisfied by N” explicitly means newly displayed relative to T in the paragraph immediately following Definition 1. Consequently the nonbaseline hypothesis in Lemma 1 is faithful, and is not a correction to that lemma. The source's other use of “score” as total observed support requires the proved fixed-baseline offset.

## Directed graph representation

`RootedBinaryLevelOne`, `SupportSubdivision`, `GraphSubdivision` and `Iso` contain graph, wire, root and label laws only. They contain no optimization or quartet attribution conclusion. The main domain is arbitrary finite directed graphs with an explicit root-preserving support-tree subdivision. It is stronger information than simply suppressing a switching and allowing its root to move; the report must identify this root-preserving reading of “built upon T.”

The realization review checks actual degree laws, reachability, directed acyclicity and disjointness of all simple undirected cycles. Directed acyclicity is proved using recipient cones to rule out returns across added arcs. The cactus proof classifies every cyclic edge by a fundamental cycle and then uses the degree-two cyclic subgraph; it does not merely verify the intended cycles.

The completeness review checks endpoint degree classification, fundamental cycle disjointness, admissible extracted pairs and canonical graph encoding. The canonical isomorphism is built from a vertex equivalence and directed wire equality. It does not assume the graph equals its extracted representation. Multiple subdivision endpoints on a shared original wire are allowed. Their possible outer-then-ghost order is proved; a one-subdivision-per-wire restriction is not imposed. The public `canonical_iso` supplies the internally proved pair injectivity and separation premises of `canonicalIso`.

The completed `single_edge_reduction` constructs the selected-edge support refinement by splitting the two actual source wires, reinserting the selected directed edge, and transporting through the proved canonical vertex bijection. Wire lists, vertex coverage and directed edges are proved for the refined graph; suppression is not an assumed display theorem. The generic split/map fields are defining graph data laws, not decomposition hypotheses. This final bridge passes review.

## Graph invariance and quartet attribution

The subdivision display bridge passes review. For arbitrary retained edge sets, connected-component colors prove reachability between original vertices exactly when the corresponding full source wires are retained. Switching correspondence keeps every forced interior incoming arc and omits only the last arc of an omitted source edge. The resulting dangling unlabelled wire tails cause no false quartet. Unique ownership of an undirected cut excludes antiparallel source arcs using the source DAG hypothesis. The proof excludes an inactive-wire cut by connectedness of the source switching.

The isomorphism display bridge is proved by transporting switchings, cuts and reachability along the finite vertex equivalence, extended to a permutation of the ambient natural numbers.

Lemma 1 existence uses the named cited Observation 2. Its bridge alternative is baseline; its cycle alternative transfers through the proved single-edge reduction. Uniqueness is proved independently: the two within-pair support paths of a nonbaseline quartet intersect, and that common vertex must lie on any responsible fundamental cycle. Two distinct responsible cycles therefore violate level-1 vertex disjointness. `novel_disjoint_union` invokes numbered Lemma 1, rather than assuming attribution. The graph Lemma 2 explicitly bridges the extracted geometry to the paper's target uniqueness argument.

## Source readings and remaining coverage

The inventory's Eq. 4/5 tests must retain MathML `menclose notation="updiagonalstrike"` as nonmembership. Plain XML text extraction loses the strike; this is an extraction artifact, not a reversed condition in the publication.

Eq. 1 is read as a sum over distinct observed quartet topologies with multiplicities as weights, consistent with §2.3. Literal occurrence-wise multiset summation counts a repeated quartet twice. The informal `Pairs(v)` criterion needs valid edge-above pairs: no root endpoints and no recipient ancestor of its donor. Ghost donors are retained.

The user-authorized at-most-budget and consistency adaptations must remain visibly distinguished from the false exact-budget monotonicity and automatic unique optimizer claims. The universal exact-budget counterexample is currently proved in the concrete `GalledNetwork` block grammar; no equivalence of that grammar with arbitrary directed graphs is supplied. The E4 optimizer counterexample additionally has an actual directed-graph certificate in `GraphCounterexamples`. Do not claim that representation bridge is already Lean-checked.

The exact-budget knapsack recurrence is implemented in the new BudgetDP modules and its finite array existence, feasibility and optimality are proved. Abstract operation/storage bounds are proved under the declared unit-cost tabulation model; correspondence to actual executable runtime is not proved. Biological model-to-empirical-support convergence, empirical experiments, the early stopping rule and actual execution of the published software remain outside the proved scope. The directed-network reticulation count bound is proved.

## Verification boundary

Review found no new blocking mathematical defect in the completed dynamic program, baseline, realization, canonical isomorphism or invariance proofs. Final kernel and route checks remain the integrating agent's responsibility. In particular, conditional use of the unproved cited Observation 2 must be stated in every completion claim. This document records a review, not final completion certification.
