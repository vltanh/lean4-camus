# Audit of CAMUS and its formalization

Paper: James Willson and Tandy Warnow, *CAMUS: scalable phylogenetic network estimation*, Bioinformatics 42, Supplement 1 (2026), [DOI 10.1093/bioinformatics/btag245](https://academic.oup.com/bioinformatics/article/42/Supplement_1/btag245/8726316). The source of record is the publisher's JATS/MathML, archived as [`sources/paper.xml`](sources/paper.xml) from [Europe PMC, PMC13340232](https://www.ebi.ac.uk/europepmc/webservices/rest/PMC13340232/fullTextXML). Publisher TeX was not available. Locations below use the published section numbers and JATS IDs. The earlier [bioRxiv version](https://doi.org/10.64898/2026.02.01.703143) first appeared on 2026-02-04; the recorded v2 is dated 2026-02-05. The published article appeared in July 2026.

**Conditional formalization, checked locally.** The full unrestricted and exact-budget CAMUS optimization statements are proved over the explicit root-preserving graph-extension domain, conditional on the named cited Observation 2. The directed-network library, all representation bridges, quartet attribution and both dynamic programs contain no proof placeholders. `lake build` passes; the 1,927-declaration axiom audit permits only Lean's three standard axioms; the reviewed source-route check and Comparator pass. Lean and NanoDa accept all four immutable target statements. The biological model implications, experimental results and correspondence with the executable published software are outside the proved scope.

## 1. Summary

The main optimization argument follows the paper's cycle decomposition, Lemmas 1–2 and Equations 1–5. The exact-budget extension is proved using maximum-pruned knapsack allocations across those hanging subproblems, with empty rows for infeasible counts; its graph theorem does not claim an early stopping rule. Feasible edge families are realized as actual directed rooted binary level-1 graphs; arbitrary graphs in the declared extension domain are canonically recovered from their support-tree subdivisions. Decomposition, realization, graph equivalence and quartet attribution are proved rather than supplied as optimality hypotheses.

Two secondary conclusions require corrections authorized by the user: exact-reticulation-budget monotonicity (§2.4) is replaced with at-most-budget monotonicity, and the automatic unique optimizer claim (§3.2) is replaced with explicit inclusion-identifiability and minimum-reticulation tie-breaking. Concrete counterexamples are kernel-checked in the block-network representation, with additional actual directed-graph certificates documented below.

Eq. 1 needs a weighted-support reading to avoid counting multiplicities twice. The candidate pair definition needs the valid-network restriction already implicit in its description. The recurrence measures newly displayed support; total support differs by a fixed baseline, with the same optimizers. Lemma 1's nonbaseline condition is faithful to the definition of “satisfied” immediately after Definition 1, not a correction to that lemma.

The only unproved mathematical premise of the main theorem is the explicitly named cited Observation 2. Standard graph, tree, finiteness and score facts are proved locally or obtained from Mathlib. No redundant published hypothesis was identified. Independent agent review found no new blocking defect in the completed recurrence, realization, canonical isomorphism, graph invariance and attribution arguments; see [`docs/review.md`](docs/review.md).

## 2. Prior results used by the paper

### Assumed: a conditional formalization

| Result | Source and source use | Formal premise | Missing formal mathematics |
| --- | --- | --- | --- |
| Observation 2: quartet display iff a bridge cut or an appropriate two-edge cycle cut separates the pairs | Warnow, Tabatabaee and Evans, *Advances in Estimating Level-1 Phylogenetic Networks from Unrooted SNPs*, Journal of Computational Biology 32(1), 3–27 (2025), [DOI 10.1089/cmb.2024.0710](https://doi.org/10.1089/cmb.2024.0710); used for Lemma 1 | [`External.WarnowTabatabaeeEvansObservation2`](Camus/External/Observation2.lean#L19), supplied explicitly to [`lemma1`](Camus/QuartetAttribution.lean#L50) and [`theorem1`](Camus/MainTheorem.lean#L42) | A proof of the graph cut characterization from the displayed-switching definition |

The premise is a named proposition, not a declared axiom. It characterizes actual graph display and does not assert unique attribution or the CAMUS decomposition. Its cycle condition retains dependence on the bottom reticulation and hence on the rooting. The form used matches the cited observation; the project proves the additional attribution and graph contraction steps. The cited paper omits the proof of that observation. The user explicitly authorized this conditional boundary.

No cited mathematical theorem is newly proved in `External/`. Citations to biological inference models, ASTRAL, other estimators and empirical datasets provide context or support unformalized pipeline claims. Their conclusions are not silently imported as premises of the optimization theorem.

### Standard facts

| Fact | Formal source |
| --- | --- |
| Unique paths in an acyclic connected switching | Mathlib simple-graph path/cycle theory, with local directed switching lemmas |
| Wire contraction and labelled-leaf cut invariance | `GraphSubdivisionColors`, `GraphSubdivisionCuts`, `GraphSubdivisionInvariance` |
| Finite weighted disjoint-union additivity | `Score` and Mathlib finite sums |
| Strong induction and finite maximum | Mathlib natural-number strong induction and `Finset.sup` |
| Probability squeeze for corrected recovery | Mathlib measure monotonicity, probability bound and ordered-limit squeeze |

## 3. Source findings

The E-numbers match the code's counterexample annotations. E1 and E2 are notation/domain gaps resolved by contextual readings, not claims that the intended optimizer theorem is false.

**E1. Eq. 1, §2.2 (`E1`; Definition 4 `mthst7`): multiplicity ambiguity.** Q is called a multiset, while δ already contains the multiplicity of q. Interpreting the displayed sum as occurrence-wise multiset summation squares that multiplicity: for Q containing two copies of q, δ(q)=2 gives 4 rather than 2. [`Counterexamples.squared_multiplicity_counterexample`](Camus/Counterexamples.lean#L104) checks this. Section 2.3 explicitly permits representing Q as a weighted set and uses its number of distinct topologies for the input size. The formalization follows that reading: [`Camus.equation1`](Camus/Score.lean#L22) sums over `Q.toFinset`, retaining `Q.count q` as the weight. This preserves the intended objective and main theorem.

**E2. Pairs(v), §2.2 (`sec7`, paragraph immediately before `E3`): admissible-domain precision.** The literal nonroot LCA condition also admits equal endpoints and recipient ancestors of donors. For example, take nonroot v, a strict descendant u, and w=v. The ordered pair (u,v) has LCA v, but adding an arc above u toward the new vertex above v creates a directed cycle. Equal endpoints also do not supply two distinct endpoint subdivisions as described. The paragraph initially describes pairs assigned to an edge that would be added to a valid network. [`EdgeAbove.Admissible`](Challenge.lean#L149) makes that contextual restriction explicit: both endpoints are nonroot nodes and the recipient is not a prefix of the donor. It retains permitted ghost lineages, where the donor is an ancestor of the recipient. The main theorem optimizes precisely the valid directed-network choices.

**E3. §2.4 (`sec9`): exact-budget optimum need not be nondecreasing.** The opening paragraph claims the score never decreases as the number of reticulations increases, and the following specification requests one network at each exact count. The feasible families for consecutive exact counts are not nested. A four-leaf example with T=(A,(B,(D,C))) and input quartet AC\|BD has a valid two-reticulation extension scoring one. Every valid four-leaf block network with exactly three reticulations is saturated with triangle galls and displays only its support-tree quartets, so scores zero. `exact_budget_nonmonotone` includes a universal upper bound at count three, not just a comparison of two individual witnesses.

The universal saturation theorem is Lean-checked for the concrete [`GalledNetwork`](Camus/Phylogeny.lean#L22) block grammar. Its equivalence to the separate arbitrary directed graph representation has not been formalized. The familiar block decomposition gives the mathematical graph interpretation, but that bridge is a formalization limitation. The approved replacement [`atMostScore_mono`](Camus/Score.lean#L131) follows nested feasible families. It does not validate the printed exact-count specification, stopping rule or restricted DP recurrence.

**E4. §3.2 (`sec12`, final paragraph): displayed-repertoire identifiability does not imply unique maximum support.** The claim that the true network uniquely satisfies all its displayed quartets fails because a competitor can display every observed quartet plus others. Take T=(O,((B,A),(D,C))) as the true network and all five quartets induced by T as input. T scores five. Add one reticulation above A toward C; the resulting network has a five-vertex cycle, keeps the outgroup outside it, and still displays T. It also scores five. Both are global maxima since there are only five input observations; their reticulation counts differ. `data_is_exact`, `uniqueness_counterexample` and `witnesses_globally_optimal` verify these facts in the concrete block representation.

`graph_uniqueness_counterexample` also certifies these witnesses as actual directed `AnchoredExtension` graphs with reticulation counts zero and one, attaining all observed support. It needs no Observation 2. This example is not excluded by a minimum-cycle or outgroup convention. Exact equality of quartet repertoires identifying a network does not prevent a strict superset repertoire from tying a positive support objective. The approved recovery theorem therefore assumes [`IdentifiableUnderInclusion`](Camus/Consistency.lean#L19) within an explicit feasible family, uses [`FewestReticulations`](Camus/Score.lean#L94) to select among support maxima, and states empirical-support convergence as a separate premise. None of these new recovery conditions is asserted to follow from the published biological model.

The E4 directed graph certificate is separate from any general block-grammar equivalence theorem; the latter remains unnecessary for this explicit witness.

## 4. Missing hypotheses

| Location | Condition required | Failure without it | Formal treatment |
| --- | --- | --- | --- |
| Pairs(v), §2.2 | The added edge must form a valid DAG with distinct nonroot endpoints | The ancestor-recipient example in E2 | [`EdgeAbove.Admissible`](Challenge.lean#L149); a domain reading of the preceding sentence |
| Automatic recovery, §3.2 | Inclusion-identifiability and a way to resolve score ties | Five-leaf tree and added five-cycle in E4 | Explicit hypotheses of [`correctedConsistency`](Camus/Consistency.lean#L32) and [`correctedStatisticalConsistency`](Camus/StatisticalConsistency.lean#L22) |
| Statistical recovery conclusion | Empirical observations eventually cover exactly the true repertoire with probability tending to one | Deterministic optimization alone does not establish a biological sampling limit | Explicit `support_convergence` premise |

The nonbaseline hypothesis of Lemma 1 is not missing from the paper: §2.1 explicitly defines satisfaction relative to T. Root preservation is a representation reading documented below. Directed acyclicity in subdivision invariance is part of the source network definition, not a new paper hypothesis.

## 5. Redundant hypotheses

No published hypothesis has been certified redundant. Some intermediate graph or geometric lemmas do not require leaf-label uniqueness or the cited quartet characterization; their narrower dependency lists do not justify deleting those conditions from the paper's main network theorem.

## 6. Precise readings and representations

- A quartet is an unordered two-pair split on four distinct increasing taxon labels. Child order in a tree only assigns addresses; it has no biological significance.
- [`PhyloTree`](Challenge.lean#L57) is a finite full binary rooted tree. Vertices have Boolean-list addresses. A graph network has a finite set of natural-number vertices and directed arcs, labelled leaves, a root, the source degree patterns, reachability, DAG law and disjoint simple undirected cycles.
- A graph is “built upon T” when T has a root-preserving support subdivision forming a switching. [`theorem1`](Camus/MainTheorem.lean#L42) quantifies over every finite directed graph satisfying that explicit `AnchoredExtension` definition. The definition excludes moving or suppressing the support root; bare suppressed displayed-tree membership is weaker. This is the reading of the paper's edge-above construction, where no edge can start above the root.
- A feasible edge family has disjoint original cycle footprints. Actual graph realization and the converse canonical isomorphism are proved. Shared original wires may contain endpoints from two different cycles; their forced outer-then-ghost order is proved rather than excluded.
- DP subproblems allow edges whose targets lie below v in the fixed original tree. This includes a ghost donor at the subproblem root, placed on its incoming wire in the full tree. It is not an isolated network construction that removes that incoming context.
- Definition 5 names children in N. Eq. 4/5 therefore test actual children in the subdivided single-edge graph. Their off-cycle child is then identified with an original hanging-subtree root. The source MathML uses a diagonal strike to encode ∉; stripping XML markup yields ∈ and must not be used as the mathematical condition.
- The source's satisfied quartet is novel relative to T. `DisplaysQuartet` denotes general switching display; `novel` implements source satisfaction. The DP returns novel score M[root]. Total observed score is `baselineScore + M[root]`, proved through [`score_offset`](Camus/Score.lean#L54); maximizing either gives the same networks.
- Weighted support uses distinct topologies and counts multiplicity once. Empty candidate maxima are zero because all weights are nonnegative. Bottom-up array and maximizing traces exist by finite construction.

The two approved changed conclusions are E3's at-most monotonicity and E4's conditional recovery. The main optimizer conclusion is preserved within the root-preserving source construction domain, conditional on Observation 2.

### Parameter and assumption audit

| Object or premise | Propositional content | Classification and witness |
| --- | --- | --- |
| [`Quartet`](Challenge.lean#L85), [`PhyloTree.WellLabelled`](Challenge.lean#L68) | Four strictly increasing labels and a split; distinct tree leaf labels | Defining laws. Explicit four/five-leaf inputs are checked in `Counterexamples` |
| `RootedBinaryLevelOne` | Finite edge endpoints, root membership and reachability, DAG, root/nonroot degree laws, bijective labelled leaves, vertex-disjoint simple cycles | Defining network laws. [`Realization.levelOne`](Camus/GraphRealizationConstruction.lean#L39) constructs them from separated cycle families |
| [`SupportSubdivision`](Challenge.lean#L285), `AnchoredExtension` | Injective original vertices, root/leaf/taxon preservation, directed wires with unique disjoint interiors, coverage, and one incoming arc per switching vertex | Defining support laws, with no attribution/decomposition/optimization field. [`Realization.support`](Camus/GraphRealizationConstruction.lean#L14) gives witnesses; completeness is proved from these laws |
| [`GraphSubdivision`](Challenge.lean#L331), `Iso` | Vertex/wire or vertex-equivalence laws preserving root, leaves, taxa and edges | Representation laws, without display assumptions. Baseline, singleton and alternative-tree subdivisions are constructed |
| Scalar `Array`, `Trace` | Literal recurrence, leaf cases and maximizing backtracking choices | Defining algorithm-output laws. `exists_array_trace` proves existence; feasibility/optimality are separate proved conclusions |
| Budget `Array` | Maximum-pruned exact-budget recurrence, with empty rows for infeasibility | Defining array law. [`BudgetDP.exists_array`](Camus/BudgetDPConstruction.lean#L78) supplies it; exact feasibility/optimality are proved |
| Named Observation 2 | Switching quartet display iff the source bridge/cycle cut alternatives | Sole assumed cited mathematical result of the optimizer; deliberately no proof or claimed witness |
| Corrected recovery premises | Exact truth support, feasible truth/selection, inclusion-identifiability, score optimality and minimum-reticulation tie-breaking | Explicit user-approved conditions of the corrected statement, not hidden in a data structure or asserted from a biological model |
| Statistical support convergence | Probability of the exact empirical-support event tends to one | Explicit condition of the approved corrected statistical theorem; model implication remains outside scope |
| `DeltaOracle` | Its Boolean output agrees with single-edge novel quartet membership | Defining access-model law. `semanticOracle` constructs a witness; no execution-time claim follows from that witness |

Finite candidate families, multisets, decidable equality instances and numerical budgets are data. No parameter structure assumes the theorem it is used to prove. The global Observation 2 proposition has no constructed proof because it is the declared conditional boundary.

## 7. Departures from the printed proofs

| Result | Printed argument | Formal argument | Why the departure is necessary | Finding |
| --- | --- | --- | --- | --- |
| Lemma 1, suppression bridge (representation only) | T+e is formed informally by deleting other non-tree edges and suppressing unary vertices; attribution then follows Observation 2 | Prove equivalence with the canonical endpoint-pair graph. Canonical ghost-wire ownership additionally reuses Lemma 2's target uniqueness | The source graph operation is not a primitive of the chosen finite wire encoding; an explicit construction bridge is necessary. This does not replace the Observation 2 attribution argument | Representation reading; no E-item |
| Reticulation-budget monotonicity | Increasing the exact count cannot reduce optimum | Inclusion of at-most-budget feasible families | The exact-count assertion is false | E3 |
| §3.2 recovery and statistical consequence | Truth automatically uniquely satisfies all observed truth quartets | Explicit inclusion-identifiability plus minimum-reticulation tie-breaking; deterministic recovery on the empirical-support event and a probability squeeze | The asserted automatic uniqueness is false; no biological convergence theorem is supplied | E4 |

The main theorem follows the source route. The supplemental representation bridge for Lemma 1 is recorded above and in [`docs/route_differences.tsv`](docs/route_differences.tsv); its additional Lemma 2 use is the same level-1 disjoint-cycle invariant, not a new quartet-attribution premise. Remaining-depth strong induction is a finite termination measure for the same proper-subproblem induction. The proved equations-to-hanging-forest bridge, directed realization, canonical isomorphism, baseline display and single-edge suppression make the informal graph operations precise. They add no assumed optimization decomposition. Observation 2 remains named and unproved by user authorization.

## 8. Dependencies and route check

The dependency summary below is checked against the generated `.lake/route_deps.tsv` from [`scripts/Audit.lean`](scripts/Audit.lean). The audit found only Lean's standard axioms; the cited Observation 2 appears as an explicit statement hypothesis. The final audit covers every library module using its own `import all` line, including the directed counterexamples and cost model.

| Source result | Formal declaration | Route |
| --- | --- | --- |
| Eq. 1 | [`Camus.equation1`](Camus/Score.lean#L22), [`DynamicProgramming.edgeWeight_score`](Camus/MainTheorem.lean#L12) | Weighted distinct support and multiplicities |
| Eq. 4/5 | [`DynamicProgramming.equation4`](Camus/PackingTheorem.lean#L13), [`DynamicProgramming.equation5`](Camus/PackingTheorem.lean#L22), `hanging_score` | Actual subdivided child test and proved frontier identities |
| Lemma 2 (`mthst4`) | [`EdgeAbove.target_unique`](Camus/TreeGeometry.lean#L122), [`lemma2`](Camus/QuartetAttribution.lean#L65) | Two cycles at one target share a vertex; graph extraction bridge |
| Lemma 1 (`mthst2`) | [`lemma1`](Camus/QuartetAttribution.lean#L50), `novel_disjoint_union` | Named Observation 2, bridge baseline, selected-cycle reduction and uniqueness from vertex-disjoint cycles |
| Theorem 1 (`mthst9`) | [`theorem1`](Camus/MainTheorem.lean#L42) | Lemma 1 score additivity; Lemma 2 in packing geometry; literal Eq. 4/5; strong induction; realization and arbitrary-graph completeness |
| Existence of DP output | [`DynamicProgramming.exists_array_trace`](Camus/PackingTheorem.lean#L298) | Finite bottom-up array stabilization and maximizing branch construction |
| n−1 reticulation bound | `anchored_reticulation_bound` | Target injection, internal-node count, canonical graph isomorphism |
| Restricted exact-budget DP | [`BudgetDP.exact_graph_optimal`](Camus/BudgetDP.lean#L55), [`BudgetDP.exists_array`](Camus/BudgetDPConstruction.lean#L78) | Maximum-pruned hanging-forest knapsack, exact-cardinality fork/gall partitions, canonical graph/count bridge |
| Abstract operation/storage bounds | [`Complexity.scalarOperations_bound`](Camus/Complexity.lean#L121), [`Complexity.budgetOperations_bound`](Camus/Complexity.lean#L141), [`Complexity.scalarSpace_bound`](Camus/Complexity.lean#L221) | Target fibers, candidate/hanging counts, observed-taxon restriction and unit-cost model |
| Corrected §3.2 recovery | [`correctedConsistency`](Camus/Consistency.lean#L32), [`correctedStatisticalConsistency`](Camus/StatisticalConsistency.lean#L22) | E4's explicit hypotheses; no unformalized biological implication |

The source proof's named dependencies are actually used, not merely restated beside a separate optimizer proof. The route check passes with 11 individually reviewed additional uses in [`docs/route_differences.tsv`](docs/route_differences.tsv): ten make the source definitions/recurrences explicit, and one is the supplementary Lemma 1 representation bridge above. Equation (2) is named in the source proof as plain JATS text and is included in the reviewed source route. Standard-axiom auditing passed. [`Challenge.lean`](Challenge.lean) holds synchronized shared definitions and unchanged target statements; [`Solution.lean`](Solution.lean) proves the same four statements; Comparator accepts them under Lean and NanoDa.

## 9. Not formalized

- Runtime correspondence between the abstract unit-operation tabulation and a costed executable implementation. `Complexity` proves explicit bounds for declared scalar/budget operation counts and compressed integer storage, matching the source asymptotic forms under unit-cost access: scalar operations ≤32n²(‖Qdistinct‖+n), budget operations ≤100n²(‖Qdistinct‖+m³n) for m≥1, and stored unit integers ≤32n⁴. `OracleWeights` identifies the counted weight scan with the semantic Eq. 1 weights and certifies the exact number of oracle queries. It does not prove Lean evaluation runtime or construct constant-time LCA/display preprocessing. The O(n⁴) input storage statement explicitly assumes the observed quartets use tree taxa.
- The §2.4 early stopping criterion. The exact-count knapsack DP, finite array existence and transfer to every arbitrary directed graph extension at the selected exact count are proved in `BudgetDP`. No monotonicity or stopping guarantee is inferred from that theorem.
- The generative genetic models, ASTRAL convergence and biological hypotheses implying empirical-support convergence or inclusion-identifiability.
- Experiments, software implementation equivalence, statistical tests, benchmark accuracy and practical scaling claims.
- A general directed graph equivalence theorem for the separate [`GalledNetwork`](Camus/Phylogeny.lean#L22) block grammar used by counterexamples.
- A proof of the cited Observation 2. This is why the main theorem is conditional.

## 10. Literature context

The search on 2026-10-08 screened the paper's cited network-reconstruction literature, primary publisher/author pages, exact-title searches for CAMUS corrections, and searches for Lean or other formalizations. The comparisons below concern the nearest level-1 quartet/quarnet reconstruction questions; they are not an exhaustive bibliography. No erratum or independently published formalization was located in these searches. That is a search result, not proof of absence.

### Before CAMUS

Warnow, Tabatabaee and Evans's 2025 Journal of Computational Biology article develops reconstruction from unrooted SNP information and supplies Observation 2 (Section 2 above). Its reconstruction conditions are not an automatic positive-support uniqueness theorem for arbitrary candidate supersets. [Published article](https://doi.org/10.1089/cmb.2024.0710).

Allman, Baños and Rhodes's NANUQ (Algorithms for Molecular Biology, 2019) estimates level-1 networks under the coalescent using quartet concordance information. Its sampling/model task differs from maximizing a finite multiset's supported quartets above a fixed rooted constraint tree. [Published article](https://doi.org/10.1186/s13015-019-0159-2).

Holtgrefe and coauthors' Squirrel (Molecular Biology and Evolution, 2025) reconstructs semi-directed level-1 networks using four-leaf networks, or quarnets, with combinatorial consistency for triangle-free networks. Quarnets retain information beyond a set of displayed quartet trees, so this does not remove E4's superset-score issue. [Published article](https://doi.org/10.1093/molbev/msaf067), [author's abstract](https://www.nielsholtgrefe.nl/publications/).

Frohn and coauthors' 2025 Journal of Computer and System Sciences article proves an O(n²)-time reconstruction algorithm using O(n log n) quarnets in its oracle model. Its reconstruction objective and four-taxon data differ from CAMUS's fixed-support-tree score maximization. [Published article](https://doi.org/10.1016/j.jcss.2025.103655), [author's abstract](https://www.nielsholtgrefe.nl/publications/).

Dinh and Baños (Molecular Biology and Evolution, March 2025) show that ASTRAL can select a tree not displayed by a hybridization network even in nonanomalous coalescent settings. This limits the generality of assuming that a tree-estimation stage supplies a support tree. It does not directly refute CAMUS's optimization theorem, which takes that support condition as input. [Published article](https://academic.oup.com/mbe/article/42/3/msaf049/8063332).

### Concurrent work

The screened literature contains overlapping reconstruction methods around CAMUS's February 2026 first public version, but no independently established theorem identical to its finite constrained support-maximization result was identified. Date proximity alone does not establish independence or priority. The 2025 quarnet work above addresses a related reconstruction question with richer input and a different objective.

### Later work

Dai and Molloy's NetCS, published at WABI on 2026-08-27, reconstructs level-1 blobs under the network multispecies coalescent once a tree of blobs is known. It combines majority voting and merge sorting and proves statistical consistency under its model conditions. Its abstract emphasizes that upstream tree-of-blobs errors remain a major obstacle. This advances a related pipeline stage, rather than proving uniqueness for CAMUS's positive support objective or correcting E3/E4. [Published proceedings article and full paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.1).

The literature comparisons and further-work discussion were independently checked by the completeness agent against the linked primary papers and their main statements.

### Formalizations

No earlier formalization of CAMUS or the cited Observation 2 was found in the searches described above. This project did not consult an external CAMUS Lean formalization. Mathlib supplies general graph, finite-sum and measure theory.

## 11. Further work

### Mathematical directions

A useful corrected recovery statement should prove an inclusion-identifiability property for a concrete network class and an explicit model, or specify an objective that penalizes unsupported additional structure. Exact-repertoire identifiability alone is insufficient, as E4 shows. The current generic recovery theorem isolates precisely the condition that would need such a proof.

A second goal is to characterize exact-budget score variation and justify a selection/stopping rule without monotonicity. E3 demonstrates that the last feasible exact budget can be worse. The article's empirical reticulation choice does not supply a theorem guaranteeing its stopping rule.

No simpler published-proof replacement is claimed by this project. The source's main decomposition already gives the formal argument. Connected-component coloring supplies a concise conceptual proof of wire cut invariance, but it formalizes an implicit graph operation rather than replacing a paper proof.

### Formalization directions

Prove Observation 2 from switching display, develop a general block/directed graph representation bridge, and relate the abstract §2.3/2.4 operation bounds to an explicit costed implementation. Biological model formalization must establish empirical-support convergence and the corrected identifiability premise, not assume the source's false optimizer uniqueness step. The directed subdivision, switching and cycle APIs developed here are candidates for reuse or a Mathlib contribution.
