# Published-source inventory

The target is DOI 10.1093/bioinformatics/btag245. Publisher TeX was unavailable; the archived full-text JATS XML is the exact statement source. XML identifiers replace TeX labels. Source hashes and provenance are in `sources/manifest.json`.

- `mthst1`: Definition 1. Each rooted binary level-1 phylogenetic network N induces a set T of rooted binary trees formed by deleting one incoming edge into each reticulation node (i.e. nodes that have indegree 2) in each of the possible ways. Thus, N can be constructed by taking one of the trees t ∈ T and adding reticulations (edges) to t. For this reason, N is said to be tree-based , and we may also say that N is built on t or that N is an extension of t . Given tree t ∈ T , we consider t in its unrooted form and define the set Q ( t ) of (unrooted) quartet trees induced in t. We note that quartet trees are also referred to more simply as quartets . A resolved quartet tree on four leaves u , v , x , y has an internal edge that separates the four leaves into two sets, such as u , v separated from x , y , and is denoted by uv | xy . We define Q ( N r ) = ∪ t ∈ T Q ( t ) ; the use of the subscript r indicates its reliance on the rooting of N.
- `mthst2`: Lemma 1. For any rooted binary tree T and extension of T into level-1 phylogenetic network N, if quartet tree q is satisfied by N, then there is a unique non-tree edge e such that q is satisfied by T + e . Thus, the set of quartets that are satisfied by N is the disjoint union of quartets satisfied by T + e , as we let e vary among the non-tree edges of N.
- `mthst3`: Definition 2. Procedure ASSIGN Given N, T, and quartet q satisfied by N and not by T, find ( u ′ , w ′ ) , the unique non-tree (directed) edge that satisfies q. Find u and w in T directly below u ′ and w ′ , respectively, and let v = l c a T ( u , w ) , where lca denotes the least common ancestor. Assign q and the non-tree edge ( u ′ , w ′ ) satisfying q to the triplet ( u , w , v ) . Denote v as the “target” of q and its satisfying non-tree edge. Figure 1 illustrates Procedure ASSIGN, with the red non-tree edge and quartet D E | A G both assigned to the triplet ( u , w , v ) .
- `mthst4`: Lemma 2. Let N be a level-1 phylogenetic network N extending T, and let v be a node in T. Then there is at most one non-tree edge in N for which v is the target.
- `mthst5`: Proof. If there were two non-tree edges in N with v the target, then N would contain two cycles, and it is easy to see that each would contain v as a node, and hence the two cycles would not be disjoint. This violates N being level-1. ▪
- `mthst6`: Definition 3. Let T be a rooted tree and u and w be nodes in N. The phrase add edge above ( u , w ) means we create two new vertices in T—one bisecting the edge above u and one bisecting the edge above w—then creating an edge from the vertex above u to the vertex above w (see Fig. 1 ). This creates a network N that has a cycle, denoted by γ ( u , w ) , for which the vertex created above w will be the bottom node of the cycle (i.e. the only node in the cycle with indegree 2).
- `mthst7`: Definition 4. Let T be a rooted tree, let q be a quartet tree, and let Q be a multiset of quartet trees. We define δ T ( q , ( u , w ) ) to be the number of times q appears in Q if q is satisfied by an edge e added above ( u , w ) ; otherwise, the value is 0.
- `mthst8`: Definition 5. Let N be a rooted level-1 phylogenetic network and v a node in N. Then l ( v ) refers to the left child of v and r ( v ) refers to the right child of v.
- `E1`: (1) s e ( u , w ) = ∑ q ∈ Q δ T ( q , ( u , w ) ) ,
- `E2`: (2) M [ v ] = max { M [ l ( v ) ] + M [ r ( v ) ] , s ( v ) ,
- `E3`: (3) s ( v ) = max ( u , w ) ∈ Pairs ( v ) ( s e ( u , w ) + s d p ( v , u , w ) ) ,
- `E4`: (4) s d p ( v , u , w ) = M [ w ] + M [ u ] + ∑ x ∈ γ ( u , w ) ∩ V ( T ) ∖ { v } { M [ l ( x ) ] if l ( x ) ∉ γ ( u , w ) M [ r ( x ) ] otherwise .
- `E5`: (5) s d p ( v , u , w ) = M [ w ] + ∑ x ∈ γ ( u , w ) ∩ V ( T ) { M [ l ( x ) ] if l ( x ) ∉ γ ( u , w ) M [ r ( x ) ] otherwise .
- `mthst9`: Theorem 1. The algorithm gives an assignment of non-tree edges to add to the tree T that maximizes the number of quartets in Q that are satisfied, under the constraint that we create a level-1 phylogenetic network.
- `mthst10`: Proof. By design, the solution that CAMUS outputs is a level-1 phylogenetic network N that extends T . Specifically, consider the target nodes for a pair of added edges defined by the backtracking through the DP matrix. If their target nodes are not in relation (neither above the other), then the cycles they create are vertex-disjoint. If some target node x is above another target node y , then this case would be handled by Equations (4) and (5) , which ensure that the created cycles do not share vertices. It is also easy to see that M[r] is the number of quartet trees in Q that are satisfied by N and not by T , where r is the root of T .

The source uses “satisfied” to mean displayed by the network but absent from its constraint tree (§2.1, paragraph immediately following Definition 1). Lemma 1 therefore already concerns novel quartets. Equations (4) and (5) have a struck-through membership symbol in MathML, meaning ∉; plain XML text extraction loses that mark.

## Additional obligations

- §2.3 preprocessing, recurrence operation counts and storage bound, with integer operations counted at unit cost.
- §2.4 exact-budget recurrence and reticulation bound; the printed exact-budget monotonicity assertion is refuted and at-most-budget monotonicity is proved, as authorized.
- Algorithm 1: frequency ordering and strict runner-up threshold; quartet multisets preserve multiplicities.
- §3.2 uniqueness assertion is refuted; recovery is proved under explicit inclusion identifiability and fewest-reticulations tie-breaking, as authorized. Biological-model support convergence remains an explicit premise.

## Representation bridges

- Binary rooted trees use boolean addresses. Quartets use four sorted labels and a split in Fin 3.
- Directed level-1 networks are finite acyclic labelled graphs with the stated degree laws and vertex-disjoint undirected cycles.
- A support switching is an explicit root-preserving subdivision of the constraint tree. Canonical construction, extraction and completeness are internal proof obligations.
- Equations (4) and (5) use the children in the subdivided single-edge network. Their equality with the frontier sum is an internal proof obligation.
- Observation 2 of Warnow–Tabatabaee–Evans (2025) is the sole approved literature hypothesis. It does not assume quartet attribution or graph decomposition.

## Independent review

The source-review agent checked the numbered statements and representation choices against the published JATS text and supplement. It confirmed the two authorized corrections, the requirement to use actual network children, and the need for the full directed-graph bridge.

## Helper correction

Subdivision invariance needs an acyclic source. Without it, antiparallel arcs become a single undirected bridge before subdivision and a cycle afterwards. The helper now requires the source rooted-network laws; this changes no paper statement. A Lean counterexample certificate remains to be added.
