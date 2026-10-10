module

public import Camus.Pipelines.NMSC.Recovery
public import Camus.Pipelines.NMSC.Swap
public import Camus.Network.TreeBased.Root
public import Camus.Network.TreeBased.Display

/-!
# Sections 3.2 and 3.3 under the NMSC: recovery through every tree of the network

Section 3.3 runs ASTRAL on the gene trees and gives its tree `T*` to CAMUS as the constraint tree:
"If we assume that the true phylogenetic network N is level-1 and that T* is one of the underlying
trees, then gene trees can differ from T* due to both ILS and HGT." The underlying trees are the
trees 𝒯 of Section 2.1, "formed by deleting one incoming edge into each reticulation node ... in
each of the possible ways", and Section 3.2 argues that CAMUS then returns `N`: "any tree t∈Q(Nr)
can be used as the basis for N (i.e. N can be obtained by adding reticulate edges to t)", and "When
Q is a multi-set version of Q(Nr), then CAMUS will add the correct reticulations and return N".
`NMSC.nmsc_recovery_graph` proves this for one tree of `N`, its base tree. This file proves it for
every tree `T` of the graph `Realization.graph (baseTree N) (pairs N)` of `N` in the sense of
Definition 1 (`RootedNetwork.BuiltOn`), when the root of the graph has an outgroup leaf as a child,
as in the pipeline of Section 3.3 ("the pipeline takes as input a set G of estimated gene trees and
an outgroup species"): the outgroup makes the graph built with the root kept on each of its trees
(`RootedNetwork.BuiltOn.anchored_of_outgroup`), the class of networks over which CAMUS optimizes.
Without an outgroup, a tree of a network need not keep its root (the report's E8). A network of the
NMSC whose root has a leaf `z` as a child gives such a graph (`NMSC.graph_outgroup`). The trees of
the graph induce exactly the quartet trees of Q(N_r) together
(`NMSC.displaysQuartet_iff_exists_builtOn`).

The displayed trees of `N` in the model (`Brooqs.Net.displayed`) are reached through the exchange
of the two sides of cycles (`Brooqs.Net.SideSwap`), which describes the same network: the gene
trees, Q(N_r) and the threshold are unchanged (`Camus/Pipelines/NMSC/Swap.lean`), and CAMUS, given
the base tree of the exchanged network `N'`, returns the graph of `N'`
(`NMSC.nmsc_recovery_sideSwap`). The base trees of the exchanges are exactly the displayed trees of
`N` that delete, at each cycle, the hybrid edge of a side with a node (`NMSC.nodeDisplayed`,
`NMSC.mem_nodeDisplayed_iff`). The other displayed trees are the base trees of no exchange: they
delete, at some cycle, the hybrid edge of a side without a node, the edge from the top node of the
cycle to its hybrid node, and hang the hybrid component below the last node of the other side. (At
a cycle whose other side has a single node, the two choices give the same tree.)

## Main results

* `NMSC.nmsc_recovery_builtOn`, `NMSC.nmsc_recovery_outgroup`: Sections 3.2 to 3.4 under the NMSC,
  through every tree of the graph of `N`, with an outgroup.
* `NMSC.graph_outgroup`, `NMSC.graph_outgroup_right`: a leaf child of the root of `N` is an
  outgroup of its graph.
* `NMSC.displaysQuartet_iff_exists_builtOn`: Q(N_r) is the union of the sets Q(T) over the trees
  `T` of the graph of `N`.
* `NMSC.nodeDisplayed`, `NMSC.nodeDisplayed_subset`, `NMSC.mem_nodeDisplayed_iff`,
  `NMSC.exists_baseTree_of_mem_nodeDisplayed`: the displayed trees that delete the hybrid edge of a
  side with a node at each cycle are the base trees of the exchanges.
* `NMSC.displaysTree_baseTree_of_sideSwap`, `NMSC.graph_sideSwap`, `NMSC.nmsc_recovery_sideSwap`:
  recovery through the base tree of `N` with the sides of some cycles exchanged, whose graph
  displays Q(N_r) and has as many reticulations as the graph of `N`.

## Proof (the paper's)

Section 3.2's argument, as in `NMSC.nmsc_recovery`, through a tree `T` of the graph `Nr` of `N`:
1. `T` can be used as the basis for `N`: with the outgroup, `Nr` is built on `T` with the root kept
   (`RootedNetwork.BuiltOn.anchored_of_outgroup`);
2. the output `Q` of Quartet Filtering is "a multi-set version of Q(Nr)"
   (`NMSC.nmsc_filterQuartets_support`), and `Nr` displays Q(N_r)
   (`NMSC.graph_displaysQuartet_iff`);
3. "CAMUS will add the correct reticulations and return N": the corrected recovery theorem
   (`recovery`), with the identifiability of `Nr` and the tie-break by the number of reticulations
   (the report's E7).
-/

@[expose] public noncomputable section

namespace Camus

namespace NMSC

open Finset Filter Topology MeasureTheory ProbabilityTheory Coalescent Algorithm1

variable {L : Finset ℕ}

/-! ### An outgroup of the graph of `N` -/

/-- The pairs of the graph of a network whose root has the leaf `z` as its left child are in the
right child of the root. -/
private theorem tr_pairs_tree_leaf {ℓ₁ ℓ₂ : ℝ} {z : L} {N' : Brooqs.Net L}
    {e : Address × Address} (he : e ∈ pairs (.tree ℓ₁ (.leaf z) ℓ₂ N')) :
    e.1 ≠ [false] ∧ e.2 ≠ [false] := by
  simp only [pairs, mem_union, mem_liftPairs, notMem_empty, false_and, exists_false,
    false_or] at he
  obtain ⟨f, -, rfl⟩ := he
  exact ⟨by simp, by simp⟩

/-- Section 3.3, "the pipeline takes as input a set G of estimated gene trees and an outgroup
species": if the root of `N` has the leaf `z` as a child, `N = tree ℓ₁ (leaf z) ℓ₂ N'`, then in
the graph `Realization.graph (baseTree N) (pairs N)` of `N` the leaf of `z` is a child of the root:
no added edge subdivides the edge above it. These are the hypotheses of
`RootedNetwork.BuiltOn.anchored_of_outgroup`. -/
theorem graph_outgroup {N N' : Brooqs.Net L} {ℓ₁ ℓ₂ : ℝ} {z : L} (hN : N.WellFormed)
    (hz : N = .tree ℓ₁ (.leaf z) ℓ₂ N') :
    (z : ℕ) ∈ (Realization.graph (baseTree N) (pairs N)).taxa ∧
      ((Realization.graph (baseTree N) (pairs N)).root,
          (Realization.graph (baseTree N) (pairs N)).leaf z) ∈
        (Realization.graph (baseTree N) (pairs N)).edges := by
  subst hz
  have hroot : (baseTree (.tree ℓ₁ (.leaf z) ℓ₂ N')).nodeAt [false] = some (.leaf z) :=
    nodeAt_fork_false _ _
  refine ⟨?_, ?_⟩
  · change (z : ℕ) ∈ (PhyloTree.fork (.leaf z) (baseTree N')).taxa
    rw [taxa_fork]
    exact mem_union_left _ (by simp [PhyloTree.taxa, PhyloTree.labels])
  -- the leaf of `z` is at the address `[false]`, and the wire above it has no added vertex
  have hleaf : Realization.leafAddress (baseTree (.tree ℓ₁ (.leaf z) ℓ₂ N')) z = [false] :=
    Realization.leafAddress_eq (wellLabelled_baseTree hN) hroot
  have hout : Realization.outerEndpoints (baseTree (.tree ℓ₁ (.leaf z) ℓ₂ N'))
      (pairs (.tree ℓ₁ (.leaf z) ℓ₂ N')) [false] = [] := by
    refine List.flatMap_eq_nil_iff.2 fun e he => ?_
    obtain ⟨h1, h2⟩ := tr_pairs_tree_leaf (Finset.mem_toList.1 he)
    simp [h1, h2]
  have hghost : Realization.ghostEndpoints (baseTree (.tree ℓ₁ (.leaf z) ℓ₂ N'))
      (pairs (.tree ℓ₁ (.leaf z) ℓ₂ N')) [false] = [] := by
    refine List.flatMap_eq_nil_iff.2 fun e he => ?_
    obtain ⟨h1, -⟩ := tr_pairs_tree_leaf (Finset.mem_toList.1 he)
    simp [h1]
  change (Address.code [], Address.code (Realization.leafAddress
      (baseTree (.tree ℓ₁ (.leaf z) ℓ₂ N')) z)) ∈
    Realization.supportEdges (baseTree (.tree ℓ₁ (.leaf z) ℓ₂ N'))
      (pairs (.tree ℓ₁ (.leaf z) ℓ₂ N')) ∪ _
  rw [hleaf]
  refine mem_union_left _ (mem_biUnion.2 ⟨[false], ?_, ?_⟩)
  · exact mem_erase.2 ⟨by simp, (PhyloTree.mem_nodes_iff _ _).2 ⟨_, hroot⟩⟩
  · simp [Realization.wire, hout, hghost, wireEdges, parent]

/-- The pairs of the graph of a network whose root has the leaf `z` as its right child are in the
left child of the root. -/
private theorem tr_pairs_tree_leaf_right {ℓ₁ ℓ₂ : ℝ} {z : L} {N' : Brooqs.Net L}
    {e : Address × Address} (he : e ∈ pairs (.tree ℓ₁ N' ℓ₂ (.leaf z))) :
    e.1 ≠ [true] ∧ e.2 ≠ [true] := by
  simp only [pairs, mem_union, mem_liftPairs, notMem_empty, false_and, exists_false,
    or_false] at he
  obtain ⟨f, -, rfl⟩ := he
  exact ⟨by simp, by simp⟩

/-- `NMSC.graph_outgroup` with the outgroup as the right child of the root:
`N = tree ℓ₁ N' ℓ₂ (leaf z)`. -/
theorem graph_outgroup_right {N N' : Brooqs.Net L} {ℓ₁ ℓ₂ : ℝ} {z : L} (hN : N.WellFormed)
    (hz : N = .tree ℓ₁ N' ℓ₂ (.leaf z)) :
    (z : ℕ) ∈ (Realization.graph (baseTree N) (pairs N)).taxa ∧
      ((Realization.graph (baseTree N) (pairs N)).root,
          (Realization.graph (baseTree N) (pairs N)).leaf z) ∈
        (Realization.graph (baseTree N) (pairs N)).edges := by
  subst hz
  have hroot : (baseTree (.tree ℓ₁ N' ℓ₂ (.leaf z))).nodeAt [true] = some (.leaf z) :=
    nodeAt_fork_true _ _
  refine ⟨?_, ?_⟩
  · change (z : ℕ) ∈ (PhyloTree.fork (baseTree N') (.leaf z)).taxa
    rw [taxa_fork]
    exact mem_union_right _ (by simp [PhyloTree.taxa, PhyloTree.labels])
  -- the leaf of `z` is at the address `[true]`, and the wire above it has no added vertex
  have hleaf : Realization.leafAddress (baseTree (.tree ℓ₁ N' ℓ₂ (.leaf z))) z = [true] :=
    Realization.leafAddress_eq (wellLabelled_baseTree hN) hroot
  have hout : Realization.outerEndpoints (baseTree (.tree ℓ₁ N' ℓ₂ (.leaf z)))
      (pairs (.tree ℓ₁ N' ℓ₂ (.leaf z))) [true] = [] := by
    refine List.flatMap_eq_nil_iff.2 fun e he => ?_
    obtain ⟨h1, h2⟩ := tr_pairs_tree_leaf_right (Finset.mem_toList.1 he)
    simp [h1, h2]
  have hghost : Realization.ghostEndpoints (baseTree (.tree ℓ₁ N' ℓ₂ (.leaf z)))
      (pairs (.tree ℓ₁ N' ℓ₂ (.leaf z))) [true] = [] := by
    refine List.flatMap_eq_nil_iff.2 fun e he => ?_
    obtain ⟨h1, -⟩ := tr_pairs_tree_leaf_right (Finset.mem_toList.1 he)
    simp [h1]
  change (Address.code [], Address.code (Realization.leafAddress
      (baseTree (.tree ℓ₁ N' ℓ₂ (.leaf z))) z)) ∈
    Realization.supportEdges (baseTree (.tree ℓ₁ N' ℓ₂ (.leaf z)))
      (pairs (.tree ℓ₁ N' ℓ₂ (.leaf z))) ∪ _
  rw [hleaf]
  refine mem_union_left _ (mem_biUnion.2 ⟨[true], ?_, ?_⟩)
  · exact mem_erase.2 ⟨by simp, (PhyloTree.mem_nodes_iff _ _).2 ⟨_, hroot⟩⟩
  · simp [Realization.wire, hout, hghost, wireEdges, parent]

/-! ### The trees of the graph of `N` and Q(N_r) -/

/-- **Definition 1** (`mthst1`) for the graph of `N`: Q(N_r) = ∪_{t∈𝒯} Q(t). A metric level-1
network `N` with distinct leaf labels on the taxa `L` displays the quartet tree `q` iff some tree
`T` of its graph `Realization.graph (baseTree N) (pairs N)`, in the sense of Definition 1, induces
`q`. In particular every tree of the graph induces only quartet trees of Q(N_r). -/
theorem displaysQuartet_iff_exists_builtOn {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (q : Quartet) :
    DisplaysQuartet N q ↔ ∃ T : PhyloTree,
      (Realization.graph (baseTree N) (pairs N)).BuiltOn T ∧ q.induced T = true :=
  (graph_displaysQuartet_iff hN htaxa q).symm.trans
    (RootedNetwork.displays_iff_exists_builtOn (graph_anchoredExtension hN).1 q)

/-! ### Recovery through every tree of the graph of `N` -/

section Genes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]

open DynamicProgramming in
/-- **Sections 3.2 to 3.4 under the NMSC, through every tree of `N`.** Let the gene trees be
independent, each with the law of the NMSC on a metric level-1 network `N` with distinct leaf
labels on the taxa `L`, without the anomalous configuration, and let `0 < t < t₀(N)`. Let
`Nr = Realization.graph (baseTree N) (pairs N)` be the graph of `N`, which displays the quartet
trees of `N` (`NMSC.graph_displaysQuartet_iff`), and let its root have an outgroup leaf `z` as a
child. Let `T` be any tree of `Nr` in the sense of Definition 1 (`T ∈ 𝒯`: "N can be constructed by
taking one of the trees t∈𝒯 and adding reticulations (edges) to t"), for instance the tree `T*`
that ASTRAL returns when it is "one of the underlying trees" (Section 3.3); then `Nr` is built on
`T` with the root kept (`RootedNetwork.BuiltOn.anchored_of_outgroup`). Assume, as `recovery` does,
that `Nr` is identifiable under inclusion among the networks built on `T`. Almost surely, for all
large numbers `n` of genes, every network built on `T` that has the best score for the output `Q`
of Quartet Filtering on the quartet trees of the first `n` gene trees, with the fewest
reticulations among the networks with the best score, is isomorphic to `Nr`: "CAMUS will add the
correct reticulations and return N" (Section 3.2). -/
theorem nmsc_recovery_builtOn {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (hna : NoAnomaly N) (G : ℕ → Ω → Finset (Finset L))
    (hind : iIndepFun G P) (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N) {z : ℕ} (hz : z ∈ (Realization.graph (baseTree N) (pairs N)).taxa)
    (hzr : ((Realization.graph (baseTree N) (pairs N)).root,
        (Realization.graph (baseTree N) (pairs N)).leaf z) ∈
      (Realization.graph (baseTree N) (pairs N)).edges)
    (T : PhyloTree) (hT : (Realization.graph (baseTree N) (pairs N)).BuiltOn T)
    (identifiable : ∀ R : RootedNetwork, R.AnchoredExtension T →
      (∀ q, (Realization.graph (baseTree N) (pairs N)).DisplaysQuartet q →
        R.DisplaysQuartet q) →
      R.reticulationCount ≤ (Realization.graph (baseTree N) (pairs N)).reticulationCount →
      Nonempty (R.Iso (Realization.graph (baseTree N) (pairs N)))) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ R : RootedNetwork, R.AnchoredExtension T →
      (∀ R' : RootedNetwork, R'.AnchoredExtension T →
        score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R') ≤
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R)) →
      (∀ R' : RootedNetwork, R'.AnchoredExtension T →
        (∀ R'' : RootedNetwork, R''.AnchoredExtension T →
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R'') ≤
            score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R')) →
        R.reticulationCount ≤ R'.reticulationCount) →
      Nonempty (R.Iso (Realization.graph (baseTree N) (pairs N))) :=
  -- the graph is built on `T` with the root kept, and displays the quartet trees of `N`
  nmsc_recovery hN htaxa hna G hind hid hlaw ht ht₀ T _ (hT.anchored_of_outgroup hz hzr)
    (graph_displaysQuartet_iff hN htaxa) identifiable

open DynamicProgramming in
/-- **Sections 3.2 to 3.4 under the NMSC, through every tree of `N`, with an outgroup at the root
of `N`.** `NMSC.nmsc_recovery_builtOn` for a network `N = tree ℓ₁ (leaf z) ℓ₂ N'` whose root has
the leaf `z` as a child (`NMSC.graph_outgroup`). -/
theorem nmsc_recovery_outgroup {N N' : Brooqs.Net L} {ℓ₁ ℓ₂ : ℝ} {z : L}
    (hNz : N = .tree ℓ₁ (.leaf z) ℓ₂ N') (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (hna : NoAnomaly N) (G : ℕ → Ω → Finset (Finset L))
    (hind : iIndepFun G P) (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N) (T : PhyloTree)
    (hT : (Realization.graph (baseTree N) (pairs N)).BuiltOn T)
    (identifiable : ∀ R : RootedNetwork, R.AnchoredExtension T →
      (∀ q, (Realization.graph (baseTree N) (pairs N)).DisplaysQuartet q →
        R.DisplaysQuartet q) →
      R.reticulationCount ≤ (Realization.graph (baseTree N) (pairs N)).reticulationCount →
      Nonempty (R.Iso (Realization.graph (baseTree N) (pairs N)))) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ R : RootedNetwork, R.AnchoredExtension T →
      (∀ R' : RootedNetwork, R'.AnchoredExtension T →
        score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R') ≤
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R)) →
      (∀ R' : RootedNetwork, R'.AnchoredExtension T →
        (∀ R'' : RootedNetwork, R''.AnchoredExtension T →
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R'') ≤
            score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R')) →
        R.reticulationCount ≤ R'.reticulationCount) →
      Nonempty (R.Iso (Realization.graph (baseTree N) (pairs N))) :=
  nmsc_recovery_builtOn hN htaxa hna G hind hid hlaw ht ht₀ (graph_outgroup hN hNz).1
    (graph_outgroup hN hNz).2 T hT identifiable

end Genes

/-! ### The base trees of the exchanges of the sides -/

/-- Exchanging the sides of cycles keeps the sides with a node. -/
theorem hasNode_of_sideSwap {S S' : Brooqs.Side L} (h : S.SideSwap S') :
    hasNode S' = hasNode S := by
  cases h <;> rfl

mutual
/-- The displayed trees of `N` (`Brooqs.Net.displayed`) that, at each cycle, delete the hybrid edge
of a side with a node: the hybrid component hangs from the bottom of `S₁` when `S₂` has a node,
and from the bottom of `S₂` when `S₁` has a node. At a cycle one of whose sides is a single hybrid
edge, from the top node to the hybrid node, the hybrid component hangs from the top node through
that edge. -/
def nodeDisplayed : Brooqs.Net L → List (Finset (Finset L))
  | .leaf x => [{{x}}]
  | .tree _ N₁ _ N₂ =>
      (nodeDisplayed N₁).flatMap fun K₁ => (nodeDisplayed N₂).map fun K₂ =>
        insert (N₁.taxa ∪ N₂.taxa) (K₁ ∪ K₂)
  | .cycle _ S₁ S₂ _ H =>
      (nodeDisplayed H).flatMap fun K =>
        (if hasNode S₂ then
          (sideNodeDisplayed S₁ H.taxa).flatMap fun K₁ => (sideNodeDisplayed S₂ ∅).map fun K₂ =>
            insert (S₁.taxa ∪ S₂.taxa ∪ H.taxa) (K ∪ K₁ ∪ K₂)
        else []) ++
        (if hasNode S₁ then
          (sideNodeDisplayed S₁ ∅).flatMap fun K₁ => (sideNodeDisplayed S₂ H.taxa).map fun K₂ =>
            insert (S₁.taxa ∪ S₂.taxa ∪ H.taxa) (K ∪ K₁ ∪ K₂)
        else [])

/-- The clusters along a side in the displayed trees of `NMSC.nodeDisplayed`, with the taxa `T`
below its hybrid edge. -/
def sideNodeDisplayed : Brooqs.Side L → Finset L → List (Finset (Finset L))
  | .hyb _, _ => [∅]
  | .node _ _ M S, T => (sideNodeDisplayed S T).flatMap fun K => (nodeDisplayed M).map fun K' =>
      insert (T ∪ S.taxa ∪ M.taxa) (K ∪ K')
end

mutual
/-- The trees of `NMSC.nodeDisplayed N` are displayed trees of `N`. -/
theorem nodeDisplayed_subset : ∀ {N : Brooqs.Net L} {K : Finset (Finset L)},
    K ∈ nodeDisplayed N → K ∈ N.displayed
  | .leaf _, _, hK => by simpa [nodeDisplayed, Brooqs.Net.displayed] using hK
  | .tree _ N₁ _ N₂, _, hK => by
      simp only [nodeDisplayed, Brooqs.Net.displayed, List.mem_flatMap, List.mem_map] at hK ⊢
      obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
      exact ⟨K₁, nodeDisplayed_subset hK₁, K₂, nodeDisplayed_subset hK₂, rfl⟩
  | .cycle _ S₁ S₂ _ H, _, hK => by
      simp only [nodeDisplayed, Brooqs.Net.displayed, List.mem_flatMap, List.mem_append] at hK ⊢
      obtain ⟨K₀, hK₀, hK⟩ := hK
      refine ⟨K₀, nodeDisplayed_subset hK₀, ?_⟩
      rcases hK with hK | hK
      · by_cases h2 : hasNode S₂ = true
        · simp only [h2, ↓reduceIte, List.mem_flatMap, List.mem_map] at hK
          obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
          exact Or.inl ⟨K₁, sideNodeDisplayed_subset hK₁,
            List.mem_map.2 ⟨K₂, sideNodeDisplayed_subset hK₂, rfl⟩⟩
        · simp [h2] at hK
      · by_cases h1 : hasNode S₁ = true
        · simp only [h1, ↓reduceIte, List.mem_flatMap, List.mem_map] at hK
          obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
          exact Or.inr ⟨K₁, sideNodeDisplayed_subset hK₁,
            List.mem_map.2 ⟨K₂, sideNodeDisplayed_subset hK₂, rfl⟩⟩
        · simp [h1] at hK

/-- The clusters along a side in `NMSC.sideNodeDisplayed` are those of the displayed trees. -/
theorem sideNodeDisplayed_subset : ∀ {S : Brooqs.Side L} {T : Finset L}
    {K : Finset (Finset L)}, K ∈ sideNodeDisplayed S T → K ∈ S.displayed T
  | .hyb _, _, _, hK => by simpa [sideNodeDisplayed, Brooqs.Side.displayed] using hK
  | .node _ _ M S, _, _, hK => by
      simp only [sideNodeDisplayed, Brooqs.Side.displayed, List.mem_flatMap,
        List.mem_map] at hK ⊢
      obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
      exact ⟨K₁, sideNodeDisplayed_subset hK₁, K₂, nodeDisplayed_subset hK₂, rfl⟩
end

mutual
/-- **The trees of `NMSC.nodeDisplayed N` are the base trees of the exchanges.** Every displayed
tree of `N` that deletes, at each cycle, the hybrid edge of a side with a node is the displayed
tree `NMSC.baseClusters N'` of the base tree of `N` with the sides of some cycles exchanged: those
whose hybrid component hangs from the bottom of `S₂`. -/
theorem exists_sideSwap_of_mem_nodeDisplayed : ∀ {N : Brooqs.Net L} {K : Finset (Finset L)},
    K ∈ nodeDisplayed N → ∃ N', N.SideSwap N' ∧ baseClusters N' = K
  | .leaf x, _, hK => by
      simp only [nodeDisplayed, List.mem_singleton] at hK
      exact ⟨.leaf x, .leaf x, by rw [hK]; rfl⟩
  | .tree _ N₁ _ N₂, _, hK => by
      simp only [nodeDisplayed, List.mem_flatMap, List.mem_map] at hK
      obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
      obtain ⟨N₁', h₁, rfl⟩ := exists_sideSwap_of_mem_nodeDisplayed hK₁
      obtain ⟨N₂', h₂, rfl⟩ := exists_sideSwap_of_mem_nodeDisplayed hK₂
      exact ⟨_, .tree h₁ h₂, by simp only [baseClusters, h₁.taxa_eq, h₂.taxa_eq]⟩
  | .cycle _ S₁ S₂ _ H, _, hK => by
      simp only [nodeDisplayed, List.mem_flatMap, List.mem_append] at hK
      obtain ⟨K₀, hK₀, hK⟩ := hK
      obtain ⟨H', hH, rfl⟩ := exists_sideSwap_of_mem_nodeDisplayed hK₀
      rcases hK with hK | hK
      -- the hybrid component hangs from `S₁`, and `S₂` has a node: no exchange
      · by_cases h2 : hasNode S₂ = true
        · simp only [h2, ↓reduceIte, List.mem_flatMap, List.mem_map] at hK
          obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
          obtain ⟨S₁', h₁, rfl⟩ := exists_sideSwap_of_mem_sideNodeDisplayed hK₁
          obtain ⟨S₂', h₂', rfl⟩ := exists_sideSwap_of_mem_sideNodeDisplayed hK₂
          refine ⟨_, .cycle h₁ h₂' hH, ?_⟩
          simp only [baseClusters, hasNode_of_sideSwap h₂', h2, ↓reduceIte, hH.taxa_eq,
            h₁.taxa_eq, h₂'.taxa_eq]
        · simp [h2] at hK
      -- the hybrid component hangs from `S₂`, and `S₁` has a node: the sides are exchanged
      · by_cases h1 : hasNode S₁ = true
        · simp only [h1, ↓reduceIte, List.mem_flatMap, List.mem_map] at hK
          obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
          obtain ⟨S₁', h₁', rfl⟩ := exists_sideSwap_of_mem_sideNodeDisplayed hK₁
          obtain ⟨S₂', h₂, rfl⟩ := exists_sideSwap_of_mem_sideNodeDisplayed hK₂
          refine ⟨_, .swap h₁' h₂ hH, ?_⟩
          simp only [baseClusters, hasNode_of_sideSwap h₁', h1, ↓reduceIte, hH.taxa_eq,
            h₁'.taxa_eq, h₂.taxa_eq]
          rw [union_comm S₂'.taxa, union_right_comm (baseClusters H')]
        · simp [h1] at hK

/-- The clusters along a side in `NMSC.sideNodeDisplayed` are those of the base tree of the side
with the sides of some cycles exchanged. -/
theorem exists_sideSwap_of_mem_sideNodeDisplayed : ∀ {S : Brooqs.Side L} {T : Finset L}
    {K : Finset (Finset L)}, K ∈ sideNodeDisplayed S T →
      ∃ S', S.SideSwap S' ∧ sideBaseClusters S' T = K
  | .hyb ℓ, _, _, hK => by
      simp only [sideNodeDisplayed, List.mem_singleton] at hK
      exact ⟨.hyb ℓ, .hyb ℓ, by rw [hK]; rfl⟩
  | .node _ _ M S, _, _, hK => by
      simp only [sideNodeDisplayed, List.mem_flatMap, List.mem_map] at hK
      obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
      obtain ⟨S', hS, rfl⟩ := exists_sideSwap_of_mem_sideNodeDisplayed hK₁
      obtain ⟨M', hM, rfl⟩ := exists_sideSwap_of_mem_nodeDisplayed hK₂
      exact ⟨_, .node hM hS, by simp only [sideBaseClusters, hS.taxa_eq, hM.taxa_eq]⟩
end

/-- A metric side without a node is a single hybrid edge, so the other side of its cycle has a
node. -/
private theorem tr_hasNode_of_not {S₁ S₂ : Brooqs.Side L} (h : S₁.nodes ≠ [] ∨ S₂.nodes ≠ [])
    (h2 : ¬ hasNode S₂ = true) : hasNode S₁ = true := by
  cases S₂ with
  | node => exact absurd rfl h2
  | hyb =>
      cases S₁ with
      | node => rfl
      | hyb => simp [Brooqs.Side.nodes] at h

mutual
/-- **The base trees of the exchanges are trees of `NMSC.nodeDisplayed N`.** For a metric network
`N` and an exchange `N'` of the sides of some of its cycles, the displayed tree
`NMSC.baseClusters N'` of the base tree of `N'` deletes, at each cycle, the hybrid edge of a side
with a node. -/
theorem baseClusters_mem_nodeDisplayed : ∀ {N N' : Brooqs.Net L}, N.SideSwap N' → N.IsMetric →
    baseClusters N' ∈ nodeDisplayed N
  | _, _, .leaf x, _ => by simp [baseClusters, nodeDisplayed]
  | _, _, .tree h₁ h₂, hm => by
      simp only [baseClusters, nodeDisplayed, List.mem_flatMap, List.mem_map]
      exact ⟨_, baseClusters_mem_nodeDisplayed h₁ hm.2.2.1, _,
        baseClusters_mem_nodeDisplayed h₂ hm.2.2.2, by rw [h₁.taxa_eq, h₂.taxa_eq]⟩
  | _, _, .cycle (S₁ := S₁) (S₂ := S₂) h₁ h₂ hH, hm => by
      obtain ⟨-, -, -, hS₁, hS₂, hHm, hne⟩ := hm
      have hK := baseClusters_mem_nodeDisplayed hH hHm
      simp only [baseClusters, nodeDisplayed, List.mem_flatMap, List.mem_append,
        hasNode_of_sideSwap h₂, ← hH.taxa_eq, ← h₁.taxa_eq, ← h₂.taxa_eq]
      by_cases h2 : hasNode S₂ = true
      -- the hybrid component hangs from `S₁`
      · simp only [h2, ↓reduceIte, List.mem_flatMap, List.mem_map]
        exact ⟨_, hK, Or.inl ⟨_, sideBaseClusters_mem_sideNodeDisplayed h₁ hS₁, _,
          sideBaseClusters_mem_sideNodeDisplayed h₂ hS₂, rfl⟩⟩
      -- `S₂` is a single hybrid edge, and the hybrid component hangs from it
      · have h1 := tr_hasNode_of_not hne h2
        simp only [h2, h1, ↓reduceIte, Bool.false_eq_true, List.mem_flatMap, List.mem_map,
          List.not_mem_nil, false_or]
        exact ⟨_, hK, _, sideBaseClusters_mem_sideNodeDisplayed h₁ hS₁, _,
          sideBaseClusters_mem_sideNodeDisplayed h₂ hS₂, rfl⟩
  | _, _, .swap (S₁ := S₁) (S₂ := S₂) h₁ h₂ hH, hm => by
      obtain ⟨-, -, -, hS₁, hS₂, hHm, hne⟩ := hm
      have hK := baseClusters_mem_nodeDisplayed hH hHm
      simp only [baseClusters, nodeDisplayed, List.mem_flatMap, List.mem_append,
        hasNode_of_sideSwap h₁, ← hH.taxa_eq, ← h₁.taxa_eq, ← h₂.taxa_eq,
        union_comm S₂.taxa S₁.taxa]
      by_cases h1 : hasNode S₁ = true
      -- the hybrid component hangs from `S₂`, the first side of the exchanged cycle
      · simp only [h1, ↓reduceIte, List.mem_flatMap, List.mem_map]
        exact ⟨_, hK, Or.inr ⟨_, sideBaseClusters_mem_sideNodeDisplayed h₁ hS₁, _,
          sideBaseClusters_mem_sideNodeDisplayed h₂ hS₂, by
            rw [union_right_comm (baseClusters _)]⟩⟩
      -- `S₁` is a single hybrid edge, and the hybrid component hangs from it
      · have h2 := tr_hasNode_of_not hne.symm h1
        simp only [h1, h2, ↓reduceIte, Bool.false_eq_true, List.mem_flatMap, List.mem_map,
          List.not_mem_nil, or_false]
        exact ⟨_, hK, _, sideBaseClusters_mem_sideNodeDisplayed h₁ hS₁, _,
          sideBaseClusters_mem_sideNodeDisplayed h₂ hS₂, by
            rw [union_right_comm (baseClusters _)]⟩

/-- The clusters along a side of the base tree of an exchange are those of a tree of
`NMSC.nodeDisplayed`. -/
theorem sideBaseClusters_mem_sideNodeDisplayed : ∀ {S S' : Brooqs.Side L} {T : Finset L},
    S.SideSwap S' → S.IsMetric → sideBaseClusters S' T ∈ sideNodeDisplayed S T
  | _, _, _, .hyb _, _ => by simp [sideBaseClusters, sideNodeDisplayed]
  | _, _, _, .node hM hS, hm => by
      simp only [sideBaseClusters, sideNodeDisplayed, List.mem_flatMap, List.mem_map]
      exact ⟨_, sideBaseClusters_mem_sideNodeDisplayed hS hm.2.2.2, _,
        baseClusters_mem_nodeDisplayed hM hm.2.2.1, by rw [hS.taxa_eq, hM.taxa_eq]⟩
end

/-- **The base trees of the exchanges.** For a metric network `N`, the displayed trees of `N` that
delete, at each cycle, the hybrid edge of a side with a node (`NMSC.nodeDisplayed N`) are exactly
the displayed trees `NMSC.baseClusters N'` of the base trees of the exchanges `N'` of the sides of
cycles of `N`. -/
theorem mem_nodeDisplayed_iff {N : Brooqs.Net L} (hN : N.IsMetric) (K : Finset (Finset L)) :
    K ∈ nodeDisplayed N ↔ ∃ N', N.SideSwap N' ∧ baseClusters N' = K :=
  ⟨exists_sideSwap_of_mem_nodeDisplayed, fun ⟨_, h, hK⟩ =>
    hK ▸ baseClusters_mem_nodeDisplayed h hN⟩

mutual
/-- Exchanging the sides of cycles keeps the number of cycles. -/
theorem cycleCount_of_sideSwap : ∀ {N N' : Brooqs.Net L}, N.SideSwap N' →
    cycleCount N' = cycleCount N
  | _, _, .leaf _ => rfl
  | _, _, .tree h₁ h₂ => by
      simp only [cycleCount, cycleCount_of_sideSwap h₁, cycleCount_of_sideSwap h₂]
  | _, _, .cycle h₁ h₂ h => by
      simp only [cycleCount, cycleCount_of_sideSwap h, sideCycleCount_of_sideSwap h₁,
        sideCycleCount_of_sideSwap h₂]
  | _, _, .swap h₁ h₂ h => by
      simp only [cycleCount, cycleCount_of_sideSwap h, sideCycleCount_of_sideSwap h₁,
        sideCycleCount_of_sideSwap h₂]
      ring

/-- Exchanging the sides of cycles keeps the number of cycles below a side. -/
theorem sideCycleCount_of_sideSwap : ∀ {S S' : Brooqs.Side L}, S.SideSwap S' →
    sideCycleCount S' = sideCycleCount S
  | _, _, .hyb _ => rfl
  | _, _, .node hM hS => by
      simp only [sideCycleCount, cycleCount_of_sideSwap hM, sideCycleCount_of_sideSwap hS]
end

/-- The graphs of `N` and of an exchange `N'` of the sides of some of its cycles display the same
quartet trees, those of Q(N_r), and have the same number of reticulations, one for each cycle. -/
theorem graph_sideSwap {N N' : Brooqs.Net L} (h : N.SideSwap N') (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) :
    (∀ q, (Realization.graph (baseTree N') (pairs N')).DisplaysQuartet q ↔
        (Realization.graph (baseTree N) (pairs N)).DisplaysQuartet q) ∧
      (Realization.graph (baseTree N') (pairs N')).reticulationCount =
        (Realization.graph (baseTree N) (pairs N)).reticulationCount := by
  refine ⟨fun q => ?_, ?_⟩
  · rw [graph_displaysQuartet_iff (h.wellFormed_iff.1 hN) (fun x => h.taxa_eq ▸ htaxa x),
      graph_displaysQuartet_iff hN htaxa, displaysQuartet_iff_of_sideSwap h]
  · rw [graph_reticulationCount, graph_reticulationCount, cycleCount_of_sideSwap h]

/-- The base tree of `N` with the sides of some cycles exchanged is a displayed tree of `N`
(`NMSC.DisplaysTree`). -/
theorem displaysTree_baseTree_of_sideSwap {N N' : Brooqs.Net L} (h : N.SideSwap N')
    (hN : N.WellFormed) (htaxa : ∀ x : L, x ∈ N.taxa) : DisplaysTree N (baseTree N') :=
  (displaysTree_iff_of_sideSwap h _).2
    (displaysTree_baseTree (h.wellFormed_iff.1 hN) fun x => h.taxa_eq ▸ htaxa x)

/-- **Every displayed tree of `NMSC.nodeDisplayed N` is a base tree.** For each displayed tree `K`
of `N` that deletes, at each cycle, the hybrid edge of a side with a node, the base tree of some
exchange `N'` of the sides of cycles of `N` has the clusters of `K` as its clades. -/
theorem exists_baseTree_of_mem_nodeDisplayed {N : Brooqs.Net L} (hN : N.WellFormed)
    {K : Finset (Finset L)} (hK : K ∈ nodeDisplayed N) :
    ∃ N', N.SideSwap N' ∧
      (baseTree N').clades.toFinset = K.image (Finset.map (Coalescent.label L)) := by
  obtain ⟨N', h, rfl⟩ := exists_sideSwap_of_mem_nodeDisplayed hK
  exact ⟨N', h, clades_baseTree N' (h.wellFormed_iff.1 hN)⟩

section Genes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]

open DynamicProgramming in
/-- **Sections 3.2 to 3.4 under the NMSC, through the base tree of an exchange.** Let the gene
trees be independent, each with the law of the NMSC on a metric level-1 network `N` with distinct
leaf labels on the taxa `L`, without the anomalous configuration, and let `0 < t < t₀(N)`. Let `N'`
be `N` with the sides of some cycles exchanged: the same network, with the same gene tree law,
Q(N_r) and `t₀(N)` (`Camus/Pipelines/NMSC/Swap.lean`). Its base tree `T` is a displayed tree of `N`
(`NMSC.displaysTree_baseTree_of_sideSwap`); these base trees are the displayed trees of
`NMSC.nodeDisplayed N` (`NMSC.exists_baseTree_of_mem_nodeDisplayed`). Assume, as `recovery` does,
that the graph `Nr = Realization.graph T (pairs N')` of `N'` is identifiable under inclusion among
the networks built on `T`. Almost surely, for all large numbers `n` of genes, every network built
on `T` that has the best score for the output `Q` of Quartet Filtering on the quartet trees of the
first `n` gene trees, with the fewest reticulations among the networks with the best score, is
isomorphic to `Nr`. -/
theorem nmsc_recovery_sideSwap {N N' : Brooqs.Net L} (hNN' : N.SideSwap N') (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (hna : NoAnomaly N) (G : ℕ → Ω → Finset (Finset L))
    (hind : iIndepFun G P) (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N)
    (identifiable : ∀ R : RootedNetwork, R.AnchoredExtension (baseTree N') →
      (∀ q, (Realization.graph (baseTree N') (pairs N')).DisplaysQuartet q →
        R.DisplaysQuartet q) →
      R.reticulationCount ≤ (Realization.graph (baseTree N') (pairs N')).reticulationCount →
      Nonempty (R.Iso (Realization.graph (baseTree N') (pairs N')))) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ R : RootedNetwork, R.AnchoredExtension (baseTree N') →
      (∀ R' : RootedNetwork, R'.AnchoredExtension (baseTree N') →
        score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R') ≤
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R)) →
      (∀ R' : RootedNetwork, R'.AnchoredExtension (baseTree N') →
        (∀ R'' : RootedNetwork, R''.AnchoredExtension (baseTree N') →
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R'') ≤
            score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R')) →
        R.reticulationCount ≤ R'.reticulationCount) →
      Nonempty (R.Iso (Realization.graph (baseTree N') (pairs N'))) :=
  -- the hypotheses on `N` are those on `N'`
  nmsc_recovery_graph (hNN'.wellFormed_iff.1 hN) (fun x => hNN'.taxa_eq ▸ htaxa x)
    ((noAnomaly_iff_of_sideSwap hNN').1 hna) G hind hid
    (fun T => (hlaw T).trans (by rw [hNN'.geneTreeDist_eq])) ht
    (threshold_eq_of_sideSwap hNN' ▸ ht₀) identifiable

end Genes

end NMSC

end Camus
