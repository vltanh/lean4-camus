module

public import Camus.Pipelines.NMSC.Recovery
public import Camus.Pipelines.NMSC.Swap
public import Camus.Network.TreeBased.Root

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
every tree of the graph `Realization.graph (baseTree N) (pairs N)` of `N` in the sense of
Definition 1 (`RootedNetwork.BuiltOn`), when the root of the graph has an outgroup leaf as a child,
as in the pipeline of Section 3.3 ("the pipeline takes as input a set G of estimated gene trees and
an outgroup species"): the outgroup makes the graph built with the root kept on each of its trees
(`RootedNetwork.BuiltOn.anchored_of_outgroup`), the class of networks over which CAMUS optimizes.
Without it, a tree of `N` need not keep the root (the report's E8). A network of the NMSC whose root
has a leaf `z` as a child gives such a graph (`NMSC.graph_outgroup`).

The same holds for the base tree of `N` with the sides of some cycles exchanged
(`Brooqs.Net.SideSwap`), which describes the same network: the gene trees, Q(N_r) and the
threshold are unchanged (`Camus/Pipelines/NMSC/Swap.lean`), and CAMUS, given the base tree of the
exchanged network, returns its graph (`NMSC.nmsc_recovery_sideSwap`). These base trees are the
displayed trees of `N` that delete, at each cycle, the hybrid edge of a side with a node
(`NMSC.nodeDisplayed`, `NMSC.exists_sideSwap_of_mem_nodeDisplayed`).

## Main results

* `NMSC.nmsc_recovery_builtOn`: Sections 3.2 to 3.4 under the NMSC, through every tree of the
  graph of `N`, with an outgroup.
* `NMSC.graph_outgroup`, `NMSC.nmsc_recovery_outgroup`: a leaf child of the root of `N` is an
  outgroup of its graph.
* `NMSC.displaysTree_baseTree_of_sideSwap`, `NMSC.nmsc_recovery_sideSwap`: recovery through the
  base tree of `N` with the sides of some cycles exchanged.
* `NMSC.nodeDisplayed`, `NMSC.nodeDisplayed_subset`, `NMSC.exists_sideSwap_of_mem_nodeDisplayed`:
  the displayed trees that delete the hybrid edge of a side with a node at each cycle are the base
  trees of the exchanges.
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
taking one of the trees t∈T and adding reticulations (edges) to t"), for instance the tree `T*`
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

end NMSC

end Camus
