module

public import Camus.Pipelines.NMSC.DisplayedTrees
public import Camus.Pipelines.Pipeline

/-!
# Section 3.3: the pipeline under the NMSC, when ASTRAL returns one of the underlying trees

Section 3.3 runs ASTRAL on the gene trees, "Estimate a species tree T and root it on the edge
leading to the outgroup (default: use ASTRAL)", and gives the result to CAMUS: "If we assume that
the true phylogenetic network N is level-1 and that T* is one of the underlying trees, then gene
trees can differ from T* due to both ILS and HGT." ASTRAL returns an unrooted tree; "one of the
underlying trees" is a displayed tree of `N` as an unrooted tree (`NMSC.DisplaysTree`). This file
shows that such a tree, rooted at the outgroup, is a tree of the graph of `N` in the sense of
Definition 1 (`NMSC.builtOn_reroot_of_displaysTree`): the displayed tree is the tree of a switching
of the graph (`NMSC.exists_builtOn_of_mem_displayed`), two trees rooted at the same outgroup that
induce the same quartet trees are equal up to the order of the children
(`PhyloTree.rootedIso_of_induced_eq`), and a network built on one is built on the other
(`PhyloTree.RootedIso.builtOn_iff`). So Section 3.2's argument applies through it, and CAMUS
returns the graph of `N` (`NMSC.nmsc_recovery_underlying`).

## Main results

* `NMSC.induced_iff_induces`: a tree of the graph with the clusters of a displayed tree induces
  the quartet trees of that displayed tree.
* `NMSC.builtOn_reroot_of_displaysTree`: a displayed tree of `N`, rooted at the outgroup, is a tree
  of the graph of `N`.
* `NMSC.nmsc_recovery_underlying`: Sections 3.2 to 3.4 under the NMSC, when the tree given to
  CAMUS is one of the underlying trees, rooted at the outgroup.
-/

@[expose] public section

namespace Camus

namespace NMSC

open Finset Filter Topology MeasureTheory ProbabilityTheory Coalescent Algorithm1

variable {L : Finset ℕ}

/-- A tree of the graph of `N` whose clades are the clusters of a displayed tree `K` induces the
quartet trees that `K` induces. -/
theorem induced_iff_induces {N : Brooqs.Net L} (hN : N.WellFormed) (htaxa : ∀ x : L, x ∈ N.taxa)
    {T : PhyloTree} (hT : (Realization.graph (baseTree N) (pairs N)).BuiltOn T)
    {K : Finset (Finset L)} (hc : T.clades.toFinset = K.image (Finset.map (Coalescent.label L)))
    (q : Quartet) : q.induced T = true ↔ Induces K q := by
  have hTt : T.taxa = L := by
    obtain ⟨-, S, ⟨H⟩⟩ := hT
    rw [← H.taxa_preserved]
    exact taxa_baseTree_eq hN.1 htaxa
  rw [induced_iff_clades, hTt]
  unfold Induces
  refine and_congr_right fun _ => ⟨fun ⟨C, hC, h⟩ => ?_, fun ⟨A, hA, h⟩ => ?_⟩
  · have hC' : C ∈ T.clades.toFinset := List.mem_toFinset.2 hC
    rw [hc] at hC'
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hC'
    exact ⟨A, hA, h⟩
  · have hA' : A.map (Coalescent.label L) ∈ T.clades.toFinset := by
      rw [hc]
      exact Finset.mem_image_of_mem _ hA
    exact ⟨_, List.mem_toFinset.1 hA', h⟩

/-- **Section 3.3: one of the underlying trees, rooted at the outgroup, is a tree of the graph.**
Let `N` be a metric level-1 network with distinct leaf labels on the taxa `L` (at least two), and
let the root of its graph `Nr = Realization.graph (baseTree N) (pairs N)` have the leaf of the
outgroup `o` as a child. If the tree `T*` on the taxa `L` is a displayed tree of `N`, as an
unrooted tree ("T* is one of the underlying trees", `NMSC.DisplaysTree`), then `T*` rooted on the
edge leading to the outgroup is a tree of `Nr` in the sense of Definition 1. -/
theorem builtOn_reroot_of_displaysTree {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) {Tstar : PhyloTree} (hw : Tstar.WellLabelled)
    (htt : Tstar.taxa = L) (hT : DisplaysTree N Tstar) (h2 : 2 ≤ L.card) {o : ℕ}
    (ho : o ∈ (Realization.graph (baseTree N) (pairs N)).taxa)
    (hor : ((Realization.graph (baseTree N) (pairs N)).root,
        (Realization.graph (baseTree N) (pairs N)).leaf o) ∈
      (Realization.graph (baseTree N) (pairs N)).edges) :
    (Realization.graph (baseTree N) (pairs N)).BuiltOn (Tstar.reroot o) := by
  -- the displayed tree of `N` that `T*` is
  obtain ⟨K, hK, hKq⟩ := hT
  -- a tree of the graph with its clusters
  obtain ⟨T, hTb, hTc⟩ := exists_builtOn_of_mem_displayed hN hK
  have hTw : T.WellLabelled := by
    obtain ⟨-, S, ⟨H⟩⟩ := hTb
    exact H.wellLabelled
  have hGt : (Realization.graph (baseTree N) (pairs N)).taxa = L := taxa_baseTree_eq hN.1 htaxa
  have hTt : T.taxa = L := by
    obtain ⟨-, S, ⟨H⟩⟩ := hTb
    rw [← H.taxa_preserved, hGt]
  -- the two trees, rooted at the outgroup, are equal up to the order of the children
  have hiso := PhyloTree.rootedIso_of_induced_eq hTw (PhyloTree.wellLabelled_reroot o hw)
    (by rw [hTt, PhyloTree.taxa_reroot, htt])
    (fun q => by
      rw [PhyloTree.induced_reroot o hw]
      exact Bool.eq_iff_iff.2 ((induced_iff_induces hN htaxa hTb hTc q).trans (hKq q)))
    (hTb.rootedAt_of_outgroup ho hor)
    (PhyloTree.rootedAt_reroot (by rw [htt]; exact hGt ▸ ho) (by rw [htt]; exact h2))
  exact (PhyloTree.RootedIso.builtOn_iff hiso _).1 hTb

section Genes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]

open DynamicProgramming in
/-- **Sections 3.2 to 3.4 under the NMSC, through one of the underlying trees.** Let the gene trees
be independent, each with the law of the NMSC on a metric level-1 network `N` with distinct leaf
labels on the taxa `L` (at least two), without the anomalous configuration, and let
`0 < t < t₀(N)`; let the root of the graph `Nr = Realization.graph (baseTree N) (pairs N)` of `N`
have the leaf of the outgroup `o` as a child. Let `T*` be a tree on the taxa `L` that is one of the
underlying trees of `N` ("If we assume that the true phylogenetic network N is level-1 and that T*
is one of the underlying trees", Section 3.3), and `T = T*` rooted on the edge leading to the
outgroup ("Estimate a species tree T and root it on the edge leading to the outgroup"). If `Nr` is
identifiable under inclusion among the networks built on `T`, then almost surely, for all large
numbers `n` of genes, every network built on `T` that has the best score for the output `Q` of
Quartet Filtering on the quartet trees of the first `n` gene trees, with the fewest reticulations
among the networks with the best score, is isomorphic to `Nr`. -/
theorem nmsc_recovery_underlying {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (hna : NoAnomaly N) (G : ℕ → Ω → Finset (Finset L))
    (hind : iIndepFun G P) (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N) (h2 : 2 ≤ L.card) {o : ℕ}
    (ho : o ∈ (Realization.graph (baseTree N) (pairs N)).taxa)
    (hor : ((Realization.graph (baseTree N) (pairs N)).root,
        (Realization.graph (baseTree N) (pairs N)).leaf o) ∈
      (Realization.graph (baseTree N) (pairs N)).edges)
    {Tstar : PhyloTree} (hw : Tstar.WellLabelled) (htt : Tstar.taxa = L)
    (hT : DisplaysTree N Tstar)
    (identifiable : ∀ R : RootedNetwork, R.AnchoredExtension (Tstar.reroot o) →
      (∀ q, (Realization.graph (baseTree N) (pairs N)).DisplaysQuartet q →
        R.DisplaysQuartet q) →
      R.reticulationCount ≤ (Realization.graph (baseTree N) (pairs N)).reticulationCount →
      Nonempty (R.Iso (Realization.graph (baseTree N) (pairs N)))) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ R : RootedNetwork, R.AnchoredExtension (Tstar.reroot o) →
      (∀ R' : RootedNetwork, R'.AnchoredExtension (Tstar.reroot o) →
        score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R') ≤
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R)) →
      (∀ R' : RootedNetwork, R'.AnchoredExtension (Tstar.reroot o) →
        (∀ R'' : RootedNetwork, R''.AnchoredExtension (Tstar.reroot o) →
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R'') ≤
            score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R')) →
        R.reticulationCount ≤ R'.reticulationCount) →
      Nonempty (R.Iso (Realization.graph (baseTree N) (pairs N))) :=
  -- `T*` rooted at the outgroup is a tree of the graph, and Section 3.2's argument applies
  nmsc_recovery_builtOn hN htaxa hna G hind hid hlaw ht ht₀ ho hor (Tstar.reroot o)
    (builtOn_reroot_of_displaysTree hN htaxa hw htt hT h2 ho hor) identifiable

end Genes

end NMSC

end Camus
