module

public import Camus.Pipelines.NMSC.Trees

/-!
# The trees of a network by the clades below the vertices of its switchings

Definition 1 builds the trees 𝒯 of a rooted binary level-1 network `N` from its switchings: delete
one of the two edges into each reticulation, in each of the possible ways, and clean up. This file
describes the clades of the tree of a switching `S` without the clean-up: they are the sets of taxa
below the vertices of `N` in `S` (`DisplayedSubdivision.clades_toFinset_eq`). So the trees of `N`,
as families of clades, are the families `N.vertices.image (N.cladeBelow S)` over the switchings
`S` of `N` (`RootedNetwork.exists_builtOn_clades`, `RootedNetwork.BuiltOn.exists_switching_clades`).
For the graph of a network `N` of the NMSC, this reduces the comparison of its trees with the
displayed trees of `N` (`Brooqs.Net.displayed`) to the clades below the vertices of its switchings
(`NMSC.exists_builtOn_of_switching_clades`), and gives the recovery of Section 3.2 through the tree
of every switching (`NMSC.nmsc_recovery_switching`).

## Main results

* `DisplayedSubdivision.clades_toFinset_eq`: the clades of the tree of a switching are the clades
  below the vertices.
* `RootedNetwork.exists_builtOn_clades`, `RootedNetwork.BuiltOn.exists_switching_clades`: the
  trees of `N` in the sense of Definition 1, by their clades, are those of its switchings.
* `NMSC.exists_builtOn_of_switching_clades`: a displayed tree of `N` is the family of clades of a
  tree of the graph of `N` as soon as it is the family of clades below the vertices of a switching.
* `NMSC.nmsc_recovery_switching`: Sections 3.2 to 3.4 under the NMSC through the tree of every
  switching of the graph of `N`, with an outgroup.
-/

@[expose] public section

namespace Camus

namespace DisplayedSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- The clades of the tree `t` of a switching `S` of `N` are the sets of taxa below the vertices of
`N` in `S`: below the image of a vertex `p` of `t` and below the interior vertices of the wire above
it lie the taxa of the clade of `p` (`DisplayedSubdivision.cladeBelow_original`,
`DisplayedSubdivision.cladeBelow_interior`), and below the vertices of the root wire all the taxa
(`DisplayedSubdivision.cladeBelow_rootWire`). -/
theorem clades_toFinset_eq (H : DisplayedSubdivision t N S) :
    t.clades.toFinset = N.vertices.image (N.cladeBelow S) := by
  have ht := H.wellLabelled
  have hroot : [] ∈ t.nodes := t.root_mem_nodes
  ext C
  simp only [List.mem_toFinset, Finset.mem_image]
  constructor
  · intro hC
    obtain ⟨p, hp, rfl⟩ := NMSC.exists_of_mem_clades hC
    refine ⟨H.original p, ?_, H.cladeBelow_original ht hp⟩
    rw [H.vertices_covered]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp))
  · rintro ⟨v, hv, rfl⟩
    rw [H.vertices_covered] at hv
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_erase] at hv
    rcases hv with (⟨p, hp, rfl⟩ | ⟨p, ⟨hp0, hp⟩, hv⟩) | hv
    · rw [H.cladeBelow_original ht hp]
      exact NMSC.taxaAt_mem_clades hp
    · rw [H.cladeBelow_interior ht hp hp0 hv]
      exact NMSC.taxaAt_mem_clades hp
    · rw [H.cladeBelow_rootWire (List.dropLast_subset _ (List.mem_toFinset.1 hv)),
        H.taxa_preserved, ← PhyloTree.taxaAt_nil]
      exact NMSC.taxaAt_mem_clades hroot

end DisplayedSubdivision

namespace RootedNetwork

variable {N : RootedNetwork}

/-- Definition 1 by the clades below the vertices: every switching `S` of a rooted binary level-1
network `N` gives a tree on which `N` is built, whose clades are the sets of taxa below the vertices
of `N` in `S`. -/
theorem exists_builtOn_clades (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)}
    (hS : N.Switching S) :
    ∃ t : PhyloTree, N.BuiltOn t ∧ t.clades.toFinset = N.vertices.image (N.cladeBelow S) := by
  obtain ⟨t, -, -, hb, ⟨H⟩⟩ := builtOn_of_switching hN hS
  exact ⟨t, hb, H.clades_toFinset_eq⟩

/-- Every tree on which `N` is built, in the sense of Definition 1, is the tree of a switching `S`,
and its clades are the sets of taxa below the vertices of `N` in `S`. -/
theorem BuiltOn.exists_switching_clades {t : PhyloTree} (h : N.BuiltOn t) :
    ∃ S, N.Switching S ∧ t.clades.toFinset = N.vertices.image (N.cladeBelow S) := by
  obtain ⟨-, S, ⟨H⟩⟩ := h
  exact ⟨S, H.switching, H.clades_toFinset_eq⟩

end RootedNetwork

namespace NMSC

open Finset Filter Topology MeasureTheory ProbabilityTheory Coalescent Algorithm1

variable {L : Finset ℕ}

/-- A displayed tree `K` of `N` is the family of clades of a tree of the graph
`Realization.graph (baseTree N) (pairs N)` of `N`, in the sense of Definition 1, as soon as some
switching of the graph has the clusters of `K` as its clades below the vertices. -/
theorem exists_builtOn_of_switching_clades {N : Brooqs.Net L} (hN : N.WellFormed)
    {K : Finset (Finset L)} {S : Finset (ℕ × ℕ)}
    (hS : (Realization.graph (baseTree N) (pairs N)).Switching S)
    (hK : (Realization.graph (baseTree N) (pairs N)).vertices.image
        ((Realization.graph (baseTree N) (pairs N)).cladeBelow S) =
      K.image (Finset.map (Coalescent.label L))) :
    ∃ T : PhyloTree, (Realization.graph (baseTree N) (pairs N)).BuiltOn T ∧
      T.clades.toFinset = K.image (Finset.map (Coalescent.label L)) := by
  obtain ⟨T, hT, hc⟩ := RootedNetwork.exists_builtOn_clades (graph_anchoredExtension hN).1 hS
  exact ⟨T, hT, hc.trans hK⟩

section Genes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]

open DynamicProgramming in
/-- **Sections 3.2 to 3.4 under the NMSC, through the tree of every switching.** Under the
hypotheses of `NMSC.nmsc_recovery_builtOn` (an outgroup leaf `z` child of the root of the graph
`Nr = Realization.graph (baseTree N) (pairs N)` of `N`), every switching `S` of `Nr` gives a tree
`T` of `Nr` (Definition 1) whose clades are the sets of taxa below the vertices of `Nr` in `S`, and
if `Nr` is identifiable under inclusion among the networks built on `T`, then almost surely, for
all large numbers `n` of genes, every network built on `T` with the best score for the output `Q` of
Quartet Filtering, with the fewest reticulations among them, is isomorphic to `Nr`. -/
theorem nmsc_recovery_switching {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (hna : NoAnomaly N) (G : ℕ → Ω → Finset (Finset L))
    (hind : iIndepFun G P) (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N) {z : ℕ} (hz : z ∈ (Realization.graph (baseTree N) (pairs N)).taxa)
    (hzr : ((Realization.graph (baseTree N) (pairs N)).root,
        (Realization.graph (baseTree N) (pairs N)).leaf z) ∈
      (Realization.graph (baseTree N) (pairs N)).edges)
    {S : Finset (ℕ × ℕ)} (hS : (Realization.graph (baseTree N) (pairs N)).Switching S) :
    ∃ T : PhyloTree, (Realization.graph (baseTree N) (pairs N)).BuiltOn T ∧
      T.clades.toFinset = (Realization.graph (baseTree N) (pairs N)).vertices.image
        ((Realization.graph (baseTree N) (pairs N)).cladeBelow S) ∧
      ((∀ R : RootedNetwork, R.AnchoredExtension T →
        (∀ q, (Realization.graph (baseTree N) (pairs N)).DisplaysQuartet q →
          R.DisplaysQuartet q) →
        R.reticulationCount ≤ (Realization.graph (baseTree N) (pairs N)).reticulationCount →
        Nonempty (R.Iso (Realization.graph (baseTree N) (pairs N)))) →
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
        Nonempty (R.Iso (Realization.graph (baseTree N) (pairs N)))) := by
  -- the tree of the switching, on which the graph is built (Definition 1)
  obtain ⟨T, hT, hc⟩ := RootedNetwork.exists_builtOn_clades (graph_anchoredExtension hN).1 hS
  -- and the recovery through it
  exact ⟨T, hT, hc, fun identifiable => nmsc_recovery_builtOn hN htaxa hna G hind hid hlaw ht
    ht₀ hz hzr T hT identifiable⟩

end Genes

end NMSC

end Camus
