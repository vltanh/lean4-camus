module

public import Camus.Pipelines.NMSC.Filtering
public import Camus.Pipelines.NMSC.Bridge
public import Camus.Pipelines.Uniqueness

/-!
# Sections 3.2 to 3.4 under the NMSC: the input of CAMUS after Quartet Filtering

Section 3.2 argues that CAMUS recovers the true network `N` once its input `Q` is "a multi-set
version of Q(Nr)", and Section 3.3 builds `Q` from gene trees that evolve down `N` under the NMSC,
with Quartet Filtering. This file shows that, for a level-1 network without the anomalous
configuration (`NMSC.NoAnomaly`) and a threshold `0 < t < t₀(N)`, almost surely, for all large
numbers of genes, the support of the output of Quartet Filtering is Q(N_r)
(`NMSC.nmsc_filterQuartets_support`): every quartet tree in Q(N_r) has positive probability, so it
eventually appears among the quartet trees of the gene trees (`NMSC.eventually_mem_geneQuartets`).
In the graph representation of CAMUS, `N` is the network `Realization.graph (baseTree N) (pairs N)`
built on the base tree of `N`, which displays the same quartet trees
(`NMSC.graph_displaysQuartet_iff`), so the support is Q(N_r) for that network too
(`NMSC.nmsc_filterQuartets_graph`). The corrected recovery theorem of Section 3.2 (`recovery`)
then applies (`NMSC.nmsc_recovery` for any network of CAMUS that displays the quartet trees of
`N`, `NMSC.nmsc_recovery_graph` for the graph of `N` and its base tree).

## Main results

* `NMSC.quartetProb_pos`: every quartet tree on the taxa has positive probability.
* `NMSC.eventually_mem_geneQuartets`: almost surely, eventually every quartet tree on the taxa
  appears.
* `NMSC.nmsc_filterQuartets_support`: almost surely, eventually the support of the output of
  Quartet Filtering is Q(N_r).
* `NMSC.nmsc_filterQuartets_graph`, `NMSC.nmsc_filterQuartets_graph_genes`: the same, with Q(N_r)
  the quartet trees displayed by the graph of `N`.
* `NMSC.nmsc_recovery`, `NMSC.nmsc_recovery_graph`: with Section 3.2's corrected recovery
  theorem.
-/

@[expose] public noncomputable section

namespace Camus

namespace NMSC

open Finset Filter Topology MeasureTheory ProbabilityTheory Coalescent Algorithm1

variable {L : Finset ℕ}

/-- Every quartet tree on the taxa of a metric network with distinct leaf labels has positive
probability under the NMSC (`Brooqs.Net.quartetCF_pos`). -/
theorem quartetProb_pos {N : Brooqs.Net L} (hN : N.WellFormed) (htaxa : ∀ x : L, x ∈ N.taxa)
    {q : Quartet} (hq : q.taxa ⊆ L) : 0 < quartetProb N q := by
  have hk : keyTaxa q.key ⊆ L := hq
  have hqk : q.key.quartet q.split = q := Quartet.key_quartet q
  obtain ⟨p0, p1, p2⟩ := quartetProb_eq_quartetCF N hN.2 q.key hk
  have hpos := fun (a b c e : Fin 4) =>
    Brooqs.Net.quartetCF_pos hN (htaxa (keyTaxon q.key hk a)) (htaxa (keyTaxon q.key hk b))
      (htaxa (keyTaxon q.key hk c)) (htaxa (keyTaxon q.key hk e))
  rw [← hqk]
  rcases (show q.split = 0 ∨ q.split = 1 ∨ q.split = 2 by omega) with h | h | h <;> rw [h]
  · rw [p0]
    exact hpos 0 1 2 3
  · rw [p1]
    exact hpos 0 2 1 3
  · rw [p2]
    exact hpos 0 3 1 2

section Genes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]

/-- For independent gene trees with the law of the NMSC on a metric network with distinct leaf
labels on the taxa `L`, almost surely, for all large numbers `n` of genes, every quartet tree on
the taxa is induced by one of the first `n` gene trees. -/
theorem eventually_mem_geneQuartets {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ q ∈ quartetsOn L, q ∈ geneQuartets (fun i => G i ω) n := by
  have h : ∀ q ∈ quartetsOn L, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      q ∈ geneQuartets (fun i => G i ω) n := by
    intro q hq
    have hp := quartetProb_pos hN htaxa (mem_quartetsOn.1 hq)
    have hconv := ae_tendsto_frequency G hind hid q
    rw [measureReal_induces N (G 0) (hid 0).aemeasurable_fst hlaw q] at hconv
    filter_upwards [hconv] with ω hω
    filter_upwards [hω.eventually_const_lt hp, eventually_gt_atTop 0] with n hn hn0
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    have hcount : (0 : ℝ) < (geneQuartets (fun i => G i ω) n).count q := by
      have h := mul_lt_mul_of_pos_right hn hn'
      rwa [zero_mul, div_mul_cancel₀ _ hn'.ne'] at h
    exact Multiset.count_pos.1 (by exact_mod_cast hcount)
  filter_upwards [(eventually_all_finset (quartetsOn L)).2 h] with ω hω
  exact (eventually_all_finset (quartetsOn L)).2 hω

/-- **Sections 3.3 and 3.4: the input of CAMUS.** Let the gene trees be independent, each with the
law of the NMSC on a metric level-1 network `N` with distinct leaf labels on the taxa `L`, without
the anomalous configuration. For every threshold `0 < t < t₀(N)`, almost surely, for all large
numbers `n` of genes, the quartet trees that Quartet Filtering returns are exactly those in
Q(N_r): its output is "a multi-set version of Q(Nr)" (Section 3.2). -/
theorem nmsc_filterQuartets_support {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (hna : NoAnomaly N) (G : ℕ → Ω → Finset (Finset L))
    (hind : iIndepFun G P) (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ q,
      q ∈ filterQuartets t (geneQuartets (fun i => G i ω) n) ↔ DisplaysQuartet N q := by
  filter_upwards [nmsc_filterQuartets_of_noAnomaly hN htaxa hna G hind hid hlaw ht ht₀,
    eventually_mem_geneQuartets hN htaxa G hind hid hlaw] with ω h1 h2
  filter_upwards [h1, h2] with n hn hall q
  rw [hn, Multiset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro hq
    obtain ⟨K, hKmem, hK⟩ := hq
    exact ⟨hall q (mem_quartetsOn.2 hK.1), ⟨K, hKmem, hK⟩⟩

open DynamicProgramming in
/-- **Sections 3.2 to 3.4 under the NMSC, with the corrected recovery theorem.** Let the gene trees
be independent, each with the law of the NMSC on a metric level-1 network `N` with distinct leaf
labels on the taxa `L`, without the anomalous configuration, and let `0 < t < t₀(N)`. Let `Nr` be a
rooted binary level-1 network of CAMUS built on the tree `T` that displays exactly the quartet
trees that `N` displays (`hbridge`; the graph of `N` is such a network,
`NMSC.nmsc_recovery_graph`), and assume, as `recovery` does, that `Nr` is identifiable under
inclusion among the networks built on `T`. Almost surely, for all large numbers `n` of genes,
every network built on `T` that has the best score for the output `Q` of Quartet Filtering on the
quartet trees of the first `n` gene trees, with the fewest reticulations among the networks with the
best score, is isomorphic to `Nr`. The paper's uniqueness claim, without the tie-break and the
identifiability, is false (the report's E7). -/
theorem nmsc_recovery {N : Brooqs.Net L} (hN : N.WellFormed) (htaxa : ∀ x : L, x ∈ N.taxa)
    (hna : NoAnomaly N) (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N) (T : PhyloTree) (Nr : RootedNetwork) (hNr : Nr.AnchoredExtension T)
    (hbridge : ∀ q, Nr.DisplaysQuartet q ↔ DisplaysQuartet N q)
    (identifiable : ∀ R : RootedNetwork, R.AnchoredExtension T →
      (∀ q, Nr.DisplaysQuartet q → R.DisplaysQuartet q) →
      R.reticulationCount ≤ Nr.reticulationCount → Nonempty (R.Iso Nr)) :
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
      Nonempty (R.Iso Nr) := by
  filter_upwards [nmsc_filterQuartets_support hN htaxa hna G hind hid hlaw ht ht₀] with ω hω
  filter_upwards [hω] with n hn R hR hopt hfew
  exact recovery T Nr hNr _ (fun q => (hn q).trans (hbridge q).symm) identifiable R hR hopt hfew

/-- **Sections 3.3 and 3.4 in the graph representation.** Under the assumptions of
`NMSC.nmsc_filterQuartets_support`, almost surely, for all large numbers `n` of genes, the quartet
trees that Quartet Filtering returns are exactly those displayed by the network
`Realization.graph (baseTree N) (pairs N)` of CAMUS, the graph of `N` built on its base tree
(`NMSC.graph_displaysQuartet_iff`). -/
theorem nmsc_filterQuartets_graph {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (hna : NoAnomaly N) (G : ℕ → Ω → Finset (Finset L))
    (hind : iIndepFun G P) (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ q,
      q ∈ filterQuartets t (geneQuartets (fun i => G i ω) n) ↔
        (Realization.graph (baseTree N) (pairs N)).DisplaysQuartet q := by
  filter_upwards [nmsc_filterQuartets_support hN htaxa hna G hind hid hlaw ht ht₀] with ω hω
  filter_upwards [hω] with n hn q
  rw [hn q, graph_displaysQuartet_iff hN htaxa q]

/-- Sections 3.3 and 3.4, for gene trees that exist: the hypotheses of
`NMSC.nmsc_filterQuartets_graph` hold for the coordinates of `N.genes hN`, the product law of
independent gene trees under the NMSC on `N` (`Brooqs.Net.genes`). -/
theorem nmsc_filterQuartets_graph_genes {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (hna : NoAnomaly N) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N) :
    ∀ᵐ ω ∂(N.genes hN), ∀ᶠ n in atTop, ∀ q,
      q ∈ filterQuartets t (geneQuartets (fun i => ω i) n) ↔
        (Realization.graph (baseTree N) (pairs N)).DisplaysQuartet q :=
  nmsc_filterQuartets_graph hN htaxa hna (fun n (ω : ℕ → Finset (Finset L)) => ω n)
    (N.genes_iIndepFun hN) (N.genes_identDistrib hN) (N.genes_law hN) ht ht₀

open DynamicProgramming in
/-- **Sections 3.2 to 3.4 under the NMSC, in the graph representation.** Let the gene trees be
independent, each with the law of the NMSC on a metric level-1 network `N` with distinct leaf
labels on the taxa `L`, without the anomalous configuration, and let `0 < t < t₀(N)`. Let `T` be
the base tree of `N`, a displayed tree of `N` (`NMSC.displaysTree_baseTree`), and
`Nr = Realization.graph T (pairs N)` the graph of `N`, a rooted binary level-1 network built on `T`
that displays the quartet trees of `N` (`NMSC.graph_anchoredExtension`,
`NMSC.graph_displaysQuartet_iff`) and has one reticulation for each cycle of `N`
(`NMSC.graph_reticulationCount`), and assume, as `recovery` does, that `Nr` is identifiable under
inclusion among the networks built on `T`. Almost surely, for all large numbers `n` of genes,
every network built on `T` that has the best score for the output `Q` of Quartet Filtering on the
quartet trees of the first `n` gene trees, with the fewest reticulations among the networks with
the best score, is isomorphic to `Nr`. -/
theorem nmsc_recovery_graph {N : Brooqs.Net L} (hN : N.WellFormed) (htaxa : ∀ x : L, x ∈ N.taxa)
    (hna : NoAnomaly N) (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N)
    (identifiable : ∀ R : RootedNetwork, R.AnchoredExtension (baseTree N) →
      (∀ q, (Realization.graph (baseTree N) (pairs N)).DisplaysQuartet q →
        R.DisplaysQuartet q) →
      R.reticulationCount ≤ (Realization.graph (baseTree N) (pairs N)).reticulationCount →
      Nonempty (R.Iso (Realization.graph (baseTree N) (pairs N)))) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ R : RootedNetwork, R.AnchoredExtension (baseTree N) →
      (∀ R' : RootedNetwork, R'.AnchoredExtension (baseTree N) →
        score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R') ≤
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R)) →
      (∀ R' : RootedNetwork, R'.AnchoredExtension (baseTree N) →
        (∀ R'' : RootedNetwork, R''.AnchoredExtension (baseTree N) →
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R'') ≤
            score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R')) →
        R.reticulationCount ≤ R'.reticulationCount) →
      Nonempty (R.Iso (Realization.graph (baseTree N) (pairs N))) :=
  nmsc_recovery hN htaxa hna G hind hid hlaw ht ht₀ (baseTree N) _ (graph_anchoredExtension hN)
    (graph_displaysQuartet_iff hN htaxa) identifiable

end Genes

end NMSC

end Camus
