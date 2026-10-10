module

public import Camus.Pipelines.NMSC.Recovery

/-!
# Section 3.2 under the NMSC: the true network need not be the unique optimum

Section 3.2 claims that CAMUS returns the true network `N` once its input is a multiset version of
Q(N_r), "since this is the unique network that can satisfy all the quartets in Q(N_r)". This is
false (the report's E7, `not_uniqueOptimum`), and the counterexample of the library carries over to
the input that Quartet Filtering builds under the NMSC. Take the five-leaf tree
`T = (O,((B,A),(D,C)))` of E7 (`Counterexamples.constraint`) as the true network, a network of the
NMSC without cycles (`NMSC.treeNet`); its graph is `T` itself, with no added edge
(`NMSC.baseTree_treeNet`, `NMSC.pairs_treeNet`). For gene trees drawn independently under the NMSC
on it and every threshold `0 < t < t₀`, almost surely, for all large numbers of genes, the output
`Q` of Quartet Filtering is a multiset version of Q(T), and the network obtained from `T` by adding
an edge above `(A, C)` (`Counterexamples.extraPair`), built on `T` with one reticulation, has the
best score for `Q`, as `T` does (`NMSC.nmsc_uniqueness_counterexample`). The corrected recovery
theorem selects `T`, the optimal network with the fewest reticulations
(`NMSC.nmsc_recovery_treeNet`).

## Main results

* `NMSC.treeNet`, `NMSC.baseTree_treeNet`, `NMSC.pairs_treeNet`, `NMSC.threshold_treeNet_pos`: the
  tree `T` as a network of the NMSC.
* `NMSC.nmsc_uniqueness_counterexample`: E7 under the NMSC.
* `NMSC.nmsc_recovery_treeNet`: the corrected recovery theorem on this example.
-/

@[expose] public noncomputable section

namespace Camus

namespace NMSC

open Finset Filter Topology MeasureTheory ProbabilityTheory Coalescent Algorithm1
  DynamicProgramming

/-- The five taxa `A = 0`, `B = 1`, `C = 2`, `D = 3`, `O = 4`. -/
abbrev taxa5 : Finset ℕ := {0, 1, 2, 3, 4}

/-- The tree `T = (O,((B,A),(D,C)))` of E7 as a network of the NMSC, without cycles, with all edges
of length `1`. -/
def treeNet : Brooqs.Net taxa5 :=
  .tree 1 (.leaf ⟨4, by decide⟩) 1
    (.tree 1 (.tree 1 (.leaf ⟨1, by decide⟩) 1 (.leaf ⟨0, by decide⟩)) 1
      (.tree 1 (.leaf ⟨3, by decide⟩) 1 (.leaf ⟨2, by decide⟩)))

theorem treeNet_wellFormed : treeNet.WellFormed :=
  ⟨by norm_num [treeNet, Brooqs.Net.IsMetric], by decide⟩

theorem treeNet_taxa : ∀ x : taxa5, x ∈ treeNet.taxa := by
  decide

/-- The base tree of the network is `T`. -/
theorem baseTree_treeNet : baseTree treeNet = Counterexamples.constraint := by
  decide

/-- The network has no cycle, so its graph has no added edge. -/
theorem pairs_treeNet : pairs treeNet = ∅ := by
  decide

/-- The network has no cycle, so no anomalous set of four taxa. -/
theorem treeNet_noAnomaly : NoAnomaly treeNet :=
  noAnomaly_of_below fun Ω => absurd Ω.mem (by simp [treeNet, Brooqs.Net.subnets])

/-- The threshold `t₀` of the network is positive, so thresholds `0 < t < t₀` exist. -/
theorem threshold_treeNet_pos : 0 < threshold treeNet :=
  threshold_pos treeNet_wellFormed
    (regular_of_noAnomaly treeNet_wellFormed treeNet_taxa treeNet_noAnomaly)

section Genes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset taxa5))] [MeasurableSingletonClass (Finset (Finset taxa5))]

/-- **E7 under the NMSC** (Section 3.2). Let the gene trees be independent, each with the law of
the NMSC on the tree `T = (O,((B,A),(D,C)))` (`NMSC.treeNet`), and let `0 < t < t₀`. Almost
surely, for all large numbers `n` of genes, the output `Q` of Quartet Filtering on the quartet
trees of the first `n` gene trees is a multiset version of Q(T), and both `T` and the network
obtained from `T` by adding an edge above `(A, C)` are built on `T` and have the best score for
`Q` among the networks built on `T`; they have zero and one reticulations, so they are not
isomorphic, and the true network is not the unique optimum. -/
theorem nmsc_uniqueness_counterexample (G : ℕ → Ω → Finset (Finset taxa5))
    (hind : iIndepFun G P) (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = treeNet.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold treeNet) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (∀ q, q ∈ filterQuartets t (geneQuartets (fun i => G i ω) n) ↔
        (Realization.graph Counterexamples.constraint ∅).DisplaysQuartet q) ∧
      (∀ R : RootedNetwork, R.AnchoredExtension Counterexamples.constraint →
        score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R) ≤
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (Realization.graph Counterexamples.constraint ∅))) ∧
      (∀ R : RootedNetwork, R.AnchoredExtension Counterexamples.constraint →
        score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R) ≤
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (Realization.graph Counterexamples.constraint {Counterexamples.extraPair}))) ∧
      (Realization.graph Counterexamples.constraint ∅).reticulationCount = 0 ∧
      (Realization.graph Counterexamples.constraint
        {Counterexamples.extraPair}).reticulationCount = 1 ∧
      IsEmpty ((Realization.graph Counterexamples.constraint {Counterexamples.extraPair}).Iso
        (Realization.graph Counterexamples.constraint ∅)) := by
  obtain ⟨hN, hP, hN0, hP1, -, -⟩ := Counterexamples.graph_uniqueness_counterexample
  have hiso : IsEmpty ((Realization.graph Counterexamples.constraint
      {Counterexamples.extraPair}).Iso (Realization.graph Counterexamples.constraint ∅)) :=
    ⟨fun i => by
      have := i.reticulationCount_eq hP.1 hN.1
      omega⟩
  filter_upwards [nmsc_filterQuartets_graph treeNet_wellFormed treeNet_taxa treeNet_noAnomaly G
    hind hid hlaw ht ht₀] with ω hω
  filter_upwards [hω] with n hn
  rw [baseTree_treeNet, pairs_treeNet] at hn
  set Q := filterQuartets t (geneQuartets (fun i => G i ω) n)
  -- every quartet tree of `Q` is displayed by `T`, and so by `T` with the added edge
  have hall : ∀ R : RootedNetwork, (∀ q, (Realization.graph Counterexamples.constraint
      ∅).DisplaysQuartet q → R.DisplaysQuartet q) → score Q (repertoire Q R) = Q.card := by
    intro R hR
    refine (score_eq_card_iff Q _).2 fun q hq => ?_
    simp only [repertoire, Finset.mem_filter]
    exact ⟨hq, hR q ((hn q).1 (Multiset.mem_toFinset.1 hq))⟩
  have hsub : ∀ q, (Realization.graph Counterexamples.constraint ∅).DisplaysQuartet q →
      (Realization.graph Counterexamples.constraint
        {Counterexamples.extraPair}).DisplaysQuartet q := by
    intro q hq
    rw [Realization.graph_displays_iff_cuts Counterexamples.constraint_wellLabelled
      Counterexamples.extraPair_separated]
    rw [Realization.baseline_displays_iff _ Counterexamples.constraint_wellLabelled] at hq
    exact ⟨(Quartet.induced_iff_taxaAt q _).1 hq |>.1, Or.inl hq⟩
  refine ⟨hn, fun R _ => ?_, fun R _ => ?_, hN0, hP1, hiso⟩
  · rw [hall _ fun q h => h]
    exact score_le_card _ _
  · rw [hall _ hsub]
    exact score_le_card _ _

/-- **Section 3.2, corrected, on E7 under the NMSC.** Under the assumptions of
`NMSC.nmsc_uniqueness_counterexample`, almost surely, for all large numbers `n` of genes, every
network built on `T` that has the best score for the output of Quartet Filtering, with the fewest
reticulations among the networks with the best score, is isomorphic to `T`
(`NMSC.nmsc_recovery_graph`, with the identifiability of the tree, `tree_identifiable`). -/
theorem nmsc_recovery_treeNet (G : ℕ → Ω → Finset (Finset taxa5)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = treeNet.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold treeNet) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ R : RootedNetwork,
      R.AnchoredExtension Counterexamples.constraint →
      (∀ R' : RootedNetwork, R'.AnchoredExtension Counterexamples.constraint →
        score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R') ≤
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
            (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R)) →
      (∀ R' : RootedNetwork, R'.AnchoredExtension Counterexamples.constraint →
        (∀ R'' : RootedNetwork, R''.AnchoredExtension Counterexamples.constraint →
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R'') ≤
            score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R')) →
        R.reticulationCount ≤ R'.reticulationCount) →
      Nonempty (R.Iso (Realization.graph Counterexamples.constraint ∅)) := by
  have h := nmsc_recovery_graph treeNet_wellFormed treeNet_taxa treeNet_noAnomaly G hind hid hlaw
    ht ht₀
  simp only [baseTree_treeNet, pairs_treeNet] at h
  exact h (tree_identifiable _ Counterexamples.constraint_wellLabelled)

end Genes

end NMSC

end Camus
