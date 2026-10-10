module

public import Camus.External.WarnowTabatabaeeEvans.Sampling
public import Camus.Pipelines.Inclusion
public import Camus.Pipelines.Statistical

/-!
# Section 3.2: the SNP pipeline in the model of Warnow, Tabatabaee and Evans

Section 3.2 of the paper runs CAMUS on the multiset `Q` of the quartets of the SNPs of an
alignment, with the constraint tree `T` returned by ASTRAL on `Q` and rooted at the outgroup, and
argues that this pipeline is statistically consistent when the sites evolve under the model of
Warnow, Tabatabaee and Evans (2025) ("WTE"; `External.SiteModel`) on the true network `N` and some
tree `t` displayed by `N` induces the most probable quartet on every four taxa. The argument has
three steps:

1. ASTRAL returns `t`, with probability tending to 1 (`astral_tendsto`,
   `astral_maximizer_tendsto` in `Camus/Pipelines/Astral.lean`, up to the classical fact that a
   binary tree is determined by its quartets);
2. "According to the theory given in Warnow et al. (2025)", the support of `Q` is `Q(N_r)`, with
   probability tending to 1 (`External.support_tendsto`);
3. "When Q is a multi-set version of Q(Nr), then CAMUS will add the correct reticulations and
   return N, since this is the unique network that can satisfy all the quartets in Q(Nr)".

Step 3 is false (the report's E6). This file proves its corrected form inside WTE's model: if `N`
is built on `t` and identifiable under inclusion, every network built on `t` that is optimal for
`Q_m` with the fewest reticulations among the optimal networks is isomorphic to `N`, with
probability tending to 1 (`snp_recovery_tendsto`); this is `correctedStatisticalConsistency`
with its hypothesis `support_convergence` proved (`snp_correctedStatisticalConsistency`). Without
identifiability under inclusion the conclusion fails, even with the tie-break: for the true
network `Counterexamples.shallowNet` and every site model on it, the network
`Counterexamples.deepNet`, which is not isomorphic to it, is optimal with the fewest
reticulations with probability tending to 1 (`snp_deeperDonor_tendsto`). Under some site model the
example also meets the paper's condition on `t` (`Counterexamples.deeperDonor_meets_hypotheses`
in `Camus/Pipelines/SNPCondition.lean`). The model assumes `p(e, s, s) > 0` on the tree edges
(`External.SiteModel`), which step 2 needs and WTE's constraints do not give
(`External.theorem6_step_needs_stay`).

## Main results

* `snp_recovery_tendsto`: step 3, corrected, in WTE's model.
* `snp_output_tendsto`: the same for any selection of an optimal network with the fewest
  reticulations.
* `snp_correctedStatisticalConsistency`: `correctedStatisticalConsistency` for the SNP multisets,
  without the hypothesis `support_convergence`.
* `snp_deeperDonor_tendsto`: E6 in WTE's model.

## Proof

On the event that the quartets of `Q_m` are exactly those displayed by `N`, whose probability
tends to 1 (`External.support_tendsto`), the corrected step 3 holds by `recovery`, and the
counterexample by `Counterexamples.deepNet_optimal_fewest` and
`Counterexamples.deep_not_iso_shallow`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace Camus

open DynamicProgramming

variable {σ : Type*} [Fintype σ] [DecidableEq σ] [Nontrivial σ] {Ω : Type*} [MeasurableSpace Ω]

/-- Section 3.2, step 3 corrected, in WTE's model. Let the true network `N` be built on the tree
`t` and be identifiable under inclusion (as in `recovery`), and let the sites `X 0, X 1, ...` be
independent with the law of a site under a model `M` on `N` with at least two states. Then the
probability that every network built on `t` that displays as many quartets of `Q_m` as any
network built on `t`, and has the fewest reticulations among those, is isomorphic to `N` tends
to 1. -/
theorem snp_recovery_tendsto (t : PhyloTree) (N : RootedNetwork) (hN : N.AnchoredExtension t)
    (identifiable : ∀ P : RootedNetwork, P.AnchoredExtension t →
      (∀ q, N.DisplaysQuartet q → P.DisplaysQuartet q) →
      P.reticulationCount ≤ N.reticulationCount → Nonempty (P.Iso N))
    (M : External.SiteModel N σ) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → External.SiteHistory N σ) (hind : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (hlaw : μ.map (X 0) = M.law hN.1) :
    Tendsto (fun m => μ {ω | ∀ P : RootedNetwork, P.AnchoredExtension t →
      (∀ R : RootedNetwork, R.AnchoredExtension t →
        score (External.sampleQuartets X m ω) (repertoire (External.sampleQuartets X m ω) R) ≤
          score (External.sampleQuartets X m ω) (repertoire (External.sampleQuartets X m ω) P)) →
      (∀ R : RootedNetwork, R.AnchoredExtension t →
        (∀ R' : RootedNetwork, R'.AnchoredExtension t →
          score (External.sampleQuartets X m ω) (repertoire (External.sampleQuartets X m ω) R') ≤
            score (External.sampleQuartets X m ω)
              (repertoire (External.sampleQuartets X m ω) R)) →
        P.reticulationCount ≤ R.reticulationCount) →
      Nonempty (P.Iso N)}) atTop (𝓝 1) := by
  -- step 2: the support of `Q_m` is `Q(N_r)` with probability tending to 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (External.support_tendsto M hN.1 X hind hid hlaw) tendsto_const_nhds
    (fun m => measure_mono fun ω hω => ?_) fun _ => prob_le_one
  -- step 3, corrected: on that event, `recovery`
  intro P hP optimal fewest
  exact recovery t N hN _ hω identifiable P hP optimal fewest

/-- Section 3.2, step 3 corrected, in WTE's model, for a selection rule: if `output m ω` is a
network built on `t` that displays as many quartets of `Q_m` as any network built on `t`, with the
fewest reticulations among those, then the probability that `output m` is isomorphic to `N` tends
to 1. -/
theorem snp_output_tendsto (t : PhyloTree) (N : RootedNetwork) (hN : N.AnchoredExtension t)
    (identifiable : ∀ P : RootedNetwork, P.AnchoredExtension t →
      (∀ q, N.DisplaysQuartet q → P.DisplaysQuartet q) →
      P.reticulationCount ≤ N.reticulationCount → Nonempty (P.Iso N))
    (M : External.SiteModel N σ) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → External.SiteHistory N σ) (hind : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (hlaw : μ.map (X 0) = M.law hN.1)
    (output : ℕ → Ω → RootedNetwork) (hout : ∀ m ω, (output m ω).AnchoredExtension t)
    (optimal : ∀ m ω, ∀ R : RootedNetwork, R.AnchoredExtension t →
      score (External.sampleQuartets X m ω) (repertoire (External.sampleQuartets X m ω) R) ≤
        score (External.sampleQuartets X m ω)
          (repertoire (External.sampleQuartets X m ω) (output m ω)))
    (fewest : ∀ m ω, ∀ R : RootedNetwork, R.AnchoredExtension t →
      (∀ R' : RootedNetwork, R'.AnchoredExtension t →
        score (External.sampleQuartets X m ω) (repertoire (External.sampleQuartets X m ω) R') ≤
          score (External.sampleQuartets X m ω) (repertoire (External.sampleQuartets X m ω) R)) →
      (output m ω).reticulationCount ≤ R.reticulationCount) :
    Tendsto (fun m => μ {ω | Nonempty ((output m ω).Iso N)}) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (snp_recovery_tendsto t N hN identifiable M X hind hid hlaw) tendsto_const_nhds
    (fun m => measure_mono fun ω hω => ?_) fun _ => prob_le_one
  exact hω _ (hout m ω) (optimal m ω) (fewest m ω)

/-- `correctedStatisticalConsistency` for the multisets `Q_m` of the SNP pipeline in WTE's model,
with its hypothesis `support_convergence` proved (`External.support_tendsto`). For a finite
family `C` of candidate networks whose member `truth` displays the quartets displayed by `N`,
identifiable under inclusion, every selection with the best score for `Q_m` and the fewest
reticulations among the best is equivalent to `truth` with probability tending to 1. -/
theorem snp_correctedStatisticalConsistency {Net : Type*} (N : RootedNetwork)
    (hN : N.RootedBinaryLevelOne) (C : Finset Net) (displayed : Net → Finset Quartet)
    (reticulations : Net → ℕ) (equivalent : Net → Net → Prop) (truth : Net)
    (truth_feasible : truth ∈ C)
    (truth_displayed : ∀ q, q ∈ displayed truth ↔ N.DisplaysQuartet q)
    (identifiable : IdentifiableUnderInclusion C displayed reticulations equivalent truth)
    (M : External.SiteModel N σ) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → External.SiteHistory N σ) (hind : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (hlaw : μ.map (X 0) = M.law hN)
    (selected : ℕ → Ω → Net)
    (optimal : ∀ m ω, Optimal C displayed (External.sampleQuartets X m ω) (selected m ω))
    (tie_break : ∀ m ω, FewestReticulations C displayed reticulations
      (External.sampleQuartets X m ω) (selected m ω)) :
    Tendsto (fun m => μ {ω | equivalent (selected m ω) truth}) atTop (𝓝 1) := by
  refine correctedStatisticalConsistency C displayed reticulations equivalent truth
    truth_feasible identifiable (fun _ => μ) (External.sampleQuartets X) selected ?_ optimal
    tie_break
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (External.support_tendsto M hN X hind hid hlaw) tendsto_const_nhds
    (fun m => measure_mono fun ω hω => ?_) fun _ => prob_le_one
  ext q
  rw [Multiset.mem_toFinset, hω q, truth_displayed q]

/-- Section 3.2, E6 in WTE's model: the conclusion "CAMUS will add the correct reticulations and
return N" fails with probability tending to 1, even with the tie-break toward the fewest
reticulations. Take for the true network `Counterexamples.shallowNet`, built on the six-leaf tree
`Counterexamples.donorTree`, any site model on it with at least two states, and independent sites
with its law. Then the probability that `Counterexamples.deepNet`, which is built on the same
tree and not isomorphic to the true network, displays as many quartets of `Q_m` as any network
built on the tree, with the fewest reticulations among those, tends to 1. -/
theorem snp_deeperDonor_tendsto (M : External.SiteModel Counterexamples.shallowNet σ)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → External.SiteHistory Counterexamples.shallowNet σ) (hind : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (hlaw : μ.map (X 0) = M.law Counterexamples.shallowNet_anchored.1) :
    Tendsto (fun m => μ {ω |
      (∀ R : RootedNetwork, R.AnchoredExtension Counterexamples.donorTree →
        score (External.sampleQuartets X m ω) (repertoire (External.sampleQuartets X m ω) R) ≤
          score (External.sampleQuartets X m ω)
            (repertoire (External.sampleQuartets X m ω) Counterexamples.deepNet)) ∧
      (∀ R : RootedNetwork, R.AnchoredExtension Counterexamples.donorTree →
        (∀ R' : RootedNetwork, R'.AnchoredExtension Counterexamples.donorTree →
          score (External.sampleQuartets X m ω) (repertoire (External.sampleQuartets X m ω) R') ≤
            score (External.sampleQuartets X m ω)
              (repertoire (External.sampleQuartets X m ω) R)) →
        Counterexamples.deepNet.reticulationCount ≤ R.reticulationCount) ∧
      IsEmpty (Counterexamples.deepNet.Iso Counterexamples.shallowNet)}) atTop (𝓝 1) := by
  -- step 2: the support of `Q_m` is `Q(N_r)` with probability tending to 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (External.support_tendsto M Counterexamples.shallowNet_anchored.1 X hind hid hlaw)
    tendsto_const_nhds (fun m => measure_mono fun ω hω => ?_) fun _ => prob_le_one
  -- on that event, the deeper donor is optimal with the fewest reticulations
  exact ⟨(Counterexamples.deepNet_optimal_fewest _ hω).1,
    (Counterexamples.deepNet_optimal_fewest _ hω).2, Counterexamples.deep_not_iso_shallow⟩

end Camus
