module

public import Camus.Pipelines.Recovery
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Order.Basic

/-!
# Section 3.2, corrected: recovery in probability

Section 3.2 of the paper argues that the SNP pipeline is statistically consistent: as the number of
sites grows, the constraint tree is a displayed tree of the true network `N` with probability
tending to 1, and, "according to the theory given in Warnow et al. (2025)", `Q` equals `Q(N_r)` as
a set with probability tending to 1; then CAMUS returns `N`. This file proves the last step in its
corrected form (`correctedConsistency`), in probability. The convergence of the support of `Q` is a
hypothesis; the estimation of `T` and `Q` by the pipeline is not formalized.

## Main results

* `correctedStatisticalConsistency`: if the probability that the support of the input is the set of
  quartets displayed by the true network tends to 1, so does the probability that the selected
  network is equivalent to the true network, under the hypotheses of `correctedConsistency`
  (identifiability under inclusion and the fewest-reticulations tie-break).
-/

@[expose] public section

namespace Camus

open scoped Topology
open MeasureTheory

/-- Section 3.2, corrected, in probability. For each `k`, let `μ k` be a probability measure on
`Ω`, and let `observations k ω` and `selected k ω` be the input multiset and the selected network.
Assume that `truth ∈ C` is identifiable under inclusion, that every `selected k ω` has the best
score for `observations k ω` with the fewest reticulations among the networks with the best score,
and that the probability that the support of `observations k` is the set of quartets displayed by
`truth` tends to 1 (`support_convergence`, the paper's appeal to Warnow et al. (2025)). Then the
probability that `selected k` is equivalent to `truth` tends to 1.

The paper's step, that the true network "is the unique network that can satisfy all the quartets
in Q(N_r)", is false (the report's E4); identifiability under inclusion and the tie-break replace
it. -/
theorem correctedStatisticalConsistency {α N Ω : Type*} [DecidableEq α]
    [MeasurableSpace Ω] (C : Finset N) (displayed : N → Finset α)
    (reticulations : N → ℕ) (equivalent : N → N → Prop) (truth : N)
    (truth_feasible : truth ∈ C)
    (identifiable : IdentifiableUnderInclusion C displayed reticulations equivalent truth)
    (μ : ℕ → Measure Ω) [∀ k, IsProbabilityMeasure (μ k)]
    (observations : ℕ → Ω → Multiset α) (selected : ℕ → Ω → N)
    (support_convergence : Filter.Tendsto
      (fun k => μ k {ω | (observations k ω).toFinset = displayed truth})
      Filter.atTop (𝓝 1))
    (optimal : ∀ k ω, Optimal C displayed (observations k ω) (selected k ω))
    (tie_break : ∀ k ω, FewestReticulations C displayed reticulations
      (observations k ω) (selected k ω)) :
    Filter.Tendsto (fun k => μ k {ω | equivalent (selected k ω) truth})
      Filter.atTop (𝓝 1) := by
  -- squeeze: the event of exact support is contained in the event of recovery
  -- (`correctedConsistency`), and probabilities are at most 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le support_convergence tendsto_const_nhds
  · intro k
    apply measure_mono
    intro ω hω
    exact correctedConsistency C displayed reticulations equivalent truth (selected k ω)
      truth_feasible (observations k ω) hω identifiable (optimal k ω) (tie_break k ω)
  · intro k
    exact prob_le_one

end Camus
