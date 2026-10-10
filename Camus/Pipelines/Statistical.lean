module

public import Camus.Pipelines.Recovery
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Order.Basic

@[expose] public section

namespace Camus

open scoped Topology
open MeasureTheory

/-- Statistical form of the corrected §3.2 theorem. The empirical-support event
has probability tending to one; deterministic recovery on this event forces the
recovery probability to tend to one as well. The support-convergence hypothesis
is stated explicitly, and is not asserted for unformalized biological models.

Departure from the paper: replaces its false automatic uniqueness step with
explicit inclusion-identifiability and minimum-reticulation tie-breaking (E4).
The probability squeeze is a consequence of this corrected deterministic step. -/
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
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le support_convergence tendsto_const_nhds
  · intro k
    apply measure_mono
    intro ω hω
    exact correctedConsistency C displayed reticulations equivalent truth (selected k ω)
      truth_feasible (observations k ω) hω identifiable (optimal k ω) (tie_break k ω)
  · intro k
    exact prob_le_one

end Camus
