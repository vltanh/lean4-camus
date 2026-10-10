module

public import Camus.Galled.Counterexamples
public import Camus.Network.Reticulations
public import Camus.Preliminaries.Lemmas

/-!
# Section 3.2: the true network is not the unique optimum

Section 3.2 of the paper concludes that CAMUS returns the true network `N` when `Q` is a multiset
version of `Q(N_r)`, "since this is the unique network that can satisfy all the quartets in
Q(N_r)". This is false (the report's E7). Take the five-leaf tree `T = (O,((B,A),(D,C)))`
(`Counterexamples.constraint`, with `A = 0`, `B = 1`, `C = 2`, `D = 3`, `O = 4`) as the true
network, and its five quartets as `Q` (`Counterexamples.data`). The network obtained by adding one
edge above `(A, C)` (`extraPair`) is built on `T`, so it displays the quartets of `T`
(`DynamicProgramming.baseline_subset`). Both networks display all of `Q`, the largest possible
score, and they have zero and one reticulations. Observation 2 is not used. The same example in the
block grammar is `Counterexamples.uniqueness_counterexample`; a corrected statement is
`correctedConsistency`.

## Main results

* `Counterexamples.graph_uniqueness_counterexample`: the two networks, their reticulations and
  their scores.
-/

@[expose] public section

namespace Camus.Counterexamples

open DynamicProgramming

/-- E7: the pair `(A, C)` of `T = (O,((B,A),(D,C)))`. The edge added above it has target
`((B,A),(D,C))`, and its cycle has five vertices. -/
def extraPair : Pair := ([true, false, true], [true, true, true])

/-- The leaf labels of `T = (O,((B,A),(D,C)))` are distinct. -/
theorem constraint_wellLabelled : constraint.WellLabelled := by decide

/-- The family `{extraPair}` is feasible. -/
theorem extraPair_separated : EdgeAbove.CycleSeparated constraint {extraPair} := by
  constructor
  · simpa only [Finset.singleton_subset_iff] using
      (show extraPair ∈ EdgeAbove.candidates constraint by decide)
  · simp

/-- The empty family is feasible. -/
theorem baseline_separated : EdgeAbove.CycleSeparated constraint ∅ := by
  simp [EdgeAbove.CycleSeparated]

/-- `T`, as a network with no added edge, displays every quartet of `data`. -/
theorem graphData_exact : DynamicProgramming.repertoire data (Realization.graph constraint ∅) =
    data.toFinset := by
  classical
  ext q
  simp only [DynamicProgramming.repertoire, Finset.mem_filter]
  constructor
  · exact fun h => h.1
  · intro hq
    exact ⟨hq, (Realization.baseline_displays_iff constraint constraint_wellLabelled q).mpr
      ((data_is_exact q).mpr (Multiset.mem_toFinset.mp hq))⟩

/-- E7 (Section 3.2): the tree `T = (O,((B,A),(D,C)))`, as a network with no added edge, and the
network obtained from `T` by adding one edge above `(A, C)` are both built on `T`, have zero and one
reticulations, and display all five quartets of `data`, the quartets of `T`. So the true network
`T` is not the unique network that displays all of `Q(N_r)`. -/
theorem graph_uniqueness_counterexample :
    (Realization.graph constraint ∅).AnchoredExtension constraint ∧
    (Realization.graph constraint {extraPair}).AnchoredExtension constraint ∧
    (Realization.graph constraint ∅).reticulationCount = 0 ∧
    (Realization.graph constraint {extraPair}).reticulationCount = 1 ∧
    score data (DynamicProgramming.repertoire data (Realization.graph constraint ∅)) = data.card ∧
    score data (DynamicProgramming.repertoire data (Realization.graph constraint {extraPair})) =
        data.card := by
  classical
  have ht := constraint_wellLabelled
  have hb := baseline_separated
  have he := extraPair_separated
  have hbase : score data (DynamicProgramming.repertoire data (Realization.graph constraint ∅)) =
      data.card := by
    apply (score_eq_card_iff data _).mpr
    rw [graphData_exact]
  have hextra : score data (DynamicProgramming.repertoire data (Realization.graph constraint
      {extraPair})) = data.card := by
    apply (score_eq_card_iff data _).mpr
    rw [← graphData_exact]
    exact baseline_subset constraint ht data {extraPair} he
  refine ⟨⟨Realization.levelOne constraint ht ∅ hb,
      ⟨Realization.supportEdges constraint ∅, ⟨Realization.support constraint ht ∅ hb⟩⟩⟩,
    ⟨Realization.levelOne constraint ht {extraPair} he,
      ⟨Realization.supportEdges constraint {extraPair}, ⟨Realization.support constraint ht
          {extraPair} he⟩⟩⟩,
    ?_, ?_, hbase, hextra⟩
  · simpa using Realization.reticulationCount_eq_card constraint ∅ hb
  · simpa using Realization.reticulationCount_eq_card constraint {extraPair} he

end Camus.Counterexamples
