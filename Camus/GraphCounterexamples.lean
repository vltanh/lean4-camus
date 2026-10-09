module

public import Camus.Counterexamples
public import Camus.ReticulationBudget
public import Camus.QuartetAttribution

@[expose] public section

namespace Camus.Counterexamples

open DynamicProgramming

/-- The same A→C witness as E4, now in the arbitrary directed-graph model. -/
def extraPair : Pair := ([true, false, true], [true, true, true])

theorem constraint_wellLabelled : constraint.WellLabelled := by decide

theorem extraPair_separated : EdgeAbove.CycleSeparated constraint {extraPair} := by
  constructor
  · simpa only [Finset.singleton_subset_iff] using
      (show extraPair ∈ EdgeAbove.candidates constraint by decide)
  · simp

theorem baseline_separated : EdgeAbove.CycleSeparated constraint ∅ := by
  simp [EdgeAbove.CycleSeparated]

theorem graphData_exact : DynamicProgramming.repertoire data (Realization.graph constraint ∅) = data.toFinset := by
  classical
  ext q
  simp only [DynamicProgramming.repertoire, Finset.mem_filter]
  constructor
  · exact fun h => h.1
  · intro hq
    exact ⟨hq, (Realization.baseline_displays_iff constraint constraint_wellLabelled q).mpr
      ((data_is_exact q).mpr (Multiset.mem_toFinset.mp hq))⟩

/-- E4 in actual rooted binary level-1 graphs: two feasible networks with
reticulation counts zero and one both attain all observed support. No cited
quartet characterization is used to certify this counterexample. -/
theorem graph_uniqueness_counterexample :
    (Realization.graph constraint ∅).AnchoredExtension constraint ∧
    (Realization.graph constraint {extraPair}).AnchoredExtension constraint ∧
    (Realization.graph constraint ∅).reticulationCount = 0 ∧
    (Realization.graph constraint {extraPair}).reticulationCount = 1 ∧
    score data (DynamicProgramming.repertoire data (Realization.graph constraint ∅)) = data.card ∧
    score data (DynamicProgramming.repertoire data (Realization.graph constraint {extraPair})) = data.card := by
  classical
  have ht := constraint_wellLabelled
  have hb := baseline_separated
  have he := extraPair_separated
  have hbase : score data (DynamicProgramming.repertoire data (Realization.graph constraint ∅)) = data.card := by
    apply (score_eq_card_iff data _).mpr
    rw [graphData_exact]
  have hextra : score data (DynamicProgramming.repertoire data (Realization.graph constraint {extraPair})) = data.card := by
    apply (score_eq_card_iff data _).mpr
    rw [← graphData_exact]
    exact baseline_subset constraint ht data {extraPair} he
  refine ⟨⟨Realization.levelOne constraint ht ∅ hb,
      ⟨Realization.supportEdges constraint ∅, ⟨Realization.support constraint ht ∅ hb⟩⟩⟩,
    ⟨Realization.levelOne constraint ht {extraPair} he,
      ⟨Realization.supportEdges constraint {extraPair}, ⟨Realization.support constraint ht {extraPair} he⟩⟩⟩,
    ?_, ?_, hbase, hextra⟩
  · simpa using Realization.reticulationCount_eq_card constraint ∅ hb
  · simpa using Realization.reticulationCount_eq_card constraint {extraPair} he

end Camus.Counterexamples
