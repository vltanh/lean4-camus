module

public import Camus.Complexity

@[expose] public section

namespace Camus.Complexity

open DynamicProgramming

/-- The access-model specification is inhabited. This semantic oracle proves
consistency of its defining law; it asserts no execution-time bound. -/
noncomputable def semanticOracle (t : PhyloTree) (Q : Multiset Quartet) : DeltaOracle t Q := by
  classical
  exact ⟨fun e q => decide (q ∈ novel t Q (Realization.graph t {e})),
    fun _ _ _ _ => by simp⟩

/-- The source weight-preprocessing loop under the explicit quartet-test
access model. Each distinct observed topology is tested once and contributes
its stored multiplicity when the test succeeds. -/
def DeltaOracle.weight {t : PhyloTree} {Q : Multiset Quartet}
    (O : DeltaOracle t Q) (e : Pair) : ℕ :=
  ∑ q ∈ Q.toFinset, if O.test e q then Q.count q else 0

/-- The oracle's defining law identifies the costed weight-preprocessing
loop with the semantic Eq. 1 weight used by the optimizer. -/
theorem DeltaOracle.weight_eq {t : PhyloTree} {Q : Multiset Quartet}
    (O : DeltaOracle t Q) {e : Pair} (he : e ∈ EdgeAbove.candidates t) :
    O.weight e = edgeWeight t Q e := by
  classical
  unfold DeltaOracle.weight edgeWeight
  apply Finset.sum_congr rfl
  intro q hq
  have h := O.correct e he q hq
  by_cases hd : q ∈ novel t Q (Realization.graph t {e})
  · simp only [hd, ite_true, h.mpr hd]
  · have ht : O.test e q = false := Bool.eq_false_iff.mpr (fun hc => hd (h.mp hc))
    simp only [ht, Bool.false_eq_true, ite_false, hd]

/-- Precisely one quartet oracle query per candidate/topology pair is made
by the source preprocessing scan. This is the quartet-query summand in the
proved abstract operation schedule. -/
theorem weight_query_count (t : PhyloTree) (Q : Multiset Quartet) :
    ∑ _e ∈ EdgeAbove.candidates t, Q.toFinset.card =
      (EdgeAbove.candidates t ×ˢ Q.toFinset).card := by
  simp

end Camus.Complexity
