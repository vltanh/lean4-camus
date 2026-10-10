module

public import Camus.Complexity.Operations

/-!
# Section 2.3: the quartet oracle and Equation (1)

Section 2.3 computes the weight `s_e(u, w)` of Equation (1) for every candidate pair `(u, w)` in a
preprocessing step, with one `O(1)` test of `δ_T(q, (u, w))` per distinct quartet `q` of `Q`. With
the quartet test as the abstract unit-cost oracle `DeltaOracle`, this file shows that such an oracle
exists, that the scan computes Equation (1), and that the scans make one query per candidate pair
and distinct quartet, the summand `|candidates| · |Q|` of `scalarOperations`. As in
`Camus/Complexity/Operations.lean`, this accounts for the paper's analysis; no implementation is
modelled.

## Main results

* `Complexity.semanticOracle`: an oracle exists.
* `Complexity.DeltaOracle.weight_eq`: the scan computes the weight of Equation (1).
* `Complexity.weight_query_count`: the scans make `|candidates| · |Q|` queries.
-/

@[expose] public section

namespace Camus.Complexity

open DynamicProgramming

/-- An oracle exists: the test that decides directly whether `q` is satisfied by the edge added
above `e`. It is defined from the specification of `DeltaOracle` and is not computable. -/
noncomputable def semanticOracle (t : PhyloTree) (Q : Multiset Quartet) : DeltaOracle t Q := by
  classical
  exact ⟨fun e q => decide (q ∈ novel t Q (Realization.graph t {e})),
    fun _ _ _ _ => by simp⟩

/-- Section 2.3: the weight preprocessing for one candidate pair `e`. Each distinct quartet of `Q`
is tested once and contributes its multiplicity when the test accepts it. This is the same sum as
`oracleWeight`. -/
def DeltaOracle.weight {t : PhyloTree} {Q : Multiset Quartet}
    (O : DeltaOracle t Q) (e : Pair) : ℕ :=
  ∑ q ∈ Q.toFinset, if O.test e q then Q.count q else 0

/-- The weight preprocessing computes Equation (1): `O.weight e = edgeWeight t Q e`, the weight used
by the dynamic program, for every candidate pair `e`. -/
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

/-- The weight preprocessing makes one query per candidate pair and distinct quartet of `Q`: the
summand `(EdgeAbove.candidates t ×ˢ Q.toFinset).card` of `scalarOperations`. -/
theorem weight_query_count (t : PhyloTree) (Q : Multiset Quartet) :
    ∑ _e ∈ EdgeAbove.candidates t, Q.toFinset.card =
      (EdgeAbove.candidates t ×ˢ Q.toFinset).card := by
  simp

end Camus.Complexity
