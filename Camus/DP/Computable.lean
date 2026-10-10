module

public import Camus.Network.SingleEdge
public import Camus.DP.Correctness

/-!
# The recurrence of Section 2.2, computably

The weights `s_e(u, w)` of Equation (1) and the values `s(v)` of Equation (3) are defined through
the displayed quartets of networks, which are not computable as such. With the clades of the tree
`T'` displayed by `T + e` (`DynamicProgramming.edgeWeight_eq_satisfies`) and the hanging subtrees of
a cycle (`DynamicProgramming.hanging_score`), `s(v)` is a finite expression that `decide` can
evaluate on a concrete input. This is how `Counterexamples.camus_may_return_deep` checks a solution
of the recurrence.

## Main results

* `DynamicProgramming.s_edgeWeight_eq`: Equation (3) with the weights of Equation (1), computably.
-/

@[expose] public section

namespace Camus.DynamicProgramming

/-- **Equation (3)** (`E3`), computably: for a well-labelled `T`, s(v) with the weights `s_e` of
Equation (1) is the largest value, over the pairs `e` with target `v`, of the number of quartets of
`Q` satisfied by the edge added above `e` (`EdgeAbove.satisfies`), counted with multiplicity, plus
the values of `M` on the roots of the subtrees hanging off the cycle of `e`
(Equations (4) and (5)). -/
theorem s_edgeWeight_eq (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (M : Address → ℕ) (v : Address) :
    s t (edgeWeight t Q) M v = (pairsAt t v).sup fun e =>
      (∑ q ∈ Q.toFinset, if EdgeAbove.satisfies t e q = true then Q.count q else 0) +
        ∑ r ∈ hanging t e, M r := by
  unfold s
  apply Finset.sup_congr rfl
  intro e he
  have hc : e ∈ EdgeAbove.candidates t := (Finset.mem_filter.mp he).1
  rw [edgeWeight_eq_satisfies ht hc, hanging_score t M e (Finset.mem_filter.mp hc).2]

end Camus.DynamicProgramming
