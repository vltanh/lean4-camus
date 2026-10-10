module

public import Camus.Restriction.Witness

/-!
# Section 2.4: the best score can decrease when the number of reticulations increases

Section 2.4 of the paper opens with: "By design, the score (the number of quartets in Q that are
satisfied) will never decrease as the number of reticulations increases", and then computes, for
each `k`, a best network with exactly `k` non-tree edges. For exact counts the claim is false
(the report's E5).

## Main results

* `ExactCountMonotone`: the claim, for exact numbers of reticulations: whenever `j ≤ k` and some
  network built on `T` has exactly `k` reticulations, every network built on `T` with exactly `j`
  reticulations is matched by one with exactly `k` that displays at least as many quartets of `Q`.
* `not_exactCountMonotone`: the claim fails. For `T = (A,(B,(D,C)))` and `Q = {AC|BD}`, a network with two
  reticulations displays `AC|BD`, while every network with three reticulations displays only the
  quartet of `T` (`Counterexamples.graph_exact_budget_nonmonotone`).

For "at most `k`" reticulations the claim holds trivially, since the feasible networks only grow
with `k` (`Camus.atMostScore_mono`).
-/

@[expose] public section

namespace Camus

open DynamicProgramming

/-- Section 2.4's monotonicity claim is false for exact numbers of reticulations (the report's
E5). For `T = (A,(B,(D,C)))` and
`Q = {AC|BD}`, some network built on `T` with two reticulations displays `AC|BD`, networks built on
`T` with three reticulations exist, and none of them displays `AC|BD`. -/
theorem not_exactCountMonotone :
    ¬ ExactCountMonotone := by
  intro h
  obtain ⟨⟨N, hN, hN2, hN1⟩, hthree, hzero⟩ :=
    Counterexamples.graph_exact_budget_nonmonotone
  obtain ⟨P, hP, hP3, hle⟩ :=
    h Counterexamples.smallConstraint (by decide) Counterexamples.oneQuartet 2 3 (by decide)
      hthree N hN hN2
  have := hzero P hP hP3
  omega

end Camus
