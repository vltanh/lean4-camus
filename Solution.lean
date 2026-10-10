module

public import Camus.DP.Theorem1
public import Camus.Restriction.Main
public import Camus.Restriction.Monotonicity
public import Camus.Pipelines.Uniqueness

/-!
# The statements of record, proved

This file restates every theorem of `Challenge.lean`, word for word, and proves it from the
library: Theorem 1 (`Camus.theorem1`), the existence of the array and of a trace
(`DynamicProgramming.exists_array_trace`), the display of the tree
(`Realization.baseline_displays_iff`), Equation (1) (`DynamicProgramming.edgeWeight_score`),
Section 2.4 (`BudgetDP.reticulation_restriction`, `BudgetDP.exists_array`,
`Camus.not_exactCountMonotone`) and Section 3.2 (`Camus.not_uniqueOptimum`, `Camus.recovery`,
`Camus.tree_identifiable`). Comparator checks that these statements are those of the Challenge.
-/

@[expose] public section

namespace Camus.Challenge

open DynamicProgramming

/-- **Theorem 1.** Let `T` be a well-labelled tree and `Q` a multiset of quartets. For every `M`
satisfying the recurrence of Equations (2)–(5) with the weights of Equation (1), and every family
`E` obtained by backtracking through `M` from the root, the network obtained from `T` by adding the
edges of `E` is built on `T` and satisfies `M[root]` quartets of `Q` (with multiplicity); no network
built on `T` satisfies more, or displays more quartets of `Q`. -/
theorem theorem1 (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (M : Address → ℕ) (hM : DynamicProgramming.Array t (edgeWeight t Q) M)
    (E : Finset Pair) (trace : Trace t (edgeWeight t Q) M [] E) :
    (Realization.graph t E).AnchoredExtension t ∧
      score Q (novel t Q (Realization.graph t E)) = M [] ∧
      (∀ N : RootedNetwork, N.AnchoredExtension t →
        score Q (novel t Q N) ≤ score Q (novel t Q (Realization.graph t E))) ∧
      (∀ N : RootedNetwork, N.AnchoredExtension t →
        score Q (repertoire Q N) ≤ score Q (repertoire Q (Realization.graph t E))) := by
  exact Camus.theorem1 t ht Q M hM E trace

/-- The hypotheses of `theorem1` can be met: for every tree and all weights, the recurrence has a
solution and a backtracking trace from the root. -/
theorem exists_array_trace (t : PhyloTree) (w : Pair → ℕ) :
    ∃ M, DynamicProgramming.Array t w M ∧ ∃ E, Trace t w M [] E := by
  exact DynamicProgramming.exists_array_trace t w

/-- The tree `T`, as the network with no added edge, displays exactly the quartets of `T`. -/
theorem tree_displays_iff (t : PhyloTree) (ht : t.WellLabelled) (q : Quartet) :
    (Realization.graph t ∅).DisplaysQuartet q ↔ q.induced t = true := by
  exact Realization.baseline_displays_iff t ht q

/-- Equation (1): the weight of a pair `e` is the number of quartets of `Q`, with multiplicity,
satisfied by the network obtained from `T` by adding the edge above `e`. -/
theorem edgeWeight_eq (t : PhyloTree) (Q : Multiset Quartet) (e : Pair) :
    edgeWeight t Q e = score Q (novel t Q (Realization.graph t {e})) := by
  exact DynamicProgramming.edgeWeight_score t Q e

/-- **Section 2.4.** Let `M` satisfy the modified recurrence with the weights of Equation (1). For
every `k`, the row `k` at the root is nonempty if and only if some network built on `T` has exactly
`k` reticulations; and each value `z` in it is the number of quartets of `Q` satisfied by a network
built on `T` with exactly `k` reticulations, which satisfies at least as many quartets of `Q`, and
displays at least as many, as every network built on `T` with exactly `k` reticulations. -/
theorem reticulation_restriction (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (M : Address → ℕ → Finset ℕ) (hM : BudgetDP.Array t (edgeWeight t Q) M) (k : ℕ) :
    ((M [] k).Nonempty ↔
        ∃ N : RootedNetwork, N.AnchoredExtension t ∧ N.reticulationCount = k) ∧
      ∀ z ∈ M [] k, ∃ E : Finset Pair,
        (Realization.graph t E).AnchoredExtension t ∧
        (Realization.graph t E).reticulationCount = k ∧
        score Q (novel t Q (Realization.graph t E)) = z ∧
        (∀ N : RootedNetwork, N.AnchoredExtension t → N.reticulationCount = k →
          score Q (novel t Q N) ≤ z) ∧
        (∀ N : RootedNetwork, N.AnchoredExtension t → N.reticulationCount = k →
          score Q (repertoire Q N) ≤ score Q (repertoire Q (Realization.graph t E))) := by
  exact BudgetDP.reticulation_restriction t ht Q M hM k

/-- The modified recurrence of Section 2.4 has a solution, for every tree and all weights. -/
theorem exists_budgetArray (t : PhyloTree) (w : Pair → ℕ) : ∃ M, BudgetDP.Array t w M := by
  exact BudgetDP.exists_array t w

/-- **Section 2.4.** The claim that the score "will never decrease as the number of reticulations
increases" is false for exact numbers of reticulations. -/
theorem not_exactCountMonotone : ¬ ExactCountMonotone := by
  exact Camus.not_exactCountMonotone

/-- **Section 3.2.** The claim that the true network is the unique optimal network built on the
constraint tree, when `Q` is a multiset version of the set of quartets it displays, is false. -/
theorem not_uniqueOptimum : ¬ UniqueOptimum := by
  exact Camus.not_uniqueOptimum

/-- **Section 3.2, corrected.** Let `N` be built on `t`, and let the quartets of `Q` be exactly
those that `N` displays. If `N` is identifiable under inclusion (every network built on `t` that
displays every quartet that `N` displays, with no more reticulations than `N`, is isomorphic to
`N`), then every network built on `t` that displays as many quartets of `Q` as any network built on
`t`, and has the fewest reticulations among such networks, is isomorphic to `N`. -/
theorem recovery (t : PhyloTree) (N : RootedNetwork) (hN : N.AnchoredExtension t)
    (Q : Multiset Quartet) (hQ : ∀ q, q ∈ Q ↔ N.DisplaysQuartet q)
    (identifiable : ∀ P : RootedNetwork, P.AnchoredExtension t →
      (∀ q, N.DisplaysQuartet q → P.DisplaysQuartet q) →
      P.reticulationCount ≤ N.reticulationCount → Nonempty (P.Iso N))
    (P : RootedNetwork) (hP : P.AnchoredExtension t)
    (optimal : ∀ R : RootedNetwork, R.AnchoredExtension t →
      score Q (repertoire Q R) ≤ score Q (repertoire Q P))
    (fewest : ∀ R : RootedNetwork, R.AnchoredExtension t →
      (∀ R' : RootedNetwork, R'.AnchoredExtension t →
        score Q (repertoire Q R') ≤ score Q (repertoire Q R)) →
      P.reticulationCount ≤ R.reticulationCount) :
    Nonempty (P.Iso N) := by
  exact Camus.recovery t N hN Q hQ identifiable P hP optimal fewest

/-- The tree `T`, as the network with no added edge, is identifiable under inclusion among the
networks built on `T`: the hypothesis `identifiable` of `recovery` holds for it. -/
theorem tree_identifiable (t : PhyloTree) (ht : t.WellLabelled) :
    ∀ P : RootedNetwork, P.AnchoredExtension t →
      (∀ q, (Realization.graph t ∅).DisplaysQuartet q → P.DisplaysQuartet q) →
      P.reticulationCount ≤ (Realization.graph t ∅).reticulationCount →
      Nonempty (P.Iso (Realization.graph t ∅)) := by
  exact Camus.tree_identifiable t ht

end Camus.Challenge
