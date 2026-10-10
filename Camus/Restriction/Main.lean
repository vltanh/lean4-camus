module

public import Camus.Restriction.Optimality
public import Camus.Restriction.Construction

/-!
# Section 2.4: the reticulation restriction, for networks

Section 2.4 of the paper modifies the dynamic program so that it returns, for each number `k` of
added edges, a level-1 network `N_k` that contains the constraint tree `T`, has exactly `k`
non-tree edges, and displays as many quartets of `Q` as possible among such networks. In the
formalization the modified array `M[v][k]` (`BudgetDP.Array`) has, at every vertex `v` and budget
`k`, an empty row when no family of `k` added edges below `v` is feasible, and otherwise the
singleton of the best value.

## Main results

* `BudgetDP.root_row_nonempty_iff`: the row of budget `k` at the root is nonempty if and only if
  some network built on `T` has exactly `k` reticulations.
* `BudgetDP.reticulation_restriction`: Section 2.4's claim. For every budget `k`, the row at the
  root is nonempty exactly when `k` reticulations are possible, and then its value is attained by
  a network built on `T` with exactly `k` reticulations, which satisfies at least as many quartets
  of `Q` as every network built on `T` with `k` reticulations.
-/

@[expose] public section

namespace Camus.BudgetDP

open DynamicProgramming

/-- Section 2.4: the row of budget `k` at the root of `T` is nonempty if and only if some network
built on `T` has exactly `k` reticulations. Rows of impossible budgets are empty, rather than
holding the value `0`. -/
theorem root_row_nonempty_iff (t : PhyloTree) (ht : t.WellLabelled) (w : Pair → ℕ)
    (M : Address → ℕ → Finset ℕ) (hM : Array t w M) (k : ℕ) :
    (M [] k).Nonempty ↔
      ∃ N : RootedNetwork, N.AnchoredExtension t ∧ N.reticulationCount = k := by
  rw [row_nonempty_iff t w M hM t.root_mem_nodes k]
  constructor
  · -- a feasible family of `k` pairs gives its canonical network
    rintro ⟨E, hE, hEk⟩
    exact ⟨Realization.graph t E, ⟨Realization.levelOne t ht E hE.1,
      ⟨Realization.supportEdges t E, ⟨Realization.support t ht E hE.1⟩⟩⟩,
      (Realization.reticulationCount_eq_card t E hE.1).trans hEk⟩
  · -- a network built on `T` is isomorphic to the canonical network of its pairs
    rintro ⟨N, hN, hNk⟩
    obtain ⟨S, ⟨H⟩⟩ := hN.2
    have hF := H.extracted_separated hN.1
    obtain ⟨i⟩ := H.canonical_iso hN.1
    refine ⟨H.extracted, ⟨hF, fun _ _ => List.nil_prefix⟩, ?_⟩
    rw [← Realization.reticulationCount_eq_card t H.extracted hF,
      ← i.reticulationCount_eq hN.1 (Realization.levelOne t ht H.extracted hF), hNk]

/-- Section 2.4: the reticulation restriction. Let `M` satisfy the budget recurrence with the
weights of Equation (1). For every `k`, the row of budget `k` at the root is nonempty if and only
if some network built on `T` has exactly `k` reticulations; and every value `z` in that row is the
number of quartets of `Q` (with multiplicity) satisfied by a network built on `T` with exactly `k`
reticulations, which satisfies at least as many quartets of `Q`, and displays at least as many, as
every network built on `T` with exactly `k` reticulations. -/
theorem reticulation_restriction
    (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (M : Address → ℕ → Finset ℕ) (hM : Array t (edgeWeight t Q) M) (k : ℕ) :
    ((M [] k).Nonempty ↔
        ∃ N : RootedNetwork, N.AnchoredExtension t ∧ N.reticulationCount = k) ∧
      ∀ z ∈ M [] k, ∃ E : Finset Pair,
        (Realization.graph t E).AnchoredExtension t ∧
        (Realization.graph t E).reticulationCount = k ∧
        score Q (novel t Q (Realization.graph t E)) = z ∧
        (∀ N : RootedNetwork, N.AnchoredExtension t → N.reticulationCount = k →
          score Q (novel t Q N) ≤ z) ∧
        (∀ N : RootedNetwork, N.AnchoredExtension t → N.reticulationCount = k →
          score Q (repertoire Q N) ≤ score Q (repertoire Q (Realization.graph t E))) :=
  ⟨root_row_nonempty_iff t ht (edgeWeight t Q) M hM k,
    fun _ hz => exact_graph_optimal t ht Q M hM hz⟩

end Camus.BudgetDP
