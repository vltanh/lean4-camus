module

public import Camus.DynamicProgramming

@[expose] public section

namespace Camus.DynamicProgramming

/-- The actual decomposition and strong-induction argument of Theorem 1 for
weighted cycle footprints. No decomposition or optimality hypothesis is added.
The graph bridge and Lemma 1 turn these weights into the paper's quartet score. -/
theorem trace_optimal (t : PhyloTree) (weight : Pair → ℕ) (M : Address → ℕ)
    (hM : Array t weight M) {v : Address} {E : Finset Pair}
    (hv : v ∈ t.nodes) (trace : Trace t weight M v E) :
    FeasibleBelow t v E ∧ value weight E = M v ∧
      ∀ F, FeasibleBelow t v F → value weight F ≤ M v := by
  sorry

/-- The bottom-up recurrence and backtracking have an instance for every
nonnegative weight function; the main algorithm statement is not vacuous. -/
theorem exists_array_trace (t : PhyloTree) (weight : Pair → ℕ) :
    ∃ M, Array t weight M ∧ ∃ E, Trace t weight M [] E := by
  sorry

/-- Equation (4): cross-branch cycle, with children interpreted in the actual
subdivided single-edge graph. The selected off-cycle child is an original node. -/
theorem equation4 (t : PhyloTree) (M : Address → ℕ) (e : Pair)
    (hcross : EdgeAbove.target e ≠ e.1) :
    sdp t M e = M e.2 + M e.1 +
      ∑ x ∈ (EdgeAbove.footprint t e).erase (EdgeAbove.target e),
        M (Realization.offChild t e x) := by
  simp only [sdp, hcross, ↓reduceIte, sdpCross]

/-- Equation (5): a ghost donor includes the target's off-cycle child in the
sum and omits the donor subtree, which contains the whole cycle. -/
theorem equation5 (t : PhyloTree) (M : Address → ℕ) (e : Pair)
    (hghost : EdgeAbove.target e = e.1) :
    sdp t M e = M e.2 + ∑ x ∈ EdgeAbove.footprint t e,
      M (Realization.offChild t e x) := by
  simp only [sdp, hghost, ↓reduceIte, sdpGhost]

/-- The forest partition converts the literal Equations 4–5 to the independent
hanging subproblems used in the induction. Both case formulas are used. -/
theorem hanging_score (t : PhyloTree) (M : Address → ℕ) (e : Pair)
    (he : EdgeAbove.Admissible t e) :
    sdp t M e = ∑ r ∈ hanging t e, M r := by
  sorry

end Camus.DynamicProgramming
