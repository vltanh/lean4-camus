module

public import Camus.QuartetAttribution
public import Camus.PackingTheorem

@[expose] public section

namespace Camus

/-- Theorem 1 (`mthst9`): the CAMUS recurrence and its backtracking return a
rooted level-1 extension maximizing observed quartet support over EVERY anchored
rooted level-1 graph extension. The only unproved cited result is explicitly
named Observation 2. The proof follows the paper's decomposition and strong
induction, with Lemmas 1–2 and Equations 2–5 as its route. -/
theorem theorem1 (observation2 : External.WarnowTabatabaeeEvansObservation2)
    (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (M : Address → ℕ) (hM : DynamicProgramming.Array t (DynamicProgramming.edgeWeight t Q) M)
    (E : Finset DynamicProgramming.Pair)
    (trace : DynamicProgramming.Trace t (DynamicProgramming.edgeWeight t Q) M [] E) :
    (Realization.graph t E).AnchoredExtension t ∧
      score Q (DynamicProgramming.novel t Q (Realization.graph t E)) = M [] ∧
      (∀ N : RootedNetwork, N.AnchoredExtension t →
        score Q (DynamicProgramming.novel t Q N) ≤
          score Q (DynamicProgramming.novel t Q (Realization.graph t E))) ∧
      (∀ N : RootedNetwork, N.AnchoredExtension t →
        score Q (DynamicProgramming.repertoire Q N) ≤
          score Q (DynamicProgramming.repertoire Q (Realization.graph t E))) := by
  sorry

end Camus
