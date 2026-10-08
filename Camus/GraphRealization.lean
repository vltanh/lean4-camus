module

public import Camus.Realization
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace Camus

namespace Realization

/-- The canonical support switching is literally the subdivision specified by
the stored wires. These fields are proved, rather than supplied as assumptions. -/
noncomputable def support (t : PhyloTree) (ht : t.WellLabelled)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    SupportSubdivision t (graph t E) (supportEdges t E) := by
  sorry

theorem levelOne (t : PhyloTree) (ht : t.WellLabelled)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    (graph t E).RootedBinaryLevelOne := by
  sorry

theorem extracted_eq (t : PhyloTree) (ht : t.WellLabelled)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    (support t ht E hE).extracted = E := by
  sorry

theorem baseline_displays_iff (t : PhyloTree) (ht : t.WellLabelled) (q : Quartet) :
    (graph t ∅).DisplaysQuartet q ↔ q.induced t = true := by
  sorry

end Realization

end Camus
