module

public import Camus.GraphRealization
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace Camus

namespace SupportSubdivision

/-- Completeness, part 1: extract admissible pairs whose original cycle
footprints are disjoint from every actual rooted level-1 support extension. -/
theorem extracted_separated {t : PhyloTree} (ht : t.WellLabelled)
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) :
    EdgeAbove.CycleSeparated t H.extracted := by
  sorry

/-- Distinct deleted edges cannot contract to the same ordered pair. -/
theorem pairOf_injective {t : PhyloTree} (ht : t.WellLabelled)
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) :
    Set.InjOn H.pairOf (N.edges \ S) := by
  sorry

/-- Completeness, part 2: canonical realization recovers the arbitrary graph,
including the forced order on any shared subdivided wire. -/
theorem canonical_iso {t : PhyloTree} (ht : t.WellLabelled)
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) :
    Nonempty (N.Iso (Realization.graph t H.extracted)) := by
  sorry

/-- Definition 1's deletion/suppression bridge: retain the selected non-tree
edge, delete the others, then suppress their unary endpoints. -/
theorem single_edge_reduction {t : PhyloTree} (ht : t.WellLabelled)
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S)
    {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    Nonempty (GraphSubdivision (Realization.graph t {H.pairOf e})
      {N with edges := insert e S}) := by
  sorry

end SupportSubdivision

end Camus
