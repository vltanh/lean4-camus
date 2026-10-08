module

public import Camus.Realization
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace Camus

namespace RootedNetwork

theorem Iso.displays_iff {N P : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) (hP : P.RootedBinaryLevelOne)
    (i : N.Iso P) (q : Quartet) : N.DisplaysQuartet q ↔ P.DisplaysQuartet q := by
  sorry

end RootedNetwork

theorem GraphSubdivision.displays_iff {P N : RootedNetwork}
    (hP : P.RootedBinaryLevelOne) (H : GraphSubdivision P N) (q : Quartet) :
    N.DisplaysQuartet q ↔ P.DisplaysQuartet q := by
  sorry

end Camus
