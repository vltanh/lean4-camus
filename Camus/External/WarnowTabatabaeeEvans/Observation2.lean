module

public import Camus.Defs

@[expose] public section

namespace Camus.External

/-- Observation 2 of Warnow–Tabatabaee–Evans (2025), DOI
10.1089/cmb.2024.0710: a displayed quartet is separated by deleting either a
cut edge or two edges of one cycle, one incident to its bottom reticulation.

This is a named, UNPROVED proposition. It may be an explicit hypothesis of
conditional theorems, as authorized by the user. It does not assert
unique attribution to an added edge and does not assume the CAMUS DP
decomposition. The
project proves graph decomposition and quartet attribution independently; only
this displayed-quartet characterization is assumed. -/
def WarnowTabatabaeeEvansObservation2 : Prop :=
  ∀ N : RootedNetwork, N.RootedBinaryLevelOne →
    ∀ q : Quartet, q.taxa ⊆ N.taxa →
      (N.DisplaysQuartet q ↔ N.CutEdgeSeparates q ∨ N.CycleSeparates q)

end Camus.External
