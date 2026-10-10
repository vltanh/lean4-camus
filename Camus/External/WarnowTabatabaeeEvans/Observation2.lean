module

public import Camus.Defs

/-!
# Observation 2 of Warnow, Tabatabaee and Evans

The paper's Lemma 1 "follows directly from Observation 2 in Warnow et al. (2025)". This file
states that observation as the proposition `WarnowTabatabaeeEvansObservation2`: a rooted binary
level-1 network displays a quartet if and only if deleting one cut edge, or two edges of one
cycle with at least one of them at the cycle's reticulation, separates its two sides. The project
does not prove it. The theorems that need it take it as a hypothesis, so the formalization is
conditional on it.
-/

@[expose] public section

namespace Camus.External

/-- Observation 2 of Tandy Warnow, Yasamin Tabatabaee and Steven N. Evans, "Advances in
Estimating Level-1 Phylogenetic Networks from Unrooted SNPs", J. Comput. Biol. 32(1):3–27, 2025,
doi:10.1089/cmb.2024.0710. Let `N` be a rooted binary level-1 network and `q` a quartet whose taxa
are taxa of `N`. Then `N` displays `q` (q ∈ Q(N_r)) if and only if the two sides of `q` are
separated by deleting either one cut edge of `N` (`RootedNetwork.CutEdgeSeparates`) or two
distinct edges of one cycle of `N`, at least one of them incident to the reticulation of that
cycle, its vertex of indegree 2 (`RootedNetwork.CycleSeparates`).

The project contains no proof of this proposition. It is assumed as a hypothesis by the theorems
that need it: Lemma 1, Theorem 1 and the results built on them. -/
def WarnowTabatabaeeEvansObservation2 : Prop :=
  ∀ N : RootedNetwork, N.RootedBinaryLevelOne →
    ∀ q : Quartet, q.taxa ⊆ N.taxa →
      (N.DisplaysQuartet q ↔ N.CutEdgeSeparates q ∨ N.CycleSeparates q)

end Camus.External
