module

public import Camus.Network.Cuts

/-!
# Displayed quartets by clades

A switching `S` of a rooted binary level-1 network `N` is a spanning tree of `N`, directed away
from the root. Deleting the edge `(x, y)` of `S` separates the taxa whose leaves lie below `y` in
`S` (`RootedNetwork.cladeBelow`) from the other taxa. So `N` displays the quartet `q`
(Definition 1) if and only if some switching `S` has an edge `(x, y)` whose clade below `y` cuts
`q`. The edge can be taken to enter a vertex that is not a reticulation: an edge into a
reticulation `y` cuts the same clade as the edge out of `y`.

## Main results

* `RootedNetwork.cladeBelow`: the clade below a vertex in a switching.
* `RootedNetwork.displays_iff_cladeBelow`: Definition 1 by clades.
* `RootedNetwork.displays_iff_treeEdge_cladeBelow`: the same, with an edge into a vertex of
  indegree 1.
-/

@[expose] public section

namespace Camus

namespace RootedNetwork

/-- The taxa whose leaves are reached from `y` by a directed path of edges of `S`. For a switching
`S` of `N`, this is the clade below `y` in the tree `S`: deleting the edge of `S` into `y`
separates it from the other taxa of `N`. -/
noncomputable def cladeBelow (N : RootedNetwork) (S : Finset (ℕ × ℕ)) (y : ℕ) : Finset ℕ := by
  classical
  exact N.taxa.filter fun a => Relation.ReflTransGen (fun u v => (u, v) ∈ S) y (N.leaf a)

/-- Definition 1 by clades: a rooted binary level-1 network `N` displays the quartet `q` if and
only if the taxa of `q` are taxa of `N` and, for some switching `S` of `N` and some edge `(x, y)`
of `S`, the clade below `y` in `S` cuts `q`. -/
theorem displays_iff_cladeBelow {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    (q : Quartet) :
    N.DisplaysQuartet q ↔ q.taxa ⊆ N.taxa ∧
      ∃ S, N.Switching S ∧ ∃ x y, (x, y) ∈ S ∧ q.cutBy (N.cladeBelow S y) = true := by
  sorry

/-- Definition 1 by clades of tree edges: as `displays_iff_cladeBelow`, with the edge `(x, y)`
entering a vertex `y` of indegree 1 (a tree vertex or a leaf), not a reticulation. -/
theorem displays_iff_treeEdge_cladeBelow {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    (q : Quartet) :
    N.DisplaysQuartet q ↔ q.taxa ⊆ N.taxa ∧
      ∃ S, N.Switching S ∧ ∃ x y, (x, y) ∈ S ∧ N.indegree y = 1 ∧
        q.cutBy (N.cladeBelow S y) = true := by
  sorry

end RootedNetwork

end Camus
