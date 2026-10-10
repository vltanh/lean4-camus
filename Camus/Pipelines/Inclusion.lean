module

public import Camus.Network.SingleEdge
public import Camus.Pipelines.Uniqueness

/-!
# Section 3.2: identifiability under inclusion fails, even for cycles of length at least five

The corrected recovery theorem (`recovery`) assumes that the true network `N` is identifiable under
inclusion: every network built on `t` that displays all the quartets of `N`, with no more
reticulations, is isomorphic to `N`. This hypothesis fails in general, even when every cycle has at
least five vertices (the condition under which Warnow, Tabatabaee and Evans recover a level-1
network from its quartets), and the tie-break toward the fewest reticulations does not help.

Take the six-leaf tree `T = ((A,B),(C,(F,(D,E))))` (`Counterexamples.donorTree`), and add one edge
from above the cherry `(D,E)` to above `A` (`shallowNet`), or from above `D` to above `A`
(`deepNet`). Moving the donor down the tree keeps every quartet that the first edge satisfies: the
second network displays every quartet that the first displays, and one more (`AD|EF`). Both have
one reticulation, and their cycles have six and seven vertices. So if `Q` is a multiset version of
`Q(N_r)` for the true network `N = shallowNet`, the network `deepNet` displays all of `Q` with the
fewest reticulations possible, and is not isomorphic to `N`.

## Main results

* `Counterexamples.shallow_subset_deep`: the inclusion of displayed quartets.
* `Counterexamples.deep_not_iso_shallow`: the two networks are not isomorphic.
* `Counterexamples.deepNet_optimal_fewest`: `deepNet` is optimal for every multiset version of
  `Q(N_r)`, with the fewest reticulations among the optimal networks.
* `Counterexamples.shallow_not_identifiable`: the hypothesis `identifiable` of `recovery` fails.
-/

@[expose] public section

namespace Camus.Counterexamples

open DynamicProgramming

/-- The six-leaf tree `((A,B),(C,(F,(D,E))))`, with `A = 0`, `B = 1`, `C = 2`, `D = 3`, `E = 4`,
`F = 5`. -/
def donorTree : PhyloTree :=
  .fork (.fork (.leaf 0) (.leaf 1))
    (.fork (.leaf 2) (.fork (.leaf 5) (.fork (.leaf 3) (.leaf 4))))

/-- The pair `((D,E), A)`: an edge from above the cherry `(D,E)` to above `A`. Its target is the
root, and its cycle has six vertices. -/
def shallowPair : Pair := ([true, true, true], [false, false])

/-- The pair `(D, A)`: an edge from above `D` to above `A`. Its donor `D` lies below the donor
`(D,E)` of `shallowPair`; its cycle has seven vertices. -/
def deepPair : Pair := ([true, true, true, false], [false, false])

/-- The network `T + ((D,E), A)`, the true network of the example. -/
noncomputable abbrev shallowNet : RootedNetwork := Realization.graph donorTree {shallowPair}

/-- The network `T + (D, A)`. -/
noncomputable abbrev deepNet : RootedNetwork := Realization.graph donorTree {deepPair}

/-- The quartet `AD|EF`, displayed by `deepNet` and not by `shallowNet`. -/
def witnessQuartet : Quartet := ⟨0, 3, 4, 5, by decide, by decide, by decide, 0⟩

/-- The leaf labels of `((A,B),(C,(F,(D,E))))` are distinct. -/
theorem donorTree_wellLabelled : donorTree.WellLabelled := by decide

/-- `shallowNet` is built on `T`. -/
theorem shallowNet_anchored : shallowNet.AnchoredExtension donorTree := by
  sorry

/-- `deepNet` is built on `T`. -/
theorem deepNet_anchored : deepNet.AnchoredExtension donorTree := by
  sorry

/-- `shallowNet` has one reticulation. -/
theorem shallowNet_reticulations : shallowNet.reticulationCount = 1 := by
  sorry

/-- `deepNet` has one reticulation. -/
theorem deepNet_reticulations : deepNet.reticulationCount = 1 := by
  sorry

/-- Every quartet displayed by `shallowNet` is displayed by `deepNet`. -/
theorem shallow_subset_deep (q : Quartet) :
    shallowNet.DisplaysQuartet q → deepNet.DisplaysQuartet q := by
  sorry

/-- `deepNet` displays `AD|EF`. -/
theorem witness_deep : deepNet.DisplaysQuartet witnessQuartet := by
  sorry

/-- `shallowNet` does not display `AD|EF`. -/
theorem witness_not_shallow : ¬ shallowNet.DisplaysQuartet witnessQuartet := by
  sorry

/-- `deepNet` and `shallowNet` are not isomorphic: isomorphic networks display the same
quartets. -/
theorem deep_not_iso_shallow : IsEmpty (deepNet.Iso shallowNet) := by
  sorry

/-- If `Q` is a multiset version of the quartets displayed by `shallowNet`, then `deepNet`
displays as many quartets of `Q` as any network built on `T`, and has the fewest reticulations
among the networks built on `T` that do. -/
theorem deepNet_optimal_fewest (Q : Multiset Quartet)
    (hQ : ∀ q, q ∈ Q ↔ shallowNet.DisplaysQuartet q) :
    (∀ R : RootedNetwork, R.AnchoredExtension donorTree →
        score Q (DynamicProgramming.repertoire Q R) ≤ score Q (DynamicProgramming.repertoire Q deepNet)) ∧
      (∀ R : RootedNetwork, R.AnchoredExtension donorTree →
        (∀ R' : RootedNetwork, R'.AnchoredExtension donorTree →
          score Q (DynamicProgramming.repertoire Q R') ≤ score Q (DynamicProgramming.repertoire Q R)) →
        deepNet.reticulationCount ≤ R.reticulationCount) := by
  sorry

/-- The hypothesis `identifiable` of `recovery` fails for `shallowNet`: `deepNet` is built on `T`,
displays every quartet that `shallowNet` displays, has no more reticulations, and is not
isomorphic to it. -/
theorem shallow_not_identifiable :
    ¬ ∀ P : RootedNetwork, P.AnchoredExtension donorTree →
      (∀ q, shallowNet.DisplaysQuartet q → P.DisplaysQuartet q) →
      P.reticulationCount ≤ shallowNet.reticulationCount → Nonempty (P.Iso shallowNet) := by
  sorry

end Camus.Counterexamples
