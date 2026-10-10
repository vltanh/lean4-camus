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

/-- An edge can be added above `((D,E), A)`. -/
theorem shallowPair_mem : shallowPair ∈ EdgeAbove.candidates donorTree := by decide

/-- An edge can be added above `(D, A)`. -/
theorem deepPair_mem : deepPair ∈ EdgeAbove.candidates donorTree := by decide

/-- The family `{shallowPair}` is feasible. -/
theorem shallowPair_separated : EdgeAbove.CycleSeparated donorTree {shallowPair} :=
  ⟨Finset.singleton_subset_iff.mpr shallowPair_mem, by simp⟩

/-- The family `{deepPair}` is feasible. -/
theorem deepPair_separated : EdgeAbove.CycleSeparated donorTree {deepPair} :=
  ⟨Finset.singleton_subset_iff.mpr deepPair_mem, by simp⟩

/-- `shallowNet` is built on `T`. -/
theorem shallowNet_anchored : shallowNet.AnchoredExtension donorTree :=
  ⟨Realization.levelOne donorTree donorTree_wellLabelled _ shallowPair_separated,
    ⟨_, ⟨Realization.support donorTree donorTree_wellLabelled _ shallowPair_separated⟩⟩⟩

/-- `deepNet` is built on `T`. -/
theorem deepNet_anchored : deepNet.AnchoredExtension donorTree :=
  ⟨Realization.levelOne donorTree donorTree_wellLabelled _ deepPair_separated,
    ⟨_, ⟨Realization.support donorTree donorTree_wellLabelled _ deepPair_separated⟩⟩⟩

/-- `shallowNet` has one reticulation. -/
theorem shallowNet_reticulations : shallowNet.reticulationCount = 1 := by
  simpa using Realization.reticulationCount_eq_card donorTree {shallowPair} shallowPair_separated

/-- `deepNet` has one reticulation. -/
theorem deepNet_reticulations : deepNet.reticulationCount = 1 := by
  simpa using Realization.reticulationCount_eq_card donorTree {deepPair} deepPair_separated

/-- A property of the quartets on four of the taxa `0, …, 5` holds for every quartet on taxa of
`T`. -/
theorem quartet_of_taxa {P : Quartet → Prop}
    (h : ∀ (a b c d : Fin 6) (hab : a.val < b.val) (hbc : b.val < c.val)
      (hcd : c.val < d.val) (s : Fin 3), P ⟨a, b, c, d, hab, hbc, hcd, s⟩)
    {q : Quartet} (hq : q.taxa ⊆ donorTree.taxa) : P q := by
  have hd : q.d < 6 := by
    have hm := hq (by simp [Quartet.taxa] : q.d ∈ q.taxa)
    simp [donorTree, PhyloTree.taxa, PhyloTree.labels] at hm
    omega
  obtain ⟨a, b, c, d, hab, hbc, hcd, s⟩ := q
  change d < 6 at hd
  exact h ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, hd⟩ hab hbc hcd s

/-- Every quartet displayed by `shallowNet` is displayed by `deepNet`. By
`Realization.single_displays_iff`, the quartets displayed by `T + e` are those on taxa of `T`
that `T` induces or that a clade of `T'` cuts; the inclusion is checked on the 45 quartets on
taxa of `T`. -/
theorem shallow_subset_deep (q : Quartet) :
    shallowNet.DisplaysQuartet q → deepNet.DisplaysQuartet q := by
  rw [Realization.single_displays_iff donorTree_wellLabelled shallowPair_mem,
    Realization.single_displays_iff donorTree_wellLabelled deepPair_mem]
  rintro ⟨hq, h⟩
  refine ⟨hq, ?_⟩
  revert h
  refine quartet_of_taxa (P := fun q =>
    (q.induced donorTree = true ∨
        ∃ C ∈ EdgeAbove.switchedClades donorTree shallowPair, q.cutBy C = true) →
      (q.induced donorTree = true ∨
        ∃ C ∈ EdgeAbove.switchedClades donorTree deepPair, q.cutBy C = true)) ?_ hq
  decide +kernel

/-- `deepNet` displays `AD|EF`. -/
theorem witness_deep : deepNet.DisplaysQuartet witnessQuartet := by
  rw [Realization.single_displays_iff donorTree_wellLabelled deepPair_mem]
  decide +kernel

/-- `shallowNet` does not display `AD|EF`. -/
theorem witness_not_shallow : ¬ shallowNet.DisplaysQuartet witnessQuartet := by
  rw [Realization.single_displays_iff donorTree_wellLabelled shallowPair_mem]
  decide +kernel

/-- `deepNet` and `shallowNet` are not isomorphic: isomorphic networks display the same
quartets. -/
theorem deep_not_iso_shallow : IsEmpty (deepNet.Iso shallowNet) :=
  ⟨fun i => witness_not_shallow
    ((i.displays_iff deepNet_anchored.1 shallowNet_anchored.1 witnessQuartet).mp witness_deep)⟩

/-- The quartet `AD|BC`, satisfied by `shallowNet`: displayed by it, and not induced by `T`. -/
def satisfiedQuartet : Quartet := ⟨0, 1, 2, 3, by decide, by decide, by decide, 2⟩

/-- `shallowNet` displays `AD|BC`. -/
theorem satisfied_shallow : shallowNet.DisplaysQuartet satisfiedQuartet := by
  rw [Realization.single_displays_iff donorTree_wellLabelled shallowPair_mem]
  decide +kernel

/-- `T` does not induce `AD|BC`. -/
theorem satisfied_not_induced : satisfiedQuartet.induced donorTree = false := by decide

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
  classical
  -- `deepNet` displays every quartet of `Q`, so its score is `|Q|`, the largest possible
  have hdeep : score Q (DynamicProgramming.repertoire Q deepNet) = Q.card := by
    apply (score_eq_card_iff Q _).mpr
    intro q hq
    simp only [DynamicProgramming.repertoire, Finset.mem_filter]
    exact ⟨hq, shallow_subset_deep q ((hQ q).mp (Multiset.mem_toFinset.mp hq))⟩
  refine ⟨fun R _ => hdeep ▸ score_le_card _ _, ?_⟩
  intro R hR hopt
  rw [deepNet_reticulations]
  -- an optimal `R` displays every quartet of `Q`
  have hRscore : score Q (DynamicProgramming.repertoire Q R) = Q.card :=
    le_antisymm (score_le_card _ _) (hdeep ▸ hopt deepNet deepNet_anchored)
  have hall : ∀ q, shallowNet.DisplaysQuartet q → R.DisplaysQuartet q := by
    intro q hq
    have hmem := (score_eq_card_iff Q _).mp hRscore (Multiset.mem_toFinset.mpr ((hQ q).mpr hq))
    simp only [DynamicProgramming.repertoire, Finset.mem_filter] at hmem
    exact hmem.2
  -- with no reticulation, `R` would be isomorphic to `T`, which does not induce `AD|BC`
  by_contra hzero
  have hbase : EdgeAbove.CycleSeparated donorTree ∅ := by simp [EdgeAbove.CycleSeparated]
  have hT : ∀ q, (Realization.graph donorTree ∅).DisplaysQuartet q → R.DisplaysQuartet q := by
    intro q hq
    have hind := (Realization.baseline_displays_iff donorTree donorTree_wellLabelled q).mp hq
    apply hall q
    rw [Realization.single_displays_iff donorTree_wellLabelled shallowPair_mem]
    exact ⟨((Quartet.induced_iff_taxaAt q donorTree).mp hind).1, Or.inl hind⟩
  obtain ⟨i⟩ := tree_identifiable donorTree donorTree_wellLabelled R hR hT (by
    rw [Realization.reticulationCount_eq_card donorTree ∅ hbase, Finset.card_empty]
    omega)
  have hRq := hall satisfiedQuartet satisfied_shallow
  have hTq := (i.displays_iff hR.1
    (Realization.levelOne donorTree donorTree_wellLabelled ∅ hbase) satisfiedQuartet).mp hRq
  rw [Realization.baseline_displays_iff donorTree donorTree_wellLabelled,
    satisfied_not_induced] at hTq
  exact Bool.false_ne_true hTq

/-- The hypothesis `identifiable` of `recovery` fails for `shallowNet`: `deepNet` is built on `T`,
displays every quartet that `shallowNet` displays, has no more reticulations, and is not
isomorphic to it. -/
theorem shallow_not_identifiable :
    ¬ ∀ P : RootedNetwork, P.AnchoredExtension donorTree →
      (∀ q, shallowNet.DisplaysQuartet q → P.DisplaysQuartet q) →
      P.reticulationCount ≤ shallowNet.reticulationCount → Nonempty (P.Iso shallowNet) := by
  intro h
  obtain ⟨i⟩ := h deepNet deepNet_anchored shallow_subset_deep
    (by rw [deepNet_reticulations, shallowNet_reticulations])
  exact deep_not_iso_shallow.false i

end Camus.Counterexamples
