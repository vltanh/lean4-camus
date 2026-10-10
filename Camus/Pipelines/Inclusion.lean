module

public import Camus.Network.SingleEdge
public import Camus.Network.SingleEdge.Deeper
public import Camus.DP.Computable
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
(`deepNet`). Moving the donor down the tree keeps every quartet that the first edge satisfies
(`Realization.deeper_donor_displays`): the second network displays every quartet that the first
displays, and three more (`AD|BE`, `AD|CE` and `AD|EF`). Of the 45 quartets on the six taxa, `T`
induces 15, `shallowNet` displays 22 and `deepNet` 25 (`induced_shallowQuartets`,
`mem_shallowQuartets`, `mem_deepQuartets`). Both networks have one reticulation, and their cycles
have six and seven vertices (`shallow_cycle_card`, `deep_cycle_card`). So if `Q` is a multiset version of `Q(N_r)` for the true
network `N = shallowNet`, the network `deepNet` displays all of `Q` with the fewest reticulations
possible, and is not isomorphic to `N`. The dynamic program itself may return `deepNet` on such an
input (`Counterexamples.camus_may_return_deep`).

## Main results

* `Counterexamples.shallow_subset_deep`: the inclusion of displayed quartets.
* `Counterexamples.deep_not_iso_shallow`: the two networks are not isomorphic.
* `Counterexamples.deepNet_optimal_fewest`: `deepNet` is optimal for every multiset version of
  `Q(N_r)`, with the fewest reticulations among the optimal networks.
* `Counterexamples.shallow_not_identifiable`: the hypothesis `identifiable` of `recovery` fails.
* `Counterexamples.camus_may_return_deep`: on the quartets of `shallowNet`, each once, the
  recurrence of Section 2.2 has a backtracking trace that returns `deepNet`.
* `Counterexamples.ghost_deeper_donor`: moving the donor down fails to keep the displayed quartets
  for a ghost pair.
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

/-- The cycle of `shallowNet` has six vertices: the root, `(A,B)`, `(C,(F,(D,E)))`, `(F,(D,E))`,
and the two new vertices. -/
theorem shallow_cycle_card : (Realization.cycleVertices donorTree shallowPair).card = 6 := by
  rw [Realization.cycleVertices_card]
  decide

/-- The cycle of `deepNet` has seven vertices: those of the cycle of `shallowNet` and `(D,E)`. -/
theorem deep_cycle_card : (Realization.cycleVertices donorTree deepPair).card = 7 := by
  rw [Realization.cycleVertices_card]
  decide

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

/-- Every quartet displayed by `shallowNet` is displayed by `deepNet`: the pair `((D,E), A)` is a
cross pair, and `D` lies below `(D,E)` (`Realization.deeper_donor_displays`). -/
theorem shallow_subset_deep (q : Quartet) :
    shallowNet.DisplaysQuartet q → deepNet.DisplaysQuartet q :=
  (Realization.deeper_donor_displays (u₂ := [true, true, true, false]) donorTree_wellLabelled
    shallowPair_mem (by decide) (by decide) (by decide) (by decide)).2 q

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

/-- The pair `((C,(F,(D,E))), (D,E))`: a ghost pair, whose donor `(C,(F,(D,E)))` is an ancestor
of its recipient `(D,E)`. -/
def ghostPair : Pair := ([true], [true, true, true])

/-- The pair `(C, (D,E))`. Its donor `C` lies below the donor `(C,(F,(D,E)))` of `ghostPair`. -/
def ghostDeeperPair : Pair := ([true, false], [true, true, true])

/-- The quartet `AD|CF`. -/
def ghostQuartet : Quartet := ⟨0, 2, 3, 5, by decide, by decide, by decide, 1⟩

/-- `Realization.deeper_donor_displays` fails for ghost pairs. In `T = ((A,B),(C,(F,(D,E))))`,
`((C,(F,(D,E))), (D,E))` is an admissible ghost pair (its target is its donor), and `(C, (D,E))`
is an admissible pair whose donor `C` lies below `(C,(F,(D,E)))`. The first network displays
`AD|CF`, through its displayed tree `((A,B),((D,E),(C,F)))`; the second does not: its displayed
trees are `T` and `((A,B),((C,(D,E)),F))`. -/
theorem ghost_deeper_donor :
    ghostPair ∈ EdgeAbove.candidates donorTree ∧ EdgeAbove.target ghostPair = ghostPair.1 ∧
      ghostDeeperPair ∈ EdgeAbove.candidates donorTree ∧
      (Realization.graph donorTree {ghostPair}).DisplaysQuartet ghostQuartet ∧
      ¬(Realization.graph donorTree {ghostDeeperPair}).DisplaysQuartet ghostQuartet := by
  have h1 : ghostPair ∈ EdgeAbove.candidates donorTree := by decide
  have h2 : ghostDeeperPair ∈ EdgeAbove.candidates donorTree := by decide
  refine ⟨h1, by decide, h2, ?_, ?_⟩
  · rw [Realization.single_displays_iff donorTree_wellLabelled h1]
    decide +kernel
  · rw [Realization.single_displays_iff donorTree_wellLabelled h2]
    decide +kernel

/-- The quartet on the taxa `a < b < c < d` with split `s`: `ab|cd` for `s = 0`, `ac|bd` for
`s = 1`, `ad|bc` for `s = 2`. -/
def mkQuartet (a b c d : ℕ) (s : Fin 3) (h : a < b ∧ b < c ∧ c < d := by decide) : Quartet :=
  ⟨a, b, c, d, h.1, h.2.1, h.2.2, s⟩

/-- The 22 quartets displayed by `shallowNet` (`mem_shallowQuartets`): the 15 quartets of `T`, one
for each set of four of its six taxa, and the 7 quartets that its added edge satisfies, `AD|BC`,
`AE|BC`, `AF|BC`, `AD|BF`, `AE|BF`, `AD|CF` and `AE|CF`. -/
def shallowQuartets : Finset Quartet :=
  {mkQuartet 0 1 2 3 0, mkQuartet 0 1 2 4 0, mkQuartet 0 1 2 5 0, mkQuartet 0 1 3 4 0,
    mkQuartet 0 1 3 5 0, mkQuartet 0 1 4 5 0, mkQuartet 0 2 3 4 0, mkQuartet 0 2 3 5 0,
    mkQuartet 0 2 4 5 0, mkQuartet 0 3 4 5 2, mkQuartet 1 2 3 4 0, mkQuartet 1 2 3 5 0,
    mkQuartet 1 2 4 5 0, mkQuartet 1 3 4 5 2, mkQuartet 2 3 4 5 2,
    mkQuartet 0 1 2 3 2, mkQuartet 0 1 2 4 2, mkQuartet 0 1 2 5 2, mkQuartet 0 1 3 5 1,
    mkQuartet 0 1 4 5 1, mkQuartet 0 2 3 5 1, mkQuartet 0 2 4 5 1}

/-- `shallowQuartets` has 22 quartets. -/
theorem shallowQuartets_card : shallowQuartets.card = 22 := by decide

/-- `shallowQuartets` is the set of quartets displayed by `shallowNet`. -/
theorem mem_shallowQuartets (q : Quartet) :
    q ∈ shallowQuartets ↔ shallowNet.DisplaysQuartet q := by
  rw [Realization.single_displays_iff donorTree_wellLabelled shallowPair_mem]
  constructor
  · revert q
    decide +kernel
  · rintro ⟨hq, h⟩
    revert h
    refine quartet_of_taxa (P := fun q =>
      (q.induced donorTree = true ∨
          ∃ C ∈ EdgeAbove.switchedClades donorTree shallowPair, q.cutBy C = true) →
        q ∈ shallowQuartets) ?_ hq
    decide +kernel

/-- The 25 quartets displayed by `deepNet` (`mem_deepQuartets`): those of `shallowNet`, and `AD|BE`,
`AD|CE` and `AD|EF`. -/
def deepQuartets : Finset Quartet :=
  shallowQuartets ∪ {mkQuartet 0 1 3 4 1, mkQuartet 0 2 3 4 1, mkQuartet 0 3 4 5 0}

/-- `deepQuartets` has 25 quartets. -/
theorem deepQuartets_card : deepQuartets.card = 25 := by decide

/-- `deepQuartets` is the set of quartets displayed by `deepNet`. -/
theorem mem_deepQuartets (q : Quartet) :
    q ∈ deepQuartets ↔ deepNet.DisplaysQuartet q := by
  rw [Realization.single_displays_iff donorTree_wellLabelled deepPair_mem]
  constructor
  · revert q
    decide +kernel
  · rintro ⟨hq, h⟩
    revert h
    refine quartet_of_taxa (P := fun q =>
      (q.induced donorTree = true ∨
          ∃ C ∈ EdgeAbove.switchedClades donorTree deepPair, q.cutBy C = true) →
        q ∈ deepQuartets) ?_ hq
    decide +kernel

/-- `T` induces 15 quartets, one for each set of four of its six taxa: they are among the quartets
displayed by `shallowNet`, and 15 of those are induced by `T`. -/
theorem induced_shallowQuartets :
    (∀ q, q.induced donorTree = true → q ∈ shallowQuartets) ∧
      (shallowQuartets.filter fun q => q.induced donorTree = true).card = 15 := by
  refine ⟨fun q hq => (mem_shallowQuartets q).mpr ?_, by decide⟩
  rw [Realization.single_displays_iff donorTree_wellLabelled shallowPair_mem]
  exact ⟨((Quartet.induced_iff_taxaAt q donorTree).mp hq).1, Or.inl hq⟩

/-- A solution of the recurrence of Section 2.2 on `T` and the quartets of `shallowNet`, each once:
`M[v] = 7` at the root, `M[v] = 2` at `(C,(F,(D,E)))` (the edge above `(C, F)` satisfies `AD|CF`
and `AE|CF`), and `M[v] = 0` elsewhere. -/
def deepArray (v : Address) : ℕ := if v = [] then 7 else if v = [true] then 2 else 0

/-- `deepArray` satisfies the recurrence (Equations (2)–(5)) on `T` and the quartets of
`shallowNet`, each once. The values `s(v)` are computed with `DynamicProgramming.s_edgeWeight_eq`:
at the root, the largest is 7, attained among others by `((D,E), A)` and by `(D, A)`, which
satisfy the 7 quartets of `Q` that `T` does not induce. -/
theorem deepArray_array :
    Array donorTree (edgeWeight donorTree shallowQuartets.val) deepArray := by
  intro v hv
  rw [s_edgeWeight_eq donorTree donorTree_wellLabelled]
  have hnodes : donorTree.nodes = {[], [false], [false, false], [false, true], [true],
      [true, false], [true, true], [true, true, false], [true, true, true],
      [true, true, true, false], [true, true, true, true]} := by decide
  rw [hnodes] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [donorTree, PhyloTree.nodeAt] <;> decide +kernel

/-- Backtracking through `deepArray` from the root may choose the pair `(D, A)`: its weight, 7,
plus the values of the subtrees hanging off its cycle, all leaves, is `M[root] = 7`. -/
theorem trace_deepPair :
    Trace donorTree (edgeWeight donorTree shallowQuartets.val) deepArray [] {deepPair} := by
  have hhang : hanging donorTree deepPair = {[false, false], [false, true], [true, false],
      [true, true, false], [true, true, true, false], [true, true, true, true]} := by
    decide
  have hg := Trace.gall (t := donorTree) (weight := edgeWeight donorTree shallowQuartets.val)
    (M := deepArray) [] deepPair (fun _ => ∅) (by decide)
    (by
      intro r hr
      rw [hhang] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [Trace.leaf _ 0 rfl, Trace.leaf _ 1 rfl, Trace.leaf _ 2 rfl, Trace.leaf _ 5 rfl,
        Trace.leaf _ 3 rfl, Trace.leaf _ 4 rfl])
    (by
      rw [edgeWeight_eq_satisfies donorTree_wellLabelled deepPair_mem,
        hanging_score donorTree deepArray deepPair (Finset.mem_filter.mp deepPair_mem).2]
      decide +kernel)
  have hE : insert deepPair ((hanging donorTree deepPair).biUnion fun _ => ∅) = {deepPair} := by
    ext x
    simp
  rw [hE] at hg
  exact hg

/-- Section 3.2: the dynamic program itself may return `deepNet` when the input is the true
network `shallowNet`. With `Q` the quartets displayed by `shallowNet`, each once, the recurrence
has a solution `M` and a backtracking trace through it from the root that adds the edge above
`(D, A)`, so that the output is `deepNet`, not `shallowNet`. By Theorem 1 the output is optimal; it
has one reticulation, the fewest possible (`deepNet_optimal_fewest`). -/
theorem camus_may_return_deep :
    (∀ q, q ∈ shallowQuartets.val ↔ shallowNet.DisplaysQuartet q) ∧
      ∃ M, Array donorTree (edgeWeight donorTree shallowQuartets.val) M ∧
        Trace donorTree (edgeWeight donorTree shallowQuartets.val) M [] {deepPair} :=
  ⟨mem_shallowQuartets, deepArray, deepArray_array, trace_deepPair⟩

end Camus.Counterexamples
