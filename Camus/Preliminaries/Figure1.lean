module

public import Camus.Network.SingleEdge
public import Camus.Network.Reticulations

/-!
# Figure 1

Figure 1 of the paper shows a tree-based network `N`, the tree `T` with one added edge from u′ above
`u` to w′ above `w`, and its caption says: "N induces two rooted trees on A,D,E,G: the rooted tree
((A,D),(E,G)) (which is also induced by T) and the rooted trees (A,((D,E),G)) (which does not appear
in T). The rooted four-leaf trees define two unrooted trees on the leafset, referred to as quartet
trees: AD|EG and DE|AG. We say that the quartet tree DE|AG is satisfied by N but not by T, and we
also say it is satisfied by the added edge"; Procedure ASSIGN assigns the edge and DE|AG to the
triplet (u, w, v), where v = lca(u, w).

The figure itself is not in the text of the paper, and the caption does not determine `T` beyond
its restriction to A, D, E, G. This file checks the caption's claims on the smallest tree that fits
them: `T = ((A,D),(E,G))` (`Figure1.tree`, with `A = 0`, `D = 3`, `E = 4`, `G = 6`), and the edge
added above `(u, w) = (E, D)` (`Figure1.pair`). On this tree it is the only pair whose second
tree is (A,((D,E),G)) (`Figure1.pair_unique`). Its target v = lca(E, D) is the root of `T`. The network `N = T + e`
(`Figure1.net`) is built on `T` and has one reticulation; on A, D, E, G it displays exactly AD|EG
and DE|AG; `T` induces AD|EG and not DE|AG; and DE|AG is the quartet satisfied by the added edge.
The two rooted trees are compared through their clades: the clades of the tree displayed through
the added edge (`EdgeAbove.switchedClades`) are those of (A,((D,E),G)).

## Main results

* `Figure1.net_displays_iff`: `N` displays exactly AD|EG and DE|AG.
* `Figure1.novel_eq`: of AD|EG and DE|AG, `N` satisfies DE|AG only.
* `Figure1.satisfies_pair`: DE|AG is satisfied by the added edge (Definition 4).
* `Figure1.switchedClades_eq`, `Figure1.tree_clades_eq`: the two rooted trees.
* `Figure1.pair_unique`: `(E, D)` is the only pair of `T` that gives (A,((D,E),G)).
-/

@[expose] public section

namespace Camus.Figure1

open DynamicProgramming

/-- The tree `T = ((A,D),(E,G))`, with `A = 0`, `D = 3`, `E = 4` and `G = 6`. -/
def tree : PhyloTree := .fork (.fork (.leaf 0) (.leaf 3)) (.fork (.leaf 4) (.leaf 6))

/-- The rooted tree (A,((D,E),G)), the second tree that `N` induces on A, D, E, G. -/
def switchedTree : PhyloTree := .fork (.leaf 0) (.fork (.fork (.leaf 3) (.leaf 4)) (.leaf 6))

/-- The pair `(u, w) = (E, D)`: the donor `u` is the leaf `E`, the recipient `w` the leaf `D`. -/
def pair : Pair := ([true, false], [false, true])

/-- The network `N = T + e` of Figure 1, with the edge `e` added above `(E, D)`. -/
noncomputable abbrev net : RootedNetwork := Realization.graph tree {pair}

/-- The quartet AD|EG. -/
def quartetAD : Quartet := ⟨0, 3, 4, 6, by decide, by decide, by decide, 0⟩

/-- The quartet AE|DG. -/
def quartetAE : Quartet := ⟨0, 3, 4, 6, by decide, by decide, by decide, 1⟩

/-- The quartet DE|AG, which is AG|DE. -/
def quartetDE : Quartet := ⟨0, 3, 4, 6, by decide, by decide, by decide, 2⟩

/-- The leaf labels of `T` are distinct. -/
theorem tree_wellLabelled : tree.WellLabelled := by decide

/-- An edge can be added above `(E, D)`. -/
theorem pair_mem : pair ∈ EdgeAbove.candidates tree := by decide

/-- The family `{(E, D)}` is cycle-separated. -/
theorem pair_separated : EdgeAbove.CycleSeparated tree {pair} :=
  ⟨Finset.singleton_subset_iff.mpr pair_mem, by simp⟩

/-- `N` is built on `T`: it is a rooted binary level-1 network with `T` as support. -/
theorem net_anchored : net.AnchoredExtension tree :=
  ⟨Realization.levelOne tree tree_wellLabelled _ pair_separated,
    ⟨_, ⟨Realization.support tree tree_wellLabelled _ pair_separated⟩⟩⟩

/-- `N` has one reticulation, w′: "N has a single cycle ... which contains a unique node of indegree
two". -/
theorem net_reticulations : net.reticulationCount = 1 := by
  simpa using Realization.reticulationCount_eq_card tree {pair} pair_separated

/-- The target v = lca(u, w) of the pair is the root of `T`. -/
theorem target_pair : EdgeAbove.target pair = [] := rfl

/-- A quartet on taxa of `T` is a quartet on A, D, E, G. -/
theorem eq_of_taxa_subset {q : Quartet} (hq : q.taxa ⊆ tree.taxa) :
    ∃ s, q = ⟨0, 3, 4, 6, by decide, by decide, by decide, s⟩ := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, s⟩ := q
  have hmem : ∀ x ∈ ({a, b, c, d} : Finset ℕ), x = 0 ∨ x = 3 ∨ x = 4 ∨ x = 6 := by
    intro x hx
    have h := hq hx
    simpa [tree, PhyloTree.taxa, PhyloTree.labels] using h
  have ha := hmem a (by simp)
  have hb := hmem b (by simp)
  have hc := hmem c (by simp)
  have hd := hmem d (by simp)
  obtain ⟨rfl, rfl, rfl, rfl⟩ : a = 0 ∧ b = 3 ∧ c = 4 ∧ d = 6 := by omega
  exact ⟨s, rfl⟩

/-- Figure 1: `N` displays exactly the quartets AD|EG and DE|AG. -/
theorem net_displays_iff (q : Quartet) :
    net.DisplaysQuartet q ↔ q = quartetAD ∨ q = quartetDE := by
  rw [Realization.single_displays_iff tree_wellLabelled pair_mem]
  constructor
  · rintro ⟨hq, h⟩
    obtain ⟨s, rfl⟩ := eq_of_taxa_subset hq
    revert h
    fin_cases s <;> decide +kernel
  · rintro (rfl | rfl) <;> decide +kernel

/-- Figure 1: `T` induces AD|EG ("also induced by T") and not DE|AG. -/
theorem tree_induces : quartetAD.induced tree = true ∧ quartetDE.induced tree = false := by
  decide

/-- Figure 1: of the two quartets AD|EG and DE|AG that `N` displays, `N` satisfies DE|AG only: "the
quartet tree DE|AG is satisfied by N but not by T". -/
theorem novel_eq : novel tree {quartetAD, quartetDE} net = {quartetDE} := by
  ext q
  rw [Realization.mem_novel_single_iff tree_wellLabelled pair_mem]
  constructor
  · rintro ⟨hq, hsat⟩
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact absurd hsat (by decide)
    · exact Finset.mem_singleton_self _
  · intro hq
    rw [Finset.mem_singleton.mp hq]
    exact ⟨by simp, by decide⟩

/-- Figure 1: DE|AG "is satisfied by the added edge" (δ_T of Definition 4). -/
theorem satisfies_pair : EdgeAbove.satisfies tree pair quartetDE = true := by decide

/-- The clades of `T`: those of the rooted tree ((A,D),(E,G)). -/
theorem tree_clades_eq :
    tree.clades.toFinset = {{0, 3, 4, 6}, {0, 3}, {4, 6}, {0}, {3}, {4}, {6}} := by
  decide

/-- Figure 1: the tree displayed by `N` through the added edge, `T` with `D` pruned and regrafted
above `E`, has the clades of the rooted tree (A,((D,E),G)). Its vertex above `A` alone, the parent
of `A` in `T`, keeps the clade {A}, and the clean-up of Definition 1 suppresses it. -/
theorem switchedClades_eq : EdgeAbove.switchedClades tree pair = switchedTree.clades.toFinset := by
  decide

/-- On `T`, the pair `(E, D)` is the only pair above which an edge can be added whose second tree
has the clades of (A,((D,E),G)). -/
theorem pair_unique : ∀ e ∈ EdgeAbove.candidates tree,
    EdgeAbove.switchedClades tree e = switchedTree.clades.toFinset → e = pair := by
  decide

end Camus.Figure1
