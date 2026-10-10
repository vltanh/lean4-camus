module

public import Camus.Network.Clades
public import Camus.Preliminaries.Lemmas

/-!
# The quartets displayed by `T + e`

Let `e = (u, w)` be an admissible pair of the rooted binary tree `T`, and `T + e` the network
obtained by adding an edge above `(u, w)` (Definition 3, `Realization.graph t {e}`). Its two
switchings give the trees `T` and `T'`, where `T'` is `T` with the subtree `T_w` pruned and
regrafted on the edge above `u`. The clades of `T'` are explicit
(`EdgeAbove.switchedClade`, `EdgeAbove.switchedClades`): the clade of a vertex `p` of `T` loses
the taxa of `T_w` if `p` is a strict ancestor of `w`, and gains them if `p` is a strict ancestor
of `u`; the new vertex u' has the clade of `u` together with `T_w`, and the new vertex w' has the
clade `T_w`. So the quartets displayed by `T + e`, and those it satisfies (displays and `T` does
not induce), are decidable, and `s_e(u, w)` of Equation (1) is a finite sum of decidable terms
(`DynamicProgramming.edgeWeight_eq_satisfies`). This is the paper's remark (Section 2.3) that
"determining which quartets are induced can be determined by the nodes they attach to in the
cycle".

## Main results

* `Realization.single_displays_iff`: the quartets displayed by `T + e`.
* `Realization.mem_novel_single_iff`: the quartets of `Q` satisfied by `T + e`.
* `EdgeAbove.satisfies`, `DynamicProgramming.edgeWeight_eq_satisfies`: δ_T of Definition 4 and
  Equation (1), computably.
-/

@[expose] public section

namespace Camus

namespace PhyloTree

/-- The labels of the leaves of the subtree of `t` at the vertex `p`: the clade of `p`. Empty if
`p` is not a vertex of `t`. -/
def taxaAt (t : PhyloTree) (p : Address) : Finset ℕ :=
  match t.nodeAt p with
  | some s => s.taxa
  | none => ∅

end PhyloTree

namespace EdgeAbove

/-- The clade of the vertex `p` of `T` in the tree `T'` displayed by `T + e` through the added
edge, for `e = (u, w)`: `T'` is `T` with the subtree `T_w` pruned and regrafted on the edge above
`u`. The clade of `p` in `T` loses the taxa of `T_w` if `p` is a strict ancestor of `w`, and gains
them if `p` is a strict ancestor of `u`. -/
def switchedClade (t : PhyloTree) (e : Address × Address) (p : Address) : Finset ℕ :=
  (if p <+: e.2 ∧ p ≠ e.2 then t.taxaAt p \ t.taxaAt e.2 else t.taxaAt p) ∪
    (if p <+: e.1 ∧ p ≠ e.1 then t.taxaAt e.2 else ∅)

/-- The clades of the tree `T'` displayed by `T + e` through the added edge `e = (u, w)`: the
clades `switchedClade t e p` of the vertices `p` of `T`, the clade of the new vertex u' (the clade
of `u` in `T'` together with `T_w`), and the clade `T_w` of the new vertex w'. -/
def switchedClades (t : PhyloTree) (e : Address × Address) : Finset (Finset ℕ) :=
  insert (switchedClade t e e.1 ∪ t.taxaAt e.2)
    (insert (t.taxaAt e.2) (t.nodes.image (switchedClade t e)))

/-- δ_T of Definition 4, as a test: the quartet `q` is satisfied by the edge added above `e`
(displayed by `T + e` and not induced by `T`). Its taxa are taxa of `T`, `T` does not induce it,
and some clade of `T'` cuts it (`Realization.mem_novel_single_iff`). -/
def satisfies (t : PhyloTree) (e : Address × Address) (q : Quartet) : Bool :=
  decide (q.taxa ⊆ t.taxa) && !q.induced t &&
    decide (∃ C ∈ switchedClades t e, q.cutBy C = true)

end EdgeAbove

namespace Realization

/-- The quartets displayed by `T + e`: for a well-labelled `T` and an admissible pair `e`, the
network `graph t {e}` displays `q` if and only if the taxa of `q` are taxa of `T` and `q` is induced
by `T` or cut by a clade of `T'`. -/
theorem single_displays_iff {t : PhyloTree} (ht : t.WellLabelled) {e : Address × Address}
    (he : e ∈ EdgeAbove.candidates t) (q : Quartet) :
    (graph t {e}).DisplaysQuartet q ↔
      q.taxa ⊆ t.taxa ∧
        (q.induced t = true ∨ ∃ C ∈ EdgeAbove.switchedClades t e, q.cutBy C = true) := by
  sorry

/-- The quartets of `Q` satisfied by `T + e` (Section 2.1): those of `Q` whose taxa are taxa of
`T`, that `T` does not induce, and that a clade of `T'` cuts. -/
theorem mem_novel_single_iff {t : PhyloTree} (ht : t.WellLabelled) {e : Address × Address}
    (he : e ∈ EdgeAbove.candidates t) (Q : Multiset Quartet) (q : Quartet) :
    q ∈ DynamicProgramming.novel t Q (graph t {e}) ↔
      q ∈ Q ∧ EdgeAbove.satisfies t e q = true := by
  sorry

end Realization

namespace DynamicProgramming

/-- Equation (1), computably: for an admissible pair `e`, `s_e(u, w)` is the sum over the distinct
quartets `q` of `Q` of δ_T(q, (u, w)), the multiplicity of `q` if the edge added above `e`
satisfies `q` (`EdgeAbove.satisfies`), and 0 otherwise. -/
theorem edgeWeight_eq_satisfies {t : PhyloTree} (ht : t.WellLabelled) {e : Address × Address}
    (he : e ∈ EdgeAbove.candidates t) (Q : Multiset Quartet) :
    edgeWeight t Q e =
      ∑ q ∈ Q.toFinset, if EdgeAbove.satisfies t e q = true then Q.count q else 0 := by
  sorry

end DynamicProgramming

end Camus
