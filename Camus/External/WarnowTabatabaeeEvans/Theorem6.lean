module

public import Camus.External.WarnowTabatabaeeEvans.SiteModel
public import Camus.Network.Realization.SupportClades

/-!
# The step of WTE's Theorem 6 needs `p(e, s, s) > 0`

The proof of Theorem 6 of Warnow, Tabatabaee and Evans (2025) ("WTE") shows that every clade of
the network `N` appears as the clade of an SNP with positive probability: for a tree edge `e`
of a displayed tree `T`, "it is easy to see that the probability that c changes on e and no other
edge in T is strictly positive". Section 3.2 of the paper relies on the same step for quartets.
With the constraints that WTE list in their Section 4.2 (`External.SiteParameters`) the step
fails: if some tree edge `f` of `T` other than `e` has `p(f, s, s) = 0`, every character changes
on `f`, so none changes on `e` alone. WTE's Theorem 7 assumes `0 < p_on ≤ p(e, s, s)`, and
`External.SiteModel` assumes it as `stay_pos`.

The counterexample is the tree `((A,B),C),D` (`External.Theorem6Gap.caterpillar`), as a network
with no reticulation, with two states and a substitution that always changes the state on the
edge from the root to the parent of `(A,B)` and `C` (`External.Theorem6Gap.alwaysChange`). Every
SNP whose clade is `{A, B}` has probability 0, although `{A, B}` is a clade of the network; and
every SNP that contributes the quartet `AB|CD`, which the network displays, has probability 0
(`External.theorem6_step_needs_stay`).

## Main results

* `External.Theorem6Gap.alwaysChange`: parameters that meet WTE's constraints of Section 4.2.
* `External.theorem6_step_needs_stay`: under them, the clade `{A, B}` and the quartet `AB|CD`
  never come from an SNP of positive probability.
-/

@[expose] public section

open scoped NNReal

namespace Camus.External

namespace Theorem6Gap

open Realization

/-- The tree `((A,B),C),D`, with `A = 0`, `B = 1`, `C = 2`, `D = 3`. -/
def caterpillar : PhyloTree :=
  .fork (.fork (.fork (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3)

theorem caterpillar_wellLabelled : caterpillar.WellLabelled := by decide

theorem empty_separated : EdgeAbove.CycleSeparated caterpillar ∅ := by
  simp [EdgeAbove.CycleSeparated]

/-- The tree `((A,B),C),D` as a network with no reticulation. -/
noncomputable abbrev treeNet : RootedNetwork := graph caterpillar ∅

theorem treeNet_levelOne : treeNet.RootedBinaryLevelOne :=
  levelOne caterpillar caterpillar_wellLabelled ∅ empty_separated

theorem treeNet_edges : treeNet.edges = supportEdges caterpillar ∅ := by
  simp [graph]

/-- The edges of `treeNet` enter the vertices of the tree other than the root. -/
theorem head_eq_code {e : ℕ × ℕ} (he : e ∈ treeNet.edges) :
    ∃ p ∈ caterpillar.nodes, p ≠ [] ∧ e.2 = Address.code p := by
  obtain ⟨hr, hv⟩ := Finset.mem_erase.mp (Switchings.head_mem_slot treeNet_levelOne he)
  rw [vertices_covered caterpillar ∅ empty_separated.1] at hv
  rcases Finset.mem_union.mp hv with horiginal | hinterior
  · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp horiginal
    refine ⟨p, hp, fun h => hr ?_, hpe.symm⟩
    rw [← hpe, h]
    rfl
  · obtain ⟨r, -, hvr⟩ := Finset.mem_biUnion.mp hinterior
    obtain ⟨f, hf, -⟩ := mem_wireInterior.mp hvr
    exact absurd hf (Finset.notMem_empty f)

/-- Every edge of `treeNet` is a tree edge. -/
theorem indegree_head {e : ℕ × ℕ} (he : e ∈ treeNet.edges) : treeNet.indegree e.2 = 1 := by
  obtain ⟨p, hp, hp0, hpe⟩ := head_eq_code he
  rw [hpe]
  exact graph_indegree_code caterpillar ∅ empty_separated.1 hp hp0

/-- `treeNet` has no reticulation. -/
theorem indegree_ne_two {v : ℕ} (hv : v ∈ treeNet.vertices) : treeNet.indegree v ≠ 2 := by
  rw [vertices_covered caterpillar ∅ empty_separated.1] at hv
  rcases Finset.mem_union.mp hv with horiginal | hinterior
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp horiginal
    by_cases hp0 : p = []
    · subst hp0
      rw [show treeNet.indegree (Address.code []) = 0 from graph_root_indegree caterpillar ∅]
      decide
    · rw [graph_indegree_code caterpillar ∅ empty_separated.1 hp hp0]
      decide
  · obtain ⟨r, -, hvr⟩ := Finset.mem_biUnion.mp hinterior
    obtain ⟨f, hf, -⟩ := mem_wireInterior.mp hvr
    exact absurd hf (Finset.notMem_empty f)

/-- The edge from the root to the parent of `(A,B)` and `C`. -/
def topEdge : ℕ × ℕ := (Address.code [], Address.code [false])

theorem topEdge_mem : topEdge ∈ treeNet.edges := by
  rw [treeNet_edges]
  refine Finset.mem_biUnion.mpr ⟨[false], by decide, ?_⟩
  simp [wire, outerEndpoints, ghostEndpoints, wireEdges, topEdge, parent]

/-- Parameters of WTE's model on `treeNet` with two states, meeting the constraints of their
Section 4.2: uniform at the root, the state always changes on `topEdge`, and the uniform row on
the other edges. There is no reticulation. -/
noncomputable def alwaysChange : SiteParameters treeNet Bool where
  transmission _ := 1
  transmission_pos e he h2 := absurd h2 (by rw [indegree_head he]; decide)
  transmission_sum v hv h2 := absurd h2 (indegree_ne_two hv)
  root _ := 2⁻¹
  root_pos _ := by norm_num
  root_sum := by simp only [Fintype.sum_bool]; norm_num
  substitution e s s' := if e = topEdge then (if s = s' then 0 else 1) else 2⁻¹
  substitution_sum e _ s := by
    by_cases h : e = topEdge
    · cases s <;> simp [h]
    · simp only [h, ite_false, Fintype.sum_bool]
      norm_num
  change_pos e _ _ s s' hs := by
    by_cases h : e = topEdge
    · simp [h, hs]
    · simp only [h, ite_false]
      norm_num
  no_change e he h2 := absurd h2 (by rw [indegree_head he]; decide)

/-- The quartet `AB|CD`. -/
def quartetABCD : Quartet := ⟨0, 1, 2, 3, by decide, by decide, by decide, 0⟩

/-- An SNP that changes on the edge above `(A,B)` has probability 0: it does not change on
`topEdge`, where the state always changes. -/
theorem weight_eq_zero {h : SiteHistory treeNet Bool} {x : ℕ}
    (hch : h.changes = {(x, Address.code [false, false])}) : alwaysChange.weight h = 0 := by
  have hS : h.switching = treeNet.edges :=
    baseline_switching_unique caterpillar caterpillar_wellLabelled h.isSwitching
  have htop : topEdge ∈ h.switching := hS ▸ topEdge_mem
  -- the state does not change on `topEdge`
  have hstay : h.state topEdge.1 = h.state topEdge.2 := by
    by_contra hne
    have hmem : topEdge ∈ h.changes := Finset.mem_filter.mpr ⟨htop, hne⟩
    rw [hch, Finset.mem_singleton] at hmem
    have hcode : Address.code [false] = Address.code [false, false] := congrArg Prod.snd hmem
    exact absurd hcode (by decide)
  unfold SiteParameters.weight
  rw [Finset.prod_eq_zero htop, mul_zero]
  change (if topEdge = topEdge then (if h.state topEdge.1 = h.state topEdge.2 then 0 else 1)
    else 2⁻¹ : ℝ≥0) = 0
  rw [ite_eq_left rfl, ite_eq_left hstay]

/-- In `treeNet`, the head of an SNP's edge whose clade cuts `AB|CD`, or is `{A, B}`, is the
vertex above `(A,B)`. -/
theorem head_of_clade {h : SiteHistory treeNet Bool} {x y : ℕ}
    (hch : h.changes = {(x, y)})
    (hclade : quartetABCD.cutBy (treeNet.cladeBelow h.switching y) = true ∨
      treeNet.cladeBelow h.switching y = {0, 1}) :
    y = Address.code [false, false] := by
  have hS : h.switching = treeNet.edges :=
    baseline_switching_unique caterpillar caterpillar_wellLabelled h.isSwitching
  have hxy : (x, y) ∈ treeNet.edges :=
    hS ▸ (Finset.mem_filter.mp (hch ▸ Finset.mem_singleton_self (x, y))).1
  obtain ⟨p, hp, -, hpy⟩ := head_eq_code hxy
  change y = Address.code p at hpy
  rw [hS, treeNet_edges, hpy,
    cladeBelow_support_code caterpillar_wellLabelled empty_separated hp] at hclade
  have hdec : ∀ p ∈ caterpillar.nodes,
      (quartetABCD.cutBy (caterpillar.taxaAt p) = true ∨ caterpillar.taxaAt p = {0, 1}) →
        p = [false, false] := by decide
  rw [hpy, hdec p hp hclade]

end Theorem6Gap

open Theorem6Gap Realization in
/-- WTE's Theorem 6 step fails under the constraints of their Section 4.2 alone. For the tree
`((A,B),C),D` as a network `N` and the parameters `alwaysChange`, which meet those constraints
but have `p(f, s, s) = 0` on one tree edge `f`: `{A, B}` is a clade of `N` (the clade below a
vertex in its switching), yet every SNP whose clade is `{A, B}` has probability 0; and `N` displays
`AB|CD`, yet every site that contributes `AB|CD` has probability 0. So no site contributes
`AB|CD`, and the support of `Q` never equals `Q(N_r)`, with probability 1. -/
theorem theorem6_step_needs_stay :
    ∃ (N : RootedNetwork) (P : SiteParameters N Bool) (S : Finset (ℕ × ℕ)) (v : ℕ),
      N.RootedBinaryLevelOne ∧ N.Switching S ∧ N.cladeBelow S v = {0, 1} ∧
      (∀ h : SiteHistory N Bool, ∀ x y : ℕ, h.changes = {(x, y)} →
        N.cladeBelow h.switching y = {0, 1} → P.weight h = 0) ∧
      N.DisplaysQuartet quartetABCD ∧
      ∀ h : SiteHistory N Bool, quartetABCD ∈ h.quartets → P.weight h = 0 := by
  refine ⟨treeNet, alwaysChange, treeNet.edges, Address.code [false, false], treeNet_levelOne,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [treeNet_edges]
    exact support_switching caterpillar ∅ empty_separated.1
  · rw [treeNet_edges, cladeBelow_support_code caterpillar_wellLabelled empty_separated
      (by decide)]
    decide
  · intro h x y hch hclade
    have hy := head_of_clade hch (Or.inr hclade)
    subst hy
    exact weight_eq_zero hch
  · exact (baseline_displays_iff caterpillar caterpillar_wellLabelled _).mpr (by decide)
  · intro h hq
    unfold SiteHistory.quartets at hq
    split_ifs at hq with hsnp
    · obtain ⟨⟨x, y⟩, hch⟩ := Finset.card_eq_one.mp hsnp
      rw [hch, Finset.singleton_biUnion] at hq
      have hy := head_of_clade hch (Or.inl (Finset.mem_filter.mp hq).2)
      subst hy
      exact weight_eq_zero hch
    · exact absurd hq (Finset.notMem_empty _)

end Camus.External
