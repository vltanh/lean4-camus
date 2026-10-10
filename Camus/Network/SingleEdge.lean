module

public import Camus.Network.Clades
public import Camus.Preliminaries.Lemmas
public import Camus.Network.SingleEdge.Switchings

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
* `Quartet.induced_iff_taxaAt`: `Q(T)` by the clades of the non-root vertices of `T`.

## Proof outline

By Definition 1 by clades (`RootedNetwork.displays_iff_cladeBelow`), `T + e` displays `q` iff the
clade below the head of some edge of some switching cuts `q`. The switchings of `T + e` are the
subdivided `T` and the subdivided `T'` (`Realization.single_switching_cases`, in
`Camus/Network/SingleEdge/Switchings.lean`, which also computes the directed reachability in
both). The clades below the heads of the edges of the first are the clades of the non-root
vertices of `T` (`Realization.support_cladeBelow_code`), and those of the second are the clades of
`T'` (`Realization.switched_cladeBelow_code`, `Realization.switched_cladeBelow_donor`,
`Realization.switched_cladeBelow_recipient`).
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

/-- The clade of `p` is the taxon set of the subtree of `t` at `p`. -/
theorem taxaAt_eq {t sub : PhyloTree} {p : Address} (h : t.nodeAt p = some sub) :
    t.taxaAt p = sub.taxa := by
  unfold taxaAt
  rw [h]

/-- The clade of the root is the taxon set of `t`. -/
theorem taxaAt_nil (t : PhyloTree) : t.taxaAt [] = t.taxa :=
  taxaAt_eq (by cases t <;> rfl)

/-- In a well-labelled tree `t`, a taxon is in the clade of the vertex `p` iff it is a taxon of
`t` whose leaf lies below `p`. -/
theorem mem_taxaAt_iff {t : PhyloTree} (ht : t.WellLabelled) {p : Address} (hp : p ∈ t.nodes)
    (a : ℕ) : a ∈ t.taxaAt p ↔ a ∈ t.taxa ∧ p <+: Realization.leafAddress t a := by
  obtain ⟨sub, hsub⟩ := (mem_nodes_iff t p).mp hp
  rw [taxaAt_eq hsub]
  constructor
  · intro ha
    have hat := subtree_taxa_subset hsub ha
    exact ⟨hat, (subtree_taxa_iff_prefix ht hsub hat).mp ha⟩
  · rintro ⟨ha, hpa⟩
    exact (subtree_taxa_iff_prefix ht hsub ha).mpr hpa

/-- The clades of the vertices of `t` are sets of taxa of `t`. -/
theorem taxaAt_subset (t : PhyloTree) (p : Address) : t.taxaAt p ⊆ t.taxa := by
  unfold taxaAt
  split
  · exact subtree_taxa_subset (by assumption)
  · exact Finset.empty_subset _

end PhyloTree

namespace Quartet

/-- Definition 1 by the clades of the non-root vertices: `q ∈ Q(t)` iff the taxa of `q` are taxa of
`t` and the clade of some non-root vertex of `t` cuts `q`. -/
theorem induced_iff_taxaAt (q : Quartet) (t : PhyloTree) :
    q.induced t = true ↔
      q.taxa ⊆ t.taxa ∧ ∃ p ∈ t.nodes, p ≠ [] ∧ q.cutBy (t.taxaAt p) = true := by
  simp only [induced, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  refine and_congr_right fun hq => ?_
  constructor
  · rintro ⟨C, hC, hcut⟩
    obtain ⟨p, sub, hsub, rfl⟩ := (PhyloTree.clades_mem_iff t C).mp hC
    have hp0 : p ≠ [] := by
      rintro rfl
      simp only [PhyloTree.nodeAt, Option.some.injEq] at hsub
      subst sub
      exact q.cutBy_not_whole _ hq hcut
    exact ⟨p, (PhyloTree.mem_nodes_iff t p).mpr ⟨sub, hsub⟩, hp0,
      (PhyloTree.taxaAt_eq hsub).symm ▸ hcut⟩
  · rintro ⟨p, hp, _, hcut⟩
    obtain ⟨sub, hsub⟩ := (PhyloTree.mem_nodes_iff t p).mp hp
    exact ⟨sub.taxa, (PhyloTree.clades_mem_iff t _).mpr ⟨p, sub, hsub, rfl⟩,
      PhyloTree.taxaAt_eq hsub ▸ hcut⟩

end Quartet

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

/-- Membership in the clade of a vertex `p` of `T` in `T'`, for a well-labelled `T` and an
admissible pair `e = (u, w)`. A taxon `a` with leaf `ℓ` below `w` is in it iff `p` lies on the
path from `w` to `ℓ` or `p` is a strict ancestor of `u` (an ancestor of `parent(u)`); a taxon
with leaf `ℓ` outside `T_w` iff `p` is an ancestor of `ℓ`. -/
theorem mem_switchedClade_iff {t : PhyloTree} (ht : t.WellLabelled) {e : Address × Address}
    (he : Admissible t e) {p : Address} (hp : p ∈ t.nodes) (a : ℕ) :
    a ∈ switchedClade t e p ↔ a ∈ t.taxa ∧
      if e.2 <+: Realization.leafAddress t a then
        (e.2 <+: p ∧ p <+: Realization.leafAddress t a) ∨ p <+: parent e.1
      else p <+: Realization.leafAddress t a := by
  have hU := Realization.prefix_parent_iff_strict (p := p) he.2.2.1
  -- a strict ancestor of `w` does not lie below `w`
  have hsw : p <+: e.2 ∧ p ≠ e.2 → ¬e.2 <+: p := fun h h' =>
    h.2 (h.1.eq_of_length_le h'.length_le)
  -- two ancestors of the leaf of `a` are comparable
  have hcmp : e.2 <+: Realization.leafAddress t a → p <+: Realization.leafAddress t a →
      ¬(p <+: e.2 ∧ p ≠ e.2) → e.2 <+: p := by
    intro h1 h2 h3
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact h
    · by_cases hpw : p = e.2
      · exact hpw ▸ List.prefix_refl _
      · exact absurd ⟨h, hpw⟩ h3
  by_cases ha : a ∈ t.taxa
  swap
  · refine iff_of_false (fun h => ha ?_) (fun h => ha h.1)
    unfold switchedClade at h
    rcases Finset.mem_union.mp h with h | h
    · split_ifs at h
      · exact PhyloTree.taxaAt_subset t p (Finset.mem_sdiff.mp h).1
      · exact PhyloTree.taxaAt_subset t p h
    · split_ifs at h
      · exact PhyloTree.taxaAt_subset t e.2 h
      · exact absurd h (Finset.notMem_empty a)
  have hP : a ∈ t.taxaAt p ↔ p <+: Realization.leafAddress t a :=
    (PhyloTree.mem_taxaAt_iff ht hp a).trans (and_iff_right ha)
  have hW : a ∈ t.taxaAt e.2 ↔ e.2 <+: Realization.leafAddress t a :=
    (PhyloTree.mem_taxaAt_iff ht he.2.1 a).trans (and_iff_right ha)
  have hE : a ∉ (∅ : Finset ℕ) := Finset.notMem_empty a
  rw [and_iff_right ha]
  unfold switchedClade
  rw [Finset.mem_union]
  by_cases h3 : e.2 <+: Realization.leafAddress t a
  · -- the leaf of `a` is in `T_w`
    rw [ite_eq_left h3]
    by_cases h1 : p <+: e.2 ∧ p ≠ e.2 <;> by_cases h2 : p <+: e.1 ∧ p ≠ e.1
    · rw [ite_eq_left h1, ite_eq_left h2, hW]
      exact iff_of_true (Or.inr h3) (Or.inr (hU.mpr h2))
    · rw [ite_eq_left h1, ite_eq_right h2, Finset.mem_sdiff, hW]
      refine iff_of_false ?_ ?_
      · rintro (⟨_, h⟩ | h)
        · exact h h3
        · exact hE h
      · rintro (⟨h, _⟩ | h)
        · exact hsw h1 h
        · exact h2 (hU.mp h)
    · rw [ite_eq_right h1, ite_eq_left h2, hW]
      exact iff_of_true (Or.inr h3) (Or.inr (hU.mpr h2))
    · rw [ite_eq_right h1, ite_eq_right h2, hP]
      constructor
      · rintro (h | h)
        · exact Or.inl ⟨hcmp h3 h h1, h⟩
        · exact absurd h hE
      · rintro (⟨_, h⟩ | h)
        · exact Or.inl h
        · exact absurd (hU.mp h) h2
  · -- the leaf of `a` is outside `T_w`
    rw [ite_eq_right h3]
    by_cases h1 : p <+: e.2 ∧ p ≠ e.2 <;> by_cases h2 : p <+: e.1 ∧ p ≠ e.1
    · rw [ite_eq_left h1, ite_eq_left h2, Finset.mem_sdiff, hP, hW]
      constructor
      · rintro (⟨h, _⟩ | h)
        · exact h
        · exact absurd h h3
      · intro h
        exact Or.inl ⟨h, h3⟩
    · rw [ite_eq_left h1, ite_eq_right h2, Finset.mem_sdiff, hP, hW]
      constructor
      · rintro (⟨h, _⟩ | h)
        · exact h
        · exact absurd h hE
      · intro h
        exact Or.inl ⟨h, h3⟩
    · rw [ite_eq_right h1, ite_eq_left h2, hP, hW]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h h3
      · exact Or.inl
    · rw [ite_eq_right h1, ite_eq_right h2, hP]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h hE
      · exact Or.inl

end EdgeAbove

namespace Realization

section Clades

variable {t : PhyloTree} {e : Pair}

/-- The clade below the vertex `y` in a switching `S` of `T + e`: the taxa of `T` whose leaves are
reached from `y` along `S`. -/
theorem single_mem_cladeBelow {S : Finset (ℕ × ℕ)} {y a : ℕ} :
    a ∈ (graph t {e}).cladeBelow S y ↔ a ∈ t.taxa ∧
      Relation.ReflTransGen (fun a b => (a, b) ∈ S) y (Address.code (leafAddress t a)) :=
  RootedNetwork.mem_cladeBelow

/-- In the subdivided `T`, the clade below a vertex `p` of `T` is its clade in `T`. -/
theorem support_cladeBelow_code (ht : t.WellLabelled) (he : EdgeAbove.Admissible t e)
    {p : Address} (hp : p ∈ t.nodes) :
    (graph t {e}).cladeBelow (supportEdges t {e}) (Address.code p) = t.taxaAt p := by
  ext a
  rw [single_mem_cladeBelow, PhyloTree.mem_taxaAt_iff ht hp]
  exact and_congr_right fun ha => (support_reach_code he (leafAddress_mem_nodes ha)).1 p hp

/-- In the subdivided `T`, the clade below u′ is the clade of `u` in `T`. -/
theorem support_cladeBelow_donor (ht : t.WellLabelled) (he : EdgeAbove.Admissible t e) :
    (graph t {e}).cladeBelow (supportEdges t {e}) (donor t e) = t.taxaAt e.1 := by
  ext a
  rw [single_mem_cladeBelow, PhyloTree.mem_taxaAt_iff ht he.1]
  exact and_congr_right fun ha => (support_reach_code he (leafAddress_mem_nodes ha)).2.1

/-- In the subdivided `T`, the clade below w′ is the clade of `w` in `T`. -/
theorem support_cladeBelow_recipient (ht : t.WellLabelled) (he : EdgeAbove.Admissible t e) :
    (graph t {e}).cladeBelow (supportEdges t {e}) (recipient t e) = t.taxaAt e.2 := by
  ext a
  rw [single_mem_cladeBelow, PhyloTree.mem_taxaAt_iff ht he.2.1]
  exact and_congr_right fun ha => (support_reach_code he (leafAddress_mem_nodes ha)).2.2

/-- In the second switching (the tree `T'`), the clade below a vertex `p` of `T` is
`EdgeAbove.switchedClade t e p`. -/
theorem switched_cladeBelow_code (ht : t.WellLabelled) (he : EdgeAbove.Admissible t e)
    {p : Address} (hp : p ∈ t.nodes) :
    (graph t {e}).cladeBelow (switchedEdges t e) (Address.code p) =
      EdgeAbove.switchedClade t e p := by
  ext a
  rw [single_mem_cladeBelow, EdgeAbove.mem_switchedClade_iff ht he hp]
  exact and_congr_right fun ha => (switched_reach_code he (leafAddress_mem_nodes ha)).1 p hp

/-- In the second switching (the tree `T'`), the clade below u′ is the clade of `u` in `T'`
together with `T_w`. -/
theorem switched_cladeBelow_donor (ht : t.WellLabelled) (he : EdgeAbove.Admissible t e) :
    (graph t {e}).cladeBelow (switchedEdges t e) (donor t e) =
      EdgeAbove.switchedClade t e e.1 ∪ t.taxaAt e.2 := by
  have hu : ¬e.1 <+: parent e.1 := fun h => (prefix_parent_iff_strict he.2.2.1).mp h |>.2 rfl
  ext a
  rw [single_mem_cladeBelow, Finset.mem_union, EdgeAbove.mem_switchedClade_iff ht he he.1,
    PhyloTree.mem_taxaAt_iff ht he.2.1]
  constructor
  · rintro ⟨ha, h⟩
    rw [(switched_reach_code he (leafAddress_mem_nodes ha)).2.1] at h
    by_cases h3 : e.2 <+: leafAddress t a
    · exact Or.inr ⟨ha, h3⟩
    · refine Or.inl ⟨ha, ?_⟩
      rw [ite_eq_right h3]
      exact h.resolve_right h3
  · rintro (⟨ha, h⟩ | ⟨ha, h⟩)
    · refine ⟨ha, (switched_reach_code he (leafAddress_mem_nodes ha)).2.1.mpr ?_⟩
      split_ifs at h with h3
      · exact Or.inr h3
      · exact Or.inl h
    · exact ⟨ha, (switched_reach_code he (leafAddress_mem_nodes ha)).2.1.mpr (Or.inr h)⟩

/-- In the second switching (the tree `T'`), the clade below w′ is the clade of `w` in `T`. -/
theorem switched_cladeBelow_recipient (ht : t.WellLabelled) (he : EdgeAbove.Admissible t e) :
    (graph t {e}).cladeBelow (switchedEdges t e) (recipient t e) = t.taxaAt e.2 := by
  ext a
  rw [single_mem_cladeBelow, PhyloTree.mem_taxaAt_iff ht he.2.1]
  exact and_congr_right fun ha => (switched_reach_code he (leafAddress_mem_nodes ha)).2.2

/-- The clade of the root of `T` in `T'` contains every taxon of `T`. -/
theorem taxa_subset_switchedClade_root (ht : t.WellLabelled) (he : EdgeAbove.Admissible t e) :
    t.taxa ⊆ EdgeAbove.switchedClade t e [] := by
  intro a ha
  rw [EdgeAbove.mem_switchedClade_iff ht he t.root_mem_nodes]
  refine ⟨ha, ?_⟩
  split_ifs
  · exact Or.inr (List.nil_prefix)
  · exact List.nil_prefix

end Clades

/-- The quartets displayed by `T + e`: for a well-labelled `T` and an admissible pair `e`, the
network `graph t {e}` displays `q` if and only if the taxa of `q` are taxa of `T` and `q` is induced
by `T` or cut by a clade of `T'`.

The proof uses Definition 1 by clades (`RootedNetwork.displays_iff_cladeBelow`). The switchings of
`T + e` are the subdivided `T` and the switching of `T'` (`Realization.single_switching_cases`).
The clades below the heads of the edges of the first are the clades of the non-root vertices of
`T`, and those of the second are the clades of `T'` (`Realization.switched_cladeBelow_code`,
`Realization.switched_cladeBelow_donor`, `Realization.switched_cladeBelow_recipient`). -/
theorem single_displays_iff {t : PhyloTree} (ht : t.WellLabelled) {e : Address × Address}
    (he : e ∈ EdgeAbove.candidates t) (q : Quartet) :
    (graph t {e}).DisplaysQuartet q ↔
      q.taxa ⊆ t.taxa ∧
        (q.induced t = true ∨ ∃ C ∈ EdgeAbove.switchedClades t e, q.cutBy C = true) := by
  have hadm : EdgeAbove.Admissible t e := (Finset.mem_filter.mp he).2
  have hsep : EdgeAbove.CycleSeparated t {e} :=
    ⟨Finset.singleton_subset_iff.mpr he, by simp⟩
  have hN := levelOne t ht {e} hsep
  have hS0 : (graph t {e}).Switching (supportEdges t {e}) := support_switching t {e} hsep.1
  have hS1 := switched_switching hadm
  rw [RootedNetwork.displays_iff_cladeBelow hN]
  change (q.taxa ⊆ t.taxa ∧ _) ↔ _
  refine and_congr_right fun hq => ?_
  constructor
  · rintro ⟨S, hS, x, y, hxy, hcut⟩
    have hy := (hN.2.1 _ (hS.1 hxy)).2
    rcases single_switching_cases he hS with rfl | rfl
    · -- in the subdivided `T`, the clade below `y` is the clade of a non-root vertex of `T`
      left
      rw [Quartet.induced_iff_taxaAt]
      refine ⟨hq, ?_⟩
      rcases single_vertex_cases hy with ⟨p, hp, rfl⟩ | rfl | rfl
      · have hp0 : p ≠ [] := by
          rintro rfl
          exact support_incoming_root hadm x hxy
        exact ⟨p, hp, hp0, support_cladeBelow_code ht hadm hp ▸ hcut⟩
      · exact ⟨e.1, hadm.1, hadm.2.2.1, support_cladeBelow_donor ht hadm ▸ hcut⟩
      · exact ⟨e.2, hadm.2.1, hadm.2.2.2.1, support_cladeBelow_recipient ht hadm ▸ hcut⟩
    · -- in the second switching, the clade below `y` is a clade of `T'`
      right
      rcases single_vertex_cases hy with ⟨p, hp, rfl⟩ | rfl | rfl
      · refine ⟨EdgeAbove.switchedClade t e p, ?_, switched_cladeBelow_code ht hadm hp ▸ hcut⟩
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp))
      · exact ⟨_, Finset.mem_insert_self _ _, switched_cladeBelow_donor ht hadm ▸ hcut⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
          switched_cladeBelow_recipient ht hadm ▸ hcut⟩
  · rintro (hind | ⟨C, hC, hcut⟩)
    · -- a clade of `T` that cuts `q` is the clade below a vertex `p` of `T` in the subdivided `T`
      obtain ⟨_, p, hp, hp0, hcut⟩ := (Quartet.induced_iff_taxaAt q t).mp hind
      refine ⟨supportEdges t {e}, hS0, supportParent t e p, Address.code p,
        (support_incoming_code hadm hp hp0 _).mpr rfl, ?_⟩
      rw [support_cladeBelow_code ht hadm hp]
      exact hcut
    · -- a clade of `T'` that cuts `q` is the clade below a vertex in the second switching
      simp only [EdgeAbove.switchedClades, Finset.mem_insert, Finset.mem_image] at hC
      rcases hC with rfl | rfl | ⟨p, hp, rfl⟩
      · refine ⟨_, hS1, Address.code (parent e.1), donor t e,
          (switched_incoming_donor hadm _).mpr rfl, ?_⟩
        rw [switched_cladeBelow_donor ht hadm]
        exact hcut
      · refine ⟨_, hS1, donor t e, recipient t e,
          (switched_incoming_recipient hadm _).mpr rfl, ?_⟩
        rw [switched_cladeBelow_recipient ht hadm]
        exact hcut
      · have hp0 : p ≠ [] := by
          rintro rfl
          exact q.cutBy_not_whole _ (hq.trans (taxa_subset_switchedClade_root ht hadm)) hcut
        refine ⟨_, hS1, supportParent t e p, Address.code p,
          (switched_incoming_code hadm hp hp0 _).mpr rfl, ?_⟩
        rw [switched_cladeBelow_code ht hadm hp]
        exact hcut

/-- The quartets of `Q` satisfied by `T + e` (Section 2.1): those of `Q` whose taxa are taxa of
`T`, that `T` does not induce, and that a clade of `T'` cuts. -/
theorem mem_novel_single_iff {t : PhyloTree} (ht : t.WellLabelled) {e : Address × Address}
    (he : e ∈ EdgeAbove.candidates t) (Q : Multiset Quartet) (q : Quartet) :
    q ∈ DynamicProgramming.novel t Q (graph t {e}) ↔
      q ∈ Q ∧ EdgeAbove.satisfies t e q = true := by
  rw [DynamicProgramming.mem_novel_iff t ht, single_displays_iff ht he, Multiset.mem_toFinset]
  refine and_congr_right fun _ => ?_
  cases hind : q.induced t <;>
    simp [EdgeAbove.satisfies, hind]

end Realization

namespace DynamicProgramming

/-- Equation (1), computably: for an admissible pair `e`, `s_e(u, w)` is the sum over the distinct
quartets `q` of `Q` of δ_T(q, (u, w)), the multiplicity of `q` if the edge added above `e`
satisfies `q` (`EdgeAbove.satisfies`), and 0 otherwise. -/
theorem edgeWeight_eq_satisfies {t : PhyloTree} (ht : t.WellLabelled) {e : Address × Address}
    (he : e ∈ EdgeAbove.candidates t) (Q : Multiset Quartet) :
    edgeWeight t Q e =
      ∑ q ∈ Q.toFinset, if EdgeAbove.satisfies t e q = true then Q.count q else 0 := by
  unfold edgeWeight
  apply Finset.sum_congr rfl
  intro q hq
  have h := Realization.mem_novel_single_iff ht he Q q
  rw [Multiset.mem_toFinset] at hq
  by_cases hs : EdgeAbove.satisfies t e q = true
  · rw [ite_eq_left (h.mpr ⟨hq, hs⟩), ite_eq_left hs]
  · rw [ite_eq_right (fun h' => hs (h.mp h').2), ite_eq_right hs]

end DynamicProgramming

end Camus
