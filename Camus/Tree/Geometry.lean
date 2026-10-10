module

public import Camus.Defs

public import Camus.Galled.Basic
public import Mathlib.Data.List.Infix
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace Camus

namespace PhyloTree

theorem mem_nodes_iff (t : PhyloTree) (p : Address) :
    p ∈ t.nodes ↔ ∃ s, t.nodeAt p = some s := by
  induction t generalizing p with
  | leaf a => cases p <;> simp [nodes, nodeAt]
  | fork l r ihl ihr =>
    cases p with
    | nil => simp [nodes, nodeAt]
    | cons b p => cases b <;> simp [nodes, nodeAt, ihl, ihr]

theorem root_mem_nodes (t : PhyloTree) : [] ∈ t.nodes := by
  cases t <;> simp [nodes]

/-- Every ancestor address of a tree vertex is a vertex of that same tree. -/
theorem nodes_prefix_closed (t : PhyloTree) {p q : Address}
    (hq : q ∈ t.nodes) (hpq : p <+: q) : p ∈ t.nodes := by
  induction t generalizing p q with
  | leaf a =>
    simp only [nodes, Finset.mem_singleton] at hq
    subst q
    have hp : p = [] := List.IsPrefix.eq_of_length_le hpq (by simp)
    subst p
    exact root_mem_nodes _
  | fork l r ihl ihr =>
    cases p with
    | nil => exact root_mem_nodes _
    | cons b p =>
      cases q with
      | nil => have := hpq.length_le; simp at this
      | cons c q =>
        obtain ⟨rfl, hpq'⟩ := List.cons_prefix_cons.mp hpq
        cases b
        · have hq' : q ∈ l.nodes := by simpa [nodes] using hq
          have hp' := ihl hq' hpq'
          simp [nodes, hp']
        · have hq' : q ∈ r.nodes := by simpa [nodes] using hq
          have hp' := ihr hq' hpq'
          simp [nodes, hp']

end PhyloTree

theorem lca_prefix_left (p q : Address) : lca p q <+: p := by
  induction p generalizing q with
  | nil => simp [lca]
  | cons a p ih =>
    cases q with
    | nil => simp [lca]
    | cons b q =>
      by_cases h : a = b
      · simp [lca, h, ih]
      · simp [lca, h]

theorem lca_prefix_right (p q : Address) : lca p q <+: q := by
  induction p generalizing q with
  | nil => simp [lca]
  | cons a p ih =>
    cases q with
    | nil => simp [lca]
    | cons b q =>
      by_cases h : a = b
      · subst b; simp [lca, ih]
      · simp [lca, h]

theorem prefix_lca {x p q : Address} (hp : x <+: p) (hq : x <+: q) :
    x <+: lca p q := by
  induction x generalizing p q with
  | nil => simp
  | cons a x ih =>
    cases p with
    | nil => have := hp.length_le; simp at this
    | cons b p =>
      cases q with
      | nil => have := hq.length_le; simp at this
      | cons c q =>
        obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.mp hp
        obtain ⟨rfl, hq'⟩ := List.cons_prefix_cons.mp hq
        simp [lca, ih hp' hq']

theorem lca_eq_left_iff (p q : Address) : lca p q = p ↔ p <+: q := by
  constructor
  · intro h; simpa only [h] using lca_prefix_right p q
  · intro h
    exact (lca_prefix_left p q).eq_of_length_le
      (prefix_lca (List.prefix_refl _) h).length_le

theorem lca_eq_right_iff (p q : Address) : lca p q = q ↔ q <+: p := by
  constructor
  · intro h; simpa only [h] using lca_prefix_left p q
  · intro h
    exact (lca_prefix_right p q).eq_of_length_le
      (prefix_lca h (List.prefix_refl _)).length_le

namespace EdgeAbove

/-- The geometric step in Lemma 2: an admissible edge's LCA really lies on its
cycle's original-vertex footprint, including an edge from a ghost lineage. -/
theorem target_mem_footprint (t : PhyloTree) (e : Address × Address)
    (he : Admissible t e) : target e ∈ footprint t e := by
  have hp := lca_prefix_right e.1 e.2
  have hnode := t.nodes_prefix_closed he.2.1 hp
  have hne : lca e.1 e.2 ≠ e.2 := by
    intro h; exact he.2.2.2.2 ((lca_eq_right_iff _ _).mp h)
  exact Finset.mem_filter.mpr ⟨hnode, List.prefix_refl _, Or.inr ⟨hp, hne⟩⟩

/-- Lemma 2 (`mthst4`) in the concrete tree-path model: two distinct disjoint cycles cannot
share a target. The proof is precisely the paper's shared-vertex contradiction.
The graph/path representation bridge is proved separately in the graph library. -/
theorem target_unique (t : PhyloTree) (E : Finset (Address × Address))
    (hE : CycleSeparated t E) {e f : Address × Address}
    (he : e ∈ E) (hf : f ∈ E) (ht : target e = target f) : e = f := by
  by_contra hne
  have ha := (Finset.mem_filter.mp (hE.1 he)).2
  have hb := (Finset.mem_filter.mp (hE.1 hf)).2
  have hdis := hE.2 he hf hne
  have hxe := target_mem_footprint t e ha
  have hxf := target_mem_footprint t f hb
  rw [← ht] at hxf
  exact Finset.disjoint_left.mp hdis hxe hxf

end EdgeAbove
end Camus
