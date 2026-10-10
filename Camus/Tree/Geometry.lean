module

public import Camus.Defs

public import Camus.Galled.Basic
public import Mathlib.Data.List.Infix
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic.SplitIfs

/-!
# Lemma 2: one non-tree edge per target

A vertex of `T` is its address, the path from the root. The ancestor order is the prefix order
`p <+: q`, and `lca` is the longest common prefix. This file proves the basic geometry of
addresses (the vertices of `T` are closed under ancestors, and `lca p q` is the least common
ancestor of `p` and `q`), and then the paper's Lemma 2 in the form used by the dynamic program:
for a network given by its family of added edges, at most one added edge has a given target.
The form for an arbitrary level-1 network built on `T`, `lemma2`, is derived from it.

## Main results

* `PhyloTree.nodes_prefix_closed`: an ancestor of a vertex of `T` is a vertex of `T`.
* `lca_prefix_left`, `lca_prefix_right`, `prefix_lca`: `lca p q` is a common ancestor of `p` and
  `q`, and every common ancestor is an ancestor of it.
* `EdgeAbove.target_mem_footprint`: the target lca(u, w) lies on the cycle γ(u, w).
* `EdgeAbove.target_unique`: Lemma 2.

## Proof (the paper's)

If two distinct added edges had the same target v, each of their cycles would contain v
(`EdgeAbove.target_mem_footprint`), so the two cycles would share a vertex, contradicting
level-1 (`EdgeAbove.target_unique`).
-/

@[expose] public section

namespace Camus

namespace PhyloTree

/-- An address is a vertex of `t` if and only if `t` has a subtree at that address. -/
theorem mem_nodes_iff (t : PhyloTree) (p : Address) :
    p ∈ t.nodes ↔ ∃ s, t.nodeAt p = some s := by
  induction t generalizing p with
  | leaf a => cases p <;> simp [nodes, nodeAt]
  | fork l r ihl ihr =>
    cases p with
    | nil => simp [nodes, nodeAt]
    | cons b p => cases b <;> simp [nodes, nodeAt, ihl, ihr]

/-- The root `[]` is a vertex of every tree. -/
theorem root_mem_nodes (t : PhyloTree) : [] ∈ t.nodes := by
  cases t <;> simp [nodes]

/-- An ancestor of a vertex of `t` is a vertex of `t`. -/
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

/-- `lca p q` is an ancestor of `p` (or `p` itself). -/
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

/-- `lca p q` is an ancestor of `q` (or `q` itself). -/
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

/-- Every common ancestor of `p` and `q` is an ancestor of `lca p q` (or equal to it), so
`lca p q` is their least common ancestor. -/
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

/-- `lca p q = p` if and only if `p` is an ancestor of `q` (or `q` itself). -/
theorem lca_eq_left_iff (p q : Address) : lca p q = p ↔ p <+: q := by
  constructor
  · intro h; simpa only [h] using lca_prefix_right p q
  · intro h
    exact (lca_prefix_left p q).eq_of_length_le
      (prefix_lca (List.prefix_refl _) h).length_le

/-- `lca p q = q` if and only if `q` is an ancestor of `p` (or `p` itself). -/
theorem lca_eq_right_iff (p q : Address) : lca p q = q ↔ q <+: p := by
  constructor
  · intro h; simpa only [h] using lca_prefix_left p q
  · intro h
    exact (lca_prefix_right p q).eq_of_length_le
      (prefix_lca h (List.prefix_refl _)).length_le

namespace EdgeAbove

/-- The target lca(u, w) of an admissible pair `e = (u, w)` lies on the cycle γ(u, w): it is in
γ(u, w) ∩ V(T) (`EdgeAbove.footprint`). This holds for a ghost lineage (`u = lca(u, w)`) too.
It is the step "each would contain v as a node" of the proof of Lemma 2. -/
theorem target_mem_footprint (t : PhyloTree) (e : Address × Address)
    (he : Admissible t e) : target e ∈ footprint t e := by
  -- v = lca(u, w) is on the path from v to `w`, and v ≠ w since `w` is not an ancestor of `u`
  have hp := lca_prefix_right e.1 e.2
  have hnode := t.nodes_prefix_closed he.2.1 hp
  have hne : lca e.1 e.2 ≠ e.2 := by
    intro h; exact he.2.2.2.2 ((lca_eq_right_iff _ _).mp h)
  exact Finset.mem_filter.mpr ⟨hnode, List.prefix_refl _, Or.inr ⟨hp, hne⟩⟩

/-- **Lemma 2** (`mthst4`), for a network given by its family of added edges. Let `E` be a
cycle-separated family of pairs (`EdgeAbove.CycleSeparated`): the cycles γ(u, w) of distinct pairs
of `E` are vertex-disjoint, i.e. `Realization.graph t E` is level-1. If two pairs of `E` have the
same target, they are equal: at most one added edge has a given target.

The proof is the paper's: the common target lies on both cycles
(`EdgeAbove.target_mem_footprint`), so the cycles of two distinct pairs would share it. -/
theorem target_unique (t : PhyloTree) (E : Finset (Address × Address))
    (hE : CycleSeparated t E) {e f : Address × Address}
    (he : e ∈ E) (hf : f ∈ E) (ht : target e = target f) : e = f := by
  -- if e ≠ f, the cycles γ(e) and γ(f) are disjoint, yet both contain the common target
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
