module

public import Camus.Network.Completeness.Degrees
public import Mathlib.Data.List.Chain

/-!
# Directed reachability along wires

This file follows directed paths of switching edges. Along a wire each vertex reaches every later
vertex, and `H.original p` reaches `H.original q` whenever `p` is an ancestor of `q` in `T`.
Since `N` is acyclic, the anchor `w` of the head of a non-tree edge is not a strict ancestor of
the anchor `u` of its tail. With `u ≠ w` (`SupportSubdivision.deleted_anchors_ne`) this shows
that the pair `(u, w)` of Definition 2 is admissible
(`SupportSubdivision.deleted_pair_admissible`).

## Main results

* `wire_chain`: a relation that holds on the edges of a wire holds between its consecutive
  vertices.
* `SupportSubdivision.original_reachable_of_prefix`: an ancestor in `T` reaches its descendants
  along switching edges.
* `SupportSubdivision.deleted_anchor_not_strict_ancestor`: if `w` is an ancestor of `u`, then
  `w = u`.
-/

@[expose] public section

namespace Camus

/-- If a relation `R` holds on every edge of the wire `l`, it holds between consecutive vertices
of `l`. -/
theorem wire_chain {R : ℕ → ℕ → Prop} (l : List ℕ)
    (h : ∀ e ∈ wireEdges l, R e.1 e.2) : l.IsChain R := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    cases l with
    | nil => exact .singleton _
    | cons b l =>
      apply List.IsChain.cons_cons
      · exact h (a,b) (by simp [wireEdges])
      · apply ih
        intro e he
        apply h e
        simpa [wireEdges] using Or.inr he

namespace SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- Along the wire of `p`, each vertex reaches every later vertex along switching edges. -/
theorem wire_reachability_pairwise (H : SupportSubdivision t N S)
    {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ []) :
    (H.wire p).Pairwise (Relation.ReflTransGen (fun u v => (u,v) ∈ S)) := by
  apply List.isChain_iff_pairwise.mp
  apply wire_chain
  intro e he
  exact Relation.ReflTransGen.single (H.wire_edge_mem_support hp hp0 he)

/-- `H.original (parent p)` reaches every vertex of the wire of `p` along switching edges. -/
theorem wire_reachable_from_head (H : SupportSubdivision t N S)
    {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ []) {v : ℕ}
    (hv : v ∈ H.wire p) :
    Relation.ReflTransGen (fun u w => (u,w) ∈ S) (H.original (parent p)) v := by
  have hlist : H.wire p ≠ [] := by
    have := (H.wire_laws p hp hp0).1
    intro hl
    simp [hl] at this
  have hhead : (H.wire p).head hlist = H.original (parent p) := by
    exact Option.some.inj ((List.head?_eq_some_head hlist).symm.trans
      (H.wire_laws p hp hp0).2.2.1)
  rw [← hhead]
  exact (H.wire_reachability_pairwise hp hp0).rel_head hv

/-- Every vertex of the wire of `p` reaches `H.original p` along switching edges. -/
theorem wire_reachable_to_last (H : SupportSubdivision t N S)
    {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ []) {v : ℕ}
    (hv : v ∈ H.wire p) :
    Relation.ReflTransGen (fun u w => (u,w) ∈ S) v (H.original p) := by
  have hlist : H.wire p ≠ [] := by
    have := (H.wire_laws p hp hp0).1
    intro hl
    simp [hl] at this
  have hlast : (H.wire p).getLast hlist = H.original p := by
    exact Option.some.inj ((List.getLast?_eq_some_getLast hlist).symm.trans
      (H.wire_laws p hp hp0).2.2.2.1)
  rw [← hlast]
  exact (H.wire_reachability_pairwise hp hp0).rel_getLast hv

/-- `H.original (parent p)` reaches `H.original p` along switching edges. -/
theorem wire_head_reaches_last (H : SupportSubdivision t N S)
    {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ []) :
    Relation.ReflTransGen (fun u w => (u,w) ∈ S)
      (H.original (parent p)) (H.original p) := by
  apply H.wire_reachable_to_last hp hp0
  apply List.mem_of_mem_head?
  rw [(H.wire_laws p hp hp0).2.2.1]
  simp

/-- If `p` is an ancestor of `q` in `T`, then `H.original p` reaches `H.original q` along
switching edges. -/
theorem original_reachable_of_prefix (H : SupportSubdivision t N S)
    {p q : Address} (hq : q ∈ t.nodes) (hpq : p <+: q) :
    Relation.ReflTransGen (fun u w => (u,w) ∈ S) (H.original p) (H.original q) := by
  obtain ⟨r,rfl⟩ := hpq
  induction r using List.reverseRecOn with
  | nil => simpa only [List.append_nil] using (Relation.ReflTransGen.refl (r := fun u w => (u,w) ∈
      S) (a := H.original p))
  | append_singleton r b ih =>
    have hpbr : p ++ (r ++ [b]) = (p ++ r) ++ [b] := List.append_assoc _ _ _ |>.symm
    have hpr : p ++ r ∈ t.nodes :=
      t.nodes_prefix_closed hq (by rw [hpbr]; exact List.prefix_append _ _)
    have h0 : p ++ (r ++ [b]) ≠ [] := by simp
    have hwire := H.wire_head_reaches_last hq h0
    rw [hpbr, parent_child] at hwire
    rw [hpbr]
    exact (ih hpr).trans hwire

/-- Let `d = (u', w')` be a non-tree edge with anchors `u` and `w`. If `w` is an ancestor of `u`,
then `w = u`. Otherwise `w'` reaches `H.original w`, which reaches `H.original (parent u)`, which
reaches `u'`, all along switching edges, and `d` closes a directed cycle. -/
theorem deleted_anchor_not_strict_ancestor (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges \ S)
    (hpref : H.anchor e.2 <+: H.anchor e.1) : H.anchor e.2 = H.anchor e.1 := by
  by_contra hne
  have hu := H.deleted_source_anchor_spec hN he
  have hw := H.deleted_target_anchor_spec hN he
  have hrw := H.wire_reachable_to_last hw.1 hw.2.1
    (List.mem_of_mem_tail (List.mem_of_mem_dropLast (List.mem_toFinset.mp hw.2.2)))
  have hwpu := H.original_reachable_of_prefix
    (t.nodes_prefix_closed hu.1 (parent_prefix _)) (prefix_parent_of_ne hpref hne)
  have hrpu := H.wire_reachable_from_head hu.1 hu.2.1
    (List.mem_of_mem_tail (List.mem_of_mem_dropLast (List.mem_toFinset.mp hu.2.2)))
  have hpath := hrw.trans (hwpu.trans hrpu)
  have hpathN := Relation.ReflTransGen.mono
    (fun a b hab => H.switching.1 hab) e.2 e.1 hpath
  exact hN.2.2.1 e.2 ((Relation.TransGen.single (Finset.mem_sdiff.mp he).1).trans_right hpathN)

end SupportSubdivision
end Camus
