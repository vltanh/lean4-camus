module

public import Camus.Network.Completeness.Encoding

/-!
# Footprints lie on the cycles of non-tree edges

The footprint `EdgeAbove.footprint t (u, w)` is the set of vertices of `T` on the cycle `γ(u, w)`
that adding an edge above `(u, w)` creates (Definition 3). This file shows that for a non-tree
edge `d` with pair `(u, w)`, the original copy of each footprint vertex lies on the cycle of `d`
in `N`. As the cycles of distinct non-tree edges are disjoint, so are their footprints: the
extracted family is cycle-separated (`SupportSubdivision.extracted_separated`).

The proof assigns to each vertex `v` of `N` the vertex `H.site v` of `T` at which it sits: `p`
for `H.original p` and for the vertices inside the wire of `p`. A switching path from a vertex
sited at or below `a` to a vertex sited elsewhere passes through `H.original (parent a)`. A child
of a footprint vertex `x` is an ancestor of one of `u` and `w` but not of the other, so the
switching path between the endpoints of `d` passes through `H.original x`.

## Main results

* `SupportSubdivision.site`: the vertex of `T` at which a vertex of `N` sits.
* `SupportSubdivision.support_path_crosses_parent`: a switching path leaving the clade below `a`
  passes through `H.original (parent a)`.
* `SupportSubdivision.footprint_mem_fundamentalCycle`: the footprint of the pair of a non-tree
  edge lies on its cycle.
-/

@[expose] public section

namespace Camus.SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- The vertex of `T` at which a vertex `v` of `N` sits: `p` if `v = H.original p`, and the
anchor of `v` if `v` lies inside a wire. So a vertex inside the wire of `p` sits at `p`. -/
noncomputable def site (H : SupportSubdivision t N S) (v : ℕ) : Address :=
  if ∃ p ∈ t.nodes, H.original p = v then H.originalAddress v else H.anchor v

/-- `H.original p` sits at `p`. -/
theorem site_original (H : SupportSubdivision t N S) {p : Address}
    (hp : p ∈ t.nodes) : H.site (H.original p) = p := by
  classical
  unfold site
  rw [ite_eq_left (show ∃ q ∈ t.nodes, H.original q = H.original p from ⟨p,hp,rfl⟩)]
  exact H.originalAddress_original hp

/-- A vertex inside the wire of `p` sits at `p`. -/
theorem site_interior (H : SupportSubdivision t N S) {p : Address}
    (hp : p ∈ t.nodes) (hp0 : p ≠ []) {v : ℕ} (hv : v ∈ wireInterior (H.wire p)) :
    H.site v = p := by
  classical
  unfold site
  rw [ite_eq_right (show ¬∃ q ∈ t.nodes, H.original q = v from
    fun ho => H.interior_not_original hp hp0 hv (Finset.mem_image.mpr ho))]
  exact H.anchor_eq hp hp0 hv

/-- The tail of a non-tree edge sits at its anchor. -/
theorem site_source_deleted (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    H.site e.1 = H.anchor e.1 := by
  have hu := H.deleted_source_anchor_spec hN he
  exact H.site_interior hu.1 hu.2.1 hu.2.2

/-- The head of a non-tree edge sits at its anchor. -/
theorem site_target_deleted (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    H.site e.2 = H.anchor e.2 := by
  have hw := H.deleted_target_anchor_spec hN he
  exact H.site_interior hw.1 hw.2.1 hw.2.2

/-- A switching edge `(x, y)` lies on the wire of a non-root vertex `p`; `y` sits at `p`, and
either `x` sits at `p` or `x = H.original (parent p)`, which sits at `parent p`. -/
theorem support_edge_sites (H : SupportSubdivision t N S) {e : ℕ × ℕ}
    (he : e ∈ S) :
    ∃ p ∈ t.nodes, p ≠ [] ∧ H.site e.2 = p ∧
      (H.site e.1 = p ∨ (e.1 = H.original (parent p) ∧ H.site e.1 = parent p)) := by
  classical
  rw [H.edges_covered] at he
  obtain ⟨p,hp,hep⟩ := Finset.mem_biUnion.mp he
  obtain ⟨hp0,hp⟩ := Finset.mem_erase.mp hp
  refine ⟨p,hp,hp0,?_,?_⟩
  · rcases H.tail_wire_cases hp hp0 (wire_edge_target_mem hep) with hi | ho
    · exact H.site_interior hp hp0 hi
    · rw [ho]
      exact H.site_original hp
  · rcases wire_vertex_cases (List.mem_of_mem_dropLast (wire_edge_source_mem hep))
      with hhead | hlast | hinner
    · have ho : e.1 = H.original (parent p) := Option.some.inj
        (hhead.symm.trans (H.wire_laws p hp hp0).2.2.1)
      refine Or.inr ⟨ho,?_⟩
      rw [ho]
      exact H.site_original (t.nodes_prefix_closed hp (parent_prefix _))
    · have ho : e.1 = H.original p := Option.some.inj
        (hlast.symm.trans (H.wire_laws p hp hp0).2.2.2.1)
      apply Or.inl
      rw [ho]
      exact H.site_original hp
    · exact Or.inl (H.site_interior hp hp0 hinner)

/-- If a switching edge `(x, y)` has one end sited at or below `a` and the other not, then
`x = H.original (parent a)`. -/
theorem support_clade_boundary (H : SupportSubdivision t N S) {a : Address}
    {e : ℕ × ℕ} (he : e ∈ S)
    (hcross : (a <+: H.site e.1) ≠ (a <+: H.site e.2)) :
    e.1 = H.original (parent a) := by
  obtain ⟨p,hp,hp0,ht,hs⟩ := H.support_edge_sites he
  rcases hs with hs | ⟨horig,hs⟩
  · exact False.elim (hcross (by rw [hs,ht]))
  · rw [hs,ht] at hcross
    have hnot : ¬a <+: parent p := by
      intro ha
      exact hcross (propext ⟨fun _ => ha.trans (parent_prefix _),fun _ => ha⟩)
    have hain : a <+: p := by
      by_contra ha
      exact hcross (propext ⟨fun h => False.elim (hnot h),fun h => False.elim (ha h)⟩)
    have hap : a = p := by
      by_contra hne
      exact hnot (prefix_parent_of_ne hain hne)
    simpa only [hap] using horig

/-- A walk of the switching from a vertex sited at or below `a` to a vertex sited elsewhere
passes through `H.original (parent a)`. -/
theorem support_path_crosses_parent (H : SupportSubdivision t N S)
    {a : Address} {u v : ℕ} (p : ({N with edges := S}).underlying.Walk u v)
    (hu : a <+: H.site u) (hv : ¬a <+: H.site v) :
    H.original (parent a) ∈ p.support := by
  induction p with
  | nil => exact False.elim (hv hu)
  | @cons u w v hadj p ih =>
    by_cases hw : a <+: H.site w
    · exact List.mem_cons_of_mem _ (ih hw hv)
    · have hcross : (a <+: H.site u) ≠ (a <+: H.site w) := by
        intro h
        exact hw (h ▸ hu)
      rcases hadj.2 with he | he
      · have heq := H.support_clade_boundary he hcross
        exact List.mem_cons.mpr (Or.inl heq.symm)
      · have heq := H.support_clade_boundary he hcross.symm
        exact List.mem_cons_of_mem _ (heq.symm ▸ p.start_mem_support)

/-- For `x` in the footprint of `(u, w)`, some child `x ++ [b]` of `x` is an ancestor of one of
`u` and `w` but not of the other. -/
theorem footprint_child_separates {e : Address × Address} {x : Address}
    (hx : x ∈ EdgeAbove.footprint t e) :
    ∃ b : Bool, (x ++ [b] <+: e.1 ∧ ¬x ++ [b] <+: e.2) ∨
      (x ++ [b] <+: e.2 ∧ ¬x ++ [b] <+: e.1) := by
  obtain ⟨hxnode,htx,hbranch⟩ := Finset.mem_filter.mp hx
  have hboth : ∀ b, ¬(x ++ [b] <+: e.1 ∧ x ++ [b] <+: e.2) := by
    intro b h
    have hprefix := (prefix_lca h.1 h.2).trans htx
    have := hprefix.length_le
    simp only [List.length_append, List.length_singleton] at this
    omega
  rcases hbranch with ⟨hxu,hne⟩ | ⟨hxw,hne⟩
  · rcases prefix_child_cases hxu hne with hleft | hright
    · exact ⟨false,Or.inl ⟨hleft,fun hw => hboth false ⟨hleft,hw⟩⟩⟩
    · exact ⟨true,Or.inl ⟨hright,fun hw => hboth true ⟨hright,hw⟩⟩⟩
  · rcases prefix_child_cases hxw hne with hleft | hright
    · exact ⟨false,Or.inr ⟨hleft,fun hu => hboth false ⟨hu,hleft⟩⟩⟩
    · exact ⟨true,Or.inr ⟨hright,fun hu => hboth true ⟨hu,hright⟩⟩⟩

/-- Let `d` be a non-tree edge with pair `(u, w)`. For every vertex `x` of `T` on `γ(u, w)`, that
is, in the footprint of `(u, w)`, `H.original x` lies on the cycle of `d`. A child of `x` is an
ancestor of one of `u` and `w` but not of the other, so the switching path between the endpoints
of `d` leaves the clade below that child, through `H.original x`. -/
theorem footprint_mem_fundamentalCycle (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges \ S)
    {x : Address} (hx : x ∈ EdgeAbove.footprint t (H.pairOf e)) :
    H.original x ∈ (RootedNetwork.fundamentalCycle hN H.switching he).support := by
  classical
  obtain ⟨b,hsep⟩ := footprint_child_separates hx
  let p := (RootedNetwork.supportPath hN H.switching he).val
  have hinp : H.original x ∈ p.support := by
    rcases hsep with ⟨hu,hw⟩ | ⟨hw,hu⟩
    · have hcoloru : x ++ [b] <+: H.site e.1 := by
        simpa only [H.site_source_deleted hN he, pairOf] using hu
      have hcolorw : ¬x ++ [b] <+: H.site e.2 := by
        simpa only [H.site_target_deleted hN he, pairOf] using hw
      have hmem := H.support_path_crosses_parent p.reverse hcoloru hcolorw
      simpa only [parent_child, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hmem
    · have hcolorw : x ++ [b] <+: H.site e.2 := by
        simpa only [H.site_target_deleted hN he, pairOf] using hw
      have hcoloru : ¬x ++ [b] <+: H.site e.1 := by
        simpa only [H.site_source_deleted hN he, pairOf] using hu
      have hmem := H.support_path_crosses_parent p hcolorw hcoloru
      simpa only [parent_child] using hmem
  change H.original x ∈ e.1 :: (p.mapLe _).support
  rw [SimpleGraph.Walk.support_mapLe_eq_support]
  exact List.mem_cons_of_mem _ hinp

end Camus.SupportSubdivision
