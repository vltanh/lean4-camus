module

public import Camus.GraphCompletenessEncoding

@[expose] public section

namespace Camus.SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

noncomputable def site (H : SupportSubdivision t N S) (v : ℕ) : Address :=
  if ∃ p ∈ t.nodes, H.original p = v then H.originalAddress v else H.anchor v

theorem site_original (H : SupportSubdivision t N S) {p : Address}
    (hp : p ∈ t.nodes) : H.site (H.original p) = p := by
  classical
  unfold site
  rw [ite_eq_left (show ∃ q ∈ t.nodes, H.original q = H.original p from ⟨p,hp,rfl⟩)]
  exact H.originalAddress_original hp

theorem site_interior (H : SupportSubdivision t N S) {p : Address}
    (hp : p ∈ t.nodes) (hp0 : p ≠ []) {v : ℕ} (hv : v ∈ wireInterior (H.wire p)) :
    H.site v = p := by
  classical
  unfold site
  rw [ite_eq_right (show ¬∃ q ∈ t.nodes, H.original q = v from
    fun ho => H.interior_not_original hp hp0 hv (Finset.mem_image.mpr ho))]
  exact H.anchor_eq hp hp0 hv

theorem site_source_deleted (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    H.site e.1 = H.anchor e.1 := by
  have hu := H.deleted_source_anchor_spec hN he
  exact H.site_interior hu.1 hu.2.1 hu.2.2

theorem site_target_deleted (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    H.site e.2 = H.anchor e.2 := by
  have hw := H.deleted_target_anchor_spec hN he
  exact H.site_interior hw.1 hw.2.1 hw.2.2

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

/-- The original-tree part of a candidate cycle lies on its actual fundamental
cycle. Each original vertex separates the two endpoint wires into child clades. -/
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
