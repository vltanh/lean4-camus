module

public import Camus.DP.Packing
public import Camus.Network.Realization.Basic

@[expose] public section

namespace Camus

theorem parent_child (p : Address) (b : Bool) : parent (p ++ [b]) = p := by
  simp [parent]

theorem lca_append (p u w : Address) : lca (p ++ u) (p ++ w) = p ++ lca u w := by
  induction p with
  | nil => rfl
  | cons b p ih => simp [lca, ih]

theorem lca_of_child_branches {p u w : Address}
    (hu : p ++ [false] <+: u) (hw : p ++ [true] <+: w) : lca u w = p := by
  obtain ⟨s, rfl⟩ := hu
  obtain ⟨r, rfl⟩ := hw
  simpa [List.append_assoc, lca] using lca_append p (false :: s) (true :: r)

theorem lca_comm (u w : Address) : lca u w = lca w u := by
  induction u generalizing w with
  | nil => cases w <;> rfl
  | cons b u ih =>
    cases w with
    | nil => rfl
    | cons c w =>
      by_cases h : b = c
      · subst c; simp [lca, ih]
      · simp [lca, h, Ne.symm h]

namespace PhyloTree

theorem fork_at_proper_ancestor {t : PhyloTree} {x u : Address}
    (hu : u ∈ t.nodes) (hxu : x <+: u) (hne : x ≠ u) :
    ∃ l r, t.nodeAt x = some (.fork l r) := by
  have hx := t.nodes_prefix_closed hu hxu
  obtain ⟨sub, hs⟩ := (t.mem_nodes_iff x).mp hx
  cases sub with
  | leaf a => exact (hne (leaf_no_descendant hs hu hxu)).elim
  | fork l r => exact ⟨l, r, hs⟩

end PhyloTree

namespace EdgeAbove

/-- Whether the original child branch touches the subdivided cycle, including
the fresh endpoint placed immediately above u or w. -/
def touches (e : Address × Address) (p : Address) (b : Bool) : Prop :=
  p ++ [b] <+: e.1 ∨ p ++ [b] <+: e.2

theorem footprint_fork {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) {x : Address} (hx : x ∈ footprint t e) :
    ∃ l r, t.nodeAt x = some (.fork l r) := by
  rcases (Finset.mem_filter.mp hx).2.2 with hu | hw
  · exact PhyloTree.fork_at_proper_ancestor he.1 hu.1 hu.2
  · exact PhyloTree.fork_at_proper_ancestor he.2.1 hw.1 hw.2

theorem child_cycle_iff {t : PhyloTree} {e : Address × Address}
    {p : Address} {b : Bool} (hp : p ∈ footprint t e)
    (hchild : p ++ [b] ∈ t.nodes) :
    Realization.child t e p b ∈ Realization.cycleVertices t e ↔ touches e p b := by
  rw [Realization.child_mem_cycleVertices_iff hchild]
  have hbelow := (Finset.mem_filter.mp hp).2.1
  constructor
  · rintro (hu | hw | hf)
    · exact Or.inl (hu ▸ List.prefix_refl _)
    · exact Or.inr (hw ▸ List.prefix_refl _)
    · exact ((Finset.mem_filter.mp hf).2.2).imp And.left And.left
  · intro h
    rcases h with hu | hw
    · by_cases heq : p ++ [b] = e.1
      · exact Or.inl heq
      · exact Or.inr (Or.inr (Finset.mem_filter.mpr
          ⟨hchild, hbelow.trans (List.prefix_append _ _), Or.inl ⟨hu, heq⟩⟩))
    · by_cases heq : p ++ [b] = e.2
      · exact Or.inr (Or.inl heq)
      · exact Or.inr (Or.inr (Finset.mem_filter.mpr
          ⟨hchild, hbelow.trans (List.prefix_append _ _), Or.inr ⟨hw, heq⟩⟩))

theorem touches_some {t : PhyloTree} {e : Address × Address} {p : Address}
    (hp : p ∈ footprint t e) : touches e p false ∨ touches e p true := by
  rcases (Finset.mem_filter.mp hp).2.2 with hu | hw
  · rcases prefix_child_cases hu.1 hu.2 with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
  · rcases prefix_child_cases hw.1 hw.2 with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

theorem touches_both_target {e : Address × Address} {p : Address}
    (hl : touches e p false) (hr : touches e p true) : target e = p := by
  rcases hl with hlu | hlw <;> rcases hr with hru | hrw
  · exact (child_cones_disjoint p ⟨e.1, hlu, hru⟩).elim
  · exact lca_of_child_branches hlu hrw
  · exact (lca_comm _ _).trans (lca_of_child_branches hlw hru)
  · exact (child_cones_disjoint p ⟨e.2, hlw, hrw⟩).elim

theorem child_not_prefix_self (p : Address) (b : Bool) : ¬p ++ [b] <+: p := by
  intro h
  have := h.length_le
  simp at this

theorem touches_both_not_donor {e : Address × Address} {p : Address}
    (hl : touches e p false) (hr : touches e p true) : p ≠ e.1 := by
  intro hp
  rcases hl with hlu | hlw <;> rcases hr with hru | hrw
  · exact child_not_prefix_self p false (hp ▸ hlu)
  · exact child_not_prefix_self p false (hp ▸ hlu)
  · exact child_not_prefix_self p true (hp ▸ hru)
  · exact child_cones_disjoint p ⟨e.2, hlw, hrw⟩

noncomputable def branchVertices (t : PhyloTree) (e : Address × Address) : Finset Address :=
  if target e = e.1 then footprint t e else (footprint t e).erase (target e)

theorem mem_branchVertices {t : PhyloTree} {e : Address × Address} {p : Address} :
    p ∈ branchVertices t e ↔ p ∈ footprint t e ∧ (p ≠ target e ∨ target e = e.1) := by
  classical
  by_cases h : target e = e.1 <;> simp [branchVertices, h, and_comm]

theorem branch_touches_unique {t : PhyloTree} {e : Address × Address} {p : Address}
    (hp : p ∈ branchVertices t e) : ¬(touches e p false ∧ touches e p true) := by
  intro h
  obtain ⟨_, hne | hghost⟩ := mem_branchVertices.mp hp
  · exact hne (touches_both_target h.1 h.2).symm
  · exact touches_both_not_donor h.1 h.2
      ((touches_both_target h.1 h.2).symm.trans hghost)

theorem offChild_properties {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) {p : Address} (hp : p ∈ branchVertices t e) :
    Realization.offChild t e p ∈ DynamicProgramming.hanging t e ∧
      Realization.offChild t e p ≠ e.1 ∧ Realization.offChild t e p ≠ e.2 ∧
      parent (Realization.offChild t e p) = p := by
  classical
  have hpf := (mem_branchVertices.mp hp).1
  obtain ⟨l, r, hnode⟩ := footprint_fork he hpf
  have hleft := PhyloTree.child_mem_nodes hnode false
  have hright := PhyloTree.child_mem_nodes hnode true
  have hsome := touches_some hpf
  have hunique := branch_touches_unique hp
  have off_properties (b : Bool) (hchild : p ++ [b] ∈ t.nodes)
      (hnot : ¬ touches e p b) :
      p ++ [b] ∈ DynamicProgramming.hanging t e ∧
        p ++ [b] ≠ e.1 ∧ p ++ [b] ≠ e.2 ∧ parent (p ++ [b]) = p := by
    refine ⟨Finset.mem_filter.mpr ⟨hchild, by simp, by simpa only [parent_child] using hpf, ?_⟩,
      ?_, ?_, parent_child p b⟩
    · intro h
      exact hnot (((Finset.mem_filter.mp h).2.2).imp And.left And.left)
    · intro h
      exact hnot (Or.inl (h ▸ List.prefix_refl _))
    · intro h
      exact hnot (Or.inr (h ▸ List.prefix_refl _))
  unfold Realization.offChild
  by_cases hl : touches e p false
  · have hmem := (child_cycle_iff hpf hleft).mpr hl
    rw [ite_eq_right (not_not.mpr hmem)]
    exact off_properties true hright (fun hr => hunique ⟨hl, hr⟩)
  · have hnot := (child_cycle_iff hpf hleft).not.mpr hl
    rw [ite_eq_left hnot]
    exact off_properties false hleft hl

theorem offChild_injective {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) :
    Set.InjOn (Realization.offChild t e) (branchVertices t e) := by
  intro p hp q hq heq
  have hp' := (offChild_properties he hp).2.2.2
  have hq' := (offChild_properties he hq).2.2.2
  exact hp'.symm.trans ((congrArg parent heq).trans hq')

theorem parent_ne_self {p : Address} (hp : p ≠ []) : parent p ≠ p := by
  intro h
  have hlen := congrArg List.length h
  have hpos : 0 < p.length := by cases p <;> simp_all
  simp only [parent, List.length_take] at hlen
  omega

theorem recipient_not_footprint {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) : e.2 ∉ footprint t e := by
  intro h
  rcases (Finset.mem_filter.mp h).2.2 with hu | hw
  · exact he.2.2.2.2 hu.1
  · exact hw.2 rfl

theorem donor_not_footprint {t : PhyloTree} {e : Address × Address}
    (hcross : target e ≠ e.1) : e.1 ∉ footprint t e := by
  intro h
  rcases (Finset.mem_filter.mp h).2.2 with hu | hw
  · exact hu.2 rfl
  · exact hcross ((lca_eq_left_iff _ _).mpr hw.1)

theorem parent_recipient_mem {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) : parent e.2 ∈ footprint t e := by
  have hneq : target e ≠ e.2 := by
    intro h
    exact he.2.2.2.2 ((lca_eq_right_iff _ _).mp h)
  exact Finset.mem_filter.mpr ⟨t.nodes_prefix_closed he.2.1 (parent_prefix _),
    prefix_parent_of_ne (lca_prefix_right _ _) hneq,
    Or.inr ⟨parent_prefix _, parent_ne_self he.2.2.2.1⟩⟩

theorem parent_donor_mem {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) (hcross : target e ≠ e.1) : parent e.1 ∈ footprint t e := by
  exact Finset.mem_filter.mpr ⟨t.nodes_prefix_closed he.1 (parent_prefix _),
    prefix_parent_of_ne (lca_prefix_left _ _) hcross,
    Or.inl ⟨parent_prefix _, parent_ne_self he.2.2.1⟩⟩

theorem recipient_mem_frontier {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) : e.2 ∈ DynamicProgramming.hanging t e :=
  Finset.mem_filter.mpr ⟨he.2.1, he.2.2.2.1,
    parent_recipient_mem he, recipient_not_footprint he⟩

theorem donor_mem_frontier {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) (hcross : target e ≠ e.1) : e.1 ∈ DynamicProgramming.hanging t e :=
  Finset.mem_filter.mpr ⟨he.1, he.2.2.1, parent_donor_mem he hcross,
    donor_not_footprint hcross⟩

theorem cross_target_touches_both {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) (hcross : target e ≠ e.1) :
    touches e (target e) false ∧ touches e (target e) true := by
  have hneq : target e ≠ e.2 := by
    intro h
    exact he.2.2.2.2 ((lca_eq_right_iff _ _).mp h)
  have same_impossible (b : Bool) (hu : target e ++ [b] <+: e.1)
      (hw : target e ++ [b] <+: e.2) : False := by
    exact child_not_prefix_self (target e) b (prefix_lca hu hw)
  rcases prefix_child_cases (lca_prefix_left _ _) hcross with hu | hu <;>
    rcases prefix_child_cases (lca_prefix_right _ _) hneq with hw | hw
  · exact (same_impossible false hu hw).elim
  · exact ⟨Or.inl hu, Or.inr hw⟩
  · exact ⟨Or.inr hw, Or.inl hu⟩
  · exact (same_impossible true hu hw).elim

theorem frontier_nonendpoint {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) {r : Address} (hr : r ∈ DynamicProgramming.hanging t e)
    (hru : r ≠ e.1) (hrw : r ≠ e.2) :
    ∃ p ∈ branchVertices t e, Realization.offChild t e p = r := by
  classical
  obtain ⟨hrnode, hrnil, hpfoot, hrnot⟩ := Finset.mem_filter.mp hr
  let p := parent r
  let b := r.getLast hrnil
  have hrchild : p ++ [b] = r := by
    exact List.take_append_getLast r hrnil
  have hchild : p ++ [b] ∈ t.nodes := hrchild ▸ hrnode
  have hnot : ¬touches e p b := by
    rw [← child_cycle_iff hpfoot hchild, Realization.child_mem_cycleVertices_iff hchild]
    simpa only [hrchild] using not_or.mpr ⟨hru, not_or.mpr ⟨hrw, hrnot⟩⟩
  have hpbranch : p ∈ branchVertices t e := by
    rw [mem_branchVertices]
    refine ⟨hpfoot, ?_⟩
    by_cases hpt : p = target e
    · by_cases hg : target e = e.1
      · exact Or.inr hg
      · have hboth := cross_target_touches_both he hg
        rw [← hpt] at hboth
        cases hb : b
        · exact (hnot (hb ▸ hboth.1)).elim
        · exact (hnot (hb ▸ hboth.2)).elim
    · exact Or.inl hpt
  refine ⟨p, hpbranch, ?_⟩
  unfold Realization.offChild
  cases hb : b
  · have hn := (child_cycle_iff hpfoot (hb ▸ hchild)).not.mpr (hb ▸ hnot)
    rw [ite_eq_left hn]
    simpa only [hb] using hrchild
  · have hl : touches e p false := by
      rcases touches_some hpfoot with hl | ht
      · exact hl
      · exact (hnot (hb ▸ ht)).elim
    obtain ⟨l, rr, hnode⟩ := footprint_fork he hpfoot
    have hlchild := PhyloTree.child_mem_nodes hnode false
    have hmem := (child_cycle_iff hpfoot hlchild).mpr hl
    rw [ite_eq_right (not_not.mpr hmem)]
    simpa only [hb] using hrchild

theorem endpoints_distinct {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) : e.2 ≠ e.1 := by
  intro h
  exact he.2.2.2.2 (h ▸ List.prefix_refl _)

theorem frontier_ghost {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) (hg : target e = e.1) :
    DynamicProgramming.hanging t e =
      insert e.2 ((branchVertices t e).image (Realization.offChild t e)) := by
  classical
  ext r
  constructor
  · intro hr
    by_cases hw : r = e.2
    · exact Finset.mem_insert.mpr (Or.inl hw)
    · have hu : r ≠ e.1 := by
        intro hu
        have hm := target_mem_footprint t e he
        rw [hg, ← hu] at hm
        exact (Finset.mem_filter.mp hr).2.2.2 hm
      obtain ⟨p, hp, heq⟩ := frontier_nonendpoint he hr hu hw
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨p, hp, heq⟩))
  · intro hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact recipient_mem_frontier he
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
      exact (offChild_properties he hp).1

theorem frontier_cross {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) (hc : target e ≠ e.1) :
    DynamicProgramming.hanging t e =
      insert e.2 (insert e.1 ((branchVertices t e).image (Realization.offChild t e))) := by
  classical
  ext r
  constructor
  · intro hr
    by_cases hw : r = e.2
    · exact Finset.mem_insert.mpr (Or.inl hw)
    · apply Finset.mem_insert.mpr
      apply Or.inr
      by_cases hu : r = e.1
      · exact Finset.mem_insert.mpr (Or.inl hu)
      · obtain ⟨p, hp, heq⟩ := frontier_nonendpoint he hr hu hw
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨p, hp, heq⟩))
  · intro hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact recipient_mem_frontier he
    · rcases Finset.mem_insert.mp hr with rfl | hr
      · exact donor_mem_frontier he hc
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
        exact (offChild_properties he hp).1

theorem endpoint_not_off_image {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) :
    e.1 ∉ (branchVertices t e).image (Realization.offChild t e) ∧
      e.2 ∉ (branchVertices t e).image (Realization.offChild t e) := by
  constructor
  · rintro h
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h
    exact (offChild_properties he hp).2.1 heq
  · rintro h
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h
    exact (offChild_properties he hp).2.2.1 heq

end EdgeAbove
end Camus
