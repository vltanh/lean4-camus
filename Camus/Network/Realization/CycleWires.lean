module

public import Camus.Network.Realization.Cycles

@[expose] public section

namespace Camus.Realization

theorem donor_parent_mem_footprint {t : PhyloTree} {e : Pair}
    (he : EdgeAbove.Admissible t e) (hne : EdgeAbove.target e ≠ e.1) :
    parent e.1 ∈ EdgeAbove.footprint t e := by
  have hprefix := lca_prefix_left e.1 e.2
  exact Finset.mem_filter.mpr
    ⟨t.nodes_prefix_closed he.1 (parent_prefix e.1),
      prefix_parent_of_ne hprefix hne,
      Or.inl ⟨parent_prefix _, parent_ne_self he.2.2.1⟩⟩

private theorem outer_owner_parent {t : PhyloTree} {e : Pair} {p : Address}
    (he : EdgeAbove.Admissible t e)
    (h : e.1 = p ∧ EdgeAbove.target e ≠ p ∨ e.2 = p) :
    parent p ∈ EdgeAbove.footprint t e := by
  rcases h with ⟨rfl, hne⟩ | rfl
  · exact donor_parent_mem_footprint he hne
  · exact recipient_parent_mem_footprint he

theorem outerEndpoints_mem_unique {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {p : Address} {v w : ℕ}
    (hv : v ∈ outerEndpoints t E p) (hw : w ∈ outerEndpoints t E p) : v = w := by
  obtain ⟨e, he, hv⟩ := mem_outerEndpoints.mp hv
  obtain ⟨f, hf, hw⟩ := mem_outerEndpoints.mp hw
  have hae := (Finset.mem_filter.mp (hE.1 he)).2
  have haf := (Finset.mem_filter.mp (hE.1 hf)).2
  have hparent_e := outer_owner_parent hae (hv.elim
    (fun h => Or.inl ⟨h.1,h.2.1⟩) (fun h => Or.inr h.1))
  have hparent_f := outer_owner_parent haf (hw.elim
    (fun h => Or.inl ⟨h.1,h.2.1⟩) (fun h => Or.inr h.1))
  have hef : e = f := by
    by_contra hne
    exact Finset.disjoint_left.mp (hE.2 he hf hne) hparent_e hparent_f
  subst f
  have hune : e.1 ≠ e.2 := by
    intro h
    exact hae.2.2.2.2 (h ▸ List.prefix_refl e.1)
  rcases hv with ⟨hu, _, hd⟩ | ⟨hr, hv⟩ <;>
    rcases hw with ⟨hu', _, hd'⟩ | ⟨hr', hw⟩
  · exact hd.trans hd'.symm
  · exact False.elim (hune (hu.trans hr'.symm))
  · exact False.elim (hune (hu'.trans hr.symm))
  · exact hv.trans hw.symm

theorem ghostEndpoints_mem_unique {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {p : Address} {v w : ℕ}
    (hv : v ∈ ghostEndpoints t E p) (hw : w ∈ ghostEndpoints t E p) : v = w := by
  obtain ⟨e, he, hu, ht, hd⟩ := mem_ghostEndpoints.mp hv
  obtain ⟨f, hf, hu', ht', hd'⟩ := mem_ghostEndpoints.mp hw
  have hef := EdgeAbove.target_unique t E hE he hf (ht.trans ht'.symm)
  subst f
  exact hd.trans hd'.symm

private theorem nodup_eq_singleton_of_mem {L : List ℕ} (hL : L.Nodup) {v : ℕ}
    (hv : v ∈ L) (huniq : ∀ w ∈ L, w = v) : L = [v] := by
  cases L with
  | nil => simp at hv
  | cons a L =>
    have ha := huniq a List.mem_cons_self
    subst a
    have hnil : L = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro w hw
      have heq := huniq w (List.mem_cons_of_mem v hw)
      exact (List.nodup_cons.mp hL).1 (heq ▸ hw)
    rw [hnil]

theorem outerEndpoints_eq_singleton {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {p : Address} {v : ℕ}
    (hv : v ∈ outerEndpoints t E p) : outerEndpoints t E p = [v] :=
  nodup_eq_singleton_of_mem (outerEndpoints_nodup t E hE.1 p) hv
    (fun _w hw => outerEndpoints_mem_unique hE hw hv)

theorem ghostEndpoints_eq_singleton {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {p : Address} {v : ℕ}
    (hv : v ∈ ghostEndpoints t E p) : ghostEndpoints t E p = [v] :=
  nodup_eq_singleton_of_mem (ghostEndpoints_nodup t E hE.1 p) hv
    (fun _w hw => ghostEndpoints_mem_unique hE hw hv)

theorem internal_cycle_wire_empty {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) {p : Address}
    (hp : p ∈ EdgeAbove.footprint t e) (hp0 : p ≠ EdgeAbove.target e) :
    outerEndpoints t E p = [] ∧ ghostEndpoints t E p = [] := by
  classical
  have hae := (Finset.mem_filter.mp (hE.1 he)).2
  have hparent_e : parent p ∈ EdgeAbove.footprint t e := by
    have hreg := EdgeAbove.footprint_region t e hae
    exact (hreg.2.2 p hp).2 (parent p)
      (prefix_parent_of_ne (Finset.mem_filter.mp hp).2.1 hp0.symm) (parent_prefix p)
  constructor
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro v hv
    obtain ⟨f, hf, hfo⟩ := mem_outerEndpoints.mp hv
    have haf := (Finset.mem_filter.mp (hE.1 hf)).2
    have hparent_f := outer_owner_parent haf (hfo.elim
      (fun h => Or.inl ⟨h.1,h.2.1⟩) (fun h => Or.inr h.1))
    have hef : e = f := by
      by_contra hne
      exact Finset.disjoint_left.mp (hE.2 he hf hne) hparent_e hparent_f
    subst f
    rcases hfo with ⟨hu, _, _⟩ | ⟨hw, _⟩
    · have hpdata := (Finset.mem_filter.mp hp).2.2
      rcases hpdata with hpu | hpw
      · exact hpu.2 hu.symm
      · have htarget := (lca_eq_left_iff e.1 e.2).mpr (hu.symm ▸ hpw.1)
        exact hp0 (hu.symm.trans htarget.symm)
    · have hpdata := (Finset.mem_filter.mp hp).2.2
      rcases hpdata with hpu | hpw
      · exact hae.2.2.2.2 (hw.symm ▸ hpu.1)
      · exact hpw.2 hw.symm
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro v hv
    obtain ⟨f, hf, hfu, hft, _⟩ := mem_ghostEndpoints.mp hv
    have haf := (Finset.mem_filter.mp (hE.1 hf)).2
    have hp_f : p ∈ EdgeAbove.footprint t f := hft ▸ EdgeAbove.target_mem_footprint t f haf
    have hef : e = f := by
      by_contra hne
      exact Finset.disjoint_left.mp (hE.2 he hf hne) hp hp_f
    subst f
    exact hp0 hft.symm

theorem internal_cycle_wire {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) {p : Address}
    (hp : p ∈ EdgeAbove.footprint t e) (hp0 : p ≠ EdgeAbove.target e) :
    wire t E p = [Address.code (parent p), Address.code p] := by
  have hnone := internal_cycle_wire_empty hE he hp hp0
  simp [wire, hnone.1, hnone.2]

theorem wireEdges_cons_subset (a : ℕ) (L : List ℕ) : wireEdges L ⊆ wireEdges (a :: L) := by
  cases L with
  | nil => simp [wireEdges]
  | cons b L => rw [wireEdges_cons_cons]; exact Finset.subset_insert _ _

theorem wireEdges_append_right_subset (A B : List ℕ) : wireEdges B ⊆ wireEdges (A ++ B) := by
  induction A with
  | nil => exact Finset.Subset.refl _
  | cons a A ih => exact ih.trans (wireEdges_cons_subset _ _)

theorem donor_boundary_edge {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E)
    (hne : EdgeAbove.target e ≠ e.1) :
    (Address.code (parent e.1), donor t e) ∈ supportEdges t E := by
  classical
  have ha := (Finset.mem_filter.mp (hE.1 he)).2
  have houter := outerEndpoints_eq_singleton hE
    (mem_outerEndpoints.mpr ⟨e, he, Or.inl ⟨rfl, hne, rfl⟩⟩)
  have hwire : wire t E e.1 = Address.code (parent e.1) :: donor t e ::
      (ghostEndpoints t E e.1 ++ [Address.code e.1]) := by
    simp [wire, houter]
  exact Finset.mem_biUnion.mpr ⟨e.1, Finset.mem_erase.mpr ⟨ha.2.2.1,ha.1⟩, by
    rw [hwire,wireEdges_cons_cons]
    exact Finset.mem_insert_self _ _⟩

theorem recipient_boundary_edge {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) :
    (Address.code (parent e.2), recipient t e) ∈ supportEdges t E := by
  classical
  have ha := (Finset.mem_filter.mp (hE.1 he)).2
  have houter := outerEndpoints_eq_singleton hE
    (mem_outerEndpoints.mpr ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩)
  have hwire : wire t E e.2 = Address.code (parent e.2) :: recipient t e ::
      (ghostEndpoints t E e.2 ++ [Address.code e.2]) := by
    simp [wire, houter]
  exact Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_erase.mpr ⟨ha.2.2.2.1,ha.2.1⟩, by
    rw [hwire,wireEdges_cons_cons]
    exact Finset.mem_insert_self _ _⟩

theorem ghost_boundary_edge {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E)
    (hghost : EdgeAbove.target e = e.1) :
    (donor t e, Address.code e.1) ∈ supportEdges t E := by
  classical
  have ha := (Finset.mem_filter.mp (hE.1 he)).2
  have hinner := ghostEndpoints_eq_singleton hE
    (mem_ghostEndpoints.mpr ⟨e, he, rfl, hghost, rfl⟩)
  have hwire : wire t E e.1 =
      ([Address.code (parent e.1)] ++ outerEndpoints t E e.1) ++ [donor t e, Address.code e.1] := by
    simp [wire, hinner, List.append_assoc]
  apply Finset.mem_biUnion.mpr
  refine ⟨e.1, Finset.mem_erase.mpr ⟨ha.2.2.1,ha.1⟩, ?_⟩
  rw [hwire]
  exact wireEdges_append_right_subset _ _ (by simp [wireEdges])

theorem internal_cycle_parent_edge {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) {p : Address}
    (hp : p ∈ EdgeAbove.footprint t e) (hp0 : p ≠ EdgeAbove.target e) :
    (Address.code (parent p), Address.code p) ∈ supportEdges t E := by
  classical
  have hnode := (Finset.mem_filter.mp hp).1
  have hnonroot : p ≠ [] := by
    intro h
    have hprefix := (Finset.mem_filter.mp hp).2.1
    have hlen := hprefix.length_le
    rw [h] at hlen
    have htarget := List.length_eq_zero_iff.mp (by simpa using hlen : (EdgeAbove.target e).length = 0)
    exact hp0 (h.trans htarget.symm)
  exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_erase.mpr ⟨hnonroot,hnode⟩, by
    rw [internal_cycle_wire hE he hp hp0]
    simp [wireEdges]⟩

end Camus.Realization
