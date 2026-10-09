module

public import Camus.GraphRealizationCycleWires

@[expose] public section

namespace Camus.Realization

noncomputable def cycleSupportGraph (t : PhyloTree) (E : Finset Pair) (e : Pair) : SimpleGraph ℕ where
  Adj u v := ({graph t E with edges := supportEdges t E}).underlying.Adj u v ∧
    u ∈ cycleVertices t e ∧ v ∈ cycleVertices t e
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro v h; exact h.1.1 rfl⟩

theorem cycleSupportGraph_le (t : PhyloTree) (E : Finset Pair) (e : Pair) :
    cycleSupportGraph t E e ≤ ({graph t E with edges := supportEdges t E}).underlying :=
  fun _ _ h => h.1

theorem code_mem_cycleVertices_of_footprint {t : PhyloTree} {e : Pair} {p : Address}
    (hp : p ∈ EdgeAbove.footprint t e) : Address.code p ∈ cycleVertices t e :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩)

theorem cycleSupportGraph_adj_of_support {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} {u v : ℕ}
    (huv : (u,v) ∈ supportEdges t E) (hu : u ∈ cycleVertices t e) (hv : v ∈ cycleVertices t e) :
    (cycleSupportGraph t E e).Adj u v :=
  ⟨⟨graph_edge_ne hE (Finset.mem_union_left _ huv),Or.inl huv⟩,hu,hv⟩

theorem original_cycle_connected {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) {p : Address}
    (hp : p ∈ EdgeAbove.footprint t e) :
    (cycleSupportGraph t E e).Reachable (Address.code (EdgeAbove.target e)) (Address.code p) := by
  have ha := (Finset.mem_filter.mp (hE.1 he)).2
  have hall : ∀ n, ∀ p : Address, p.length = n → p ∈ EdgeAbove.footprint t e →
      (cycleSupportGraph t E e).Reachable (Address.code (EdgeAbove.target e)) (Address.code p) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hlen hp
      by_cases hp0 : p = EdgeAbove.target e
      · rw [hp0]
      · have hnonroot : p ≠ [] := by
          intro h
          have hprefix := (Finset.mem_filter.mp hp).2.1
          have hzero : (EdgeAbove.target e).length = 0 := by simpa [h] using hprefix.length_le
          have ht := List.length_eq_zero_iff.mp hzero
          exact hp0 (h.trans ht.symm)
        have hparent : parent p ∈ EdgeAbove.footprint t e :=
          ((EdgeAbove.footprint_region t e ha).2.2 p hp).2 (parent p)
            (prefix_parent_of_ne (Finset.mem_filter.mp hp).2.1 (Ne.symm hp0)) (parent_prefix p)
        have hplen : (parent p).length < n := by
          have hpos := List.length_pos_iff.mpr hnonroot
          simp only [parent,List.length_take]
          omega
        have hreach := ih _ hplen (parent p) rfl hparent
        exact hreach.trans (SimpleGraph.Adj.reachable
          (cycleSupportGraph_adj_of_support hE (internal_cycle_parent_edge hE he hp hp0)
            (code_mem_cycleVertices_of_footprint hparent) (code_mem_cycleVertices_of_footprint hp)))
  exact hall p.length p rfl hp

theorem donor_cycle_connected {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) :
    (cycleSupportGraph t E e).Reachable (Address.code (EdgeAbove.target e)) (donor t e) := by
  classical
  have ha := (Finset.mem_filter.mp (hE.1 he)).2
  have hd : donor t e ∈ cycleVertices t e := by simp [cycleVertices]
  by_cases hghost : EdgeAbove.target e = e.1
  · have hroot : Address.code e.1 ∈ cycleVertices t e :=
      code_mem_cycleVertices_of_footprint (hghost ▸ EdgeAbove.target_mem_footprint t e ha)
    rw [hghost]
    exact (SimpleGraph.Adj.reachable
      (cycleSupportGraph_adj_of_support hE (ghost_boundary_edge hE he hghost) hd hroot)).symm
  · have hparent := donor_parent_mem_footprint ha hghost
    exact (original_cycle_connected hE he hparent).trans (SimpleGraph.Adj.reachable
      (cycleSupportGraph_adj_of_support hE (donor_boundary_edge hE he hghost)
        (code_mem_cycleVertices_of_footprint hparent) hd))

theorem recipient_cycle_connected {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) :
    (cycleSupportGraph t E e).Reachable (Address.code (EdgeAbove.target e)) (recipient t e) := by
  classical
  have ha := (Finset.mem_filter.mp (hE.1 he)).2
  have hparent := recipient_parent_mem_footprint ha
  have hr : recipient t e ∈ cycleVertices t e := by simp [cycleVertices]
  exact (original_cycle_connected hE he hparent).trans (SimpleGraph.Adj.reachable
    (cycleSupportGraph_adj_of_support hE (recipient_boundary_edge hE he)
      (code_mem_cycleVertices_of_footprint hparent) hr))

theorem cycleSupportGraph_walk_support {t : PhyloTree} {E : Finset Pair} {e : Pair}
    {u v : ℕ} (p : (cycleSupportGraph t E e).Walk u v)
    (hu : u ∈ cycleVertices t e) : p.support.toFinset ⊆ cycleVertices t e := by
  intro w hw
  have hw := List.mem_toFinset.mp hw
  induction p with
  | nil => exact List.mem_singleton.mp hw ▸ hu
  | cons hadj p ih =>
    rcases List.mem_cons.mp hw with rfl | htail
    · exact hu
    · exact ih hadj.2.2 (List.mem_toFinset.mpr htail) htail

theorem cycleSupportPath_support_subset (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) (e : Pair) (he : e ∈ E) :
    (cycleSupportPath t E hE e he).val.support.toFinset ⊆ cycleVertices t e := by
  classical
  let p := ((recipient_cycle_connected hE he).symm.trans (donor_cycle_connected hE he)).some.toPath
  let pS := p.val.mapLe (cycleSupportGraph_le t E e)
  have hPS : pS.IsPath := p.isPath.mapLe _
  have heq : pS = (cycleSupportPath t E hE e he).val :=
    Subtype.mk.inj ((support_acyclic t E hE).subsingleton_path _ _ |>.elim
      ⟨pS,hPS⟩ (cycleSupportPath t E hE e he))
  rw [←heq, SimpleGraph.Walk.support_mapLe_eq_support]
  exact cycleSupportGraph_walk_support p.val (by simp [cycleVertices])

theorem fundamentalCycle_support_subset (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) (e : Pair) (he : e ∈ E) :
    (fundamentalCycle t E hE e he).support.toFinset ⊆ cycleVertices t e := by
  intro v hv
  change v ∈ (donor t e ::
    ((cycleSupportPath t E hE e he).val.mapLe (support_underlying_le t E)).support).toFinset at hv
  have hmem : v = donor t e ∨ v ∈ (cycleSupportPath t E hE e he).val.support := by
    simpa only [SimpleGraph.Walk.support_mapLe_eq_support, List.mem_toFinset, List.mem_cons] using hv
  rcases hmem with rfl | hmem
  · simp [cycleVertices]
  · exact cycleSupportPath_support_subset t E hE e he (List.mem_toFinset.mpr hmem)

theorem cycleVertices_disjoint {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e f : Pair} (he : e ∈ E) (hf : f ∈ E) (hef : e ≠ f) :
    Disjoint (cycleVertices t e) (cycleVertices t f) := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hw
  simp only [cycleVertices, Finset.mem_union, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton] at hv hw
  rcases hv with ⟨p,hp,hpc⟩ | hd | hr <;> rcases hw with ⟨q,hq,hqc⟩ | hd' | hr'
  · have hpq := Address.code_injective (hpc.trans hqc.symm)
    exact Finset.disjoint_left.mp (hE.2 he hf hef) hp (hpq.symm ▸ hq)
  · exact donor_ne_code f (Finset.mem_filter.mp hp).1 (hd'.symm.trans hpc.symm)
  · exact recipient_ne_code f (Finset.mem_filter.mp hp).1 (hr'.symm.trans hpc.symm)
  · exact donor_ne_code e (Finset.mem_filter.mp hq).1 (hd.symm.trans hqc.symm)
  · exact hef (donor_injective t (hE.1 he) (hE.1 hf) (hd.symm.trans hd'))
  · exact donor_ne_recipient t e f (hd.symm.trans hr')
  · exact recipient_ne_code e (Finset.mem_filter.mp hq).1 (hr.symm.trans hqc.symm)
  · exact donor_ne_recipient t f e (hd'.symm.trans hr)
  · exact hef (recipient_injective t (hE.1 he) (hE.1 hf) (hr.symm.trans hr'))

theorem fundamentalCycles_disjoint {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e f : Pair} (he : e ∈ E) (hf : f ∈ E) (hef : e ≠ f) :
    Disjoint (fundamentalCycle t E hE e he).support.toFinset
      (fundamentalCycle t E hE f hf).support.toFinset :=
  Finset.disjoint_of_subset_left (fundamentalCycle_support_subset t E hE e he)
    (Finset.disjoint_of_subset_right (fundamentalCycle_support_subset t E hE f hf)
      (cycleVertices_disjoint hE he hf hef))

end Camus.Realization
