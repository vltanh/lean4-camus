module

public import Camus.Network.Completeness.Reachability

@[expose] public section

namespace Camus

theorem path_between_chain_members {G : SimpleGraph ℕ} {l : List ℕ}
    (hchain : l.IsChain G.Adj) {u v : ℕ} (hu : u ∈ l) (hv : v ∈ l) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.support ⊆ l := by
  classical
  have hne : l ≠ [] := List.ne_nil_of_mem hu
  let w := SimpleGraph.Walk.ofSupport l hne hchain
  have hwu : u ∈ w.support := by simpa only [w, SimpleGraph.Walk.support_ofSupport] using hu
  have hwv : v ∈ w.support := by simpa only [w, SimpleGraph.Walk.support_ofSupport] using hv
  let a := w.takeUntil u hwu
  let b := w.takeUntil v hwv
  let z := a.reverse.append b
  refine ⟨z.toPath, z.toPath.isPath, ?_⟩
  intro x hx
  have hxz := z.support_toPath_subset_support hx
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxz with ha | hb
  · have hxa : x ∈ a.support := by simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using ha
    have hxw := w.support_takeUntil_subset_support hwu hxa
    simpa only [w, SimpleGraph.Walk.support_ofSupport] using hxw
  · have hxw := w.support_takeUntil_subset_support hwv hb
    simpa only [w, SimpleGraph.Walk.support_ofSupport] using hxw

namespace RootedNetwork

theorem cycle_support_mem_vertices {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {v : ℕ} {c : N.underlying.Walk v v} (hc : c.IsCycle) {x : ℕ}
    (hx : x ∈ c.support) : x ∈ N.vertices := by
  obtain ⟨f,hf,hxf⟩ := (c.mem_support_iff_exists_mem_edges_of_not_nil hc.not_nil).mp hx
  have hfN := c.edges_subset_edgeSet hf
  obtain ⟨y,hfy⟩ := Sym2.mem_iff_exists.mp hxf
  rw [hfy] at hfN
  have hadj : N.underlying.Adj x y := hfN
  rcases hadj.2 with h | h
  · exact (hN.2.1 _ h).1
  · exact (hN.2.1 _ h).2

end RootedNetwork

namespace SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

theorem fundamentalCycle_contains_original (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    ∃ p ∈ t.nodes, H.original p ∈ (RootedNetwork.fundamentalCycle hN H.switching he).support := by
  classical
  let c := RootedNetwork.fundamentalCycle hN H.switching he
  have hc := RootedNetwork.fundamentalCycle_isCycle hN H.switching he
  by_contra hno
  have hsub : c.support.tail.toFinset ⊆ {e.1,e.2} := by
    intro v hv
    have hvc : v ∈ c.support := List.mem_of_mem_tail (List.mem_toFinset.mp hv)
    have hvN := RootedNetwork.cycle_support_mem_vertices hN hc hvc
    rcases H.vertex_cases hvN with horig | hinterior
    · obtain ⟨p,hp,hpv⟩ := horig
      exact False.elim (hno ⟨p,hp,hpv ▸ hvc⟩)
    · obtain ⟨f,hf,hfv⟩ := H.interior_is_deleted_endpoint hN
        hinterior.1 hinterior.2.1 hinterior.2.2
      have hve : v ∈ (RootedNetwork.fundamentalCycle hN H.switching hf).support := by
        rcases hfv with hs | ht
        · rw [← hs]
          exact RootedNetwork.fundamentalCycle_source_mem hN H.switching hf
        · rw [← ht]
          exact RootedNetwork.fundamentalCycle_target_mem hN H.switching hf
      have hfe : f = e := by
        by_contra hfe
        exact Finset.disjoint_left.mp (RootedNetwork.fundamentalCycles_disjoint
          hN H.switching hf he hfe) (List.mem_toFinset.mpr hve) (List.mem_toFinset.mpr hvc)
      subst f
      rcases hfv with hs | ht
      · exact Finset.mem_insert.mpr (Or.inl hs.symm)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr ht.symm))
  have hcard := Finset.card_mono hsub
  rw [List.toFinset_card_of_nodup hc.support_nodup] at hcard
  have hlen := hc.three_le_length
  simp only [List.length_tail, SimpleGraph.Walk.length_support] at hcard
  have hpair : ({e.1,e.2} : Finset ℕ).card ≤ 2 := by
    by_cases h : e.1 = e.2 <;> simp [h]
  omega

theorem deleted_anchors_ne (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    H.anchor e.1 ≠ H.anchor e.2 := by
  classical
  intro heq
  have hu := H.deleted_source_anchor_spec hN he
  have hw := H.deleted_target_anchor_spec hN he
  rw [← heq] at hw
  have hchain : (H.wire (H.anchor e.1)).IsChain ({N with edges := S}).underlying.Adj := by
    apply wire_chain
    intro f hf
    have hfS := H.wire_edge_mem_support hu.1 hu.2.1 hf
    exact ⟨RootedNetwork.edge_ne hN (H.switching.1 hfS), Or.inl hfS⟩
  obtain ⟨p,hp,hps⟩ := path_between_chain_members hchain.tail.dropLast
    (List.mem_toFinset.mp hw.2.2) (List.mem_toFinset.mp hu.2.2)
  have hpeq : p = (RootedNetwork.supportPath hN H.switching he).val :=
    Subtype.mk.inj ((RootedNetwork.switching_acyclic hN H.switching).subsingleton_path _ _
      |>.elim ⟨p,hp⟩ (RootedNetwork.supportPath hN H.switching he))
  obtain ⟨q,hq,hcq⟩ := H.fundamentalCycle_contains_original hN he
  change H.original q ∈ e.1 ::
    ((RootedNetwork.supportPath hN H.switching he).val.mapLe _).support at hcq
  rw [SimpleGraph.Walk.support_mapLe_eq_support, ← hpeq] at hcq
  rcases List.mem_cons.mp hcq with hsource | hpath
  · exact H.deleted_source_not_original hN he (Finset.mem_image.mpr ⟨q,hq,hsource⟩)
  · exact H.interior_not_original hu.1 hu.2.1
      (List.mem_toFinset.mpr (hps hpath)) (Finset.mem_image.mpr ⟨q,hq,rfl⟩)

theorem deleted_pair_admissible (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    EdgeAbove.Admissible t (H.pairOf e) := by
  have hu := H.deleted_source_anchor_spec hN he
  have hw := H.deleted_target_anchor_spec hN he
  refine ⟨hu.1,hw.1,hu.2.1,hw.2.1,?_⟩
  intro hpref
  exact H.deleted_anchors_ne hN he (H.deleted_anchor_not_strict_ancestor hN he hpref).symm

end SupportSubdivision
end Camus
