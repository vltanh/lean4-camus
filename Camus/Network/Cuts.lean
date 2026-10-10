module

public import Camus.Network.Completeness.Cycles

/-!
# Switchings, cut edges and cycle cuts

General facts about a rooted binary level-1 network `N` and a switching `S` of `N` (one incoming
edge kept at every vertex other than the root): the edges of `S` form a spanning tree of `N`, and
every edge `d` of `N` that `S` leaves out closes a cycle with the path of `S` between its ends
(`RootedNetwork.fundamentalCycle`). Since the cycles of `N` are vertex-disjoint, deleting a cut
edge of `N`, or two edges of one cycle, leaves the same components in `N` as in the switching with
that cycle's edge put back. These facts give Observation 2 of Warnow, Tabatabaee and Evans
(`Camus/External/WarnowTabatabaeeEvans/Observation2.lean`) and the existence part of Lemma 1
(`Camus/Preliminaries/Lemma1/Cuts.lean`).

## Main results

* `RootedNetwork.exists_switching`: every rooted binary level-1 network has a switching.
* `RootedNetwork.indegree_eq_two_of_deleted`: the head of an edge that a switching leaves out is a
  reticulation.
* `RootedNetwork.bridge_cut_reachable_iff`: deleting a cut edge leaves the same components in `N`
  and in any switching.
* `RootedNetwork.cycle_cut_reachable_iff`: deleting edges of the cycle of a left-out edge `d` leaves
  the same components in `N` and in the switching with `d` put back.
* `RootedNetwork.bridge_mem_switching`: every switching keeps every cut edge.
* `RootedNetwork.deleted_incoming_of_reticulation`,
  `RootedNetwork.cycle_eq_fundamental_of_reticulation`: every reticulation is the head of a
  left-out edge, and a cycle through it is the cycle of that edge.
* `RootedNetwork.fundamental_cycle_cut_displays_raw`: a cut of the cycle of `d` that separates a
  quartet in `N`, one of its edges entering the head of `d`, gives a switching of the network with
  the other left-out edges deleted that displays the quartet.
-/

@[expose] public section

namespace Camus.RootedNetwork

open SimpleGraph

/-- Every rooted binary level-1 network has a switching: keep one incoming edge at every vertex
other than the root. -/
theorem exists_switching {N : RootedNetwork} (hN : N.RootedBinaryLevelOne) :
    ∃ R, N.Switching R := by
  classical
  have hin (v : ℕ) (hv : v ∈ N.vertices) (hvr : v ≠ N.root) :
      (N.edges.filter (fun e => e.2 = v)).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < N.indegree v
    rcases hN.2.2.2.2.2.2.2.2.2.1 v hv hvr with h | h | h <;> omega
  let pick : ℕ → ℕ × ℕ := fun v =>
    if h : (N.edges.filter (fun e => e.2 = v)).Nonempty then h.choose else (0, 0)
  have hpick (v : ℕ) (h : (N.edges.filter (fun e => e.2 = v)).Nonempty) :
      pick v ∈ N.edges ∧ (pick v).2 = v := by
    simp only [pick, h, ↓reduceDIte]
    exact Finset.mem_filter.mp h.choose_spec
  refine ⟨(N.vertices.erase N.root).image pick, ?_, ?_⟩
  · intro e he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hvr, hvN⟩ := Finset.mem_erase.mp hv
    exact (hpick v (hin v hvN hvr)).1
  · intro v hv hvr
    have hfilter : ((N.vertices.erase N.root).image pick).filter (fun e => e.2 = v) =
        {pick v} := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_erase, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨w, ⟨hwr, hwN⟩, rfl⟩, hw⟩
        rw [(hpick w (hin w hwN hwr)).2] at hw
        rw [hw]
      · rintro rfl
        exact ⟨⟨v, ⟨hvr, hv⟩, rfl⟩, (hpick v (hin v hv hvr)).2⟩
    rw [hfilter, Finset.card_singleton]

/-- The head of an edge that a switching leaves out is a reticulation: it has indegree 2. -/
theorem indegree_eq_two_of_deleted {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {R : Finset (ℕ × ℕ)} (hR : N.Switching R) {d : ℕ × ℕ} (hd : d ∈ N.edges \ R) :
    N.indegree d.2 = 2 := by
  classical
  obtain ⟨hdN, hdR⟩ := Finset.mem_sdiff.mp hd
  have hv : d.2 ∈ N.vertices := (hN.2.1 d hdN).2
  have hvr : d.2 ≠ N.root := by
    intro h
    have hpos : 0 < N.indegree N.root := by
      apply Finset.card_pos.mpr
      exact ⟨d, Finset.mem_filter.mpr ⟨hdN, h⟩⟩
    rw [hN.2.2.2.1] at hpos
    omega
  obtain ⟨g, hg⟩ := Finset.card_pos.mp (show 0 < (R.filter (fun e => e.2 = d.2)).card by
    rw [hR.2 d.2 hv hvr]; omega)
  obtain ⟨hgR, hgd⟩ := Finset.mem_filter.mp hg
  have hgd' : g ≠ d := fun h => hdR (h ▸ hgR)
  have htwo : 2 ≤ N.indegree d.2 := by
    have hsub : ({d, g} : Finset (ℕ × ℕ)) ⊆ N.edges.filter (fun e => e.2 = d.2) := by
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact Finset.mem_filter.mpr ⟨hdN, rfl⟩
      · rw [Finset.mem_singleton.mp he]
        exact Finset.mem_filter.mpr ⟨hR.1 hgR, hgd⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair (Ne.symm hgd')] at hcard
    exact hcard
  rcases hN.2.2.2.2.2.2.2.2.2.1 d.2 hv hvr with h | h | h <;> omega

/-- Let `S ⊆ R ⊆ N.edges` with `S` a switching of `N`, and let `B` be a set of edges that avoids the
path of `S` joining the ends of each edge of `N.edges \ R`. Then after deleting `B`, two vertices
are connected in `N` iff they are connected in `{N with edges := R}`: each edge outside `R` is
replaced by its path. -/
theorem reachable_reduce_iff {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    (R : Finset (ℕ × ℕ)) (hSR : S ⊆ R) (hRN : R ⊆ N.edges)
    (B : Set (Sym2 ℕ))
    (havoid : ∀ d (hd : d ∈ N.edges \ R),
      ∀ b ∈ B, b ∉ (supportPath hN hS
        (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hd).1,
          fun hs => (Finset.mem_sdiff.mp hd).2 (hSR hs)⟩)).val.edges)
    (u v : ℕ) :
    (N.underlying.deleteEdges B).Reachable u v ↔
      (({N with edges := R}).underlying.deleteEdges B).Reachable u v := by
  classical
  have hle : (({N with edges := S}).underlying.deleteEdges B) ≤
      (({N with edges := R}).underlying.deleteEdges B) := by
    intro a b hab
    rw [SimpleGraph.deleteEdges_adj] at hab ⊢
    exact ⟨⟨hab.1.1, hab.1.2.imp (fun h => hSR h) (fun h => hSR h)⟩,hab.2⟩
  have step (a b : ℕ) (hab : (N.underlying.deleteEdges B).Adj a b) :
      (({N with edges := R}).underlying.deleteEdges B).Reachable a b := by
    obtain ⟨hab,hcut⟩ := SimpleGraph.deleteEdges_adj.mp hab
    have oriented (a b : ℕ) (he : (a,b) ∈ N.edges) (hcut : s(a,b) ∉ B) :
        (({N with edges := R}).underlying.deleteEdges B).Reachable a b := by
      by_cases hr : (a,b) ∈ R
      · exact (show (({N with edges := R}).underlying.deleteEdges B).Adj a b from
          SimpleGraph.deleteEdges_adj.mpr ⟨⟨edge_ne hN he,Or.inl hr⟩,hcut⟩).reachable
      · have hd : (a,b) ∈ N.edges \ R := Finset.mem_sdiff.mpr ⟨he,hr⟩
        have hs : (a,b) ∈ N.edges \ S :=
          Finset.mem_sdiff.mpr ⟨he,fun hs => hr (hSR hs)⟩
        have hp := (supportPath hN hS hs).val.toDeleteEdges B
          (fun e he hB => havoid (a,b) hd e hB he)
        exact hp.reachable.symm.mono hle
    rcases hab.2 with hab | hba
    · exact oriented a b hab hcut
    · exact (oriented b a hba (by simpa only [Sym2.eq_swap] using hcut)).symm
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact .refl _
    | cons hab p ih => exact (step _ _ hab).trans ih
  · intro h
    apply h.mono
    intro a b hab
    rw [SimpleGraph.deleteEdges_adj] at hab ⊢
    exact ⟨⟨hab.1.1,hab.1.2.imp (fun h => hRN h) (fun h => hRN h)⟩,hab.2⟩

/-- After deleting a cut edge `b` of `N`, two vertices are connected in `N` iff they are connected
in a switching `S` (`{N with edges := S}`): `b` lies on no cycle, so no path of `S` replacing a
non-tree edge uses it. -/
theorem bridge_cut_reachable_iff {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    (b : Sym2 ℕ) (hb : N.underlying.IsBridge b) (u v : ℕ) :
    (N.underlying.deleteEdges {b}).Reachable u v ↔
      (({N with edges := S}).underlying.deleteEdges {b}).Reachable u v := by
  apply reachable_reduce_iff hN hS S (fun _ h => h) hS.1 {b}
  intro d hd e he
  have heq : e = b := Set.mem_singleton_iff.mp he
  subst e
  intro hm
  apply hb.notMem_edges_of_isCycle (fundamentalCycle_isCycle hN hS hd)
  change b ∈ s(d.1,d.2) ::
    ((supportPath hN hS hd).val.mapLe (switching_underlying_le hS)).edges
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  exact List.mem_cons_of_mem _ hm

/-- Let `d` be a non-tree edge and `B` a set of edges of the cycle of `d`. After deleting `B`, two
vertices are connected in `N` iff they are connected in `{N with edges := insert d S}`, where the
other non-tree edges are deleted: their cycles are vertex-disjoint from that of `d`, so the paths of
`S` replacing them avoid `B`. -/
theorem cycle_cut_reachable_iff {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {d : ℕ × ℕ} (hd : d ∈ N.edges \ S) (B : Set (Sym2 ℕ))
    (hB : ∀ b ∈ B, b ∈ (fundamentalCycle hN hS hd).edges) (u v : ℕ) :
    (N.underlying.deleteEdges B).Reachable u v ↔
      (({N with edges := insert d S}).underlying.deleteEdges B).Reachable u v := by
  classical
  apply reachable_reduce_iff hN hS (insert d S) (Finset.subset_insert _ _)
    (Finset.insert_subset (Finset.mem_sdiff.mp hd).1 hS.1) B
  intro f hf b hb hpath
  obtain ⟨hfN,hfnot⟩ := Finset.mem_sdiff.mp hf
  have hfS : f ∈ N.edges \ S :=
    Finset.mem_sdiff.mpr ⟨hfN,fun hs => hfnot (Finset.mem_insert_of_mem hs)⟩
  have hdf : d ≠ f := by
    intro h
    exact hfnot (h ▸ Finset.mem_insert_self d S)
  have hdis := fundamentalCycles_disjoint hN hS hd hfS hdf
  have hfb : b ∈ (fundamentalCycle hN hS hfS).edges := by
    change b ∈ s(f.1,f.2) ::
      ((supportPath hN hS hfS).val.mapLe (switching_underlying_le hS)).edges
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
    exact List.mem_cons_of_mem _ hpath
  have hdb := hB b hb
  induction b using Sym2.inductionOn with
  | _ a z =>
    exact Finset.disjoint_left.mp hdis
      (List.mem_toFinset.mpr ((fundamentalCycle hN hS hd).fst_mem_support_of_mem_edges hdb))
      (List.mem_toFinset.mpr ((fundamentalCycle hN hS hfS).fst_mem_support_of_mem_edges hfb))

/-- A cut edge of `N` is an edge of every switching `S` of `N`. -/
theorem bridge_mem_switching {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {b : Sym2 ℕ} (hb : b ∈ N.underlying.edgeSet) (hbridge : N.underlying.IsBridge b) :
    b ∈ ({N with edges := S}).underlying.edgeSet := by
  classical
  induction b using Sym2.inductionOn with
  | _ u v =>
    rcases hb.2 with hd | hd
    · by_cases hs : (u,v) ∈ S
      · exact ⟨hb.1,Or.inl hs⟩
      · have he : (u,v) ∈ N.edges \ S := Finset.mem_sdiff.mpr ⟨hd,hs⟩
        exact False.elim (hbridge.notMem_edges_of_isCycle
          (fundamentalCycle_isCycle hN hS he) (fundamentalCycle_mem_edges hN hS he))
    · by_cases hs : (v,u) ∈ S
      · exact ⟨hb.1,Or.inr hs⟩
      · have he : (v,u) ∈ N.edges \ S := Finset.mem_sdiff.mpr ⟨hd,hs⟩
        exact False.elim (hbridge.notMem_edges_of_isCycle
          (fundamentalCycle_isCycle hN hS he)
          (by simpa only [Sym2.eq_swap] using fundamentalCycle_mem_edges hN hS he))

/-- Every reticulation `r` of `N` (a vertex of indegree 2) is the head of a non-tree edge
`d ∈ N.edges \ S`. -/
theorem deleted_incoming_of_reticulation {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) (r : ℕ) (hr : N.indegree r = 2) :
    ∃ d, d ∈ N.edges \ S ∧ d.2 = r := by
  classical
  have hn : (N.edges.filter (fun e => e.2 = r)).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < N.indegree r
    omega
  obtain ⟨d,hd⟩ := hn
  obtain ⟨hdN,hdr⟩ := Finset.mem_filter.mp hd
  have hrN : r ∈ N.vertices := hdr ▸ (hN.2.1 _ hdN).2
  have hrroot : r ≠ N.root := by
    intro h
    rw [h,hN.2.2.2.1] at hr
    omega
  by_contra hno
  have hsub : N.edges.filter (fun e => e.2 = r) ⊆ S.filter (fun e => e.2 = r) := by
    intro e he
    obtain ⟨heN,her⟩ := Finset.mem_filter.mp he
    have heS : e ∈ S := by
      by_contra hn
      exact hno ⟨e,Finset.mem_sdiff.mpr ⟨heN,hn⟩,her⟩
    exact Finset.mem_filter.mpr ⟨heS,her⟩
  have hcard := Finset.card_le_card hsub
  change N.indegree r ≤ _ at hcard
  rw [hr,hS.2 r hrN hrroot] at hcard
  omega

/-- A cycle of `N` through the head `r` of a non-tree edge `d` has the same edges as the cycle of
`d`: in the level-1 network `N`, two cycles with a common vertex have the same edges. -/
theorem cycle_eq_fundamental_of_reticulation {N : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {v : ℕ} (c : N.underlying.Walk v v) (hc : c.IsCycle) {r : ℕ}
    (hr : r ∈ c.support) {d : ℕ × ℕ} (hd : d ∈ N.edges \ S) (hdr : d.2 = r) :
    c.edges.toFinset = (fundamentalCycle hN hS hd).edges.toFinset := by
  classical
  by_contra hne
  have hdis := hN.2.2.2.2.2.2.2.2.2.2 v d.1 c (fundamentalCycle hN hS hd)
    hc (fundamentalCycle_isCycle hN hS hd) hne
  have hrf : r ∈ (fundamentalCycle hN hS hd).support := by
    rw [← hdr]
    exact (fundamentalCycle hN hS hd).snd_mem_support_of_mem_edges
      (fundamentalCycle_mem_edges hN hS hd)
  exact Finset.disjoint_left.mp hdis (List.mem_toFinset.mpr hr) (List.mem_toFinset.mpr hrf)

/-- In `{N with edges := insert d S}`, deleting either edge entering the head of `d` leaves a
switching: every other vertex keeps its one incoming edge of `S`. -/
theorem singleton_switching_erase_incoming {N : RootedNetwork}
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {d g : ℕ × ℕ} (hd : d ∈ N.edges \ S) (hg : g ∈ insert d S)
    (hhead : g.2 = d.2) :
    ({N with edges := insert d S}).Switching ((insert d S).erase g) := by
  classical
  refine ⟨Finset.erase_subset _ _,?_⟩
  intro v hv hvroot
  rw [Finset.filter_erase]
  by_cases hdv : d.2 = v
  · have hgv : g.2 = v := hhead.trans hdv
    have hgm : g ∈ (insert d S).filter (fun e => e.2 = v) :=
      Finset.mem_filter.mpr ⟨hg,hgv⟩
    rw [Finset.card_erase_of_mem hgm, Finset.filter_insert]
    simp only [hdv, ↓reduceIte]
    have hnot : d ∉ S.filter (fun e => e.2 = v) :=
      fun h => (Finset.mem_sdiff.mp hd).2 (Finset.mem_filter.mp h).1
    rw [Finset.card_insert_of_notMem hnot,hS.2 v hv hvroot]
  · have hgv : g.2 ≠ v := fun h => hdv (hhead.symm.trans h)
    rw [Finset.filter_insert]
    simp only [hdv, ↓reduceIte]
    rw [Finset.erase_eq_of_notMem (by simp only [Finset.mem_filter, hgv, and_false, not_false_eq_true])]
    exact hS.2 v hv hvroot

/-- Removing an edge `g` from a set `R` of edges of `N` removes its undirected edge from the
underlying graph and nothing else: `N` is acyclic, so it has no edge opposite to `g`. -/
theorem underlying_erase_eq {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    (R : Finset (ℕ × ℕ)) (hR : R ⊆ N.edges) (g : ℕ × ℕ) (hg : g ∈ R) :
    ({N with edges := R.erase g}).underlying =
      ({N with edges := R}).underlying.deleteEdges {s(g.1,g.2)} := by
  classical
  ext a b
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · intro hab
    have hne : s(a,b) ≠ s(g.1,g.2) := by
      intro heq
      rcases hab.2 with ha | hb
      · have h := directed_edge_eq_of_sym2_eq hN (hR (Finset.mem_erase.mp ha).2) (hR hg) heq
        exact (Finset.mem_erase.mp ha).1 h
      · have h := directed_edge_eq_of_sym2_eq hN (hR (Finset.mem_erase.mp hb).2) (hR hg)
          (by simpa only [Sym2.eq_swap] using heq)
        exact (Finset.mem_erase.mp hb).1 h
    exact ⟨⟨hab.1,hab.2.imp (fun h => (Finset.mem_erase.mp h).2)
      (fun h => (Finset.mem_erase.mp h).2)⟩,hne⟩
  · rintro ⟨hab,hne⟩
    have hne' : s(a,b) ≠ s(g.1,g.2) := by simpa only [Set.mem_singleton_iff] using hne
    refine ⟨hab.1,?_⟩
    rcases hab.2 with ha | hb
    · exact Or.inl (Finset.mem_erase.mpr ⟨fun h => hne' (congrArg (fun e : ℕ × ℕ => s(e.1,e.2)) h),ha⟩)
    · exact Or.inr (Finset.mem_erase.mpr ⟨fun h => hne'
        ((Sym2.eq_swap).trans (congrArg (fun e : ℕ × ℕ => s(e.1,e.2)) h)),hb⟩)

/-- Every edge of the cycle of `d` is an edge of `{N with edges := insert d S}`. -/
theorem fundamentalCycle_mem_reduce {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) {d : ℕ × ℕ}
    (hd : d ∈ N.edges \ S) {b : Sym2 ℕ}
    (hb : b ∈ (fundamentalCycle hN hS hd).edges) :
    b ∈ ({N with edges := insert d S}).underlying.edgeSet := by
  change b ∈ s(d.1,d.2) ::
    ((supportPath hN hS hd).val.mapLe (switching_underlying_le hS)).edges at hb
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges,List.mem_cons] at hb
  rcases hb with h | h
  · rw [h]
    exact ⟨edge_ne hN (Finset.mem_sdiff.mp hd).1,Or.inl (Finset.mem_insert_self _ _)⟩
  · have hle : ({N with edges := S}).underlying ≤
        ({N with edges := insert d S}).underlying := by
      intro a z haz
      exact ⟨haz.1,haz.2.imp (fun h => Finset.mem_insert_of_mem h)
        (fun h => Finset.mem_insert_of_mem h)⟩
    exact SimpleGraph.edgeSet_mono hle ((supportPath hN hS hd).val.edges_subset_edgeSet h)

/-- Let `e ≠ f` be edges of the cycle of a non-tree edge `d`, with `e` incident to the head of `d`.
If deleting `e` and `f` separates `q` in `N`, then `{N with edges := insert d S}` (the other
non-tree edges deleted) displays `q`: deleting `e`, an edge entering the head of `d`, leaves a
switching, and deleting `f` from it separates `q`. -/
theorem fundamental_cycle_cut_displays_raw {N : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    {d : ℕ × ℕ} (hd : d ∈ N.edges \ S) (q : Quartet) (hqt : q.taxa ⊆ N.taxa)
    (e f : Sym2 ℕ) (he : e ∈ (fundamentalCycle hN hS hd).edges)
    (hf : f ∈ (fundamentalCycle hN hS hd).edges) (hef : e ≠ f)
    (hr : d.2 ∈ e) (hsep : N.Separates (N.underlying.deleteEdges {e,f}) q) :
    ({N with edges := insert d S}).DisplaysQuartet q := by
  classical
  obtain ⟨a,ha,heq⟩ := fundamentalCycle_recipient_edge_incoming hN hS hd he hr
  let g : ℕ × ℕ := (a,d.2)
  let R := insert d S
  have hRN : R ⊆ N.edges := Finset.insert_subset (Finset.mem_sdiff.mp hd).1 hS.1
  have hg : g ∈ R := by
    have hem := fundamentalCycle_mem_reduce hN hS hd he
    rw [heq] at hem
    rcases hem.2 with hg | hrev
    · exact hg
    · exact False.elim (edge_reverse_not_mem hN ha (hRN hrev))
  have hsw := singleton_switching_erase_incoming hS hd hg (show g.2 = d.2 from rfl)
  have hgraph : ({N with edges := R.erase g}).underlying.deleteEdges {f} =
      ({N with edges := R}).underlying.deleteEdges {e,f} := by
    rw [underlying_erase_eq hN R hRN g hg, ← heq,SimpleGraph.deleteEdges_deleteEdges]
    congr 1
  have hfedge : f ∈ ({N with edges := R.erase g}).underlying.edgeSet := by
    rw [underlying_erase_eq hN R hRN g hg,← heq,SimpleGraph.edgeSet_deleteEdges]
    exact ⟨fundamentalCycle_mem_reduce hN hS hd hf,
      by simpa only [Set.mem_singleton_iff] using hef.symm⟩
  have hB : ∀ b ∈ ({e,f} : Set (Sym2 ℕ)), b ∈ (fundamentalCycle hN hS hd).edges := by
    intro b hb
    rcases Set.mem_insert_iff.mp hb with hb | hb
    · exact hb ▸ he
    · exact Set.mem_singleton_iff.mp hb ▸ hf
  have hsepR : N.Separates (({N with edges := R}).underlying.deleteEdges {e,f}) q := by
    obtain ⟨h1,h2,h3⟩ := hsep
    refine ⟨?_,?_,?_⟩
    · intro x hx y hy
      exact (cycle_cut_reachable_iff hN hS hd {e,f} hB _ _).mp (h1 x hx y hy)
    · intro x hx y hy
      exact (cycle_cut_reachable_iff hN hS hd {e,f} hB _ _).mp (h2 x hx y hy)
    · intro x hx y hy h
      exact h3 x hx y hy ((cycle_cut_reachable_iff hN hS hd {e,f} hB _ _).mpr h)
  refine ⟨hqt,R.erase g,hsw,f,hfedge,?_⟩
  change N.Separates (({N with edges := R.erase g}).underlying.deleteEdges {f}) q
  rw [hgraph]
  exact hsepR

/-- Removing an edge of a switching that the switching keeps, and the edge it leaves out on the
same fundamental cycle, leaves the same components as removing the kept edge from the
switching. -/
theorem switching_cut_graph {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {R : Finset (ℕ × ℕ)} (hR : N.Switching R) {d : ℕ × ℕ} (hd : d ∈ N.edges \ R)
    (e : Sym2 ℕ) :
    ({N with edges := insert d R}).underlying.deleteEdges {e, s(d.1, d.2)} =
      ({N with edges := R}).underlying.deleteEdges {e} := by
  classical
  have hRd : R ⊆ N.edges := hR.1
  have hins : insert d R ⊆ N.edges := Finset.insert_subset (Finset.mem_sdiff.mp hd).1 hRd
  have herase : (insert d R).erase d = R :=
    Finset.erase_insert (Finset.mem_sdiff.mp hd).2
  have h := underlying_erase_eq hN (insert d R) hins d (Finset.mem_insert_self d R)
  rw [herase] at h
  rw [h, SimpleGraph.deleteEdges_deleteEdges]
  congr 1
  ext b
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  tauto

end Camus.RootedNetwork
