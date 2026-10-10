module

public import Camus.Network.Completeness.Cycles
public import Camus.Network.Completeness.Baseline
public import Camus.Network.Realization.Construction
public import Camus.Network.Baseline.Main
public import Camus.Network.Completeness.Main
public import Camus.Network.Isomorphism.Invariance
public import Camus.Network.Subdivision.Invariance
public import Camus.External.WarnowTabatabaeeEvans.Observation2

@[expose] public section

namespace Camus.RootedNetwork

/-- Removing chords preserves connectivity after a specified cut whenever each
removed chord has a support-tree replacement path avoiding that cut. -/
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

/-- A bridge cut gives exactly the same leaf components in the full network
and its support switching. No quartet attribution theorem is used. -/
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

/-- Cuts lying on one fundamental cycle are insensitive to removing all other
non-tree edges, because those edges have vertex-disjoint replacement paths. -/
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

/-- Full-network bridges are retained by every support switching. -/
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

/-- The cut-edge alternative of Observation 2 contributes only baseline
quartets. This proves that a novel quartet must use a cycle. -/
theorem cutEdgeSeparates_baseline {t : PhyloTree} (ht : t.WellLabelled)
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S)
    (q : Quartet) (hqt : q.taxa ⊆ N.taxa) (hq : N.CutEdgeSeparates q) :
    q.induced t = true := by
  classical
  obtain ⟨b,hb,hbridge,hsep⟩ := hq
  have hsepS : ({N with edges := S}).Separates
      (({N with edges := S}).underlying.deleteEdges {b}) q := by
    obtain ⟨h1,h2,h3⟩ := hsep
    refine ⟨?_,?_,?_⟩
    · intro a ha c hc
      exact (bridge_cut_reachable_iff hN H.switching b hbridge _ _).mp (h1 a ha c hc)
    · intro a ha c hc
      exact (bridge_cut_reachable_iff hN H.switching b hbridge _ _).mp (h2 a ha c hc)
    · intro a ha c hc h
      exact h3 a ha c hc ((bridge_cut_reachable_iff hN H.switching b hbridge _ _).mpr h)
  have hraw : ({N with edges := S}).DisplaysQuartet q :=
    ⟨hqt,S,⟨Finset.Subset.refl _,H.switching.2⟩,b,
      bridge_mem_switching hN H.switching hb hbridge,hsepS⟩
  have hbase : EdgeAbove.CycleSeparated t ∅ := by simp [EdgeAbove.CycleSeparated]
  have hbq := (H.baseline_subdivision.displays_iff
    (Realization.levelOne t ht ∅ hbase) q).mp hraw
  exact (Realization.baseline_displays_iff t ht q).mp hbq

/-- Exactly one incoming reticulation edge is absent from the support switching. -/
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

/-- The cycle occurring in Observation 2 is the fundamental cycle of the
support edge deleted at its reticulation. This follows from vertex disjointness. -/
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

/-- Select either incoming edge of the retained reticulation; every other
vertex keeps its unique support incoming edge. -/
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

/-- In a directed acyclic graph, removing one arc removes exactly its
undirected edge; there is no opposite arc that could preserve that edge. -/
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

/-- Observation 2's cycle separation becomes an actual switching witness in
the graph retaining just that cycle's non-tree edge. -/
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

/-- Existence in Lemma 1 follows the cited Observation 2 route: exclude its
bridge alternative, retain its one cycle, and construct a switching witness. -/
theorem novel_edge_exists (observation2 : External.WarnowTabatabaeeEvansObservation2)
    {t : PhyloTree} (ht : t.WellLabelled) {N : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)}
    (H : SupportSubdivision t N S) (q : Quartet)
    (hq : N.DisplaysQuartet q) (hnot : q.induced t ≠ true) :
    ∃ d, d ∈ N.edges \ S ∧
      (Realization.graph t {H.pairOf d}).DisplaysQuartet q := by
  classical
  rcases (observation2 N hN q hq.1).mp hq with hcut | hcycle
  · exact False.elim (hnot (cutEdgeSeparates_baseline ht hN H q hq.1 hcut))
  · obtain ⟨v,c,hc,r,hr,hret,e,he,f,hf,hef,hrcut,hsep⟩ := hcycle
    obtain ⟨d,hd,hdr⟩ := deleted_incoming_of_reticulation hN H.switching r hret
    have hceq := cycle_eq_fundamental_of_reticulation hN H.switching c hc hr hd hdr
    have heF : e ∈ (fundamentalCycle hN H.switching hd).edges := by
      apply List.mem_toFinset.mp
      rw [← hceq]
      exact List.mem_toFinset.mpr he
    have hfF : f ∈ (fundamentalCycle hN H.switching hd).edges := by
      apply List.mem_toFinset.mp
      rw [← hceq]
      exact List.mem_toFinset.mpr hf
    have hraw : ({N with edges := insert d S}).DisplaysQuartet q := by
      rcases hrcut with hre | hrf
      · exact fundamental_cycle_cut_displays_raw hN H.switching hd q hq.1 e f heF hfF hef
          (hdr.symm ▸ hre) hsep
      · exact fundamental_cycle_cut_displays_raw hN H.switching hd q hq.1 f e hfF heF hef.symm
          (hdr.symm ▸ hrf) (by simpa only [Set.pair_comm] using hsep)
    have hExtract := H.extracted_separated hN
    have hm : H.pairOf d ∈ H.extracted := Finset.mem_image.mpr ⟨d,hd,rfl⟩
    have hsing : EdgeAbove.CycleSeparated t {H.pairOf d} := by
      refine ⟨Finset.singleton_subset_iff.mpr (hExtract.1 hm),?_⟩
      simp
    obtain ⟨D⟩ := H.single_edge_reduction hN hd
    exact ⟨d,hd,(D.displays_iff (Realization.levelOne t ht _ hsing) q).mp hraw⟩

end Camus.RootedNetwork
