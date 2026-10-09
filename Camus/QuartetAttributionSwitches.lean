module

public import Camus.QuartetAttributionCuts
public import Camus.QuartetAttributionTree

@[expose] public section

namespace Camus.RootedNetwork

/-- Cutting a subgraph and replacing its missing chords by support paths. -/
theorem reachable_subgraph_reduce_iff {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S)
    (T R : Finset (ℕ × ℕ)) (hSR : S ⊆ R) (hRT : R ⊆ T) (hTN : T ⊆ N.edges)
    (B : Set (Sym2 ℕ))
    (havoid : ∀ d (hd : d ∈ T \ R),
      ∀ b ∈ B, b ∉ (supportPath hN hS
        (Finset.mem_sdiff.mpr ⟨hTN (Finset.mem_sdiff.mp hd).1,
          fun hs => (Finset.mem_sdiff.mp hd).2 (hSR hs)⟩)).val.edges)
    (u v : ℕ) :
    (({N with edges := T}).underlying.deleteEdges B).Reachable u v ↔
      (({N with edges := R}).underlying.deleteEdges B).Reachable u v := by
  classical
  have hle : (({N with edges := S}).underlying.deleteEdges B) ≤
      (({N with edges := R}).underlying.deleteEdges B) := by
    intro a b hab
    rw [SimpleGraph.deleteEdges_adj] at hab ⊢
    exact ⟨⟨hab.1.1, hab.1.2.imp (fun h => hSR h) (fun h => hSR h)⟩,hab.2⟩
  have step (a b : ℕ) (hab : (({N with edges := T}).underlying.deleteEdges B).Adj a b) :
      (({N with edges := R}).underlying.deleteEdges B).Reachable a b := by
    obtain ⟨hab,hcut⟩ := SimpleGraph.deleteEdges_adj.mp hab
    have oriented (a b : ℕ) (he : (a,b) ∈ T) (hcut : s(a,b) ∉ B) :
        (({N with edges := R}).underlying.deleteEdges B).Reachable a b := by
      by_cases hr : (a,b) ∈ R
      · exact (show (({N with edges := R}).underlying.deleteEdges B).Adj a b from
          SimpleGraph.deleteEdges_adj.mpr ⟨⟨edge_ne hN (hTN he),Or.inl hr⟩,hcut⟩).reachable
      · have hd : (a,b) ∈ T \ R := Finset.mem_sdiff.mpr ⟨he,hr⟩
        have hs : (a,b) ∈ N.edges \ S :=
          Finset.mem_sdiff.mpr ⟨hTN he,fun hs => hr (hSR hs)⟩
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
    exact ⟨⟨hab.1.1,hab.1.2.imp (fun h => hRT h) (fun h => hRT h)⟩,hab.2⟩

/-- A single-edge switching can remove a support arc only at that edge's recipient. -/
theorem single_switch_missing_head {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S K : Finset (ℕ × ℕ)} (hS : N.Switching S) (hK : N.Switching K)
    {d : ℕ × ℕ} (hKraw : K ⊆ insert d S) {g : ℕ × ℕ}
    (hg : g ∈ S) (hgK : g ∉ K) : g.2 = d.2 := by
  classical
  have hv : g.2 ∈ N.vertices := (hN.2.1 g (hS.1 hg)).2
  have hvroot : g.2 ≠ N.root := by
    intro heq
    have hm : g ∈ N.edges.filter (fun e => e.2 = N.root) :=
      Finset.mem_filter.mpr ⟨hS.1 hg,heq⟩
    have hz := Finset.card_eq_zero.mp hN.2.2.2.1
    rw [hz] at hm
    exact Finset.notMem_empty _ hm
  obtain ⟨k,hk⟩ := Finset.card_pos.mp (by rw [hK.2 _ hv hvroot]; omega)
  obtain ⟨hkK,hkg⟩ := Finset.mem_filter.mp hk
  rcases Finset.mem_insert.mp (hKraw hkK) with hk | hk
  · exact hkg.symm.trans (congrArg Prod.snd hk)
  · have hkEq : k = g := Prod.ext
      (switching_incoming_unique hN hS (by rw [← hkg]; exact hk) hg) hkg
    exact False.elim (hgK (hkEq ▸ hkK))

/-- Every support arc omitted by a single-edge switching lies on that cycle. -/
theorem single_switch_missing_on_cycle {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S K : Finset (ℕ × ℕ)} (hS : N.Switching S) (hK : N.Switching K)
    {d : ℕ × ℕ} (hd : d ∈ N.edges \ S) (hKraw : K ⊆ insert d S)
    {g : ℕ × ℕ} (hg : g ∈ S) (hgK : g ∉ K) :
    s(g.1,g.2) ∈ (fundamentalCycle hN hS hd).edges := by
  have hhead := single_switch_missing_head hN hS hK hKraw hg hgK
  have hfirst := switching_path_first_incoming hN hS
    (supportPath hN hS hd).val (supportPath hN hS hd).isPath (Finset.mem_sdiff.mp hd).1
  have hgfirst : g.1 = (supportPath hN hS hd).val.snd :=
    switching_incoming_unique hN hS (by rw [← hhead]; exact hg) hfirst
  change s(g.1,g.2) ∈ s(d.1,d.2) ::
    ((supportPath hN hS hd).val.mapLe (switching_underlying_le hS)).edges
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  apply List.mem_cons_of_mem
  rw [hgfirst,hhead,Sym2.eq_swap]
  have hpne : ¬(supportPath hN hS hd).val.Nil := by
    intro hp
    exact edge_ne hN (Finset.mem_sdiff.mp hd).1 (SimpleGraph.Walk.Nil.eq hp).symm
  exact (supportPath hN hS hd).val.mk_start_snd_mem_edges hpne

/-- Outside the selected cycle, a single-edge switching and the original support
have identical cut components. -/
theorem single_switch_cut_reachable_iff {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S K : Finset (ℕ × ℕ)} (hS : N.Switching S) (hK : N.Switching K)
    {d : ℕ × ℕ} (hd : d ∈ N.edges \ S) (hKraw : K ⊆ insert d S)
    (b : Sym2 ℕ) (hb : b ∉ (fundamentalCycle hN hS hd).edges) (u v : ℕ) :
    (({N with edges := K}).underlying.deleteEdges {b}).Reachable u v ↔
      (({N with edges := S}).underlying.deleteEdges {b}).Reachable u v := by
  classical
  have hrawN : insert d S ⊆ N.edges := Finset.insert_subset (Finset.mem_sdiff.mp hd).1 hS.1
  have hKiff := reachable_subgraph_reduce_iff hN hK (insert d S) K
    (Finset.Subset.refl _) hKraw hrawN {b} ?_ u v
  swap
  · intro g hg z hz hpath
    subst z
    have hgNK : g ∈ N.edges \ K := Finset.mem_sdiff.mpr
      ⟨hrawN (Finset.mem_sdiff.mp hg).1,(Finset.mem_sdiff.mp hg).2⟩
    have hgcycle : s(g.1,g.2) ∈ (fundamentalCycle hN hS hd).edges := by
      rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp hg).1 with h | h
      · subst g
        exact fundamentalCycle_mem_edges hN hS hd
      · exact single_switch_missing_on_cycle hN hS hK hd hKraw h (Finset.mem_sdiff.mp hg).2
    have hEq := cycle_eq_fundamental_of_reticulation hN hK
      (fundamentalCycle hN hS hd) (fundamentalCycle_isCycle hN hS hd)
      ((fundamentalCycle hN hS hd).snd_mem_support_of_mem_edges hgcycle) hgNK rfl
    apply hb
    apply List.mem_toFinset.mp
    rw [hEq]
    apply List.mem_toFinset.mpr
    change b ∈ s(g.1,g.2) ::
      ((supportPath hN hK hgNK).val.mapLe (switching_underlying_le hK)).edges
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
    exact List.mem_cons_of_mem _ hpath
  have hSiff := reachable_subgraph_reduce_iff hN hS (insert d S) S
    (Finset.Subset.refl _) (Finset.subset_insert _ _) hrawN {b} ?_ u v
  swap
  · intro g hg z hz hpath
    subst z
    have hgd : g = d := (Finset.mem_insert.mp (Finset.mem_sdiff.mp hg).1).resolve_right
      (Finset.mem_sdiff.mp hg).2
    subst g
    apply hb
    change b ∈ s(d.1,d.2) ::
      ((supportPath hN hS hd).val.mapLe (switching_underlying_le hS)).edges
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
    exact List.mem_cons_of_mem _ hpath
  exact hKiff.symm.trans hSiff

/-- A switching witness for a novel quartet must cut the selected cycle. -/
theorem single_raw_novel_cut_on_cycle {t : PhyloTree} (ht : t.WellLabelled)
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)}
    (H : SupportSubdivision t N S) {d : ℕ × ℕ} (hd : d ∈ N.edges \ S)
    {K : Finset (ℕ × ℕ)} (hK : N.Switching K) (hKraw : K ⊆ insert d S)
    (q : Quartet) (hqt : q.taxa ⊆ N.taxa) (hnot : q.induced t ≠ true)
    (b : Sym2 ℕ) (hb : b ∈ ({N with edges := K}).underlying.edgeSet)
    (hsep : N.Separates (({N with edges := K}).underlying.deleteEdges {b}) q) :
    b ∈ (fundamentalCycle hN H.switching hd).edges := by
  classical
  by_contra hbnot
  have hi := single_switch_cut_reachable_iff hN H.switching hK hd hKraw b hbnot
  have hbS : b ∈ ({N with edges := S}).underlying.edgeSet := by
    induction b using Sym2.inductionOn with
    | _ a z =>
      refine ⟨hb.1,?_⟩
      rcases hb.2 with he | he
      · rcases Finset.mem_insert.mp (hKraw he) with he | he
        · have hdmem := fundamentalCycle_mem_edges hN H.switching hd
          exact False.elim (hbnot (he.symm ▸ hdmem))
        · exact Or.inl he
      · rcases Finset.mem_insert.mp (hKraw he) with he | he
        · have hdmem := fundamentalCycle_mem_edges hN H.switching hd
          have heq : s(a,z) = s(d.1,d.2) := by
            rw [Sym2.eq_swap]
            exact congrArg (fun e : ℕ × ℕ => s(e.1,e.2)) he
          exact False.elim (hbnot (heq ▸ hdmem))
        · exact Or.inr he
  have hsepS : N.Separates (({N with edges := S}).underlying.deleteEdges {b}) q := by
    obtain ⟨h1,h2,h3⟩ := hsep
    refine ⟨fun a ha c hc => (hi _ _).mp (h1 a ha c hc),
      fun a ha c hc => (hi _ _).mp (h2 a ha c hc),
      fun a ha c hc h => h3 a ha c hc ((hi _ _).mpr h)⟩
  have hraw : ({N with edges := S}).DisplaysQuartet q :=
    ⟨hqt,S,⟨Finset.Subset.refl _,H.switching.2⟩,b,hbS,hsepS⟩
  have hbase : EdgeAbove.CycleSeparated t ∅ := by simp [EdgeAbove.CycleSeparated]
  have hbaseq := (H.baseline_subdivision.displays_iff
    (Realization.levelOne t ht ∅ hbase) q).mp hraw
  exact hnot ((Realization.baseline_displays_iff t ht q).mp hbaseq)

end Camus.RootedNetwork
