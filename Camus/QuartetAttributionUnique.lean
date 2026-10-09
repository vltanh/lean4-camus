module

public import Camus.QuartetAttributionSwitches

@[expose] public section

namespace Camus

namespace Quartet

theorem sides_pairs (q : Quartet) :
    ∃ a b c d, q.sides = ({a,b}, {c,d}) := by
  unfold sides
  split_ifs
  · exact ⟨q.a,q.b,q.c,q.d,rfl⟩
  · exact ⟨q.a,q.c,q.b,q.d,rfl⟩
  · exact ⟨q.a,q.d,q.b,q.c,rfl⟩

end Quartet

namespace RootedNetwork

theorem separates_of_pair_connections (N : RootedNetwork) (q : Quartet)
    {a b c d : ℕ} (hs : q.sides = ({a,b},{c,d})) (G : SimpleGraph ℕ)
    (hab : G.Reachable (N.leaf a) (N.leaf b))
    (hcd : G.Reachable (N.leaf c) (N.leaf d))
    (hac : ¬G.Reachable (N.leaf a) (N.leaf c)) : N.Separates G q := by
  have hfirst (x : ℕ) (hx : x ∈ q.sides.1) : G.Reachable (N.leaf x) (N.leaf a) := by
    rw [hs] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact .refl _
    · exact hab.symm
  have hsecond (x : ℕ) (hx : x ∈ q.sides.2) : G.Reachable (N.leaf x) (N.leaf c) := by
    rw [hs] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact .refl _
    · exact hcd.symm
  exact ⟨fun x hx y hy => (hfirst x hx).trans (hfirst y hy).symm,
    fun x hx y hy => (hsecond x hx).trans (hsecond y hy).symm,
    fun x hx y hy h => hac ((hfirst x hx).symm.trans (h.trans (hsecond y hy)))⟩

/-- The two within-pair paths of a nonbaseline quartet must intersect. -/
theorem nonbaseline_pair_paths_intersect {t : PhyloTree} (ht : t.WellLabelled)
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)}
    (H : SupportSubdivision t N S) (q : Quartet) (hqt : q.taxa ⊆ N.taxa)
    (hnot : q.induced t ≠ true) {a b c d : ℕ}
    (hs : q.sides = ({a,b},{c,d}))
    (p : ({N with edges := S}).underlying.Walk (N.leaf a) (N.leaf b))
    (r : ({N with edges := S}).underlying.Walk (N.leaf c) (N.leaf d)) :
    ∃ v, v ∈ p.support ∧ v ∈ r.support := by
  classical
  by_contra hnone
  have hdis : p.support.Disjoint r.support := by
    intro v hp hr
    exact hnone ⟨v,hp,hr⟩
  have ha : a ∈ N.taxa := hqt (q.sides_subset_taxa.1 (by rw [hs]; simp))
  have hc : c ∈ N.taxa := hqt (q.sides_subset_taxa.2 (by rw [hs]; simp))
  obtain ⟨w,hw,_⟩ := switching_existsUnique_path hN H.switching
    (hN.2.2.2.2.2.2.2.1 a ha).1 (hN.2.2.2.2.2.2.2.1 c hc).1
  obtain ⟨e,he,hab,hcd,hac⟩ := disjoint_paths_separating_edge
    (switching_acyclic hN H.switching) p r hdis w hw
  have hraw : ({N with edges := S}).DisplaysQuartet q :=
    ⟨hqt,S,⟨Finset.Subset.refl _,H.switching.2⟩,e,he,
      separates_of_pair_connections N q hs _ hab hcd hac⟩
  have hbase : EdgeAbove.CycleSeparated t ∅ := by simp [EdgeAbove.CycleSeparated]
  have hbaseq := (H.baseline_subdivision.displays_iff
    (Realization.levelOne t ht ∅ hbase) q).mp hraw
  exact hnot ((Realization.baseline_displays_iff t ht q).mp hbaseq)

theorem fundamentalCycle_support_iff {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) {d : ℕ × ℕ}
    (hd : d ∈ N.edges \ S) (v : ℕ) :
    v ∈ (fundamentalCycle hN hS hd).support ↔ v ∈ (supportPath hN hS hd).val.support := by
  change v ∈ d.1 :: ((supportPath hN hS hd).val.mapLe _).support ↔ _
  rw [SimpleGraph.Walk.support_mapLe_eq_support,List.mem_cons]
  constructor
  · rintro (rfl | h)
    · exact (supportPath hN hS hd).val.end_mem_support
    · exact h
  · exact Or.inr

/-- A shared vertex of the two pair paths belongs to every cycle that produces
this novel quartet. The proof uses the support tree, not an attribution law. -/
theorem single_novel_pair_vertex_on_cycle {t : PhyloTree} (ht : t.WellLabelled)
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)}
    (H : SupportSubdivision t N S) (q : Quartet) (hnot : q.induced t ≠ true)
    {a b c d : ℕ} (hs : q.sides = ({a,b},{c,d}))
    (p : ({N with edges := S}).underlying.Walk (N.leaf a) (N.leaf b)) (hp : p.IsPath)
    (r : ({N with edges := S}).underlying.Walk (N.leaf c) (N.leaf d)) (hr : r.IsPath)
    {v : ℕ} (hvp : v ∈ p.support) (hvr : v ∈ r.support)
    {e : ℕ × ℕ} (he : e ∈ N.edges \ S)
    (hq : ({N with edges := insert e S}).DisplaysQuartet q) :
    v ∈ (fundamentalCycle hN H.switching he).support := by
  classical
  obtain ⟨hqt,K,hK,cut,hb,hsep⟩ := hq
  have hrawN : insert e S ⊆ N.edges := Finset.insert_subset (Finset.mem_sdiff.mp he).1 H.switching.1
  have hKN : N.Switching K := ⟨hK.1.trans hrawN,hK.2⟩
  have hbcycle := single_raw_novel_cut_on_cycle ht hN H he hKN hK.1 q hqt hnot cut hb hsep
  by_contra hvnot
  let C : Set ℕ := {x | x ∈ (supportPath hN H.switching he).val.support}
  have hvC : v ∉ C := fun hvC => hvnot ((fundamentalCycle_support_iff hN H.switching he v).mpr hvC)
  have hC : ∀ x ∈ C, ∀ y ∈ C, ∃ w : ({N with edges := S}).underlying.Walk x y,
      w.IsPath ∧ ∀ z ∈ w.support, z ∈ C := by
    intro x hx y hy
    obtain ⟨w,hw,hwS⟩ := path_between_chain_members
      (supportPath hN H.switching he).val.isChain_adj_support hx hy
    exact ⟨w,hw,hwS⟩
  let B : Set (Sym2 ℕ) := ((S \ K).image (fun g => s(g.1,g.2)) : Set (Sym2 ℕ)) ∪ {cut}
  have hB : ∀ f ∈ B, ∀ x ∈ f, x ∈ C := by
    intro f hf x hx
    have hfcycle : f ∈ (fundamentalCycle hN H.switching he).edges := by
      rcases hf with hf | hf
      · obtain ⟨g,hg,hgf⟩ := Finset.mem_image.mp hf
        rw [← hgf]
        exact single_switch_missing_on_cycle hN H.switching hKN he hK.1
          (Finset.mem_sdiff.mp hg).1 (Finset.mem_sdiff.mp hg).2
      · exact Set.mem_singleton_iff.mp hf ▸ hbcycle
    exact (fundamentalCycle_support_iff hN H.switching he x).mp
      ((fundamentalCycle hN H.switching he).mem_support_of_mem_edges hfcycle hx)
  have hle : (({N with edges := S}).underlying.deleteEdges B) ≤
      (({N with edges := K}).underlying.deleteEdges {cut}) := by
    intro x y hxy
    obtain ⟨hxy,hBxy⟩ := SimpleGraph.deleteEdges_adj.mp hxy
    have hkeep (g : ℕ × ℕ) (hg : g ∈ S) (hgsym : s(g.1,g.2) = s(x,y)) : g ∈ K := by
      by_contra hn
      apply hBxy
      exact Or.inl (hgsym ▸ Finset.mem_image.mpr ⟨g,Finset.mem_sdiff.mpr ⟨hg,hn⟩,rfl⟩)
    refine SimpleGraph.deleteEdges_adj.mpr ⟨⟨hxy.1,?_⟩,?_⟩
    · rcases hxy.2 with h | h
      · exact Or.inl (hkeep (x,y) h rfl)
      · exact Or.inr (hkeep (y,x) h Sym2.eq_swap)
    · exact fun h => hBxy (Or.inr h)
  have hpa := path_outside_region_reachable (switching_acyclic hN H.switching)
    C hC B hB p hp hvp hvC
  have hra := path_outside_region_reachable (switching_acyclic hN H.switching)
    C hC B hB r hr hvr hvC
  have hside1 : ∃ x ∈ q.sides.1,
      (({N with edges := K}).underlying.deleteEdges {cut}).Reachable (N.leaf x) v := by
    rcases hpa with h | h
    · exact ⟨a,by rw [hs]; simp,h.mono hle⟩
    · exact ⟨b,by rw [hs]; simp,h.symm.mono hle⟩
  have hside2 : ∃ x ∈ q.sides.2,
      (({N with edges := K}).underlying.deleteEdges {cut}).Reachable (N.leaf x) v := by
    rcases hra with h | h
    · exact ⟨c,by rw [hs]; simp,h.mono hle⟩
    · exact ⟨d,by rw [hs]; simp,h.symm.mono hle⟩
  obtain ⟨x,hx,hxv⟩ := hside1
  obtain ⟨y,hy,hyv⟩ := hside2
  exact hsep.2.2 x hx y hy (hxv.trans hyv.symm)

/-- Uniqueness in Lemma 1: two distinct cycles cannot both contain the shared
vertex of the two pair paths of a nonbaseline quartet. -/
theorem novel_edge_unique {t : PhyloTree} (ht : t.WellLabelled)
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne) {S : Finset (ℕ × ℕ)}
    (H : SupportSubdivision t N S) (q : Quartet) (hnot : q.induced t ≠ true)
    {e f : ℕ × ℕ} (he : e ∈ N.edges \ S) (hf : f ∈ N.edges \ S)
    (hqe : (Realization.graph t {H.pairOf e}).DisplaysQuartet q)
    (hqf : (Realization.graph t {H.pairOf f}).DisplaysQuartet q) : e = f := by
  classical
  have hExtract := H.extracted_separated hN
  have hsingle (g : ℕ × ℕ) (hg : g ∈ N.edges \ S) :
      EdgeAbove.CycleSeparated t {H.pairOf g} := by
    refine ⟨Finset.singleton_subset_iff.mpr
      (hExtract.1 (Finset.mem_image.mpr ⟨g,hg,rfl⟩)),?_⟩
    simp
  obtain ⟨De⟩ := H.single_edge_reduction hN he
  obtain ⟨Df⟩ := H.single_edge_reduction hN hf
  have hrawE := (De.displays_iff (Realization.levelOne t ht _ (hsingle e he)) q).mpr hqe
  have hrawF := (Df.displays_iff (Realization.levelOne t ht _ (hsingle f hf)) q).mpr hqf
  have hqt : q.taxa ⊆ N.taxa := hrawE.1
  obtain ⟨a,b,c,d,hs⟩ := q.sides_pairs
  have ha : a ∈ N.taxa := hqt (q.sides_subset_taxa.1 (by rw [hs]; simp))
  have hb : b ∈ N.taxa := hqt (q.sides_subset_taxa.1 (by rw [hs]; simp))
  have hc : c ∈ N.taxa := hqt (q.sides_subset_taxa.2 (by rw [hs]; simp))
  have hd : d ∈ N.taxa := hqt (q.sides_subset_taxa.2 (by rw [hs]; simp))
  have hleaf (x : ℕ) (hx : x ∈ N.taxa) : N.leaf x ∈ N.vertices :=
    (hN.2.2.2.2.2.2.2.1 x hx).1
  obtain ⟨p,hp,_⟩ := switching_existsUnique_path hN H.switching (hleaf a ha) (hleaf b hb)
  obtain ⟨r,hr,_⟩ := switching_existsUnique_path hN H.switching (hleaf c hc) (hleaf d hd)
  obtain ⟨v,hvp,hvr⟩ := nonbaseline_pair_paths_intersect ht hN H q hqt hnot hs p r
  have hve := single_novel_pair_vertex_on_cycle ht hN H q hnot hs p hp r hr hvp hvr he hrawE
  have hvf := single_novel_pair_vertex_on_cycle ht hN H q hnot hs p hp r hr hvp hvr hf hrawF
  by_contra hef
  exact Finset.disjoint_left.mp (fundamentalCycles_disjoint hN H.switching he hf hef)
    (List.mem_toFinset.mpr hve) (List.mem_toFinset.mpr hvf)

end RootedNetwork
end Camus
