module

public import Camus.GraphProperties
public import Camus.GraphRealizationSubdivision
public import Camus.DynamicProgramming
public import Camus.QuartetAttributionUnique

@[expose] public section

namespace Camus

namespace Realization

/-- A switching of the single-edge reduction is also a switching of the full
network after the other non-tree edges are restored. -/
theorem single_displays_full (t : PhyloTree) (ht : t.WellLabelled)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) {e : Pair}
    (he : e ∈ E) (q : Quartet)
    (hq : (graph t {e}).DisplaysQuartet q) : (graph t E).DisplaysQuartet q := by
  classical
  let N := graph t E
  let S := supportEdges t E
  let H := support t ht E hE
  have hN : N.RootedBinaryLevelOne := levelOne t ht E hE
  have hExtract : H.extracted = E := extracted_eq t ht E hE
  have hx : e ∈ (N.edges \ S).image H.pairOf := by
    change e ∈ H.extracted
    rw [hExtract]
    exact he
  obtain ⟨d,hd,hde⟩ := Finset.mem_image.mp hx
  obtain ⟨D⟩ := H.single_edge_reduction hN hd
  rw [hde] at D
  have hsing : EdgeAbove.CycleSeparated t {e} := by
    refine ⟨Finset.singleton_subset_iff.mpr (hE.1 he), ?_⟩
    simp
  have hraw := (D.displays_iff (levelOne t ht {e} hsing) q).mpr hq
  apply RootedNetwork.displays_of_edges_subset (N := N) (S := insert d S) _ q hraw
  exact Finset.insert_subset (Finset.mem_sdiff.mp hd).1 H.switching.1

end Realization

/-- Lemma 1 (`mthst2`) for an arbitrary rooted graph with an anchored support
switching. The single-pair realization is Definition 3's T+e. Completeness and
suppression bridges justify this representation; attribution is not assumed.
The only cited hypothesis is precisely the named literature Observation 2. -/
theorem lemma1 (observation2 : External.WarnowTabatabaeeEvansObservation2)
    (t : PhyloTree) (ht : t.WellLabelled) (N : RootedNetwork)
    (hN : N.RootedBinaryLevelOne) (S : Finset (ℕ × ℕ))
    (H : SupportSubdivision t N S) (q : Quartet)
    (hq : N.DisplaysQuartet q) (hnot : q.induced t ≠ true) :
    ∃! e, e ∈ N.edges \ S ∧
      (Realization.graph t {H.pairOf e}).DisplaysQuartet q := by
  obtain ⟨e,he,hqe⟩ := RootedNetwork.novel_edge_exists observation2 ht hN H q hq hnot
  refine ⟨e,⟨he,hqe⟩,?_⟩
  intro f hf
  exact RootedNetwork.novel_edge_unique ht hN H q hnot hf.1 he hf.2 hqe

/-- Directed-graph bridge for Lemma 2: two non-tree edges with the same original LCA target
would yield cycles sharing that vertex. This uses the concrete footprint bridge
and the paper's shared-target contradiction. -/
theorem lemma2 (t : PhyloTree) (ht : t.WellLabelled) (N : RootedNetwork)
    (hN : N.RootedBinaryLevelOne) (S : Finset (ℕ × ℕ))
    (H : SupportSubdivision t N S) {e f : ℕ × ℕ}
    (he : e ∈ N.edges \ S) (hf : f ∈ N.edges \ S)
    (htarget : EdgeAbove.target (H.pairOf e) = EdgeAbove.target (H.pairOf f)) : e = f := by
  apply H.pairOf_injective hN (by simpa using he) (by simpa using hf)
  apply EdgeAbove.target_unique t H.extracted (H.extracted_separated hN)
  · exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  · exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
  · exact htarget

namespace DynamicProgramming

theorem mem_novel_iff (t : PhyloTree) (ht : t.WellLabelled)
    (Q : Multiset Quartet) (N : RootedNetwork) (q : Quartet) :
    q ∈ novel t Q N ↔ q ∈ Q.toFinset ∧ N.DisplaysQuartet q ∧ ¬q.induced t = true := by
  classical
  simp only [novel, repertoire, Finset.mem_sdiff, Finset.mem_filter,
    Realization.baseline_displays_iff t ht q]
  tauto

/-- Set-valued disjoint-union consequence of Lemma 1. This proof must use the
numbered Lemma 1, rather than bypass it through an assumed score identity. -/
theorem novel_disjoint_union
    (observation2 : External.WarnowTabatabaeeEvansObservation2)
    (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    novel t Q (Realization.graph t E) =
        E.biUnion (fun e => novel t Q (Realization.graph t {e})) ∧
      (E : Set Pair).Pairwise (fun e f =>
        Disjoint (novel t Q (Realization.graph t {e}))
          (novel t Q (Realization.graph t {f}))) := by
  classical
  let N := Realization.graph t E
  let S := Realization.supportEdges t E
  let H := Realization.support t ht E hE
  have hN : N.RootedBinaryLevelOne := Realization.levelOne t ht E hE
  have hExtract : H.extracted = E := Realization.extracted_eq t ht E hE
  have hpair (d : ℕ × ℕ) (hd : d ∈ N.edges \ S) : H.pairOf d ∈ E := by
    have hm : H.pairOf d ∈ H.extracted := Finset.mem_image.mpr ⟨d,hd,rfl⟩
    simpa only [hExtract] using hm
  have hindex (e : Pair) (he : e ∈ E) :
      ∃ d, d ∈ N.edges \ S ∧ H.pairOf d = e := by
    have hx : e ∈ (N.edges \ S).image H.pairOf := by
      change e ∈ H.extracted
      rw [hExtract]
      exact he
    exact Finset.mem_image.mp hx
  constructor
  · ext q
    constructor
    · intro hq
      obtain ⟨hQ,hdisplay,hnot⟩ := (mem_novel_iff t ht Q N q).mp hq
      obtain ⟨d,hd,_⟩ := lemma1 observation2 t ht N hN S H q hdisplay hnot
      exact Finset.mem_biUnion.mpr ⟨H.pairOf d,hpair d hd.1,
        (mem_novel_iff t ht Q _ q).mpr ⟨hQ,hd.2,hnot⟩⟩
    · intro hq
      obtain ⟨e,he,hqe⟩ := Finset.mem_biUnion.mp hq
      obtain ⟨hQ,hdisplay,hnot⟩ := (mem_novel_iff t ht Q _ q).mp hqe
      exact (mem_novel_iff t ht Q N q).mpr ⟨hQ,
        Realization.single_displays_full t ht E hE he q hdisplay,hnot⟩
  · intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro q hqe hqf
    obtain ⟨_,heDisplay,hnot⟩ := (mem_novel_iff t ht Q _ q).mp hqe
    obtain ⟨_,hfDisplay,_⟩ := (mem_novel_iff t ht Q _ q).mp hqf
    have hdisplay := Realization.single_displays_full t ht E hE he q heDisplay
    obtain ⟨d,_,hunique⟩ := lemma1 observation2 t ht N hN S H q hdisplay hnot
    obtain ⟨de,hde,hpe⟩ := hindex e he
    obtain ⟨df,hdf,hpf⟩ := hindex f hf
    have hdeq : de = d := hunique de ⟨hde,by rw [hpe]; exact heDisplay⟩
    have hdfq : df = d := hunique df ⟨hdf,by rw [hpf]; exact hfDisplay⟩
    apply hef
    calc
      e = H.pairOf de := hpe.symm
      _ = H.pairOf df := congrArg H.pairOf (hdeq.trans hdfq.symm)
      _ = f := hpf

theorem baseline_subset (t : PhyloTree) (ht : t.WellLabelled)
    (Q : Multiset Quartet) (E : Finset Pair) (hE : EdgeAbove.CycleSeparated t E) :
    repertoire Q (Realization.graph t ∅) ⊆ repertoire Q (Realization.graph t E) := by
  classical
  intro q hq
  obtain ⟨hQ,hdisplay⟩ := Finset.mem_filter.mp hq
  have hbase : EdgeAbove.CycleSeparated t ∅ := by simp [EdgeAbove.CycleSeparated]
  have D := Realization.supportGraphSubdivision t E hE.1
  have hraw := (D.displays_iff (Realization.levelOne t ht ∅ hbase) q).mpr hdisplay
  have hS := (Realization.support t ht E hE).switching.1
  exact Finset.mem_filter.mpr ⟨hQ, RootedNetwork.displays_of_edges_subset hS q hraw⟩

end DynamicProgramming
end Camus
