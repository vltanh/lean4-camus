module

public import Camus.Network.Subdivision.Switching
public import Camus.Network.Isomorphism.Invariance

@[expose] public section

namespace Camus

noncomputable def eraseArc (B : Finset (ℕ × ℕ)) (edge : Sym2 ℕ) : Finset (ℕ × ℕ) :=
  B.filter (fun arc => s(arc.1,arc.2) ≠ edge)

theorem underlying_eraseArc (N : RootedNetwork) (B : Finset (ℕ × ℕ)) (edge : Sym2 ℕ) :
    ({N with edges := B}).underlying.deleteEdges {edge} = ({N with edges := eraseArc B edge}).underlying := by
  classical
  ext u v
  simp only [SimpleGraph.deleteEdges_adj, RootedNetwork.underlying, eraseArc,
    Finset.mem_filter, Set.mem_singleton_iff]
  have hswap : s(v,u) = s(u,v) := Sym2.eq_swap
  rw [hswap]
  tauto

theorem edgeSet_arc_exists (N : RootedNetwork) {edge : Sym2 ℕ}
    (hedge : edge ∈ N.underlying.edgeSet) : ∃ arc ∈ N.edges, s(arc.1,arc.2) = edge := by
  induction edge using Sym2.inductionOn with
  | _ u v =>
    rcases hedge.2 with he | he
    · exact ⟨(u,v), he, rfl⟩
    · exact ⟨(v,u), he, Sym2.eq_swap⟩

theorem source_eraseArc {P : RootedNetwork} (hP : P.RootedBinaryLevelOne)
    {R : Finset (ℕ × ℕ)} (hR : R ⊆ P.edges) {e : ℕ × ℕ} (he : e ∈ P.edges) :
    eraseArc R s(e.1,e.2) = R.erase e := by
  classical
  ext f
  simp only [eraseArc, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hf, hsym⟩
    exact ⟨fun h => hsym (h ▸ rfl), hf⟩
  · rintro ⟨hfe, hf⟩
    refine ⟨hf, ?_⟩
    intro hsym
    rcases Sym2.mk_eq_mk_iff.mp hsym with h | h
    · exact hfe h
    · have hreverse : (e.2,e.1) ∈ P.edges := by
        change e.swap ∈ P.edges
        rw [← h]
        exact hR hf
      exact RootedNetwork.edge_reverse_not_mem hP he hreverse

namespace GraphSubdivision

variable {P N : RootedNetwork}

theorem wire_source_original (H : GraphSubdivision P N) {e arc : ℕ × ℕ}
    (he : e ∈ P.edges) (harc : arc ∈ wireEdges (H.wire e))
    (horig : arc.1 ∈ P.vertices.image H.original) : arc.1 = H.original e.1 := by
  rcases wire_source_cases (H.wire_laws e he).2.1 harc with hhead | hinner
  · exact Option.some.inj (hhead.symm.trans (H.wire_laws e he).2.2.1)
  · obtain ⟨u, hu, h⟩ := Finset.mem_image.mp horig
    exact (H.interior_not_original he hinner hu h.symm).elim

theorem wire_target_original (H : GraphSubdivision P N) {e arc : ℕ × ℕ}
    (he : e ∈ P.edges) (harc : arc ∈ wireEdges (H.wire e))
    (horig : arc.2 ∈ P.vertices.image H.original) : arc.2 = H.original e.2 := by
  rcases wire_target_cases (H.wire_laws e he).2.1 harc with hlast | hinner
  · exact Option.some.inj (hlast.symm.trans (H.wire_laws e he).2.2.2.1)
  · obtain ⟨u, hu, h⟩ := Finset.mem_image.mp horig
    exact (H.interior_not_original he hinner hu h.symm).elim

theorem reverse_arc_not_mem (H : GraphSubdivision P N) (hP : P.RootedBinaryLevelOne)
    {arc : ℕ × ℕ} (harc : arc ∈ N.edges) : arc.swap ∉ N.edges := by
  classical
  intro hrev
  rw [H.edges_covered] at harc hrev
  obtain ⟨e, he, hwire⟩ := Finset.mem_biUnion.mp harc
  obtain ⟨f, hf, hrevwire⟩ := Finset.mem_biUnion.mp hrev
  have same_impossible (hef : e = f) : False := by
    subst f
    have hi := wire_edge_idxOf (H.wire_laws e he).2.1 hwire
    have hj := wire_edge_idxOf (H.wire_laws e he).2.1 hrevwire
    simp only [Prod.fst_swap, Prod.snd_swap] at hj
    omega
  by_cases hfirst : arc.1 ∈ P.vertices.image H.original
  · by_cases hsecond : arc.2 ∈ P.vertices.image H.original
    · have hse := H.wire_source_original he hwire hfirst
      have hte := H.wire_target_original he hwire hsecond
      have hsf := H.wire_source_original hf hrevwire hsecond
      have htf := H.wire_target_original hf hrevwire hfirst
      have h₁ : f.1 = e.2 := H.original_injective (H.edge_endpoints f hf).1
        (H.edge_endpoints e he).2 (hsf.symm.trans hte)
      have h₂ : f.2 = e.1 := H.original_injective (H.edge_endpoints f hf).2
        (H.edge_endpoints e he).1 (htf.symm.trans hse)
      have hfe : f = (e.2,e.1) := Prod.ext h₁ h₂
      rw [hfe] at hf
      exact RootedNetwork.edge_reverse_not_mem hP he hf
    · have hin₁ : arc.2 ∈ wireInterior (H.wire e) := by
        rcases wire_target_cases (H.wire_laws e he).2.1 hwire with h | h
        · exact (hsecond (Finset.mem_image.mpr ⟨e.2, (H.edge_endpoints e he).2,
            Option.some.inj ((H.wire_laws e he).2.2.2.1.symm.trans h)⟩)).elim
        · exact h
      have hin₂ : arc.2 ∈ wireInterior (H.wire f) := by
        rcases wire_source_cases (H.wire_laws f hf).2.1 hrevwire with h | h
        · exact (hsecond (Finset.mem_image.mpr ⟨f.1, (H.edge_endpoints f hf).1,
            Option.some.inj ((H.wire_laws f hf).2.2.1.symm.trans h)⟩)).elim
        · exact h
      exact same_impossible (H.interior_unique he hf hin₁ hin₂)
  · have hin₁ : arc.1 ∈ wireInterior (H.wire e) := by
      rcases wire_source_cases (H.wire_laws e he).2.1 hwire with h | h
      · exact (hfirst (Finset.mem_image.mpr ⟨e.1, (H.edge_endpoints e he).1,
          Option.some.inj ((H.wire_laws e he).2.2.1.symm.trans h)⟩)).elim
      · exact h
    have hin₂ : arc.1 ∈ wireInterior (H.wire f) := by
      rcases wire_target_cases (H.wire_laws f hf).2.1 hrevwire with h | h
      · exact (hfirst (Finset.mem_image.mpr ⟨f.2, (H.edge_endpoints f hf).2,
          Option.some.inj ((H.wire_laws f hf).2.2.2.1.symm.trans h)⟩)).elim
      · exact h
    exact same_impossible (H.interior_unique he hf hin₁ hin₂)

theorem sym_owner_unique (H : GraphSubdivision P N) (hP : P.RootedBinaryLevelOne)
    {e f a b : ℕ × ℕ} (he : e ∈ P.edges) (hf : f ∈ P.edges)
    (ha : a ∈ wireEdges (H.wire e)) (hb : b ∈ wireEdges (H.wire f))
    (hsym : s(a.1,a.2) = s(b.1,b.2)) : e = f := by
  rcases Sym2.mk_eq_mk_iff.mp hsym with hab | hab
  · exact H.edge_owner_unique he hf ha (hab ▸ hb)
  · have haN : a ∈ N.edges := by rw [H.edges_covered]; exact Finset.mem_biUnion.mpr ⟨e, he, ha⟩
    have hbN : b ∈ N.edges := by rw [H.edges_covered]; exact Finset.mem_biUnion.mpr ⟨f, hf, hb⟩
    have hba : b = a.swap := by simpa using (congrArg Prod.swap hab).symm
    exact (H.reverse_arc_not_mem hP haN (hba ▸ hbN)).elim

theorem active_eraseArc (H : GraphSubdivision P N) (hP : P.RootedBinaryLevelOne)
    {B : Finset (ℕ × ℕ)} {e arc : ℕ × ℕ}
    (he : e ∈ P.edges) (harc : arc ∈ wireEdges (H.wire e)) :
    H.active (eraseArc B s(arc.1,arc.2)) = (H.active B).erase e := by
  classical
  ext f
  rw [Finset.mem_erase]
  simp only [active, Finset.mem_filter]
  constructor
  · rintro ⟨hf, hfull⟩
    refine ⟨?_, hf, fun a ha => (Finset.mem_filter.mp (hfull ha)).1⟩
    intro hfe
    subst f
    exact (Finset.mem_filter.mp (hfull harc)).2 rfl
  · rintro ⟨hfe, hf, hfull⟩
    refine ⟨hf, ?_⟩
    intro a ha
    apply Finset.mem_filter.mpr
    refine ⟨hfull ha, ?_⟩
    intro hsym
    exact hfe (H.sym_owner_unique hP hf he ha harc hsym)

theorem separates_iff (H : GraphSubdivision P N) {B : Finset (ℕ × ℕ)}
    (hB : B ⊆ N.edges) (q : Quartet) (hq : q.taxa ⊆ P.taxa) :
    N.Separates ({N with edges := B}).underlying q ↔
      P.Separates ({P with edges := H.active B}).underlying q := by
  have reach a b (ha : a ∈ P.taxa) (hb : b ∈ P.taxa) :
      ({N with edges := B}).underlying.Reachable (N.leaf a) (N.leaf b) ↔
        ({P with edges := H.active B}).underlying.Reachable (P.leaf a) (P.leaf b) := by
    rw [← H.leaves_preserved a ha, ← H.leaves_preserved b hb]
    exact H.reachable_iff hB (H.leaves_left a ha) (H.leaves_left b hb)
  have hfirst a (ha : a ∈ q.sides.1) : a ∈ P.taxa := hq (q.sides_subset_taxa.1 ha)
  have hsecond a (ha : a ∈ q.sides.2) : a ∈ P.taxa := hq (q.sides_subset_taxa.2 ha)
  constructor
  · rintro ⟨hAA, hBB, hAB⟩
    exact ⟨fun a ha b hb => (reach a b (hfirst a ha) (hfirst b hb)).mp (hAA a ha b hb),
      fun a ha b hb => (reach a b (hsecond a ha) (hsecond b hb)).mp (hBB a ha b hb),
      fun a ha b hb h => hAB a ha b hb ((reach a b (hfirst a ha) (hsecond b hb)).mpr h)⟩
  · rintro ⟨hAA, hBB, hAB⟩
    exact ⟨fun a ha b hb => (reach a b (hfirst a ha) (hfirst b hb)).mpr (hAA a ha b hb),
      fun a ha b hb => (reach a b (hsecond a ha) (hsecond b hb)).mpr (hBB a ha b hb),
      fun a ha b hb h => hAB a ha b hb ((reach a b (hfirst a ha) (hsecond b hb)).mp h)⟩

theorem separates_cut_iff (H : GraphSubdivision P N) (hP : P.RootedBinaryLevelOne)
    {B : Finset (ℕ × ℕ)} (hB : B ⊆ N.edges) {e arc : ℕ × ℕ}
    (he : e ∈ P.edges) (harc : arc ∈ wireEdges (H.wire e))
    (q : Quartet) (hq : q.taxa ⊆ P.taxa) :
    N.Separates (({N with edges := B}).underlying.deleteEdges {s(arc.1,arc.2)}) q ↔
      P.Separates (({P with edges := H.active B}).underlying.deleteEdges {s(e.1,e.2)}) q := by
  have hcutB : eraseArc B s(arc.1,arc.2) ⊆ N.edges := (Finset.filter_subset _ _).trans hB
  have hactive : H.active B ⊆ P.edges := Finset.filter_subset _ _
  rw [underlying_eraseArc, H.separates_iff hcutB q hq,
    H.active_eraseArc hP he harc, underlying_eraseArc,
    source_eraseArc hP hactive he]

end GraphSubdivision
end Camus
