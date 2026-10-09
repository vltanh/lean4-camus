module

public import Camus.GraphSubdivisionColors
public import Camus.GraphRealizationSupport

@[expose] public section

namespace Camus

theorem wire_last_not_mem_dropLast {L : List ℕ} (hL : L.Nodup) {v : ℕ}
    (hv : L.getLast? = some v) : v ∉ L.dropLast := by
  have hne : L ≠ [] := by intro h; simp [h] at hv
  have hlast : L.getLast hne = v := Option.some.inj
    ((List.getLast?_eq_some_getLast hne).symm.trans hv)
  have hn : (L.dropLast ++ [v]).Nodup := by
    rw [← hlast, List.dropLast_append_getLast hne]
    exact hL
  intro h
  exact (List.nodup_append.mp hn).2.2 _ h _ (by simp) rfl

theorem wire_source_cases {L : List ℕ} (hL : L.Nodup) {f : ℕ × ℕ}
    (hf : f ∈ wireEdges L) : L.head? = some f.1 ∨ f.1 ∈ wireInterior L := by
  rcases wire_vertex_cases (List.mem_of_mem_dropLast (wire_edge_source_mem hf)) with h | h | h
  · exact Or.inl h
  · exact (wire_last_not_mem_dropLast hL h (wire_edge_source_mem hf)).elim
  · exact Or.inr h

theorem wire_target_cases {L : List ℕ} (hL : L.Nodup) {f : ℕ × ℕ}
    (hf : f ∈ wireEdges L) : L.getLast? = some f.2 ∨ f.2 ∈ wireInterior L := by
  rcases wire_vertex_cases (List.mem_of_mem_tail (wire_edge_target_mem hf)) with h | h | h
  · exact (wire_head_not_mem_tail hL h (wire_edge_target_mem hf)).elim
  · exact Or.inl h
  · exact Or.inr h

namespace GraphSubdivision

variable {P N : RootedNetwork}

theorem original_mem_vertices (H : GraphSubdivision P N) {u : ℕ} (hu : u ∈ P.vertices) :
    H.original u ∈ N.vertices := by
  rw [H.vertices_covered]
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)

theorem interior_mem_vertices (H : GraphSubdivision P N) {e : ℕ × ℕ}
    (he : e ∈ P.edges) {v : ℕ} (hv : v ∈ wireInterior (H.wire e)) : v ∈ N.vertices := by
  rw [H.vertices_covered]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, hv⟩)

theorem edge_owner_unique (H : GraphSubdivision P N) {e f arc : ℕ × ℕ}
    (he : e ∈ P.edges) (hf : f ∈ P.edges)
    (h1 : arc ∈ wireEdges (H.wire e)) (h2 : arc ∈ wireEdges (H.wire f)) : e = f := by
  have heleaf := H.edge_endpoints e he
  have hfleaf := H.edge_endpoints f hf
  have source_eq {e : ℕ × ℕ} (he : e ∈ P.edges) (h : (H.wire e).head? = some arc.1) :
      arc.1 = H.original e.1 := Option.some.inj (h.symm.trans (H.wire_laws e he).2.2.1)
  have target_eq {e : ℕ × ℕ} (he : e ∈ P.edges) (h : (H.wire e).getLast? = some arc.2) :
      arc.2 = H.original e.2 := Option.some.inj (h.symm.trans (H.wire_laws e he).2.2.2.1)
  rcases wire_source_cases (H.wire_laws e he).2.1 h1 with hsrc₁ | hsrc₁ <;>
    rcases wire_source_cases (H.wire_laws f hf).2.1 h2 with hsrc₂ | hsrc₂
  · have hs : e.1 = f.1 := H.original_injective heleaf.1 hfleaf.1
      ((source_eq he hsrc₁).symm.trans (source_eq hf hsrc₂))
    rcases wire_target_cases (H.wire_laws e he).2.1 h1 with htgt₁ | htgt₁ <;>
      rcases wire_target_cases (H.wire_laws f hf).2.1 h2 with htgt₂ | htgt₂
    · exact Prod.ext hs (H.original_injective heleaf.2 hfleaf.2
        ((target_eq he htgt₁).symm.trans (target_eq hf htgt₂)))
    · exact (H.interior_not_original hf htgt₂ heleaf.2 (target_eq he htgt₁)).elim
    · exact (H.interior_not_original he htgt₁ hfleaf.2 (target_eq hf htgt₂)).elim
    · exact H.interior_unique he hf htgt₁ htgt₂
  · exact (H.interior_not_original hf hsrc₂ heleaf.1 (source_eq he hsrc₁)).elim
  · exact (H.interior_not_original he hsrc₁ hfleaf.1 (source_eq hf hsrc₂)).elim
  · exact H.interior_unique he hf hsrc₁ hsrc₂

theorem terminal_exists (H : GraphSubdivision P N) {e : ℕ × ℕ} (he : e ∈ P.edges) :
    ∃ arc ∈ wireEdges (H.wire e), arc.2 = H.original e.2 := by
  have hl := H.wire_laws e he
  have hlast : H.original e.2 ∈ H.wire e := List.mem_of_mem_getLast? (by rw [hl.2.2.2.1]; simp)
  have hheadne : (H.wire e).head? ≠ some (H.original e.2) := by
    intro h
    have hboth : H.original e.2 ∈ (H.wire e).dropLast := wire_head_mem_dropLast hl.1 h
    exact wire_last_not_mem_dropLast hl.2.1 hl.2.2.2.1 hboth
  have htail : H.original e.2 ∈ (H.wire e).tail := by
    cases hw : H.wire e with
    | nil => simp [hw] at hl
    | cons a L =>
      simp only [hw, List.mem_cons] at hlast
      rcases hlast with h | h
      · exact (hheadne (by simp [hw, h])).elim
      · simpa only [hw, List.tail_cons] using h
  obtain ⟨u, hu⟩ := wire_edge_target_exists htail
  exact ⟨(u, H.original e.2), hu, rfl⟩

noncomputable def terminal (H : GraphSubdivision P N) (e : ℕ × ℕ) : ℕ × ℕ :=
  if h : e ∈ P.edges then Classical.choose (H.terminal_exists h) else (0,0)

theorem terminal_spec (H : GraphSubdivision P N) {e : ℕ × ℕ} (he : e ∈ P.edges) :
    H.terminal e ∈ wireEdges (H.wire e) ∧ (H.terminal e).2 = H.original e.2 := by
  classical
  simpa only [terminal, dite_eq_left he] using Classical.choose_spec (H.terminal_exists he)

theorem terminal_injective (H : GraphSubdivision P N) : Set.InjOn H.terminal P.edges := by
  intro e he f hf heq
  apply H.edge_owner_unique he hf (H.terminal_spec he).1
  exact heq ▸ (H.terminal_spec hf).1

theorem original_incoming_owner (H : GraphSubdivision P N) {u : ℕ}
    (hu : u ∈ P.vertices) {arc : ℕ × ℕ} (harc : arc ∈ N.edges)
    (htarget : arc.2 = H.original u) :
    ∃ e ∈ P.edges, e.2 = u ∧ H.terminal e = arc := by
  rw [H.edges_covered] at harc
  obtain ⟨e, he, hwire⟩ := Finset.mem_biUnion.mp harc
  have hlast : (H.wire e).getLast? = some arc.2 := by
    rcases wire_target_cases (H.wire_laws e he).2.1 hwire with h | h
    · exact h
    · exact (H.interior_not_original he h hu htarget).elim
  have he2 := H.original_injective (H.edge_endpoints e he).2 hu
    ((Option.some.inj ((H.wire_laws e he).2.2.2.1.symm.trans hlast)).trans htarget)
  refine ⟨e, he, he2, ?_⟩
  exact wire_incoming_unique (H.wire_laws e he).2.1 (H.terminal_spec he).1 hwire
    ((H.terminal_spec he).2.trans (he2 ▸ htarget.symm))

theorem interior_incoming_eq (H : GraphSubdivision P N) {e : ℕ × ℕ}
    (he : e ∈ P.edges) {v : ℕ} (hv : v ∈ wireInterior (H.wire e)) :
    N.edges.filter (fun f => f.2 = v) = (wireEdges (H.wire e)).filter (fun f => f.2 = v) := by
  classical
  ext arc
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨harc, hatarget⟩
    rw [H.edges_covered] at harc
    obtain ⟨f, hf, hw⟩ := Finset.mem_biUnion.mp harc
    have htarget : v ∈ wireInterior (H.wire f) := by
      rcases wire_target_cases (H.wire_laws f hf).2.1 hw with hlast | hinner
      · have hlast' : arc.2 = H.original f.2 :=
          Option.some.inj (hlast.symm.trans (H.wire_laws f hf).2.2.2.1)
        exact (H.interior_not_original he hv (H.edge_endpoints f hf).2
          (hatarget.symm.trans hlast')).elim
      · exact hatarget ▸ hinner
    have heq := H.interior_unique hf he htarget hv
    exact ⟨heq ▸ hw, hatarget⟩
  · rintro ⟨harc, hatarget⟩
    exact ⟨by rw [H.edges_covered]; exact Finset.mem_biUnion.mpr ⟨e, he, harc⟩, hatarget⟩

theorem interior_incoming_card (H : GraphSubdivision P N) {e : ℕ × ℕ}
    (he : e ∈ P.edges) {v : ℕ} (hv : v ∈ wireInterior (H.wire e)) :
    (N.edges.filter (fun f => f.2 = v)).card = 1 := by
  rw [H.interior_incoming_eq he hv, Realization.incoming_wire_card _ (H.wire_laws e he).2.1]
  have htail : v ∈ (H.wire e).tail := List.mem_of_mem_dropLast (List.mem_toFinset.mp hv)
  exact ite_eq_left htail

theorem interior_incoming_retained (H : GraphSubdivision P N)
    {B : Finset (ℕ × ℕ)} (hB : N.Switching B) {e arc : ℕ × ℕ}
    (he : e ∈ P.edges) (harc : arc ∈ N.edges)
    (hv : arc.2 ∈ wireInterior (H.wire e)) : arc ∈ B := by
  classical
  have hroot : arc.2 ≠ N.root := by
    rw [← H.root_preserved]
    exact H.interior_not_original he hv H.root_left
  have hcB := hB.2 _ (H.interior_mem_vertices he hv) hroot
  have hsub := Finset.filter_subset_filter (fun f : ℕ × ℕ => f.2 = arc.2) hB.1
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcB, H.interior_incoming_card he hv])
  have hm : arc ∈ B.filter (fun f => f.2 = arc.2) := by rw [heq]; exact Finset.mem_filter.mpr ⟨harc, rfl⟩
  exact (Finset.mem_filter.mp hm).1

noncomputable def retained (H : GraphSubdivision P N) (B : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  P.edges.filter (fun e => H.terminal e ∈ B)

theorem original_incoming_card (H : GraphSubdivision P N) {B : Finset (ℕ × ℕ)}
    (hB : B ⊆ N.edges) {u : ℕ} (hu : u ∈ P.vertices) :
    ((H.retained B).filter (fun e => e.2 = u)).card =
      (B.filter (fun arc => arc.2 = H.original u)).card := by
  classical
  apply Finset.card_bij (fun e _ => H.terminal e)
  · intro e he
    obtain ⟨her, he2⟩ := Finset.mem_filter.mp he
    obtain ⟨heP, heB⟩ := Finset.mem_filter.mp her
    exact Finset.mem_filter.mpr ⟨heB, (H.terminal_spec heP).2.trans (congrArg H.original he2)⟩
  · intro e he f hf heq
    exact H.terminal_injective (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
      (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).1 heq
  · intro arc harc
    obtain ⟨heB, he2⟩ := Finset.mem_filter.mp harc
    obtain ⟨e, heP, he2, heq⟩ := H.original_incoming_owner hu (hB heB) he2
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heP, heq ▸ heB⟩, he2⟩, heq⟩

theorem retained_switching (H : GraphSubdivision P N) {B : Finset (ℕ × ℕ)}
    (hB : N.Switching B) : P.Switching (H.retained B) := by
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro u hu hroot
  rw [H.original_incoming_card hB.1 hu]
  apply hB.2 _ (H.original_mem_vertices hu)
  rw [← H.root_preserved]
  exact fun h => hroot (H.original_injective hu H.root_left h)

theorem active_eq_retained (H : GraphSubdivision P N) {B : Finset (ℕ × ℕ)}
    (hB : N.Switching B) : H.active B = H.retained B := by
  classical
  ext e
  simp only [active, retained, Finset.mem_filter]
  constructor
  · rintro ⟨he, hfull⟩
    exact ⟨he, hfull (H.terminal_spec he).1⟩
  · rintro ⟨he, hterm⟩
    refine ⟨he, ?_⟩
    intro arc harc
    rcases wire_target_cases (H.wire_laws e he).2.1 harc with hlast | hinner
    · have heq : H.terminal e = arc := wire_incoming_unique (H.wire_laws e he).2.1
        (H.terminal_spec he).1 harc ((H.terminal_spec he).2.trans
          (Option.some.inj ((H.wire_laws e he).2.2.2.1.symm.trans hlast)))
      exact heq ▸ hterm
    · apply H.interior_incoming_retained hB he ?_ hinner
      rw [H.edges_covered]
      exact Finset.mem_biUnion.mpr ⟨e, he, harc⟩

theorem active_switching (H : GraphSubdivision P N) {B : Finset (ℕ × ℕ)}
    (hB : N.Switching B) : P.Switching (H.active B) := by
  rw [H.active_eq_retained hB]
  exact H.retained_switching hB

end GraphSubdivision
end Camus
