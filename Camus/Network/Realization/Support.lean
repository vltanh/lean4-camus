module

public import Camus.Network.Realization.Wires

/-!
# The canonical network of an edge family: the support switching

The support edges `Realization.supportEdges t E` of `Realization.graph t E` are the edges of all
wires; they form the subdivision of `T` inside the network, its support. For a family of
admissible pairs, this file proves that the support edges form a switching of the network
(`RootedNetwork.Switching`: exactly one support edge ends at each non-root vertex, as when
Definition 1 deletes one incoming edge of each reticulation), and that the other edges of the
network are the added edges `u′ → w′`. It also proves that in any support subdivision the anchor
of a vertex inside the wire above `p` is `p`.

## Main results

* `Realization.support_switching`: the support edges form a switching of the network.
* `Realization.added_edge_not_support`: the added edge `u′ → w′` is not a support edge.
* `Realization.nonSupportEdges`: the edges outside the support are the added edges.
* `SupportSubdivision.anchor_eq`: the anchor of a vertex inside the wire above `p` is `p`.
-/

@[expose] public section

namespace Camus.Realization

/-- The edges of the path `a, b, …` are `a → b` and the edges of the path `b, …`. -/
theorem wireEdges_cons_cons (a b : ℕ) (L : List ℕ) :
    wireEdges (a :: b :: L) = insert (a,b) (wireEdges (b :: L)) := by
  simp [wireEdges]

/-- The end of an edge of the path `L` is in the tail of `L`. -/
theorem edge_second_mem_tail {L : List ℕ} {e : ℕ × ℕ} (he : e ∈ wireEdges L) :
    e.2 ∈ L.tail := by
  exact (List.of_mem_zip (List.mem_toFinset.mp he)).2

/-- The start of an edge of the path `L` is a vertex of `L`. -/
theorem edge_first_mem {L : List ℕ} {e : ℕ × ℕ} (he : e ∈ wireEdges L) :
    e.1 ∈ L := by
  exact (List.of_mem_zip (List.mem_toFinset.mp he)).1

/-- On a path `L` without repetition, one edge of `L` ends at `v` if `v` is in the tail of
`L`, and none otherwise. -/
theorem incoming_wire_card (L : List ℕ) (hL : L.Nodup) (v : ℕ) :
    ((wireEdges L).filter (fun e => e.2 = v)).card = if v ∈ L.tail then 1 else 0 := by
  classical
  induction L with
  | nil => simp [wireEdges]
  | cons a L ih =>
    cases L with
    | nil => simp [wireEdges]
    | cons b L =>
      have htail := (List.nodup_cons.mp hL).2
      have hbm := (List.nodup_cons.mp htail).1
      rw [wireEdges_cons_cons]
      by_cases hv : v = b
      · subst v
        have hfilter : (wireEdges (b :: L)).filter (fun e => e.2 = b) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro e he heq
          exact hbm (heq ▸ edge_second_mem_tail he)
        simp [Finset.filter_insert, hfilter]
      · simp only [Finset.filter_insert, Ne.symm hv, ite_false]
        rw [ih htail]
        simp only [List.tail_cons, List.mem_cons, hv, false_or]
        rfl

/-- The vertices of the wire above `p`, its first vertex `parent(p)` excepted, are the
vertices inside it and `p`. -/
theorem mem_tail_wire {t : PhyloTree} {E : Finset Pair} {p : Address} {v : ℕ} :
    v ∈ (wire t E p).tail ↔ v ∈ wireInterior (wire t E p) ∨ v = Address.code p := by
  rw [wireInterior_eq]
  simp [wire, List.append_assoc, or_assoc]

/-- For a family of admissible pairs and distinct vertices `p ≠ q` of `T`, the wires above
`p` and above `q`, each without its first vertex, are disjoint. -/
theorem tail_wires_disjoint (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {p q : Address}
    (hp : p ∈ t.nodes) (hq : q ∈ t.nodes) (hpq : p ≠ q) :
    List.Disjoint (wire t E p).tail (wire t E q).tail := by
  classical
  rw [List.disjoint_left]
  intro v hv hw
  rcases mem_tail_wire.mp hv with hi | hc <;> rcases mem_tail_wire.mp hw with hi' | hc'
  · exact Finset.disjoint_left.mp (interiors_disjoint t E hE hpq) hi hi'
  · exact Finset.disjoint_left.mp (wireInterior_disjoint_original t E p) hi
      (Finset.mem_image.mpr ⟨q, hq, hc'.symm⟩)
  · exact Finset.disjoint_left.mp (wireInterior_disjoint_original t E q) hi'
      (Finset.mem_image.mpr ⟨p, hp, hc.symm⟩)
  · exact hpq (Address.code_injective (hc.symm.trans hc'))

/-- For a family of admissible pairs, if `v` lies on the wire above a non-root vertex `p` of `T`
and is not its first vertex, the support edges ending at `v` are the edges of this wire ending
at `v`. -/
theorem support_incoming_eq_wire (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ [])
    {v : ℕ} (hv : v ∈ (wire t E p).tail) :
    (supportEdges t E).filter (fun e => e.2 = v) =
      (wireEdges (wire t E p)).filter (fun e => e.2 = v) := by
  classical
  ext e
  simp only [supportEdges, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_erase]
  constructor
  · rintro ⟨⟨q, hq, he⟩, heq⟩
    have hmem : v ∈ (wire t E q).tail := heq ▸ edge_second_mem_tail he
    have hpq : p = q := by
      by_contra hne
      exact List.disjoint_left.mp (tail_wires_disjoint t E hE hp hq.2 hne) hv hmem
    subst q
    exact ⟨he, heq⟩
  · rintro ⟨he, heq⟩
    exact ⟨⟨p, ⟨hp0, hp⟩, he⟩, heq⟩

/-- For a family of admissible pairs, the support edges form a switching of
`Realization.graph t E`: exactly one support edge ends at each non-root vertex. -/
theorem support_switching (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) :
    (graph t E).Switching (supportEdges t E) := by
  classical
  constructor
  · exact Finset.subset_union_left
  · intro v hv hvroot
    have hcover := vertices_covered t E hE
    rw [hcover] at hv
    have hwire : ∃ p ∈ t.nodes, p ≠ [] ∧ v ∈ (wire t E p).tail := by
      rcases Finset.mem_union.mp hv with horiginal | hinterior
      · obtain ⟨p, hp, hcode⟩ := Finset.mem_image.mp horiginal
        have hp0 : p ≠ [] := by
          intro h
          subst p
          exact hvroot hcode.symm
        exact ⟨p, hp, hp0, mem_tail_wire.mpr (Or.inr hcode.symm)⟩
      · obtain ⟨p, hp, hv⟩ := Finset.mem_biUnion.mp hinterior
        have hp' := Finset.mem_erase.mp hp
        exact ⟨p, hp'.2, hp'.1, mem_tail_wire.mpr (Or.inl hv)⟩
    obtain ⟨p, hp, hp0, hv⟩ := hwire
    rw [support_incoming_eq_wire t E hE hp hp0 hv]
    exact (incoming_wire_card _ (wire_nodup t E hE hp hp0) v).trans (ite_eq_left hv)

/-- For `(u, w)` in a family of admissible pairs, the added edge `u′ → w′` is not a support
edge: `u′` and `w′` are inside the wires above `u` and above `w`, and `u ≠ w`. -/
theorem added_edge_not_support {t : PhyloTree} {E : Finset Pair}
    (hE : E ⊆ EdgeAbove.candidates t) {e : Pair} (he : e ∈ E) :
    (donor t e, recipient t e) ∉ supportEdges t E := by
  classical
  intro h
  obtain ⟨p, hp, hpedge⟩ := Finset.mem_biUnion.mp h
  have hp' := Finset.mem_erase.mp hp
  have hparent : parent p ∈ t.nodes := t.nodes_prefix_closed hp'.2 (parent_prefix p)
  have hd : donor t e ∈ wireInterior (wire t E p) := by
    have hv := edge_first_mem hpedge
    rcases mem_wire.mp hv with hroot | hinner | hlast
    · exact False.elim (donor_ne_code e hparent hroot)
    · exact hinner
    · exact False.elim (donor_ne_code e hp'.2 hlast)
  have hr : recipient t e ∈ wireInterior (wire t E p) := by
    have hv := edge_second_mem_tail hpedge
    rcases mem_tail_wire.mp hv with hinner | hlast
    · exact hinner
    · exact False.elim (recipient_ne_code e hp'.2 hlast)
  have hu := donor_mem_wireInterior_iff hE he |>.mp hd
  have hw := recipient_mem_wireInterior_iff hE he |>.mp hr
  have ha := (Finset.mem_filter.mp (hE he)).2
  exact ha.2.2.2.2 ((hw.trans hu.symm) ▸ List.prefix_refl e.1)

/-- For a family of admissible pairs, the edges of `Realization.graph t E` outside the support
are the added edges `u′ → w′`, `(u, w) ∈ E`. -/
theorem nonSupportEdges (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) :
    (graph t E).edges \ supportEdges t E = E.image (fun e => (donor t e, recipient t e)) := by
  classical
  ext e
  simp only [graph, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hs | he, hn⟩
    · exact False.elim (hn hs)
    · exact he
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact ⟨Or.inr (Finset.mem_image.mpr ⟨f, hf, rfl⟩), added_edge_not_support hE hf⟩

end Camus.Realization

namespace Camus.SupportSubdivision

/-- In a support subdivision `H` of `T` in `N`, the anchor of a vertex inside the wire above a
non-root vertex `p` of `T` is `p`. -/
theorem anchor_eq {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}
    (H : SupportSubdivision t N S) {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ [])
    {v : ℕ} (hv : v ∈ wireInterior (H.wire p)) : H.anchor v = p := by
  classical
  have hex : ∃ p ∈ t.nodes, p ≠ [] ∧ v ∈ wireInterior (H.wire p) :=
    ⟨p, hp, hp0, hv⟩
  unfold anchor
  simp only [dite_eq_left hex]
  obtain ⟨hq, hq0, hqv⟩ := hex.choose_spec
  by_contra hne
  exact Finset.disjoint_left.mp
    (H.interiors_disjoint (Finset.mem_erase.mpr ⟨hq0, hq⟩)
      (Finset.mem_erase.mpr ⟨hp0, hp⟩) hne) hqv hv

end Camus.SupportSubdivision
