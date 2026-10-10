module

public import Camus.Network.Completeness.Cycles
public import Mathlib.Data.List.Nodup

/-!
# Wires of a support subdivision

The wire `H.wire p` of a non-root vertex `p` of `T` is the directed path of `N` that subdivides
the edge of `T` above `p`, from `H.original (parent p)` to `H.original p`. A list `l` is read as
a path: `wireEdges l` are its consecutive pairs, and `wireInterior l` its vertices other than the
first and the last. This file proves the list facts used throughout the completeness proof and
the basic properties of the wires of `H`: their edges lie in the switching `S`, their vertices in
`N`, two wires with their first vertices removed are disjoint, and a vertex inside a wire has one
outgoing switching edge.

## Main results

* `wire_vertex_cases`: a vertex of a wire is its first vertex, its last vertex, or inside it.
* `SupportSubdivision.wire_edge_mem_support`: the edges of a wire are switching edges.
* `SupportSubdivision.tail_wires_disjoint`: the wires of distinct vertices, their first vertices
  removed, are disjoint.
* `SupportSubdivision.interior_outdegree_support`: a vertex inside a wire has outdegree one in
  `S`.
-/

@[expose] public section

namespace Camus

/-- The tails of the edges of a wire `l`, in order, form `l` without its last vertex. -/
theorem wire_edges_map_fst (l : List ℕ) :
    (l.zip l.tail).map Prod.fst = l.dropLast := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases l with
    | nil => rfl
    | cons y l =>
      simpa only [List.tail_cons, List.zip_cons_cons, List.map_cons,
        List.dropLast_cons_cons] using congrArg (List.cons x) ih

/-- The heads of the edges of a wire `l`, in order, form `l` without its first vertex. -/
theorem wire_edges_map_snd (l : List ℕ) :
    (l.zip l.tail).map Prod.snd = l.tail :=
  List.map_snd_zip (by simp)

/-- The tail of an edge of a wire `l` lies in `l.dropLast`. -/
theorem wire_edge_source_mem {l : List ℕ} {e : ℕ × ℕ} (he : e ∈ wireEdges l) :
    e.1 ∈ l.dropLast := by
  rw [← wire_edges_map_fst]
  exact List.mem_map.mpr ⟨e, List.mem_toFinset.mp he, rfl⟩

/-- The head of an edge of a wire `l` lies in `l.tail`. -/
theorem wire_edge_target_mem {l : List ℕ} {e : ℕ × ℕ} (he : e ∈ wireEdges l) :
    e.2 ∈ l.tail := by
  rw [← wire_edges_map_snd]
  exact List.mem_map.mpr ⟨e, List.mem_toFinset.mp he, rfl⟩

/-- Every vertex of `l.dropLast` is the tail of an edge of the wire `l`. -/
theorem wire_edge_source_exists {l : List ℕ} {v : ℕ} (hv : v ∈ l.dropLast) :
    ∃ w, (v,w) ∈ wireEdges l := by
  rw [← wire_edges_map_fst] at hv
  obtain ⟨e, he, hv⟩ := List.mem_map.mp hv
  refine ⟨e.2, ?_⟩
  subst v
  exact List.mem_toFinset.mpr he

/-- Every vertex of `l.tail` is the head of an edge of the wire `l`. -/
theorem wire_edge_target_exists {l : List ℕ} {v : ℕ} (hv : v ∈ l.tail) :
    ∃ u, (u,v) ∈ wireEdges l := by
  rw [← wire_edges_map_snd] at hv
  obtain ⟨e, he, hv⟩ := List.mem_map.mp hv
  refine ⟨e.1, ?_⟩
  subst v
  exact List.mem_toFinset.mpr he

/-- In a wire without repeated vertices, a vertex is the tail of at most one edge. -/
theorem wire_outgoing_unique {l : List ℕ} (hl : l.Nodup) {e f : ℕ × ℕ}
    (he : e ∈ wireEdges l) (hf : f ∈ wireEdges l) (hv : e.1 = f.1) : e = f := by
  have hm : ((l.zip l.tail).map Prod.fst).Nodup := by
    rw [wire_edges_map_fst]
    exact hl.sublist (List.dropLast_sublist _)
  exact List.inj_on_of_nodup_map hm (List.mem_toFinset.mp he)
    (List.mem_toFinset.mp hf) hv

/-- In a wire without repeated vertices, a vertex is the head of at most one edge. -/
theorem wire_incoming_unique {l : List ℕ} (hl : l.Nodup) {e f : ℕ × ℕ}
    (he : e ∈ wireEdges l) (hf : f ∈ wireEdges l) (hv : e.2 = f.2) : e = f := by
  have hm : ((l.zip l.tail).map Prod.snd).Nodup := by
    rw [wire_edges_map_snd]
    exact hl.tail
  exact List.inj_on_of_nodup_map hm (List.mem_toFinset.mp he)
    (List.mem_toFinset.mp hf) hv

/-- A vertex of a wire is its first vertex, its last vertex, or an interior vertex. -/
theorem wire_vertex_cases {l : List ℕ} {v : ℕ} (hv : v ∈ l) :
    l.head? = some v ∨ l.getLast? = some v ∨ v ∈ wireInterior l := by
  classical
  cases l with
  | nil => simp at hv
  | cons a l =>
    rcases List.mem_cons.mp hv with h | hv
    · subst v
      exact Or.inl rfl
    · cases l with
      | nil => simp at hv
      | cons b l =>
        by_cases hlast : (b :: l).getLast? = some v
        · exact Or.inr (Or.inl (by simpa using hlast))
        · apply Or.inr ∘ Or.inr
          apply List.mem_toFinset.mpr
          apply List.mem_dropLast_of_mem_of_ne_getLast? hv
          exact Ne.symm hlast

/-- An interior vertex of `l` lies in `l.dropLast`. -/
theorem wire_interior_mem_dropLast {l : List ℕ} {v : ℕ}
    (hv : v ∈ wireInterior l) : v ∈ l.dropLast := by
  cases l with
  | nil => simp [wireInterior] at hv
  | cons a l =>
    cases l with
    | nil => simp [wireInterior] at hv
    | cons b l =>
      exact List.mem_cons_of_mem a (List.mem_toFinset.mp hv)

/-- In a wire without repeated vertices, the first vertex does not occur again. -/
theorem wire_head_not_mem_tail {l : List ℕ} (hl : l.Nodup) {v : ℕ}
    (hv : l.head? = some v) : v ∉ l.tail := by
  cases l with
  | nil => simp at hv
  | cons a l =>
    simp only [List.head?_cons, Option.some.injEq] at hv
    subst v
    exact (List.nodup_cons.mp hl).1

/-- In a wire with at least two vertices, the first vertex lies in `l.dropLast`. -/
theorem wire_head_mem_dropLast {l : List ℕ} (hlen : 2 ≤ l.length) {v : ℕ}
    (hv : l.head? = some v) : v ∈ l.dropLast := by
  cases l with
  | nil => simp at hlen
  | cons a l =>
    cases l with
    | nil => simp at hlen
    | cons b l =>
      simp only [List.head?_cons, Option.some.injEq] at hv
      subst v
      simp

namespace SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- The edges of the wire of a non-root vertex of `T` are switching edges. -/
theorem wire_edge_mem_support (H : SupportSubdivision t N S) {p : Address}
    (hp : p ∈ t.nodes) (hp0 : p ≠ []) {e : ℕ × ℕ}
    (he : e ∈ wireEdges (H.wire p)) : e ∈ S := by
  classical
  rw [H.edges_covered]
  exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_erase.mpr ⟨hp0,hp⟩, he⟩

/-- The vertices of the wire of a non-root vertex of `T` are vertices of `N`. -/
theorem wire_mem_vertices (H : SupportSubdivision t N S) {p : Address}
    (hp : p ∈ t.nodes) (hp0 : p ≠ []) {v : ℕ} (hv : v ∈ H.wire p) :
    v ∈ N.vertices := by
  rcases wire_vertex_cases hv with hhead | hlast | hinner
  · have heq : H.original (parent p) = v :=
      Option.some.inj ((H.wire_laws p hp hp0).2.2.1.symm.trans hhead)
    rw [← heq]
    exact H.original_mem_vertices
      (t.nodes_prefix_closed hp (parent_prefix p))
  · have heq : H.original p = v :=
      Option.some.inj ((H.wire_laws p hp hp0).2.2.2.1.symm.trans hlast)
    rw [← heq]
    exact H.original_mem_vertices hp
  · exact H.interior_mem_vertices hp hp0 hinner

/-- A vertex of the wire of `p` that is not an original vertex lies inside the wire. -/
theorem interior_of_mem_wire_not_original (H : SupportSubdivision t N S)
    {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ []) {v : ℕ}
    (hv : v ∈ H.wire p) (hno : v ∉ t.nodes.image H.original) :
    v ∈ wireInterior (H.wire p) := by
  classical
  rcases wire_vertex_cases hv with hhead | hlast | hinner
  · have heq : H.original (parent p) = v :=
      Option.some.inj ((H.wire_laws p hp hp0).2.2.1.symm.trans hhead)
    exact False.elim (hno (Finset.mem_image.mpr
      ⟨parent p, t.nodes_prefix_closed hp (parent_prefix p), heq⟩))
  · have heq : H.original p = v :=
      Option.some.inj ((H.wire_laws p hp hp0).2.2.2.1.symm.trans hlast)
    exact False.elim (hno (Finset.mem_image.mpr ⟨p,hp,heq⟩))
  · exact hinner

/-- A vertex of the wire of `p` other than the first lies inside the wire or is `H.original p`. -/
theorem tail_wire_cases (H : SupportSubdivision t N S) {p : Address}
    (hp : p ∈ t.nodes) (hp0 : p ≠ []) {v : ℕ} (hv : v ∈ (H.wire p).tail) :
    v ∈ wireInterior (H.wire p) ∨ v = H.original p := by
  rcases wire_vertex_cases (List.mem_of_mem_tail hv) with hhead | hlast | hinner
  · exact False.elim (wire_head_not_mem_tail (H.wire_laws p hp hp0).2.1 hhead hv)
  · exact Or.inr (Option.some.inj (hlast.symm.trans (H.wire_laws p hp hp0).2.2.2.1))
  · exact Or.inl hinner

/-- The wires of distinct non-root vertices `p ≠ q`, their first vertices removed, are
disjoint. -/
theorem tail_wires_disjoint (H : SupportSubdivision t N S) {p q : Address}
    (hp : p ∈ t.nodes) (hp0 : p ≠ []) (hq : q ∈ t.nodes) (hq0 : q ≠ [])
    (hpq : p ≠ q) : List.Disjoint (H.wire p).tail (H.wire q).tail := by
  classical
  rw [List.disjoint_left]
  intro v hvp hvq
  rcases H.tail_wire_cases hp hp0 hvp with hi | ho <;>
    rcases H.tail_wire_cases hq hq0 hvq with hi' | ho'
  · exact hpq (H.interior_unique hp hp0 hq hq0 hi hi')
  · exact H.interior_not_original hp hp0 hi
      (Finset.mem_image.mpr ⟨q,hq,ho'.symm⟩)
  · exact H.interior_not_original hq hq0 hi'
      (Finset.mem_image.mpr ⟨p,hp,ho.symm⟩)
  · exact hpq (H.original_injective hp hq (ho.symm.trans ho'))

/-- The wire of `p` leaves `H.original (parent p)` by a switching edge to one of its later
vertices. -/
theorem wire_head_outgoing_exists (H : SupportSubdivision t N S) {p : Address}
    (hp : p ∈ t.nodes) (hp0 : p ≠ []) :
    ∃ v, (H.original (parent p),v) ∈ S ∧ v ∈ (H.wire p).tail := by
  have hw := H.wire_laws p hp hp0
  obtain ⟨v,he⟩ := wire_edge_source_exists (wire_head_mem_dropLast hw.1 hw.2.2.1)
  exact ⟨v,H.wire_edge_mem_support hp hp0 he,wire_edge_target_mem he⟩

/-- A vertex inside a wire is the tail of at most one switching edge. -/
theorem interior_outgoing_unique (H : SupportSubdivision t N S)
    {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ []) {v : ℕ}
    (hv : v ∈ wireInterior (H.wire p)) {e f : ℕ × ℕ}
    (he : e ∈ S) (hf : f ∈ S) (hev : e.1 = v) (hfv : f.1 = v) : e = f := by
  classical
  have hno := H.interior_not_original hp hp0 hv
  rw [H.edges_covered] at he hf
  obtain ⟨q, hq, heq⟩ := Finset.mem_biUnion.mp he
  obtain ⟨r, hr, hfr⟩ := Finset.mem_biUnion.mp hf
  obtain ⟨hq0,hq⟩ := Finset.mem_erase.mp hq
  obtain ⟨hr0,hr⟩ := Finset.mem_erase.mp hr
  have hvq : v ∈ wireInterior (H.wire q) :=
    H.interior_of_mem_wire_not_original hq hq0
      (hev ▸ List.mem_of_mem_dropLast (wire_edge_source_mem heq)) hno
  have hvr : v ∈ wireInterior (H.wire r) :=
    H.interior_of_mem_wire_not_original hr hr0
      (hfv ▸ List.mem_of_mem_dropLast (wire_edge_source_mem hfr)) hno
  have hqp := H.interior_unique hq hq0 hp hp0 hvq hv
  have hrp := H.interior_unique hr hr0 hp hp0 hvr hv
  subst q r
  exact wire_outgoing_unique (H.wire_laws p hp hp0).2.1 heq hfr
    (hev.trans hfv.symm)

/-- A vertex inside a wire has outdegree one in the switching `S`. -/
theorem interior_outdegree_support (H : SupportSubdivision t N S)
    {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ []) {v : ℕ}
    (hv : v ∈ wireInterior (H.wire p)) :
    ({N with edges := S}).outdegree v = 1 := by
  classical
  obtain ⟨w, he⟩ := wire_edge_source_exists (wire_interior_mem_dropLast hv)
  apply Finset.card_eq_one_iff_existsUnique.mpr
  refine ⟨(v,w), Finset.mem_filter.mpr
    ⟨H.wire_edge_mem_support hp hp0 he, rfl⟩, ?_⟩
  intro f hf
  obtain ⟨hf, hfv⟩ := Finset.mem_filter.mp hf
  exact H.interior_outgoing_unique hp hp0 hv hf
    (H.wire_edge_mem_support hp hp0 he) hfv rfl

end SupportSubdivision
end Camus
