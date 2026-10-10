module

public import Camus.Network.Realization.Support
public import Camus.DP.Packing
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The canonical network of an edge family: degree laws

This file computes the indegree and the outdegree of every vertex of `Realization.graph t E`,
for a family `E` of admissible pairs. The root has indegree `0`. Every other vertex of `T` has
indegree `1`. A vertex of `T` has as many outgoing edges as children in `T`: `0` at a leaf, `2`
at an internal vertex. For `(u, w) ∈ E`, the donor `u′` has indegree `1` and outdegree `2`, and
the recipient `w′` has indegree `2` and outdegree `1`. So the reticulations of the network are
the recipients `w′`, as Definition 3 says of the bottom vertex of `γ(u, w)`. The proofs count
separately the support edges, which lie on the wires (paths without repetition), and the added
edges.

## Main results

* `Realization.graph_root_indegree`: the root has indegree `0`.
* `Realization.graph_indegree_code`: a non-root vertex of `T` has indegree `1`.
* `Realization.graph_outdegree_code`, `Realization.graph_outdegree_leaf`,
  `Realization.graph_outdegree_fork`: the outdegree of a vertex of `T` is its number of
  children, `0` at a leaf and `2` at an internal vertex.
* `Realization.endpoint_degrees`: `u′` has indegree `1` and outdegree `2`; `w′` has indegree `2`
  and outdegree `1`.
-/

@[expose] public section

namespace Camus.Realization

theorem edge_first_mem_dropLast {L : List ℕ} {e : ℕ × ℕ} (he : e ∈ wireEdges L) :
    e.1 ∈ L.dropLast := by
  induction L with
  | nil => simp [wireEdges] at he
  | cons a L ih =>
    cases L with
    | nil => simp [wireEdges] at he
    | cons b L =>
      rw [wireEdges_cons_cons] at he
      rcases Finset.mem_insert.mp he with rfl | he
      · simp
      · exact List.mem_cons_of_mem _ (ih he)

/-- On a path `L` without repetition, one edge of `L` starts at `v` if `v` is in `L` without
its last vertex, and none otherwise. -/
theorem outgoing_wire_card (L : List ℕ) (hL : L.Nodup) (v : ℕ) :
    ((wireEdges L).filter (fun e => e.1 = v)).card = if v ∈ L.dropLast then 1 else 0 := by
  classical
  induction L with
  | nil => simp [wireEdges]
  | cons a L ih =>
    cases L with
    | nil => simp [wireEdges]
    | cons b L =>
      have htail := (List.nodup_cons.mp hL).2
      have ham := (List.nodup_cons.mp hL).1
      rw [wireEdges_cons_cons]
      by_cases hv : v = a
      · subst v
        have hfilter : (wireEdges (b :: L)).filter (fun e => e.1 = a) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro e he heq
          exact ham (heq ▸ edge_first_mem he)
        simp [Finset.filter_insert, hfilter]
      · simp only [Finset.filter_insert, Ne.symm hv, ite_false]
        rw [ih htail]
        simp only [List.dropLast_cons_cons, List.mem_cons, hv, false_or]


theorem mem_dropLast_wire {t : PhyloTree} {E : Finset Pair} {p : Address} {v : ℕ} :
    v ∈ (wire t E p).dropLast ↔
      v = Address.code (parent p) ∨ v ∈ wireInterior (wire t E p) := by
  rw [wireInterior_eq]
  simp only [wire, List.dropLast_append_of_ne_nil (by simp : [Address.code p] ≠ []),
    List.dropLast_singleton, List.append_nil, List.mem_append, List.mem_singleton]
  simp [or_assoc]

theorem wires_edges_disjoint (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {p q : Address}
    (hp : p ∈ t.nodes) (hq : q ∈ t.nodes) (hpq : p ≠ q) :
    Disjoint (wireEdges (wire t E p)) (wireEdges (wire t E q)) := by
  classical
  rw [Finset.disjoint_left]
  intro e he hf
  exact List.disjoint_left.mp (tail_wires_disjoint t E hE hp hq hpq)
    (edge_second_mem_tail he) (edge_second_mem_tail hf)

theorem mem_code_tail_iff {t : PhyloTree} {E : Finset Pair} {p q : Address}
    (hq : q ∈ t.nodes) : Address.code q ∈ (wire t E p).tail ↔ q = p := by
  classical
  rw [mem_tail_wire]
  have hno : Address.code q ∉ wireInterior (wire t E p) := by
    intro h
    exact Finset.disjoint_left.mp (wireInterior_disjoint_original t E p) h
      (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  simp [hno, Address.code_injective.eq_iff]

theorem mem_code_dropLast_iff {t : PhyloTree} {E : Finset Pair} {p q : Address}
    (hq : q ∈ t.nodes) : Address.code q ∈ (wire t E p).dropLast ↔ q = parent p := by
  classical
  rw [mem_dropLast_wire]
  have hno : Address.code q ∉ wireInterior (wire t E p) := by
    intro h
    exact Finset.disjoint_left.mp (wireInterior_disjoint_original t E p) h
      (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  simp [hno, Address.code_injective.eq_iff]

/-- No support edge ends at the root. -/
theorem support_root_incoming_empty (t : PhyloTree) (E : Finset Pair) :
    (supportEdges t E).filter (fun e => e.2 = Address.code []) = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro e he heq
  obtain ⟨p, hp, hwire⟩ := Finset.mem_biUnion.mp he
  have hp' := Finset.mem_erase.mp hp
  have htail : Address.code [] ∈ (wire t E p).tail := heq ▸ edge_second_mem_tail hwire
  exact hp'.1 ((mem_code_tail_iff t.root_mem_nodes).mp htail).symm

theorem added_incoming_code_empty (t : PhyloTree) (E : Finset Pair)
    {p : Address} (hp : p ∈ t.nodes) :
    (E.image (fun e => (donor t e, recipient t e))).filter
      (fun e => e.2 = Address.code p) = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro e he heq
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
  exact recipient_ne_code f hp heq

/-- The root of `Realization.graph t E` has indegree `0`. -/
theorem graph_root_indegree (t : PhyloTree) (E : Finset Pair) :
    (graph t E).indegree (graph t E).root = 0 := by
  classical
  change ((supportEdges t E ∪ E.image (fun e => (donor t e, recipient t e))).filter
    (fun e => e.2 = Address.code [])).card = 0
  rw [Finset.filter_union, support_root_incoming_empty,
    added_incoming_code_empty t E t.root_mem_nodes]
  simp

/-- For a family of admissible pairs, a non-root vertex of `T` has indegree `1` in
`Realization.graph t E`. -/
theorem graph_indegree_code (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ []) :
    (graph t E).indegree (Address.code p) = 1 := by
  classical
  change ((supportEdges t E ∪ E.image (fun e => (donor t e, recipient t e))).filter
    (fun e => e.2 = Address.code p)).card = 1
  rw [Finset.filter_union, added_incoming_code_empty t E hp, Finset.union_empty]
  apply (support_switching t E hE).2
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  · exact fun h => hp0 (Address.code_injective h)

/-- For a family of admissible pairs, the number of support edges starting at a vertex `p` of
`T` is the number of children of `p` in `T`. -/
theorem support_outgoing_code (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {p : Address} (hp : p ∈ t.nodes) :
    ((supportEdges t E).filter (fun e => e.1 = Address.code p)).card =
      ((t.nodes.erase []).filter (fun q => parent q = p)).card := by
  classical
  unfold supportEdges
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  · calc
      _ = ∑ q ∈ t.nodes.erase [], if parent q = p then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [outgoing_wire_card _
          (wire_nodup t E hE (Finset.mem_erase.mp hq).2 (Finset.mem_erase.mp hq).1)]
        simp only [mem_code_dropLast_iff hp, eq_comm]
      _ = _ := by rw [← Finset.sum_filter]; simp
  · intro q hq r hr hqr
    exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
        (wires_edges_disjoint t E hE (Finset.mem_erase.mp hq).2
          (Finset.mem_erase.mp hr).2 hqr))

theorem parent_append_singleton (p : Address) (b : Bool) : parent (p ++ [b]) = p := by
  simp [parent]

/-- The non-root address `q` has parent `p` iff `q` is `p ++ [false]` or `p ++ [true]`. -/
theorem parent_eq_iff {p q : Address} (hq : q ≠ []) :
    parent q = p ↔ q = p ++ [false] ∨ q = p ++ [true] := by
  constructor
  · intro h
    have hqeq : parent q ++ [q.getLast hq] = q := List.take_append_getLast q hq
    rw [h] at hqeq
    cases hb : q.getLast hq
    · exact Or.inl (by simpa [hb] using hqeq.symm)
    · exact Or.inr (by simpa [hb] using hqeq.symm)
  · rintro (rfl | rfl) <;> exact parent_append_singleton _ _

theorem children_filter_leaf {t : PhyloTree} {p : Address} {a : ℕ}
    (hp : t.nodeAt p = some (.leaf a)) :
    (t.nodes.erase []).filter (fun q => parent q = p) = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro q hq hpar
  have hq' := Finset.mem_erase.mp hq
  have hpq : p <+: q := hpar ▸ parent_prefix q
  have heq := PhyloTree.leaf_no_descendant hp hq'.2 hpq
  have hlen : (parent q).length < q.length := by
    have hpos := List.length_pos_iff.mpr hq'.1
    simp only [parent, List.length_take]
    omega
  rw [hpar, heq] at hlen
  omega

theorem children_filter_fork {t l r : PhyloTree} {p : Address}
    (hp : t.nodeAt p = some (.fork l r)) :
    (t.nodes.erase []).filter (fun q => parent q = p) = {p ++ [false], p ++ [true]} := by
  classical
  ext q
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    exact (parent_eq_iff h.1.1).mp h.2
  · rintro (rfl | rfl) <;>
      exact ⟨⟨by simp, PhyloTree.child_mem_nodes hp _⟩, parent_append_singleton _ _⟩

theorem added_outgoing_code_empty (t : PhyloTree) (E : Finset Pair)
    {p : Address} (hp : p ∈ t.nodes) :
    (E.image (fun e => (donor t e, recipient t e))).filter
      (fun e => e.1 = Address.code p) = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro e he heq
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
  exact donor_ne_code f hp heq

/-- For a family of admissible pairs, the outdegree of a vertex `p` of `T` in
`Realization.graph t E` is the number of children of `p` in `T`. -/
theorem graph_outdegree_code (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {p : Address} (hp : p ∈ t.nodes) :
    (graph t E).outdegree (Address.code p) =
      ((t.nodes.erase []).filter (fun q => parent q = p)).card := by
  classical
  change ((supportEdges t E ∪ E.image (fun e => (donor t e, recipient t e))).filter
    (fun e => e.1 = Address.code p)).card = _
  rw [Finset.filter_union, added_outgoing_code_empty t E hp, Finset.union_empty]
  exact support_outgoing_code t E hE hp

/-- For a family of admissible pairs, a leaf of `T` has outdegree `0` in
`Realization.graph t E`. -/
theorem graph_outdegree_leaf {t : PhyloTree} {E : Finset Pair}
    (hE : E ⊆ EdgeAbove.candidates t) {p : Address} {a : ℕ}
    (hp : t.nodeAt p = some (.leaf a)) : (graph t E).outdegree (Address.code p) = 0 := by
  rw [graph_outdegree_code t E hE ((t.mem_nodes_iff p).mpr ⟨_, hp⟩), children_filter_leaf hp]
  rfl

/-- For a family of admissible pairs, an internal vertex of `T` has outdegree `2` in
`Realization.graph t E`. -/
theorem graph_outdegree_fork {t l r : PhyloTree} {E : Finset Pair}
    (hE : E ⊆ EdgeAbove.candidates t) {p : Address}
    (hp : t.nodeAt p = some (.fork l r)) : (graph t E).outdegree (Address.code p) = 2 := by
  classical
  rw [graph_outdegree_code t E hE ((t.mem_nodes_iff p).mpr ⟨_, hp⟩), children_filter_fork hp]
  simp

theorem support_outgoing_eq_wire (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ [])
    {v : ℕ} (hv : v ∈ wireInterior (wire t E p)) :
    (supportEdges t E).filter (fun e => e.1 = v) =
      (wireEdges (wire t E p)).filter (fun e => e.1 = v) := by
  classical
  ext e
  simp only [supportEdges, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_erase]
  constructor
  · rintro ⟨⟨q, hq, he⟩, heq⟩
    have hmem : v ∈ (wire t E q).dropLast := heq ▸ edge_first_mem_dropLast he
    rcases mem_dropLast_wire.mp hmem with hcode | hinterior
    · have hparent := t.nodes_prefix_closed hq.2 (parent_prefix q)
      exact False.elim (Finset.disjoint_left.mp (wireInterior_disjoint_original t E p) hv
        (Finset.mem_image.mpr ⟨parent q, hparent, hcode.symm⟩))
    · have hpq : p = q := by
        by_contra hne
        exact Finset.disjoint_left.mp (interiors_disjoint t E hE hne) hv hinterior
      subst q
      exact ⟨he, heq⟩
  · rintro ⟨he, heq⟩
    exact ⟨⟨p, ⟨hp0, hp⟩, he⟩, heq⟩

/-- For a family of admissible pairs, exactly one support edge starts at a vertex inside a
wire. -/
theorem support_outgoing_interior_card (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ [])
    {v : ℕ} (hv : v ∈ wireInterior (wire t E p)) :
    ((supportEdges t E).filter (fun e => e.1 = v)).card = 1 := by
  rw [support_outgoing_eq_wire t E hE hp hp0 hv,
    outgoing_wire_card _ (wire_nodup t E hE hp hp0)]
  exact ite_eq_left (mem_dropLast_wire.mpr (Or.inr hv))

theorem added_incoming_donor_empty (t : PhyloTree) (E : Finset Pair) (e : Pair) :
    (E.image (fun f => (donor t f, recipient t f))).filter
      (fun f => f.2 = donor t e) = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro f hf hfe
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
  exact donor_ne_recipient t e g hfe.symm

theorem added_outgoing_recipient_empty (t : PhyloTree) (E : Finset Pair) (e : Pair) :
    (E.image (fun f => (donor t f, recipient t f))).filter
      (fun f => f.1 = recipient t e) = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro f hf hfe
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
  exact donor_ne_recipient t g e hfe

theorem added_incoming_recipient_singleton (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {e : Pair} (he : e ∈ E) :
    (E.image (fun f => (donor t f, recipient t f))).filter
      (fun f => f.2 = recipient t e) = {(donor t e, recipient t e)} := by
  classical
  ext f
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hf, hfe⟩
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    have hge := recipient_injective t (hE hg) (hE he) hfe
    subst g
    rfl
  · rintro rfl
    exact ⟨Finset.mem_image.mpr ⟨e, he, rfl⟩, rfl⟩

theorem added_outgoing_donor_singleton (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {e : Pair} (he : e ∈ E) :
    (E.image (fun f => (donor t f, recipient t f))).filter
      (fun f => f.1 = donor t e) = {(donor t e, recipient t e)} := by
  classical
  ext f
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hf, hfe⟩
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    have hge := donor_injective t (hE hg) (hE he) hfe
    subst g
    rfl
  · rintro rfl
    exact ⟨Finset.mem_image.mpr ⟨e, he, rfl⟩, rfl⟩

/-- For `(u, w)` in a family `E` of admissible pairs, in `Realization.graph t E` the donor
`u′` has indegree `1` and outdegree `2` (to the vertex after it on its wire, and to `w′`), and
the recipient `w′` has indegree `2` (from the vertex before it on its wire, and from `u′`) and
outdegree `1`. -/
theorem endpoint_degrees (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {e : Pair} (he : e ∈ E) :
    (graph t E).indegree (donor t e) = 1 ∧
    (graph t E).outdegree (donor t e) = 2 ∧
    (graph t E).indegree (recipient t e) = 2 ∧
    (graph t E).outdegree (recipient t e) = 1 := by
  classical
  have ha := (Finset.mem_filter.mp (hE he)).2
  have hd := (donor_mem_wireInterior_iff hE he).mpr (rfl : e.1 = e.1)
  have hr := (recipient_mem_wireInterior_iff hE he).mpr (rfl : e.2 = e.2)
  have hdin : ((supportEdges t E).filter (fun f => f.2 = donor t e)).card = 1 := by
    rw [support_incoming_eq_wire t E hE ha.1 ha.2.2.1
      (mem_tail_wire.mpr (Or.inl hd)), incoming_wire_card _ (wire_nodup t E hE ha.1 ha.2.2.1)]
    exact ite_eq_left (mem_tail_wire.mpr (Or.inl hd))
  have hrin : ((supportEdges t E).filter (fun f => f.2 = recipient t e)).card = 1 := by
    rw [support_incoming_eq_wire t E hE ha.2.1 ha.2.2.2.1
      (mem_tail_wire.mpr (Or.inl hr)), incoming_wire_card _ (wire_nodup t E hE ha.2.1 ha.2.2.2.1)]
    exact ite_eq_left (mem_tail_wire.mpr (Or.inl hr))
  have hdout := support_outgoing_interior_card t E hE ha.1 ha.2.2.1 hd
  have hrout := support_outgoing_interior_card t E hE ha.2.1 ha.2.2.2.1 hr
  have hn := added_edge_not_support hE he
  unfold RootedNetwork.indegree RootedNetwork.outdegree
  change
    ((supportEdges t E ∪ E.image (fun f => (donor t f, recipient t f))).filter
      (fun f => f.2 = donor t e)).card = 1 ∧
    ((supportEdges t E ∪ E.image (fun f => (donor t f, recipient t f))).filter
      (fun f => f.1 = donor t e)).card = 2 ∧
    ((supportEdges t E ∪ E.image (fun f => (donor t f, recipient t f))).filter
      (fun f => f.2 = recipient t e)).card = 2 ∧
    ((supportEdges t E ∪ E.image (fun f => (donor t f, recipient t f))).filter
      (fun f => f.1 = recipient t e)).card = 1
  simp only [Finset.filter_union, added_incoming_donor_empty, added_outgoing_recipient_empty,
    added_incoming_recipient_singleton t E hE he, added_outgoing_donor_singleton t E hE he,
    Finset.union_empty, hdin, hrout, Finset.union_singleton]
  have hn1 : (donor t e, recipient t e) ∉ (supportEdges t E).filter (fun f => f.1 = donor t e) :=
    fun h => hn (Finset.mem_filter.mp h).1
  have hn2 : (donor t e, recipient t e) ∉ (supportEdges t E).filter (fun f => f.2 = recipient t e)
      :=
    fun h => hn (Finset.mem_filter.mp h).1
  simp [Finset.card_insert_of_notMem hn1, Finset.card_insert_of_notMem hn2, hdout, hrin]

end Camus.Realization
