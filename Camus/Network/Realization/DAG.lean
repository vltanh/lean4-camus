module

public import Camus.Network.Realization.Cones

/-!
# The canonical network of an edge family: acyclicity

This file proves that `Realization.graph t E` has no directed cycle when `E` is cycle-separated
(`Realization.graph_dag`), and that every vertex is reached from the root along support edges
(`Realization.support_reaches`). The support edges form a spanning arborescence: no support
edge ends at the root, exactly one ends at every other vertex (`Realization.support_switching`,
`Realization.support_incoming_unique`), and every vertex is reached from the root, so there is
no directed cycle of support edges (`Realization.support_dag`). A directed cycle of the network
cannot use an added edge `u′ → w′`, since no directed path leads back from `w′` to `u′`
(`Realization.no_return_added_edge`); so it would consist of support edges
(`Realization.cyclic_path_support`).

## Main results

* `Realization.graph_edge_endpoints`: both ends of every edge are vertices of the network.
* `Realization.support_reaches`: every vertex is reached from the root along support edges.
* `Realization.support_incoming_unique`: at most one support edge ends at a given vertex.
* `Realization.graph_dag`: `Realization.graph t E` has no directed cycle.
-/

@[expose] public section

namespace Camus.Realization

/-- For a family of admissible pairs, the vertices of the wire above a non-root vertex of `T`
are vertices of `Realization.graph t E`. -/
theorem wire_mem_vertices {t : PhyloTree} {E : Finset Pair}
    (hE : E ⊆ EdgeAbove.candidates t) {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ [])
    {v : ℕ} (hv : v ∈ wire t E p) : v ∈ (graph t E).vertices := by
  classical
  rw [vertices_covered t E hE]
  rcases mem_wire.mp hv with hparent | hinterior | hlast
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨parent p, t.nodes_prefix_closed hp (parent_prefix p), hparent.symm⟩)
  · exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨p, Finset.mem_erase.mpr ⟨hp0, hp⟩, hinterior⟩)
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, hlast.symm⟩)

/-- For a family of admissible pairs, both ends of a support edge are vertices of
`Realization.graph t E`. -/
theorem support_edge_endpoints (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {u v : ℕ} (he : (u,v) ∈ supportEdges t E) :
    u ∈ (graph t E).vertices ∧ v ∈ (graph t E).vertices := by
  obtain ⟨p, hp, hw⟩ := Finset.mem_biUnion.mp he
  have hp' := Finset.mem_erase.mp hp
  exact ⟨wire_mem_vertices hE hp'.2 hp'.1 (edge_first_mem hw),
    wire_mem_vertices hE hp'.2 hp'.1 (List.mem_of_mem_tail (edge_second_mem_tail hw))⟩

/-- For a family of admissible pairs, both ends of every edge of `Realization.graph t E` are
vertices of it. -/
theorem graph_edge_endpoints (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {u v : ℕ} (he : (u,v) ∈ (graph t E).edges) :
    u ∈ (graph t E).vertices ∧ v ∈ (graph t E).vertices := by
  rcases Finset.mem_union.mp he with hs | ha
  · exact support_edge_endpoints t E hE hs
  · obtain ⟨e, he, hpair⟩ := Finset.mem_image.mp ha
    have hd : u = donor t e := (congrArg Prod.fst hpair).symm
    have hr : v = recipient t e := (congrArg Prod.snd hpair).symm
    constructor
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, by simp [hd]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, by simp [hr]⟩)

/-- Every vertex of the path `a, …` is reached from `a` along the edges of the path. -/
theorem list_wire_reaches (a : ℕ) (L : List ℕ) {v : ℕ} (hv : v ∈ a :: L) :
    Relation.ReflTransGen (fun u v => (u,v) ∈ wireEdges (a :: L)) a v := by
  induction L generalizing a with
  | nil =>
    have h : v = a := List.mem_singleton.mp hv
    subst v
    exact .refl
  | cons b L ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · exact .refl
    · have htail := ih b hv
      have htail' : Relation.ReflTransGen
          (fun u v => (u,v) ∈ wireEdges (a :: b :: L)) b v :=
        Relation.ReflTransGen.mono
          (fun u v he => by rw [wireEdges_cons_cons]; exact Finset.mem_insert_of_mem he) _ _ htail
      exact (Relation.ReflTransGen.single
          (by rw [wireEdges_cons_cons]; exact Finset.mem_insert_self _ _)).trans htail'

/-- Every vertex of the wire above a non-root vertex `p` of `T` is reached from `parent(p)`
along support edges. -/
theorem support_wire_reaches {t : PhyloTree} {E : Finset Pair} {p : Address}
    (hp : p ∈ t.nodes) (hp0 : p ≠ []) {v : ℕ} (hv : v ∈ wire t E p) :
    Relation.ReflTransGen (fun u v => (u,v) ∈ supportEdges t E)
      (Address.code (parent p)) v := by
  have hwire : wire t E p = Address.code (parent p) ::
      (outerEndpoints t E p ++ ghostEndpoints t E p ++ [Address.code p]) := by
    simp [wire, List.append_assoc]
  rw [hwire] at hv
  have hreach := list_wire_reaches _ _ hv
  apply Relation.ReflTransGen.mono (r := fun u v => (u,v) ∈ wireEdges _) ?_ _ _ hreach
  intro u v he
  apply Finset.mem_biUnion.mpr
  exact ⟨p, Finset.mem_erase.mpr ⟨hp0, hp⟩, by simpa only [hwire] using he⟩

/-- Every vertex of `T` is reached from the root along support edges. -/
theorem support_reaches_original (t : PhyloTree) (E : Finset Pair) {p : Address}
    (hp : p ∈ t.nodes) :
    Relation.ReflTransGen (fun u v => (u,v) ∈ supportEdges t E)
      (Address.code []) (Address.code p) := by
  have hall : ∀ n, ∀ p : Address, p.length = n → p ∈ t.nodes →
      Relation.ReflTransGen (fun u v => (u,v) ∈ supportEdges t E)
        (Address.code []) (Address.code p) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hlen hp
      by_cases hp0 : p = []
      · subst p
        exact .refl
      · have hparent := t.nodes_prefix_closed hp (parent_prefix p)
        have hplen : (parent p).length < n := by
          have hpos := List.length_pos_iff.mpr hp0
          simp only [parent, List.length_take]
          omega
        have hr := ih _ hplen (parent p) rfl hparent
        exact hr.trans (support_wire_reaches hp hp0 (mem_wire.mpr (Or.inr (Or.inr rfl))))
  exact hall p.length p rfl hp

/-- For a family of admissible pairs, every vertex of `Realization.graph t E` is reached from
the root along support edges. -/
theorem support_reaches (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {v : ℕ} (hv : v ∈ (graph t E).vertices) :
    Relation.ReflTransGen (fun u v => (u,v) ∈ supportEdges t E)
      (graph t E).root v := by
  rw [vertices_covered t E hE] at hv
  rcases Finset.mem_union.mp hv with horiginal | hinterior
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp horiginal
    exact support_reaches_original t E hp
  · obtain ⟨p, hp, hv⟩ := Finset.mem_biUnion.mp hinterior
    have hp' := Finset.mem_erase.mp hp
    exact (support_reaches_original t E (t.nodes_prefix_closed hp'.2 (parent_prefix p))).trans
      (support_wire_reaches hp'.2 hp'.1 (mem_wire.mpr (Or.inr (Or.inl hv))))

/-- For a family of admissible pairs, at most one support edge ends at a given vertex. -/
theorem support_incoming_unique (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) {u v w : ℕ}
    (hu : (u,v) ∈ supportEdges t E) (hw : (w,v) ∈ supportEdges t E) : u = w := by
  classical
  by_cases hv : v = Address.code []
  · have he : (u,Address.code []) ∈
        (supportEdges t E).filter (fun e => e.2 = Address.code []) :=
      Finset.mem_filter.mpr ⟨by simpa [hv] using hu, rfl⟩
    rw [support_root_incoming_empty] at he
    exact False.elim (Finset.notMem_empty _ he)
  · have hvmem := (support_edge_endpoints t E hE hu).2
    have hcard := (support_switching t E hE).2 v hvmem hv
    have heq := Finset.card_le_one.mp (by omega :
        ((supportEdges t E).filter (fun e => e.2 = v)).card ≤ 1)
      (u,v) (Finset.mem_filter.mpr ⟨hu,rfl⟩)
      (w,v) (Finset.mem_filter.mpr ⟨hw,rfl⟩)
    exact congrArg Prod.fst heq

/-- For a family of admissible pairs, there is no directed cycle of support edges. A directed
cycle through `v` also passes through the start of the only support edge ending at `v`; going
back along a path from the root, it would pass through the root, where no support edge ends. -/
theorem support_dag (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) (v : ℕ) :
    ¬Relation.TransGen (fun u v => (u,v) ∈ supportEdges t E) v v := by
  intro hloop
  obtain ⟨w, hback, hw⟩ := Relation.TransGen.tail'_iff.mp hloop
  have hv := (support_edge_endpoints t E hE hw).2
  have hroot := support_reaches t E hE hv
  have hacyclic : ∀ {v}, Relation.ReflTransGen (fun u v => (u,v) ∈ supportEdges t E)
      (Address.code []) v → ¬Relation.TransGen (fun u v => (u,v) ∈ supportEdges t E) v v := by
    intro v hreach
    induction hreach with
    | refl =>
      intro hloop
      obtain ⟨w, hback, hw⟩ := Relation.TransGen.tail'_iff.mp hloop
      have he : (w,Address.code []) ∈
          (supportEdges t E).filter (fun e => e.2 = Address.code []) :=
        Finset.mem_filter.mpr ⟨hw,rfl⟩
      rw [support_root_incoming_empty] at he
      exact Finset.notMem_empty _ he
    | @tail u v hreach huv ih =>
      intro hloop
      obtain ⟨w, hback, hw⟩ := Relation.TransGen.tail'_iff.mp hloop
      have heq := support_incoming_unique t E hE huv hw
      subst w
      exact ih (Relation.TransGen.head' huv hback)
  exact hacyclic hroot hloop

/-- For a cycle-separated family `E`, every edge of a closed directed walk of
`Realization.graph t E` is a support edge, since an added edge `u′ → w′` lies on no closed
directed walk (`Realization.no_return_added_edge`). Stated for a nonempty directed path from `u`
to `v` followed by a directed path from `v` back to `u`. -/
theorem cyclic_path_support {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {u v : ℕ}
    (hpath : Relation.TransGen (fun u v => (u,v) ∈ (graph t E).edges) u v)
    (hback : Relation.ReflTransGen (fun u v => (u,v) ∈ (graph t E).edges) v u) :
    Relation.TransGen (fun u v => (u,v) ∈ supportEdges t E) u v := by
  have hedge : ∀ {a b}, (a,b) ∈ (graph t E).edges →
      Relation.ReflTransGen (fun u v => (u,v) ∈ (graph t E).edges) b a →
      (a,b) ∈ supportEdges t E := by
    intro a b hab hba
    rcases Finset.mem_union.mp hab with hs | ha
    · exact hs
    · obtain ⟨e, he, hpair⟩ := Finset.mem_image.mp ha
      have hu : a = donor t e := (congrArg Prod.fst hpair).symm
      have hv : b = recipient t e := (congrArg Prod.snd hpair).symm
      exact False.elim (no_return_added_edge hE he (by simpa [hu,hv] using hba))
  induction hpath with
  | single h => exact .single (hedge h hback)
  | @tail w v hpath hwv ih =>
    have hbw := hback.trans hpath.to_reflTransGen
    have hsupport := hedge hwv hbw
    have hwu := (Relation.ReflTransGen.single hwv).trans hback
    exact (ih hwu).tail hsupport

/-- For a cycle-separated family `E`, `Realization.graph t E` has no directed cycle. -/
theorem graph_dag (t : PhyloTree) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) (v : ℕ) :
    ¬Relation.TransGen (fun u v => (u,v) ∈ (graph t E).edges) v v := by
  intro hloop
  exact support_dag t E hE.1 v (cyclic_path_support hE hloop .refl)

end Camus.Realization
