module

public import Camus.Network.Realization.Degrees

/-!
# The canonical network of an edge family: reachability cones

For `(u, w)` in a cycle-separated family `E`, no directed path of `Realization.graph t E` leads
from `w′` back to `u′` (`Realization.no_return_added_edge`). This is the key step of acyclicity
(`Realization.graph_dag`). The cone below a vertex `p` of `T` (`Realization.Below`) consists of
the vertices of the subtree `T_p` and the fresh vertices on the edges above them, the edge above
`p` included. The cone below `w` is closed under the edges of the network
(`Realization.recipient_cone_closed`). Wire edges stay in it. An added edge `u₁′ → w₁′` with
`u₁` in `T_w` has `w₁` in `T_w` as well (`Realization.recipient_cone_closed_pairs`): otherwise
`lca(u₁, w₁)` is a strict ancestor of `w`, and `parent(w)`, which lies on `γ(u, w)`, lies on the
path from `lca(u₁, w₁)` to `u₁`, hence on `γ(u₁, w₁)`, against cycle separation. The cone below
`w` contains `w′` but not `u′`, since `w` is not an ancestor of `u`.

## Main results

* `Realization.Below`: the cone below a vertex of `T`.
* `Realization.recipient_cone_closed_pairs`: an added edge whose donor end is in `T_w` has its
  recipient end in `T_w`.
* `Realization.recipient_cone_closed_reachable`: the cone below `w` is closed under directed
  paths.
* `Realization.no_return_added_edge`: no directed path leads from `w′` to `u′`.
-/

@[expose] public section

namespace Camus.Realization

/-- A non-root address is not its own parent. -/
theorem parent_ne_self {p : Address} (hp : p ≠ []) : parent p ≠ p := by
  intro h
  have hpos := List.length_pos_iff.mpr hp
  have hlen := congrArg List.length h
  simp only [parent, List.length_take] at hlen
  omega

/-- For an admissible pair `(u, w)`, `parent(w)` is in the footprint of `(u, w)`: it is a
vertex of `γ(u, w)`. -/
theorem recipient_parent_mem_footprint {t : PhyloTree} {e : Pair}
    (he : EdgeAbove.Admissible t e) : parent e.2 ∈ EdgeAbove.footprint t e := by
  have hprefix := lca_prefix_right e.1 e.2
  have hne : EdgeAbove.target e ≠ e.2 := by
    intro h
    exact he.2.2.2.2 ((lca_eq_right_iff _ _).mp h)
  exact Finset.mem_filter.mpr
    ⟨t.nodes_prefix_closed he.2.1 (parent_prefix e.2),
      prefix_parent_of_ne hprefix hne,
      Or.inr ⟨parent_prefix _, parent_ne_self he.2.2.2.1⟩⟩

/-- Let `e = (u, w)` and `f = (u₁, w₁)` be pairs of a cycle-separated family. If `u₁` is in
the subtree `T_w`, so is `w₁`. Otherwise `lca(u₁, w₁)` is a strict ancestor of `w`, and
`parent(w)` lies on the path from `lca(u₁, w₁)` to `u₁`, so it is in the footprints of both
pairs. Cycle separation then gives `e = f`, and `w` would be an ancestor of `u`. -/
theorem recipient_cone_closed_pairs {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e f : Pair} (he : e ∈ E) (hf : f ∈ E)
    (hinside : e.2 <+: f.1) : e.2 <+: f.2 := by
  have hae := (Finset.mem_filter.mp (hE.1 he)).2
  have haf := (Finset.mem_filter.mp (hE.1 hf)).2
  -- Suppose `w₁` is not in `T_w`; then `lca(u₁, w₁)` is a strict ancestor of `w`.
  by_contra houtside
  have ht : EdgeAbove.target f <+: e.2 := by
    rcases List.prefix_or_prefix_of_prefix (lca_prefix_left f.1 f.2) hinside with h | h
    · exact h
    · exact False.elim (houtside (h.trans (lca_prefix_right f.1 f.2)))
  have htne : EdgeAbove.target f ≠ e.2 := by
    intro h
    exact houtside (h ▸ lca_prefix_right f.1 f.2)
  have hparent_u : parent e.2 <+: f.1 := (parent_prefix e.2).trans hinside
  have hparent_ne : parent e.2 ≠ f.1 := by
    intro h
    have hlen := hinside.length_le
    rw [← h] at hlen
    have hpos := List.length_pos_iff.mpr hae.2.2.2.1
    simp only [parent, List.length_take] at hlen
    omega
  -- So `parent(w)`, on the path from `lca(u₁, w₁)` to `u₁` and above `u₁`, is in the footprint
  -- of `f`.
  have hparent_f : parent e.2 ∈ EdgeAbove.footprint t f := by
    exact Finset.mem_filter.mpr
      ⟨t.nodes_prefix_closed hae.2.1 (parent_prefix e.2),
        prefix_parent_of_ne ht htne, Or.inl ⟨hparent_u, hparent_ne⟩⟩
  -- It is also in the footprint of `e`; `e = f` would make `w` an ancestor of `u`.
  by_cases hef : e = f
  · subst f
    exact hae.2.2.2.2 hinside
  · exact Finset.disjoint_left.mp (hE.2 he hf hef)
      (recipient_parent_mem_footprint hae) hparent_f

/-- The cone below a vertex `p` of `T` in `Realization.graph t E`: the vertices of the subtree
`T_p`, and the fresh vertices on the edges above them, that is, the donors `u′` and the
recipients `w′` of the pairs `(u, w) ∈ E` with `u`, respectively `w`, in `T_p`. -/
def Below (t : PhyloTree) (E : Finset Pair) (p : Address) (v : ℕ) : Prop :=
  (∃ q ∈ t.nodes, p <+: q ∧ Address.code q = v) ∨
    (∃ e ∈ E, (p <+: e.1 ∧ donor t e = v) ∨ (p <+: e.2 ∧ recipient t e = v))

/-- A vertex `q` of `T` is in the cone below `p` iff `q` is in `T_p`. -/
theorem below_code_iff {t : PhyloTree} {E : Finset Pair} {p q : Address}
    (hq : q ∈ t.nodes) : Below t E p (Address.code q) ↔ p <+: q := by
  constructor
  · rintro (⟨r, hr, hp, hc⟩ | ⟨e, he, (⟨hp, hc⟩ | ⟨hp, hc⟩)⟩)
    · exact Address.code_injective hc ▸ hp
    · exact False.elim (donor_ne_code e hq hc)
    · exact False.elim (recipient_ne_code e hq hc)
  · intro hp
    exact Or.inl ⟨q, hq, hp, rfl⟩

/-- For `(u, w)` in a family `E` of admissible pairs, `u′` is in the cone below `p` iff `u` is
in `T_p`. -/
theorem below_donor_iff {t : PhyloTree} {E : Finset Pair}
    (hE : E ⊆ EdgeAbove.candidates t) {e : Pair} (he : e ∈ E) {p : Address} :
    Below t E p (donor t e) ↔ p <+: e.1 := by
  constructor
  · rintro (⟨q, hq, hp, hc⟩ | ⟨f, hf, (⟨hp, hc⟩ | ⟨hp, hc⟩)⟩)
    · exact False.elim (donor_ne_code e hq hc.symm)
    · exact donor_injective t (hE hf) (hE he) hc ▸ hp
    · exact False.elim (donor_ne_recipient t e f hc.symm)
  · intro hp
    exact Or.inr ⟨e, he, Or.inl ⟨hp, rfl⟩⟩

/-- For `(u, w)` in a family `E` of admissible pairs, `w′` is in the cone below `p` iff `w` is
in `T_p`. -/
theorem below_recipient_iff {t : PhyloTree} {E : Finset Pair}
    (hE : E ⊆ EdgeAbove.candidates t) {e : Pair} (he : e ∈ E) {p : Address} :
    Below t E p (recipient t e) ↔ p <+: e.2 := by
  constructor
  · rintro (⟨q, hq, hp, hc⟩ | ⟨f, hf, (⟨hp, hc⟩ | ⟨hp, hc⟩)⟩)
    · exact False.elim (recipient_ne_code e hq hc.symm)
    · exact False.elim (donor_ne_recipient t f e hc)
    · exact recipient_injective t (hE hf) (hE he) hc ▸ hp
  · intro hp
    exact Or.inr ⟨e, he, Or.inr ⟨hp, rfl⟩⟩

/-- For a family of admissible pairs, a vertex inside the wire above `q` is in the cone below
`p` iff `q` is in `T_p`. -/
theorem below_interior_iff {t : PhyloTree} {E : Finset Pair}
    (hE : E ⊆ EdgeAbove.candidates t) {p q : Address} {v : ℕ}
    (hv : v ∈ wireInterior (wire t E q)) : Below t E p v ↔ p <+: q := by
  obtain ⟨e, he, hin⟩ := mem_wireInterior.mp hv
  rcases hin with ⟨hu, rfl⟩ | ⟨hw, rfl⟩
  · rw [below_donor_iff hE he, hu]
  · rw [below_recipient_iff hE he, hw]

/-- For a family of admissible pairs, a vertex of the wire above a vertex `q` of `T`, other than
its first vertex, is in the cone below `p` iff `q` is in `T_p`. -/
theorem below_tail_iff {t : PhyloTree} {E : Finset Pair}
    (hE : E ⊆ EdgeAbove.candidates t) {p q : Address} (hq : q ∈ t.nodes) {v : ℕ}
    (hv : v ∈ (wire t E q).tail) : Below t E p v ↔ p <+: q := by
  rcases mem_tail_wire.mp hv with hin | rfl
  · exact below_interior_iff hE hin
  · exact below_code_iff hq

/-- For a family of admissible pairs, a support edge that starts in the cone below `p` ends in
it. -/
theorem below_support_closed {t : PhyloTree} {E : Finset Pair}
    (hE : E ⊆ EdgeAbove.candidates t) {p : Address} {u v : ℕ}
    (hu : Below t E p u) (huv : (u,v) ∈ supportEdges t E) : Below t E p v := by
  obtain ⟨q, hq, he⟩ := Finset.mem_biUnion.mp huv
  have hq' := Finset.mem_erase.mp hq
  have hparent := t.nodes_prefix_closed hq'.2 (parent_prefix q)
  have hfirst := edge_first_mem he
  have hpq : p <+: q := by
    rcases mem_wire.mp hfirst with hroot | hinner | hlast
    · change u = Address.code (parent q) at hroot
      rw [hroot] at hu
      exact ((below_code_iff hparent).mp hu).trans (parent_prefix q)
    · exact (below_interior_iff hE hinner).mp hu
    · change u = Address.code q at hlast
      rw [hlast] at hu
      exact (below_code_iff hq'.2).mp hu
  exact (below_tail_iff hE hq'.2 (edge_second_mem_tail he)).mpr hpq

/-- For `(u, w)` in a cycle-separated family `E`, every edge of `Realization.graph t E` that
starts in the cone below `w` ends in it. -/
theorem recipient_cone_closed {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) {u v : ℕ}
    (hu : Below t E e.2 u) (huv : (u,v) ∈ (graph t E).edges) : Below t E e.2 v := by
  rcases Finset.mem_union.mp huv with hs | ha
  · exact below_support_closed hE.1 hu hs
  · obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp ha
    have hud : u = donor t f := (congrArg Prod.fst hfe).symm
    have hvr : v = recipient t f := (congrArg Prod.snd hfe).symm
    rw [hud, below_donor_iff hE.1 hf] at hu
    rw [hvr, below_recipient_iff hE.1 hf]
    exact recipient_cone_closed_pairs hE he hf hu

/-- For `(u, w)` in a cycle-separated family `E`, every vertex reached by a directed path from
the cone below `w` is in it. -/
theorem recipient_cone_closed_reachable {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) {u v : ℕ}
    (hu : Below t E e.2 u)
    (huv : Relation.ReflTransGen (fun u v => (u,v) ∈ (graph t E).edges) u v) :
    Below t E e.2 v := by
  induction huv with
  | refl => exact hu
  | tail h hstep ih => exact recipient_cone_closed hE he ih hstep

/-- For `(u, w)` in a cycle-separated family `E`, no directed path of `Realization.graph t E`
leads from `w′` to `u′`: every vertex reached from `w′` is in the cone below `w`, and `u′` is
not, since `w` is not an ancestor of `u`. -/
theorem no_return_added_edge {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) :
    ¬Relation.ReflTransGen (fun u v => (u,v) ∈ (graph t E).edges)
      (recipient t e) (donor t e) := by
  intro hret
  have hstart : Below t E e.2 (recipient t e) :=
    (below_recipient_iff hE.1 he).mpr (List.prefix_refl _)
  have hend := recipient_cone_closed_reachable hE he hstart hret
  have ha := (Finset.mem_filter.mp (hE.1 he)).2
  exact ha.2.2.2.2 ((below_donor_iff hE.1 he).mp hend)

end Camus.Realization
