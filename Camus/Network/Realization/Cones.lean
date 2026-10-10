module

public import Camus.Network.Realization.Degrees

@[expose] public section

namespace Camus.Realization

theorem parent_ne_self {p : Address} (hp : p ≠ []) : parent p ≠ p := by
  intro h
  have hpos := List.length_pos_iff.mpr hp
  have hlen := congrArg List.length h
  simp only [parent, List.length_take] at hlen
  omega

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

/-- A reticulation arc cannot leave another reticulation's recipient subtree:
its support path would cross the original vertex just above that subtree. -/
theorem recipient_cone_closed_pairs {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e f : Pair} (he : e ∈ E) (hf : f ∈ E)
    (hinside : e.2 <+: f.1) : e.2 <+: f.2 := by
  have hae := (Finset.mem_filter.mp (hE.1 he)).2
  have haf := (Finset.mem_filter.mp (hE.1 hf)).2
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
  have hparent_f : parent e.2 ∈ EdgeAbove.footprint t f := by
    exact Finset.mem_filter.mpr
      ⟨t.nodes_prefix_closed hae.2.1 (parent_prefix e.2),
        prefix_parent_of_ne ht htne, Or.inl ⟨hparent_u, hparent_ne⟩⟩
  by_cases hef : e = f
  · subst f
    exact hae.2.2.2.2 hinside
  · exact Finset.disjoint_left.mp (hE.2 he hf hef)
      (recipient_parent_mem_footprint hae) hparent_f

/-- Membership below an original address includes all endpoints on the incoming
wires of descendants. The closed-cone theorem proves a graph fact, rather than
postulating a decomposition in the network data. -/
def Below (t : PhyloTree) (E : Finset Pair) (p : Address) (v : ℕ) : Prop :=
  (∃ q ∈ t.nodes, p <+: q ∧ Address.code q = v) ∨
    (∃ e ∈ E, (p <+: e.1 ∧ donor t e = v) ∨ (p <+: e.2 ∧ recipient t e = v))

theorem below_code_iff {t : PhyloTree} {E : Finset Pair} {p q : Address}
    (hq : q ∈ t.nodes) : Below t E p (Address.code q) ↔ p <+: q := by
  constructor
  · rintro (⟨r, hr, hp, hc⟩ | ⟨e, he, (⟨hp, hc⟩ | ⟨hp, hc⟩)⟩)
    · exact Address.code_injective hc ▸ hp
    · exact False.elim (donor_ne_code e hq hc)
    · exact False.elim (recipient_ne_code e hq hc)
  · intro hp
    exact Or.inl ⟨q, hq, hp, rfl⟩

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

theorem below_interior_iff {t : PhyloTree} {E : Finset Pair}
    (hE : E ⊆ EdgeAbove.candidates t) {p q : Address} {v : ℕ}
    (hv : v ∈ wireInterior (wire t E q)) : Below t E p v ↔ p <+: q := by
  obtain ⟨e, he, hin⟩ := mem_wireInterior.mp hv
  rcases hin with ⟨hu, rfl⟩ | ⟨hw, rfl⟩
  · rw [below_donor_iff hE he, hu]
  · rw [below_recipient_iff hE he, hw]

theorem below_tail_iff {t : PhyloTree} {E : Finset Pair}
    (hE : E ⊆ EdgeAbove.candidates t) {p q : Address} (hq : q ∈ t.nodes) {v : ℕ}
    (hv : v ∈ (wire t E q).tail) : Below t E p v ↔ p <+: q := by
  rcases mem_tail_wire.mp hv with hin | rfl
  · exact below_interior_iff hE hin
  · exact below_code_iff hq

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

theorem recipient_cone_closed_reachable {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) {u v : ℕ}
    (hu : Below t E e.2 u)
    (huv : Relation.ReflTransGen (fun u v => (u,v) ∈ (graph t E).edges) u v) :
    Below t E e.2 v := by
  induction huv with
  | refl => exact hu
  | tail h hstep ih => exact recipient_cone_closed hE he ih hstep

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
