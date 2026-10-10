module

public import Camus.Network.Clades
public import Camus.Preliminaries.Lemmas

/-!
# The two switchings of `T + e`

Let `e = (u, w)` be an admissible pair of `T`, and `T + e = Realization.graph t {e}` the network
obtained by adding an edge above `(u, w)` (Definition 3). Its only reticulation is w′, entered by
the edge from `parent(w)` and by the added edge from u′. So `T + e` has two switchings: the
support edges `Realization.supportEdges t {e}` (the subdivided `T`), and
`Realization.switchedEdges t e`, where the edge from `parent(w)` to w′ is replaced by the added edge
(u′, w′). The second subdivides the tree `T'` obtained from `T` by pruning the subtree `T_w` and
regrafting it on the edge above `u`. This file computes the directed reachability in both
switchings, from a vertex of `T`, from u′ and from w′ to a vertex of `T`.

## Main results

* `Realization.switchedEdges`: the second switching.
* `Realization.single_switching_cases`: every switching of `T + e` is one of the two.
* `Realization.support_reach_code`: reachability in the subdivided `T`.
* `Realization.switched_reach_code`: reachability in the second switching.
-/

@[expose] public section

namespace Camus.Realization

/-- The second switching of `T + e`, for `e = (u, w)`: the support edges of
`Realization.graph t {e}`, with the edge from `parent(w)` to w′ replaced by the added edge
(u′, w′). It subdivides the tree `T'` obtained from `T` by pruning the subtree `T_w` and
regrafting it on the edge above `u`. -/
noncomputable def switchedEdges (t : PhyloTree) (e : Pair) : Finset (ℕ × ℕ) :=
  insert (donor t e, recipient t e)
    ((supportEdges t {e}).erase (Address.code (parent e.2), recipient t e))

/-- If the only edge of `S` into `v` comes from `p`, then `v` is reached from `y` along `S` iff
`y = v` or `p` is reached from `y`. -/
theorem reach_iff_of_incoming {S : Finset (ℕ × ℕ)} {v p : ℕ}
    (hin : ∀ z, (z, v) ∈ S ↔ z = p) (y : ℕ) :
    Relation.ReflTransGen (fun a b => (a, b) ∈ S) y v ↔
      y = v ∨ Relation.ReflTransGen (fun a b => (a, b) ∈ S) y p := by
  constructor
  · intro h
    rcases h.cases_tail with h | ⟨c, hc, hcv⟩
    · exact Or.inl h.symm
    · exact Or.inr ((hin c).mp hcv ▸ hc)
  · rintro (rfl | h)
    · exact .refl
    · exact h.tail ((hin p).mpr rfl)

/-- If no edge of `S` enters `v`, then `v` is reached from `y` along `S` only if `y = v`. -/
theorem reach_iff_of_no_incoming {S : Finset (ℕ × ℕ)} {v : ℕ}
    (hin : ∀ z, (z, v) ∉ S) (y : ℕ) :
    Relation.ReflTransGen (fun a b => (a, b) ∈ S) y v ↔ y = v := by
  constructor
  · intro h
    rcases h.cases_tail with h | ⟨c, _, hcv⟩
    · exact h.symm
    · exact absurd hcv (hin c)
  · rintro rfl
    exact .refl

/-- If the only edge of `S` into `v` comes from `p`, then exactly one edge of `S` enters `v`. -/
theorem incoming_card_of_incoming {S : Finset (ℕ × ℕ)} {v p : ℕ}
    (hin : ∀ z, (z, v) ∈ S ↔ z = p) : (S.filter (fun f => f.2 = v)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨(p, v), ?_⟩
  ext f
  obtain ⟨z, v'⟩ := f
  simp only [Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hf, rfl⟩
    exact ⟨(hin z).mp hf, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨(hin z).mpr rfl, rfl⟩

/-- A vertex is an ancestor of the non-root vertex `x` iff it is `x` or an ancestor of
`parent x`. -/
theorem prefix_iff_eq_or_prefix_parent {p x : Address} (hx : x ≠ []) :
    p <+: x ↔ p = x ∨ p <+: parent x := by
  constructor
  · intro h
    by_cases hpx : p = x
    · exact Or.inl hpx
    · exact Or.inr (prefix_parent_of_ne h hpx)
  · rintro (rfl | h)
    · exact List.prefix_refl _
    · exact h.trans (parent_prefix x)

/-- A vertex is an ancestor of `parent x`, for `x` not the root, iff it is a strict ancestor of
`x`. -/
theorem prefix_parent_iff_strict {p x : Address} (hx : x ≠ []) :
    p <+: parent x ↔ p <+: x ∧ p ≠ x := by
  constructor
  · intro h
    refine ⟨h.trans (parent_prefix x), ?_⟩
    rintro rfl
    have hlen := h.length_le
    have hpos := List.length_pos_iff.mpr hx
    simp only [parent, List.length_take] at hlen
    omega
  · rintro ⟨h, hne⟩
    exact prefix_parent_of_ne h hne

/-- The parent of a non-root vertex is shorter. -/
theorem parent_length_lt {x : Address} (hx : x ≠ []) : (parent x).length < x.length := by
  have hpos := List.length_pos_iff.mpr hx
  simp only [parent, List.length_take]
  omega

section Single

variable {t : PhyloTree} {e : Pair}

/-- The support edges of `T + e`, for an admissible pair `e = (u, w)`: the edges of the wires,
`parent(u) → u′ → u`, `parent(w) → w′ → w`, and `parent(p) → p` for every other non-root vertex
`p` of `T`. -/
theorem single_support_mem_iff (he : EdgeAbove.Admissible t e) (f : ℕ × ℕ) :
    f ∈ supportEdges t {e} ↔ ∃ p ∈ t.nodes, p ≠ [] ∧
      if p = e.1 then
        f = (Address.code (parent p), donor t e) ∨ f = (donor t e, Address.code p)
      else if p = e.2 then
        f = (Address.code (parent p), recipient t e) ∨ f = (recipient t e, Address.code p)
      else f = (Address.code (parent p), Address.code p) := by
  classical
  unfold supportEdges
  simp only [Finset.mem_biUnion, Finset.mem_erase]
  constructor
  · rintro ⟨p, ⟨hp0, hp⟩, hf⟩
    refine ⟨p, hp, hp0, ?_⟩
    rw [singleton_wire he p] at hf
    split_ifs at hf ⊢ <;> simpa [wireEdges] using hf
  · rintro ⟨p, hp, hp0, hf⟩
    refine ⟨p, ⟨hp0, hp⟩, ?_⟩
    rw [singleton_wire he p]
    split_ifs at hf ⊢ <;> simpa [wireEdges] using hf

/-- The tail of the support edge of `T + e` into the non-root vertex `x` of `T`, for
`e = (u, w)`: u′ if `x = u`, w′ if `x = w`, and `parent(x)` otherwise. -/
noncomputable def supportParent (t : PhyloTree) (e : Pair) (x : Address) : ℕ :=
  if x = e.1 then donor t e else if x = e.2 then recipient t e else Address.code (parent x)

/-- The support edges of `T + e` into a non-root vertex `x` of `T`. -/
theorem support_incoming_code (he : EdgeAbove.Admissible t e) {x : Address}
    (hx : x ∈ t.nodes) (hx0 : x ≠ []) (z : ℕ) :
    (z, Address.code x) ∈ supportEdges t {e} ↔ z = supportParent t e x := by
  have hd := donor_ne_code e hx
  have hr := recipient_ne_code e hx
  rw [single_support_mem_iff he]
  constructor
  · rintro ⟨p, hp, hp0, hf⟩
    unfold supportParent
    split_ifs at hf with hpu hpw
    · rcases hf with hf | hf
      · exact absurd (Prod.mk.inj hf).2 (Ne.symm hd)
      · obtain ⟨rfl, hc⟩ := Prod.mk.inj hf
        rw [ite_eq_left ((Address.code_injective hc).trans hpu)]
    · rcases hf with hf | hf
      · exact absurd (Prod.mk.inj hf).2 (Ne.symm hr)
      · obtain ⟨rfl, hc⟩ := Prod.mk.inj hf
        have hxp := Address.code_injective hc
        subst hxp
        rw [ite_eq_right hpu, ite_eq_left hpw]
    · obtain ⟨rfl, hc⟩ := Prod.mk.inj hf
      have hxp := Address.code_injective hc
      subst hxp
      rw [ite_eq_right hpu, ite_eq_right hpw]
  · intro hz
    refine ⟨x, hx, hx0, ?_⟩
    unfold supportParent at hz
    split_ifs at hz ⊢ with hxu hxw
    · exact Or.inr (by rw [hz])
    · exact Or.inr (by rw [hz])
    · rw [hz]

/-- The support edge of `T + e` into u′ comes from `parent(u)`, for `e = (u, w)`. -/
theorem support_incoming_donor (he : EdgeAbove.Admissible t e) (z : ℕ) :
    (z, donor t e) ∈ supportEdges t {e} ↔ z = Address.code (parent e.1) := by
  rw [single_support_mem_iff he]
  constructor
  · rintro ⟨p, hp, hp0, hf⟩
    split_ifs at hf with hpu hpw
    · rcases hf with hf | hf
      · rw [(Prod.mk.inj hf).1, hpu]
      · exact absurd (Prod.mk.inj hf).2 (donor_ne_code e hp)
    · rcases hf with hf | hf
      · exact absurd (Prod.mk.inj hf).2 (donor_ne_recipient t e e)
      · exact absurd (Prod.mk.inj hf).2 (donor_ne_code e hp)
    · exact absurd (Prod.mk.inj hf).2 (donor_ne_code e hp)
  · rintro rfl
    exact ⟨e.1, he.1, he.2.2.1, by rw [ite_eq_left rfl]; exact Or.inl rfl⟩

/-- The support edge of `T + e` into w′ comes from `parent(w)`, for `e = (u, w)`. -/
theorem support_incoming_recipient (he : EdgeAbove.Admissible t e) (z : ℕ) :
    (z, recipient t e) ∈ supportEdges t {e} ↔ z = Address.code (parent e.2) := by
  have hne : e.2 ≠ e.1 := fun h => he.2.2.2.2 (h ▸ List.prefix_refl _)
  rw [single_support_mem_iff he]
  constructor
  · rintro ⟨p, hp, hp0, hf⟩
    split_ifs at hf with hpu hpw
    · rcases hf with hf | hf
      · exact absurd (Prod.mk.inj hf).2.symm (donor_ne_recipient t e e)
      · exact absurd (Prod.mk.inj hf).2 (recipient_ne_code e hp)
    · rcases hf with hf | hf
      · rw [(Prod.mk.inj hf).1, hpw]
      · exact absurd (Prod.mk.inj hf).2 (recipient_ne_code e hp)
    · exact absurd (Prod.mk.inj hf).2 (recipient_ne_code e hp)
  · rintro rfl
    exact ⟨e.2, he.2.1, he.2.2.2.1, by rw [ite_eq_right hne, ite_eq_left rfl]; exact Or.inl rfl⟩

/-- No support edge of `T + e` enters the root. -/
theorem support_incoming_root (he : EdgeAbove.Admissible t e) (z : ℕ) :
    (z, Address.code []) ∉ supportEdges t {e} := by
  rw [single_support_mem_iff he]
  rintro ⟨p, hp, hp0, hf⟩
  have hroot := t.root_mem_nodes
  split_ifs at hf with hpu hpw
  · rcases hf with hf | hf
    · exact donor_ne_code e hroot (Prod.mk.inj hf).2.symm
    · exact hp0 (Address.code_injective (Prod.mk.inj hf).2).symm
  · rcases hf with hf | hf
    · exact recipient_ne_code e hroot (Prod.mk.inj hf).2.symm
    · exact hp0 (Address.code_injective (Prod.mk.inj hf).2).symm
  · exact hp0 (Address.code_injective (Prod.mk.inj hf).2).symm

/-- The edges of the second switching into a non-root vertex `x` of `T` are those of the
support. -/
theorem switched_incoming_code (he : EdgeAbove.Admissible t e) {x : Address}
    (hx : x ∈ t.nodes) (hx0 : x ≠ []) (z : ℕ) :
    (z, Address.code x) ∈ switchedEdges t e ↔ z = supportParent t e x := by
  rw [← support_incoming_code he hx hx0]
  have hr := recipient_ne_code e hx
  unfold switchedEdges
  rw [Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact absurd (Prod.mk.inj h).2 (Ne.symm hr)
    · exact h
  · intro h
    exact Or.inr ⟨fun h' => hr (Prod.mk.inj h').2.symm, h⟩

/-- The edge of the second switching into u′ comes from `parent(u)`. -/
theorem switched_incoming_donor (he : EdgeAbove.Admissible t e) (z : ℕ) :
    (z, donor t e) ∈ switchedEdges t e ↔ z = Address.code (parent e.1) := by
  rw [← support_incoming_donor he]
  have hdr := donor_ne_recipient t e e
  unfold switchedEdges
  rw [Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact absurd (Prod.mk.inj h).2 hdr
    · exact h
  · intro h
    exact Or.inr ⟨fun h' => hdr (Prod.mk.inj h').2, h⟩

/-- The edge of the second switching into w′ is the added edge, from u′. -/
theorem switched_incoming_recipient (he : EdgeAbove.Admissible t e) (z : ℕ) :
    (z, recipient t e) ∈ switchedEdges t e ↔ z = donor t e := by
  unfold switchedEdges
  rw [Finset.mem_insert, Finset.mem_erase, support_incoming_recipient he]
  constructor
  · rintro (h | ⟨h, h'⟩)
    · exact (Prod.mk.inj h).1
    · exact absurd (by rw [h']) h
  · intro h
    exact Or.inl (by rw [h])

/-- No edge of the second switching enters the root. -/
theorem switched_incoming_root (he : EdgeAbove.Admissible t e) (z : ℕ) :
    (z, Address.code []) ∉ switchedEdges t e := by
  have hr := recipient_ne_code e t.root_mem_nodes
  simp only [switchedEdges, Finset.mem_insert, Finset.mem_erase, Prod.mk.injEq, Ne.symm hr,
    and_false, false_or, not_and]
  exact fun _ => support_incoming_root he z

/-- Directed reachability in the subdivided `T`, for an admissible pair `e = (u, w)`: a vertex
`x` of `T` is reached from a vertex `p` of `T` iff `p` is an ancestor of `x`, from u′ iff `u` is,
and from w′ iff `w` is. -/
theorem support_reach_code (he : EdgeAbove.Admissible t e) {x : Address}
    (hx : x ∈ t.nodes) :
    (∀ p ∈ t.nodes, Relation.ReflTransGen (fun a b => (a, b) ∈ supportEdges t {e})
        (Address.code p) (Address.code x) ↔ p <+: x) ∧
      (Relation.ReflTransGen (fun a b => (a, b) ∈ supportEdges t {e})
        (donor t e) (Address.code x) ↔ e.1 <+: x) ∧
      (Relation.ReflTransGen (fun a b => (a, b) ∈ supportEdges t {e})
        (recipient t e) (Address.code x) ↔ e.2 <+: x) := by
  have hu0 : e.1 ≠ [] := he.2.2.1
  have hw0 : e.2 ≠ [] := he.2.2.2.1
  have hwu : ¬e.2 <+: e.1 := he.2.2.2.2
  have hne : e.1 ≠ e.2 := fun h => hwu (h ▸ List.prefix_refl _)
  have hdr := donor_ne_recipient t e e
  have hdonor := reach_iff_of_incoming (support_incoming_donor he)
  have hrecipient := reach_iff_of_incoming (support_incoming_recipient he)
  suffices h : ∀ n, ∀ x ∈ t.nodes, x.length = n →
      (∀ p ∈ t.nodes, Relation.ReflTransGen (fun a b => (a, b) ∈ supportEdges t {e})
          (Address.code p) (Address.code x) ↔ p <+: x) ∧
        (Relation.ReflTransGen (fun a b => (a, b) ∈ supportEdges t {e})
          (donor t e) (Address.code x) ↔ e.1 <+: x) ∧
        (Relation.ReflTransGen (fun a b => (a, b) ∈ supportEdges t {e})
          (recipient t e) (Address.code x) ↔ e.2 <+: x) from h _ x hx rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx hlen
  by_cases hx0 : x = []
  · subst x
    have hroot := reach_iff_of_no_incoming (support_incoming_root he)
    refine ⟨fun p _ => ?_, ?_, ?_⟩
    · rw [hroot, Address.code_injective.eq_iff, List.prefix_nil]
    · rw [hroot, List.prefix_nil]
      exact iff_of_false (donor_ne_code e t.root_mem_nodes) hu0
    · rw [hroot, List.prefix_nil]
      exact iff_of_false (recipient_ne_code e t.root_mem_nodes) hw0
  have hpx := t.nodes_prefix_closed hx (parent_prefix x)
  obtain ⟨ihp, ihd, ihr⟩ := ih _ (hlen ▸ parent_length_lt hx0) (parent x) hpx rfl
  have hstep := reach_iff_of_incoming (support_incoming_code he hx hx0)
  have hdx := donor_ne_code e hx
  have hrx := recipient_ne_code e hx
  by_cases hxu : x = e.1
  · -- `x = u`: its support edge comes from u′, whose support edge comes from `parent(u)`
    have hpar : supportParent t e x = donor t e := by
      unfold supportParent
      rw [ite_eq_left hxu]
    refine ⟨fun p hp => ?_, ?_, ?_⟩
    · rw [hstep, hpar, hdonor, ← hxu, ihp p hp, Address.code_injective.eq_iff,
        prefix_iff_eq_or_prefix_parent hx0]
      have := donor_ne_code e hp
      tauto
    · rw [hstep, hpar]
      exact iff_of_true (Or.inr .refl) (hxu ▸ List.prefix_refl _)
    · rw [hstep, hpar, hdonor, ← hxu, ihr]
      refine iff_of_false ?_ (hxu ▸ hwu)
      rintro (h | h | h)
      · exact hrx h
      · exact hdr h.symm
      · exact hwu (hxu ▸ h.trans (parent_prefix x))
  by_cases hxw : x = e.2
  · -- `x = w`: its support edge comes from w′, whose support edge comes from `parent(w)`
    have hpar : supportParent t e x = recipient t e := by
      unfold supportParent
      rw [ite_eq_right hxu, ite_eq_left hxw]
    refine ⟨fun p hp => ?_, ?_, ?_⟩
    · rw [hstep, hpar, hrecipient, ← hxw, ihp p hp, Address.code_injective.eq_iff,
        prefix_iff_eq_or_prefix_parent hx0]
      have := recipient_ne_code e hp
      tauto
    · rw [hstep, hpar, hrecipient, ← hxw, ihd, prefix_iff_eq_or_prefix_parent hx0]
      have : e.1 ≠ x := fun h => hxu h.symm
      tauto
    · rw [hstep, hpar]
      exact iff_of_true (Or.inr .refl) (hxw ▸ List.prefix_refl _)
  · -- any other `x`: its support edge comes from `parent(x)`
    have hpar : supportParent t e x = Address.code (parent x) := by
      unfold supportParent
      rw [ite_eq_right hxu, ite_eq_right hxw]
    refine ⟨fun p hp => ?_, ?_, ?_⟩
    · rw [hstep, hpar, ihp p hp, Address.code_injective.eq_iff,
        prefix_iff_eq_or_prefix_parent hx0]
    · rw [hstep, hpar, ihd, prefix_iff_eq_or_prefix_parent hx0]
      have : e.1 ≠ x := fun h => hxu h.symm
      tauto
    · rw [hstep, hpar, ihr, prefix_iff_eq_or_prefix_parent hx0]
      have : e.2 ≠ x := fun h => hxw h.symm
      tauto

/-- Directed reachability in the second switching, to a vertex `x` of `T` outside `T_w`, for an
admissible pair `e = (u, w)`: `x` is reached from a vertex `p` of `T` iff `p` is an ancestor of
`x`, from u′ iff `u` is, and not from w′. -/
theorem switched_reach_code_outside (he : EdgeAbove.Admissible t e) {x : Address}
    (hx : x ∈ t.nodes) (hwx : ¬e.2 <+: x) :
    (∀ p ∈ t.nodes, Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
        (Address.code p) (Address.code x) ↔ p <+: x) ∧
      (Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
        (donor t e) (Address.code x) ↔ e.1 <+: x) ∧
      ¬Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
        (recipient t e) (Address.code x) := by
  have hu0 : e.1 ≠ [] := he.2.2.1
  have hwu : ¬e.2 <+: e.1 := he.2.2.2.2
  have hdr := donor_ne_recipient t e e
  have hdonor := reach_iff_of_incoming (switched_incoming_donor he)
  suffices h : ∀ n, ∀ x ∈ t.nodes, x.length = n → ¬e.2 <+: x →
      (∀ p ∈ t.nodes, Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
          (Address.code p) (Address.code x) ↔ p <+: x) ∧
        (Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
          (donor t e) (Address.code x) ↔ e.1 <+: x) ∧
        ¬Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
          (recipient t e) (Address.code x) from h _ x hx rfl hwx
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx hlen hwx
  by_cases hx0 : x = []
  · subst x
    have hroot := reach_iff_of_no_incoming (switched_incoming_root he)
    refine ⟨fun p _ => ?_, ?_, ?_⟩
    · rw [hroot, Address.code_injective.eq_iff, List.prefix_nil]
    · rw [hroot, List.prefix_nil]
      exact iff_of_false (donor_ne_code e t.root_mem_nodes) hu0
    · rw [hroot]
      exact recipient_ne_code e t.root_mem_nodes
  have hpx := t.nodes_prefix_closed hx (parent_prefix x)
  have hwpx : ¬e.2 <+: parent x := fun h => hwx (h.trans (parent_prefix x))
  obtain ⟨ihp, ihd, ihr⟩ := ih _ (hlen ▸ parent_length_lt hx0) (parent x) hpx rfl hwpx
  have hstep := reach_iff_of_incoming (switched_incoming_code he hx hx0)
  have hdx := donor_ne_code e hx
  have hrx := recipient_ne_code e hx
  have hxw : x ≠ e.2 := fun h => hwx (h ▸ List.prefix_refl _)
  by_cases hxu : x = e.1
  · -- `x = u`: its edge comes from u′, whose edge comes from `parent(u)`
    have hpar : supportParent t e x = donor t e := by
      unfold supportParent
      rw [ite_eq_left hxu]
    refine ⟨fun p hp => ?_, ?_, ?_⟩
    · rw [hstep, hpar, hdonor, ← hxu, ihp p hp, Address.code_injective.eq_iff,
        prefix_iff_eq_or_prefix_parent hx0]
      have := donor_ne_code e hp
      tauto
    · rw [hstep, hpar]
      exact iff_of_true (Or.inr .refl) (hxu ▸ List.prefix_refl _)
    · rw [hstep, hpar, hdonor, ← hxu]
      rintro (h | h | h)
      · exact hrx h
      · exact hdr h.symm
      · exact ihr h
  · -- any other `x`: its edge comes from `parent(x)`
    have hpar : supportParent t e x = Address.code (parent x) := by
      unfold supportParent
      rw [ite_eq_right hxu, ite_eq_right hxw]
    refine ⟨fun p hp => ?_, ?_, ?_⟩
    · rw [hstep, hpar, ihp p hp, Address.code_injective.eq_iff,
        prefix_iff_eq_or_prefix_parent hx0]
    · rw [hstep, hpar, ihd, prefix_iff_eq_or_prefix_parent hx0]
      have : e.1 ≠ x := fun h => hxu h.symm
      tauto
    · rw [hstep, hpar]
      rintro (h | h)
      · exact hrx h
      · exact ihr h

/-- Directed reachability in the second switching, to a vertex `x` of `T_w`, for an admissible
pair `e = (u, w)`: `x` is reached from a vertex `p` of `T` iff `p` lies on the path from `w` to
`x` or `p` is a strict ancestor of `u` (an ancestor of `parent(u)`), and from u′ and from w′. -/
theorem switched_reach_code_inside (he : EdgeAbove.Admissible t e) {x : Address}
    (hx : x ∈ t.nodes) (hwx : e.2 <+: x) :
    (∀ p ∈ t.nodes, Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
        (Address.code p) (Address.code x) ↔ (e.2 <+: p ∧ p <+: x) ∨ p <+: parent e.1) ∧
      Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
        (donor t e) (Address.code x) ∧
      Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
        (recipient t e) (Address.code x) := by
  have hu : e.1 ∈ t.nodes := he.1
  have hu0 : e.1 ≠ [] := he.2.2.1
  have hw0 : e.2 ≠ [] := he.2.2.2.1
  have hwu : ¬e.2 <+: e.1 := he.2.2.2.2
  have hne : e.1 ≠ e.2 := fun h => hwu (h ▸ List.prefix_refl _)
  have hdr := donor_ne_recipient t e e
  have hdonor := reach_iff_of_incoming (switched_incoming_donor he)
  have hrecipient := reach_iff_of_incoming (switched_incoming_recipient he)
  have hpu := t.nodes_prefix_closed hu (parent_prefix e.1)
  have hwpu : ¬e.2 <+: parent e.1 := fun h => hwu (h.trans (parent_prefix e.1))
  obtain ⟨hpu_code, _, _⟩ := switched_reach_code_outside he hpu hwpu
  suffices h : ∀ n, ∀ x ∈ t.nodes, x.length = n → e.2 <+: x →
      (∀ p ∈ t.nodes, Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
          (Address.code p) (Address.code x) ↔ (e.2 <+: p ∧ p <+: x) ∨ p <+: parent e.1) ∧
        Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
          (donor t e) (Address.code x) ∧
        Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
          (recipient t e) (Address.code x) from h _ x hx rfl hwx
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx hlen hwx
  have hx0 : x ≠ [] := by
    rintro rfl
    exact hw0 (List.prefix_nil.mp hwx)
  have hxu : x ≠ e.1 := fun h => hwu (h ▸ hwx)
  have hstep := reach_iff_of_incoming (switched_incoming_code he hx hx0)
  by_cases hxw : x = e.2
  · -- `x = w`: its edge comes from w′, whose edge comes from u′, whose edge comes from
    -- `parent(u)`
    subst hxw
    have hpar : supportParent t e e.2 = recipient t e := by
      unfold supportParent
      rw [ite_eq_right (Ne.symm hne), ite_eq_left rfl]
    refine ⟨fun p hp => ?_, ?_, ?_⟩
    · rw [hstep, hpar, hrecipient, hdonor, hpu_code p hp, Address.code_injective.eq_iff]
      have := donor_ne_code e hp
      have := recipient_ne_code e hp
      constructor
      · rintro (h | h | h | h)
        · exact Or.inl ⟨h ▸ List.prefix_refl _, h ▸ List.prefix_refl _⟩
        · exact absurd h.symm (by assumption)
        · exact absurd h.symm (by assumption)
        · exact Or.inr h
      · rintro (⟨h, h'⟩ | h)
        · exact Or.inl (h'.eq_of_length_le h.length_le)
        · exact Or.inr (Or.inr (Or.inr h))
    · rw [hstep, hpar, hrecipient, hdonor]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [hstep, hpar]
      exact Or.inr .refl
  · -- any other `x` in `T_w`: its edge comes from `parent(x)`, which is in `T_w`
    have hpx := t.nodes_prefix_closed hx (parent_prefix x)
    have hwpx : e.2 <+: parent x := prefix_parent_of_ne hwx (Ne.symm hxw)
    obtain ⟨ihp, ihd, ihr⟩ := ih _ (hlen ▸ parent_length_lt hx0) (parent x) hpx rfl hwpx
    have hpar : supportParent t e x = Address.code (parent x) := by
      unfold supportParent
      rw [ite_eq_right hxu, ite_eq_right hxw]
    refine ⟨fun p hp => ?_, ?_, ?_⟩
    · rw [hstep, hpar, ihp p hp, Address.code_injective.eq_iff,
        prefix_iff_eq_or_prefix_parent hx0]
      constructor
      · rintro (rfl | ⟨h, h'⟩ | h)
        · exact Or.inl ⟨hwx, Or.inl rfl⟩
        · exact Or.inl ⟨h, Or.inr h'⟩
        · exact Or.inr h
      · rintro (⟨h, rfl | h'⟩ | h)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨h, h'⟩)
        · exact Or.inr (Or.inr h)
    · rw [hstep, hpar]
      exact Or.inr ihd
    · rw [hstep, hpar]
      exact Or.inr ihr

/-- Directed reachability in the second switching, for an admissible pair `e = (u, w)` and a
vertex `x` of `T`. If `x` is in `T_w`, it is reached from a vertex `p` of `T` iff `p` lies on the
path from `w` to `x` or `p` is a strict ancestor of `u`; otherwise iff `p` is an ancestor of `x`.
It is reached from u′ iff `u` or `w` is an ancestor of `x`, and from w′ iff `w` is. -/
theorem switched_reach_code (he : EdgeAbove.Admissible t e) {x : Address}
    (hx : x ∈ t.nodes) :
    (∀ p ∈ t.nodes, Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
        (Address.code p) (Address.code x) ↔
          if e.2 <+: x then (e.2 <+: p ∧ p <+: x) ∨ p <+: parent e.1 else p <+: x) ∧
      (Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
        (donor t e) (Address.code x) ↔ e.1 <+: x ∨ e.2 <+: x) ∧
      (Relation.ReflTransGen (fun a b => (a, b) ∈ switchedEdges t e)
        (recipient t e) (Address.code x) ↔ e.2 <+: x) := by
  by_cases hwx : e.2 <+: x
  · obtain ⟨hp, hd, hr⟩ := switched_reach_code_inside he hx hwx
    refine ⟨fun p hq => ?_, iff_of_true hd (Or.inr hwx), iff_of_true hr hwx⟩
    rw [ite_eq_left hwx]
    exact hp p hq
  · obtain ⟨hp, hd, hr⟩ := switched_reach_code_outside he hx hwx
    refine ⟨fun p hq => ?_, ?_, iff_of_false hr hwx⟩
    · rw [ite_eq_right hwx]
      exact hp p hq
    · rw [hd]
      tauto

/-- The vertices of `T + e`: the vertices of `T`, u′ and w′. -/
theorem single_vertex_cases {v : ℕ} (hv : v ∈ (graph t {e}).vertices) :
    (∃ x ∈ t.nodes, v = Address.code x) ∨ v = donor t e ∨ v = recipient t e := by
  simp only [graph, Finset.mem_union, Finset.mem_image, Finset.singleton_biUnion,
    Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with ⟨x, hx, rfl⟩ | h | h
  · exact Or.inl ⟨x, hx, rfl⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The edges of `T + e`: the support edges and the added edge (u′, w′). -/
theorem single_edges_mem_iff (f : ℕ × ℕ) :
    f ∈ (graph t {e}).edges ↔ f ∈ supportEdges t {e} ∨ f = (donor t e, recipient t e) := by
  simp only [graph, Finset.mem_union, Finset.image_singleton, Finset.mem_singleton]

/-- The second switching is a switching of `T + e`. -/
theorem switched_switching (he : EdgeAbove.Admissible t e) :
    (graph t {e}).Switching (switchedEdges t e) := by
  refine ⟨?_, ?_⟩
  · intro f hf
    rw [single_edges_mem_iff]
    rcases Finset.mem_insert.mp hf with h | h
    · exact Or.inr h
    · exact Or.inl (Finset.mem_erase.mp h).2
  · intro v hv hvr
    rcases single_vertex_cases hv with ⟨x, hx, rfl⟩ | rfl | rfl
    · have hx0 : x ≠ [] := by
        rintro rfl
        exact hvr rfl
      exact incoming_card_of_incoming (switched_incoming_code he hx hx0)
    · exact incoming_card_of_incoming (switched_incoming_donor he)
    · exact incoming_card_of_incoming (switched_incoming_recipient he)

/-- `T + e` has two switchings: the subdivided `T` (`Realization.supportEdges t {e}`) and the
second switching (`Realization.switchedEdges t e`). Every vertex other than the root and w′ has
one incoming edge, which a switching keeps; at w′, a switching keeps one of the two incoming
edges. -/
theorem single_switching_cases (he : e ∈ EdgeAbove.candidates t) {S : Finset (ℕ × ℕ)}
    (hS : (graph t {e}).Switching S) :
    S = supportEdges t {e} ∨ S = switchedEdges t e := by
  classical
  have hadm : EdgeAbove.Admissible t e := (Finset.mem_filter.mp he).2
  have hE : ({e} : Finset Pair) ⊆ EdgeAbove.candidates t := Finset.singleton_subset_iff.mpr he
  have hrv : recipient t e ∈ (graph t {e}).vertices :=
    Finset.mem_union_right _ (by simp)
  have hrr : recipient t e ≠ (graph t {e}).root := recipient_ne_code e t.root_mem_nodes
  -- at a vertex other than w′, the edges of `S` are the support edges
  have hother (z v : ℕ) (hv : v ≠ recipient t e) :
      (z, v) ∈ S ↔ (z, v) ∈ supportEdges t {e} := by
    constructor
    · intro h
      rcases (single_edges_mem_iff _).mp (hS.1 h) with h | h
      · exact h
      · exact absurd (Prod.mk.inj h).2 hv
    · intro h
      obtain ⟨_, hvN⟩ := support_edge_endpoints t {e} hE h
      have hvr : v ≠ (graph t {e}).root := by
        intro hr
        change v = Address.code [] at hr
        subst hr
        exact support_incoming_root hadm z h
      obtain ⟨g, hg⟩ := Finset.card_pos.mp (show 0 < (S.filter (fun f => f.2 = v)).card by
        rw [hS.2 v hvN hvr]; omega)
      obtain ⟨hgS, hgv⟩ := Finset.mem_filter.mp hg
      obtain ⟨z', v'⟩ := g
      change v' = v at hgv
      subst hgv
      have hg0 : (z', v') ∈ supportEdges t {e} := by
        rcases (single_edges_mem_iff _).mp (hS.1 hgS) with h | h
        · exact h
        · exact absurd (Prod.mk.inj h).2 hv
      rwa [support_incoming_unique t {e} hE h hg0]
  -- at w′, `S` keeps exactly one incoming edge
  have hcard := hS.2 _ hrv hrr
  have hunique (z z' : ℕ) (hz : (z, recipient t e) ∈ S) (hz' : (z', recipient t e) ∈ S) :
      z = z' := by
    have := Finset.card_le_one.mp hcard.le _ (Finset.mem_filter.mpr ⟨hz, rfl⟩) _
      (Finset.mem_filter.mpr ⟨hz', rfl⟩)
    exact (Prod.mk.inj this).1
  obtain ⟨g, hg⟩ := Finset.card_pos.mp (show 0 < (S.filter (fun f => f.2 = recipient t e)).card
    by rw [hcard]; omega)
  obtain ⟨hgS, hgv⟩ := Finset.mem_filter.mp hg
  obtain ⟨z, v⟩ := g
  change v = recipient t e at hgv
  subst hgv
  rcases (single_edges_mem_iff _).mp (hS.1 hgS) with h | h
  · -- `S` keeps the edge from `parent(w)`
    have hz := (support_incoming_recipient hadm z).mp h
    subst hz
    left
    ext ⟨a, b⟩
    by_cases hb : b = recipient t e
    · subst hb
      rw [support_incoming_recipient hadm]
      exact ⟨fun h' => hunique _ _ h' hgS, fun h' => h' ▸ hgS⟩
    · exact hother a b hb
  · -- `S` keeps the added edge
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    right
    ext ⟨a, b⟩
    by_cases hb : b = recipient t e
    · subst hb
      rw [switched_incoming_recipient hadm]
      exact ⟨fun h' => hunique _ _ h' hgS, fun h' => h' ▸ hgS⟩
    · rw [hother a b hb]
      unfold switchedEdges
      rw [Finset.mem_insert, Finset.mem_erase]
      constructor
      · intro h'
        exact Or.inr ⟨fun h'' => hb (Prod.mk.inj h'').2, h'⟩
      · rintro (h' | ⟨_, h'⟩)
        · exact absurd (Prod.mk.inj h').2 hb
        · exact h'

end Single

end Camus.Realization
