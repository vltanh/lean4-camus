module

public import Camus.Network.Code
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Find

/-!
# The canonical network of an edge family: vertex numbering

Definition 3 adds an edge above a pair `(u, w)` of vertices of `T`: it places a vertex `u′` on
the edge above `u` and a vertex `w′` on the edge above `w`, and adds the edge `u′ → w′`. The
canonical network `Realization.graph t E` (defined in `Camus/Defs.lean`) does this for all pairs
of a family `E` at once. Its vertices are natural numbers. A vertex `p` of `T` is
`Address.code p`. The admissible pair `e` with index `i` in a fixed enumeration of
`EdgeAbove.candidates t` gets the donor `Realization.donor t e = b + 2i + 1`, its vertex `u′`,
and the recipient `Realization.recipient t e = b + 2i + 2`, its vertex `w′`, where
`b = Realization.bound t` is the largest code of a vertex of `T`. This file proves that these
numbers are pairwise distinct. It also proves the facts on leaf addresses used to place the
labelled leaves.

## Main results

* `Realization.donor_injective`, `Realization.recipient_injective`: distinct admissible pairs
  have distinct donors and distinct recipients.
* `Realization.donor_ne_recipient`, `Realization.donor_ne_code`, `Realization.recipient_ne_code`:
  no donor is a recipient, and no donor or recipient is a vertex of `T`.
* `Realization.code_mem_cycleVertices_iff`: a vertex of `T` is a vertex of the cycle `γ(u, w)`
  iff it is in the footprint of `(u, w)`.
* `Realization.leafAddress_eq`: in a well-labelled tree, `Realization.leafAddress t a` is the
  address of the leaf labelled `a`.
-/

@[expose] public section

namespace Camus

namespace PhyloTree

/-- The label of a leaf of `T` is one of the labels of `T`. -/
theorem leaf_label_mem {t : PhyloTree} {p : Address} {a : ℕ}
    (hp : t.nodeAt p = some (.leaf a)) : a ∈ t.labels := by
  induction t generalizing p with
  | leaf b =>
    cases p with
    | nil =>
      simp only [nodeAt, Option.some.injEq, PhyloTree.leaf.injEq] at hp
      simpa [labels] using hp.symm
    | cons c p => simp [nodeAt] at hp
  | fork l r ihl ihr =>
    cases p with
    | nil => simp [nodeAt] at hp
    | cons c p =>
      cases c
      · exact List.mem_append_left _ (ihl hp)
      · exact List.mem_append_right _ (ihr hp)

/-- Every label of `T` is carried by a leaf of `T`. -/
theorem exists_leaf_address {t : PhyloTree} {a : ℕ} (ha : a ∈ t.labels) :
    ∃ p, t.nodeAt p = some (.leaf a) := by
  induction t with
  | leaf b =>
    have h : a = b := by simpa [labels] using ha
    exact ⟨[], by simp [nodeAt, h]⟩
  | fork l r ihl ihr =>
    rcases List.mem_append.mp ha with hal | har
    · obtain ⟨p, hp⟩ := ihl hal
      exact ⟨false :: p, hp⟩
    · obtain ⟨p, hp⟩ := ihr har
      exact ⟨true :: p, hp⟩

/-- In a well-labelled tree, two leaves with the same label have the same address. -/
theorem leaf_address_unique {t : PhyloTree} (ht : t.WellLabelled)
    {p q : Address} {a : ℕ} (hp : t.nodeAt p = some (.leaf a))
    (hq : t.nodeAt q = some (.leaf a)) : p = q := by
  induction t generalizing p q with
  | leaf b =>
    cases p <;> cases q <;> simp_all [nodeAt]
  | fork l r ihl ihr =>
    have hnodup := List.nodup_append.mp ht
    cases p with
    | nil => simp [nodeAt] at hp
    | cons b p =>
      cases q with
      | nil => simp [nodeAt] at hq
      | cons c q =>
        cases b <;> cases c
        · exact congrArg (false :: ·) (ihl hnodup.1 hp hq)
        · exact False.elim (hnodup.2.2 a (leaf_label_mem (t := l) hp) a (leaf_label_mem (t := r) hq) rfl)
        · exact False.elim (hnodup.2.2 a (leaf_label_mem (t := l) hq) a (leaf_label_mem (t := r) hp) rfl)
        · exact congrArg (true :: ·) (ihr hnodup.2.1 hp hq)

end PhyloTree

namespace Realization

/-- The code of a vertex of `T` is at most `Realization.bound t`. -/
theorem code_le_bound {t : PhyloTree} {p : Address} (hp : p ∈ t.nodes) :
    Address.code p ≤ bound t := Finset.le_sup hp

/-- Donors are numbered above `Realization.bound t`. -/
theorem bound_lt_donor (t : PhyloTree) (e : Pair) : bound t < donor t e := by
  unfold donor
  omega

/-- Recipients are numbered above `Realization.bound t`. -/
theorem bound_lt_recipient (t : PhyloTree) (e : Pair) : bound t < recipient t e := by
  unfold recipient
  omega

/-- Distinct admissible pairs have distinct indices in the enumeration of
`EdgeAbove.candidates t`. -/
theorem index_injective (t : PhyloTree) : Set.InjOn (index t) (EdgeAbove.candidates t) := by
  intro e he f hf h
  apply (List.idxOf_inj (Finset.mem_toList.mpr he)).mp h

/-- Distinct admissible pairs have distinct donors. -/
theorem donor_injective (t : PhyloTree) : Set.InjOn (donor t) (EdgeAbove.candidates t) := by
  intro e he f hf h
  apply index_injective t he hf
  unfold donor at h
  omega

/-- Distinct admissible pairs have distinct recipients. -/
theorem recipient_injective (t : PhyloTree) :
    Set.InjOn (recipient t) (EdgeAbove.candidates t) := by
  intro e he f hf h
  apply index_injective t he hf
  unfold recipient at h
  omega

/-- No donor is a recipient: above `Realization.bound t`, donors have odd offsets and
recipients even ones. -/
theorem donor_ne_recipient (t : PhyloTree) (e f : Pair) : donor t e ≠ recipient t f := by
  unfold donor recipient
  omega

/-- A donor is not the code of a vertex of `T`. -/
theorem donor_ne_code {t : PhyloTree} (e : Pair) {p : Address} (hp : p ∈ t.nodes) :
    donor t e ≠ Address.code p := by
  have := code_le_bound hp
  have := bound_lt_donor t e
  omega

/-- A recipient is not the code of a vertex of `T`. -/
theorem recipient_ne_code {t : PhyloTree} (e : Pair) {p : Address} (hp : p ∈ t.nodes) :
    recipient t e ≠ Address.code p := by
  have := code_le_bound hp
  have := bound_lt_recipient t e
  omega

/-- A vertex `p` of `T` is in `Realization.cycleVertices t e`, the vertex set of the cycle
`γ(u, w)` for `e = (u, w)`, iff `p` is in the footprint `EdgeAbove.footprint t e`. -/
theorem code_mem_cycleVertices_iff {t : PhyloTree} {e : Pair} {p : Address}
    (hp : p ∈ t.nodes) :
    Address.code p ∈ cycleVertices t e ↔ p ∈ EdgeAbove.footprint t e := by
  classical
  simp only [cycleVertices, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
    Finset.mem_singleton]
  have hd := donor_ne_code e hp
  have hr := recipient_ne_code e hp
  constructor
  · rintro (⟨x, hx, hcode⟩ | hdonor | hrecipient)
    · exact Address.code_injective hcode ▸ hx
    · exact False.elim (hd hdonor.symm)
    · exact False.elim (hr hrecipient.symm)
  · intro h
    exact Or.inl ⟨p, h, rfl⟩

/-- Let `p ++ [b]` be a child of `p` in `T`, and `e = (u, w)`. The child of `p` on side `b` in
`T + e` (`Realization.child`: `u′` if `p ++ [b] = u`, `w′` if `p ++ [b] = w`, and `p ++ [b]`
otherwise) is a vertex of `γ(u, w)` iff `p ++ [b]` is `u`, is `w`, or is in the footprint of
`e`. This characterizes the test `l(x) ∉ γ(u, w)` of Equations (4) and (5)
(`Realization.offChild`), with the children `l(x)` and `r(x)` of Definition 5. -/
theorem child_mem_cycleVertices_iff {t : PhyloTree} {e : Pair} {p : Address}
    {b : Bool} (hp : p ++ [b] ∈ t.nodes) :
    child t e p b ∈ cycleVertices t e ↔
      p ++ [b] = e.1 ∨ p ++ [b] = e.2 ∨ p ++ [b] ∈ EdgeAbove.footprint t e := by
  classical
  by_cases hu : p ++ [b] = e.1
  · simp [child, hu, cycleVertices]
  · by_cases hw : p ++ [b] = e.2
    · simp only [child, ite_eq_right hu, ite_eq_left hw]
      simp [hw, cycleVertices]
    · simp [child, hu, hw, code_mem_cycleVertices_iff hp]

/-- For a label `a` of `T`, `Realization.leafAddress t a` is a leaf of `T` labelled `a`. -/
theorem leafAddress_nodeAt {t : PhyloTree} {a : ℕ} (ha : a ∈ t.taxa) :
    t.nodeAt (leafAddress t a) = some (.leaf a) := by
  classical
  obtain ⟨p, hp⟩ := PhyloTree.exists_leaf_address (List.mem_toFinset.mp ha)
  have hmem : p ∈ t.nodes := (t.mem_nodes_iff p).mpr ⟨_, hp⟩
  have hex : ((t.nodes.toList).find? (fun q => t.nodeAt q = some (.leaf a))).isSome := by
    rw [List.find?_isSome]
    exact ⟨p, Finset.mem_toList.mpr hmem, by simpa using hp⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hex
  have hnode : t.nodeAt q = some (.leaf a) := by simpa using List.find?_some hq
  simpa [leafAddress, hq] using hnode

/-- For a label `a` of `T`, `Realization.leafAddress t a` is a vertex of `T`. -/
theorem leafAddress_mem_nodes {t : PhyloTree} {a : ℕ} (ha : a ∈ t.taxa) :
    leafAddress t a ∈ t.nodes := (t.mem_nodes_iff _).mpr ⟨_, leafAddress_nodeAt ha⟩

/-- In a well-labelled tree, `Realization.leafAddress t a` is the address of the leaf
labelled `a`. -/
theorem leafAddress_eq {t : PhyloTree} (ht : t.WellLabelled) {p : Address} {a : ℕ}
    (hp : t.nodeAt p = some (.leaf a)) : leafAddress t a = p := by
  classical
  have hmem : p ∈ t.nodes := (t.mem_nodes_iff p).mpr ⟨_, hp⟩
  have hex : ((t.nodes.toList).find? (fun q => t.nodeAt q = some (.leaf a))).isSome := by
    rw [List.find?_isSome]
    exact ⟨p, Finset.mem_toList.mpr hmem, by simpa using hp⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hex
  have hnode : t.nodeAt q = some (.leaf a) := by
    simpa using List.find?_some hq
  have heq := t.leaf_address_unique ht hnode hp
  simp [leafAddress, hq, heq]

end Realization
end Camus
