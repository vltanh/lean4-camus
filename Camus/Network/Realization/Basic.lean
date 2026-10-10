module

public import Camus.Network.Code
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Find

@[expose] public section

namespace Camus

namespace PhyloTree

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

theorem code_le_bound {t : PhyloTree} {p : Address} (hp : p ∈ t.nodes) :
    Address.code p ≤ bound t := Finset.le_sup hp

theorem bound_lt_donor (t : PhyloTree) (e : Pair) : bound t < donor t e := by
  unfold donor
  omega

theorem bound_lt_recipient (t : PhyloTree) (e : Pair) : bound t < recipient t e := by
  unfold recipient
  omega

theorem index_injective (t : PhyloTree) : Set.InjOn (index t) (EdgeAbove.candidates t) := by
  intro e he f hf h
  apply (List.idxOf_inj (Finset.mem_toList.mpr he)).mp h

theorem donor_injective (t : PhyloTree) : Set.InjOn (donor t) (EdgeAbove.candidates t) := by
  intro e he f hf h
  apply index_injective t he hf
  unfold donor at h
  omega

theorem recipient_injective (t : PhyloTree) :
    Set.InjOn (recipient t) (EdgeAbove.candidates t) := by
  intro e he f hf h
  apply index_injective t he hf
  unfold recipient at h
  omega

theorem donor_ne_recipient (t : PhyloTree) (e f : Pair) : donor t e ≠ recipient t f := by
  unfold donor recipient
  omega

theorem donor_ne_code {t : PhyloTree} (e : Pair) {p : Address} (hp : p ∈ t.nodes) :
    donor t e ≠ Address.code p := by
  have := code_le_bound hp
  have := bound_lt_donor t e
  omega

theorem recipient_ne_code {t : PhyloTree} (e : Pair) {p : Address} (hp : p ∈ t.nodes) :
    recipient t e ≠ Address.code p := by
  have := code_le_bound hp
  have := bound_lt_recipient t e
  omega

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

theorem leafAddress_mem_nodes {t : PhyloTree} {a : ℕ} (ha : a ∈ t.taxa) :
    leafAddress t a ∈ t.nodes := (t.mem_nodes_iff _).mpr ⟨_, leafAddress_nodeAt ha⟩

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
