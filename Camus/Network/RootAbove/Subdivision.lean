module

public import Camus.Network.RootAbove.Outgroup
public import Camus.Network.Completeness.Degrees
public import Camus.Network.Realization.Basic

/-!
# With an outgroup, the root of `T⁺` is the root of `N⁺`

Let `N` be built on `T` in the sense of Definition 1, through a displayed subdivision `H`: the
switching `S` is `T` subdivided, below a directed path, the root wire, from the root of `N` to the
root of `T`. Add an outgroup: a new taxon `z`, the tree `T⁺ = fork (leaf z) T`, and the network
`N⁺` with a new root `ρ` whose children are the root of `N` and a new leaf `ℓ` labelled `z`
(`RootedNetwork.withOutgroup`). Then `N⁺` is built on `T⁺` with the root of `T⁺` at its root
(`DisplayedSubdivision.toOutgroup`): the root of `T⁺` is `ρ`, the wire above the leaf `z` is the
edge from `ρ` to `ℓ`, and the wire above the root of `T` (the vertex `[true]` of `T⁺`) is the root
wire of `N`, preceded by `ρ`. The other wires are those of `H`.

So the completeness theorem applies to `N⁺`: it is isomorphic to the canonical network of its
pairs. These pairs do not involve the leaf `z`, whose wire has no interior vertex
(`DisplayedSubdivision.outgroup_extracted_mem`).

## Main results

* `DisplayedSubdivision.toOutgroup`: the support subdivision of `T⁺` in `N⁺`.
* `DisplayedSubdivision.outgroup_extracted_mem`: every pair extracted from `N⁺` is
  `(true :: u, true :: w)` for vertices `u`, `w` of `T`.
-/

@[expose] public section

namespace Camus

namespace PhyloTree

/-- The vertices of `T⁺ = fork (leaf z) T`: the root, the leaf `z` at `[false]`, and the vertices
`true :: p` for the vertices `p` of `T`. -/
theorem mem_outgroup_nodes {t : PhyloTree} {z : ℕ} {p : Address} :
    p ∈ (PhyloTree.fork (.leaf z) t).nodes ↔
      p = [] ∨ p = [false] ∨ ∃ p' ∈ t.nodes, p = true :: p' := by
  simp only [PhyloTree.nodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    Finset.mem_singleton]
  constructor
  · rintro (h | ⟨a, rfl, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨a, ha, rfl⟩)
  · rintro (h | rfl | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨[], rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨a, ha, rfl⟩)

/-- The taxa of `T⁺ = fork (leaf z) T` are `z` and the taxa of `T`. -/
theorem outgroup_taxa (t : PhyloTree) (z : ℕ) :
    (PhyloTree.fork (.leaf z) t).taxa = insert z t.taxa := by
  simp [taxa, labels]

end PhyloTree

/-- The parent of the vertex `true :: p` of `T⁺`, for `p` not the root of `T`, is
`true :: parent p`. -/
theorem parent_cons_true {p : Address} (hp : p ≠ []) : parent (true :: p) = true :: parent p := by
  cases p with
  | nil => exact absurd rfl hp
  | cons b p => simp [parent]

namespace DisplayedSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- The image of a vertex of `T` is a vertex of `N`. -/
theorem original_mem (H : DisplayedSubdivision t N S) {p : Address} (hp : p ∈ t.nodes) :
    H.original p ∈ N.vertices := by
  rw [H.vertices_covered]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp))

/-- An interior vertex of a wire is a vertex of `N`. -/
theorem interior_mem (H : DisplayedSubdivision t N S) {p : Address} (hp : p ∈ t.nodes)
    (hp0 : p ≠ []) {v : ℕ} (hv : v ∈ wireInterior (H.wire p)) : v ∈ N.vertices := by
  rw [H.vertices_covered]
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨p, Finset.mem_erase.mpr ⟨hp0, hp⟩, hv⟩))

/-- The root wire is not empty: it starts at the root of `N`. -/
theorem rootWire_ne_nil (H : DisplayedSubdivision t N S) : H.rootWire ≠ [] := by
  intro h
  have hhead := H.rootWire_laws.2.1
  rw [h] at hhead
  simp at hhead

/-- The root wire is the root of `N` followed by the rest of the root wire. -/
theorem rootWire_eq_cons (H : DisplayedSubdivision t N S) :
    H.rootWire = N.root :: H.rootWire.tail := by
  have hhead := H.rootWire_laws.2.1
  cases h : H.rootWire with
  | nil => exact absurd h H.rootWire_ne_nil
  | cons x xs =>
    rw [h] at hhead
    simp only [List.head?_cons, Option.some.injEq] at hhead
    rw [hhead, List.tail_cons]

/-- The vertices of the root wire are vertices of `N`. -/
theorem rootWire_mem (H : DisplayedSubdivision t N S) {v : ℕ} (hv : v ∈ H.rootWire) :
    v ∈ N.vertices := by
  rw [← List.dropLast_append_getLast H.rootWire_ne_nil] at hv
  rcases List.mem_append.mp hv with h | h
  · rw [H.vertices_covered]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr h)
  · have hlast := H.rootWire_laws.2.2.1
    rw [List.getLast?_eq_some_getLast H.rootWire_ne_nil, Option.some.injEq] at hlast
    rw [List.mem_singleton.mp h, hlast]
    exact H.original_mem t.root_mem_nodes

/-- The vertex of `N⁺` at the vertex `p` of `T⁺ = fork (leaf z) T`: the new root `ρ` at the root,
the new leaf `ℓ` at the leaf `z`, and `H.original p'` at `true :: p'`. -/
def outgroupOriginal (H : DisplayedSubdivision t N S) (ρ ℓ : ℕ) : Address → ℕ
  | [] => ρ
  | false :: _ => ℓ
  | true :: p => H.original p

/-- The wire of `N⁺` above the vertex `p` of `T⁺ = fork (leaf z) T`: the edge from `ρ` to `ℓ` above
the leaf `z`, the root wire of `N` preceded by `ρ` above the root of `T` (the vertex `[true]`), and
`H.wire p'` above `true :: p'` otherwise. -/
def outgroupWire (H : DisplayedSubdivision t N S) (ρ ℓ : ℕ) : Address → List ℕ
  | [] => []
  | [false] => [ρ, ℓ]
  | false :: _ :: _ => []
  | [true] => ρ :: H.rootWire
  | true :: b :: p => H.wire (b :: p)

/-- Below the root of `T`, the wires of `N⁺` are those of `H`. -/
theorem outgroupWire_cons_true (H : DisplayedSubdivision t N S) (ρ ℓ : ℕ) {p : Address}
    (hp : p ≠ []) : H.outgroupWire ρ ℓ (true :: p) = H.wire p := by
  cases p with
  | nil => exact absurd rfl hp
  | cons b p => rfl

/-- The images of the vertices of `T⁺` in `N⁺`: `ρ`, `ℓ`, and the images of the vertices of
`T`. -/
theorem mem_outgroup_image (H : DisplayedSubdivision t N S) {z ρ ℓ v : ℕ} :
    v ∈ (PhyloTree.fork (.leaf z) t).nodes.image (H.outgroupOriginal ρ ℓ) ↔
      v = ρ ∨ v = ℓ ∨ v ∈ t.nodes.image H.original := by
  simp only [Finset.mem_image, PhyloTree.mem_outgroup_nodes]
  constructor
  · rintro ⟨p, hp | hp | ⟨p', hp', rfl⟩, rfl⟩
    · subst hp
      exact Or.inl rfl
    · subst hp
      exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨p', hp', rfl⟩)
  · rintro (rfl | rfl | ⟨p', hp', rfl⟩)
    · exact ⟨[], Or.inl rfl, rfl⟩
    · exact ⟨[false], Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨true :: p', Or.inr (Or.inr ⟨p', hp', rfl⟩), rfl⟩

/-- A set of vertices of `N` that avoids the images of the vertices of `T` avoids the images of
the vertices of `T⁺`. -/
theorem disjoint_outgroup_image (H : DisplayedSubdivision t N S) {z ρ ℓ : ℕ}
    (hρ : ρ ∉ N.vertices) (hℓ : ℓ ∉ N.vertices) {X : Finset ℕ}
    (hX : ∀ v ∈ X, v ∈ N.vertices) (hd : Disjoint X (t.nodes.image H.original)) :
    Disjoint X ((PhyloTree.fork (.leaf z) t).nodes.image (H.outgroupOriginal ρ ℓ)) := by
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  rcases (H.mem_outgroup_image).mp hv' with rfl | rfl | h
  · exact hρ (hX _ hv)
  · exact hℓ (hX _ hv)
  · exact Finset.disjoint_left.mp hd hv h

/-- The support subdivision of `T⁺ = fork (leaf z) T` in `N⁺`, with switching `S` and the two
edges out of `ρ`, which keeps the root: the root of `T⁺` is the root `ρ` of `N⁺`, the wire above
the leaf `z` is the edge from `ρ` to `ℓ`, the wire above the root of `T` is the root wire of `N`
preceded by `ρ`, and the other wires are those of `H`. -/
noncomputable def toOutgroup (H : DisplayedSubdivision t N S) (hN : N.RootedBinaryLevelOne)
    {z ρ ℓ : ℕ} (hρ : ρ ∉ N.vertices) (hℓ : ℓ ∉ N.vertices) (hρℓ : ρ ≠ ℓ) (hz : z ∉ t.taxa) :
    SupportSubdivision (.fork (.leaf z) t) (N.withOutgroup z ρ ℓ)
      (insert (ρ, N.root) (insert (ρ, ℓ) S)) where
  original := H.outgroupOriginal ρ ℓ
  wire := H.outgroupWire ρ ℓ
  original_injective := by
    intro p hp q hq hpq
    have hp' := PhyloTree.mem_outgroup_nodes.mp hp
    have hq' := PhyloTree.mem_outgroup_nodes.mp hq
    rcases hp' with rfl | rfl | ⟨p', hp', rfl⟩ <;>
      rcases hq' with rfl | rfl | ⟨q', hq', rfl⟩ <;>
      simp only [outgroupOriginal] at hpq
    · rfl
    · exact absurd hpq hρℓ
    · exact absurd (hpq ▸ H.original_mem hq') hρ
    · exact absurd hpq.symm hρℓ
    · rfl
    · exact absurd (hpq ▸ H.original_mem hq') hℓ
    · exact absurd (hpq.symm ▸ H.original_mem hp') hρ
    · exact absurd (hpq.symm ▸ H.original_mem hp') hℓ
    · rw [H.original_injective hp' hq' hpq]
  root_preserved := rfl
  taxa_preserved := by
    change insert z N.taxa = _
    rw [PhyloTree.outgroup_taxa, H.taxa_preserved]
  leaves_preserved := by
    intro p hp a hleaf
    rcases PhyloTree.mem_outgroup_nodes.mp hp with rfl | rfl | ⟨p', hp', rfl⟩
    · simp [PhyloTree.nodeAt] at hleaf
    · simp only [PhyloTree.nodeAt, Option.some.injEq, PhyloTree.leaf.injEq] at hleaf
      subst hleaf
      change ℓ = if z = z then ℓ else N.leaf z
      rw [ite_eq_left rfl]
    · have hat : a ∈ t.taxa := List.mem_toFinset.mpr (PhyloTree.leaf_label_mem hleaf)
      have haz : a ≠ z := fun h => hz (h ▸ hat)
      change H.original p' = if a = z then ℓ else N.leaf a
      rw [ite_eq_right haz]
      exact H.leaves_preserved p' hp' a hleaf
  wire_laws := by
    intro p hp hp0
    rcases PhyloTree.mem_outgroup_nodes.mp hp with rfl | rfl | ⟨p', hp', rfl⟩
    · exact absurd rfl hp0
    -- the edge from `ρ` to `ℓ` above the leaf `z`
    · refine ⟨by simp [outgroupWire], by simp [outgroupWire, hρℓ], rfl, rfl, ?_⟩
      simp [outgroupWire, wireInterior]
    · by_cases hp'0 : p' = []
      -- the root wire of `N`, preceded by `ρ`, above the root of `T`
      · subst hp'0
        have hne := H.rootWire_ne_nil
        refine ⟨?_, ?_, rfl, ?_, ?_⟩
        · change 2 ≤ (ρ :: H.rootWire).length
          have : 0 < H.rootWire.length := List.length_pos_iff.mpr hne
          simp only [List.length_cons]
          omega
        · change (ρ :: H.rootWire).Nodup
          exact List.nodup_cons.mpr ⟨fun h => hρ (H.rootWire_mem h), H.rootWire_laws.1⟩
        · change (ρ :: H.rootWire).getLast? = some (H.original [])
          rw [List.getLast?_cons, H.rootWire_laws.2.2.1]
          rfl
        · change Disjoint H.rootWire.dropLast.toFinset _
          apply H.disjoint_outgroup_image hρ hℓ
          · intro v hv
            exact H.rootWire_mem (List.dropLast_subset _ (List.mem_toFinset.mp hv))
          · exact H.rootWire_laws.2.2.2
      -- the wires of `H` below the root of `T`
      · rw [H.outgroupWire_cons_true ρ ℓ hp'0, parent_cons_true hp'0]
        obtain ⟨h1, h2, h3, h4, h5⟩ := H.wire_laws p' hp' hp'0
        refine ⟨h1, h2, h3, h4, ?_⟩
        exact H.disjoint_outgroup_image hρ hℓ (fun v hv => H.interior_mem hp' hp'0 hv) h5
  interiors_disjoint := by
    intro p hp q hq hpq
    obtain ⟨hp0, hp⟩ := Finset.mem_erase.mp hp
    obtain ⟨hq0, hq⟩ := Finset.mem_erase.mp hq
    have hfalse : wireInterior (H.outgroupWire ρ ℓ [false]) = ∅ := by
      simp [outgroupWire, wireInterior]
    rcases PhyloTree.mem_outgroup_nodes.mp hp with rfl | rfl | ⟨p', hp', rfl⟩
    · exact absurd rfl hp0
    · rw [hfalse]
      exact Finset.disjoint_empty_left _
    rcases PhyloTree.mem_outgroup_nodes.mp hq with rfl | rfl | ⟨q', hq', rfl⟩
    · exact absurd rfl hq0
    · rw [hfalse]
      exact Finset.disjoint_empty_right _
    have hpq' : p' ≠ q' := fun h => hpq (h ▸ rfl)
    by_cases hp'0 : p' = [] <;> by_cases hq'0 : q' = []
    · exact absurd (hp'0.trans hq'0.symm) hpq'
    · subst hp'0
      rw [H.outgroupWire_cons_true ρ ℓ hq'0]
      exact H.rootWire_disjoint q' hq' hq'0
    · subst hq'0
      rw [H.outgroupWire_cons_true ρ ℓ hp'0]
      exact (H.rootWire_disjoint p' hp' hp'0).symm
    · rw [H.outgroupWire_cons_true ρ ℓ hp'0, H.outgroupWire_cons_true ρ ℓ hq'0]
      exact H.interiors_disjoint (Finset.mem_erase.mpr ⟨hp'0, hp'⟩)
        (Finset.mem_erase.mpr ⟨hq'0, hq'⟩) hpq'
  vertices_covered := by
    ext v
    rw [RootedNetwork.withOutgroup_mem_vertices, Finset.mem_union, H.mem_outgroup_image,
      Finset.mem_biUnion]
    have hcov := H.vertices_covered
    constructor
    · rintro (rfl | rfl | hv)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr (Or.inl rfl))
      · rw [hcov, Finset.mem_union, Finset.mem_union, Finset.mem_biUnion] at hv
        rcases hv with (hv | ⟨p, hp, hv⟩) | hv
        · exact Or.inl (Or.inr (Or.inr hv))
        · obtain ⟨hp0, hp⟩ := Finset.mem_erase.mp hp
          refine Or.inr ⟨true :: p, Finset.mem_erase.mpr ⟨by simp,
            PhyloTree.mem_outgroup_nodes.mpr (Or.inr (Or.inr ⟨p, hp, rfl⟩))⟩, ?_⟩
          rw [H.outgroupWire_cons_true ρ ℓ hp0]
          exact hv
        · exact Or.inr ⟨[true], Finset.mem_erase.mpr ⟨by simp,
            PhyloTree.mem_outgroup_nodes.mpr (Or.inr (Or.inr ⟨[], t.root_mem_nodes, rfl⟩))⟩, hv⟩
    · rintro ((rfl | rfl | hv) | ⟨p, hp, hv⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
        exact Or.inr (Or.inr (H.original_mem hp))
      · obtain ⟨hp0, hp⟩ := Finset.mem_erase.mp hp
        rcases PhyloTree.mem_outgroup_nodes.mp hp with rfl | rfl | ⟨p', hp', rfl⟩
        · exact absurd rfl hp0
        · simp [outgroupWire, wireInterior] at hv
        · by_cases hp'0 : p' = []
          · subst hp'0
            change v ∈ H.rootWire.dropLast.toFinset at hv
            exact Or.inr (Or.inr (H.rootWire_mem
              (List.dropLast_subset _ (List.mem_toFinset.mp hv))))
          · rw [H.outgroupWire_cons_true ρ ℓ hp'0] at hv
            exact Or.inr (Or.inr (H.interior_mem hp' hp'0 hv))
  edges_covered := by
    ext e
    rw [Finset.mem_insert, Finset.mem_insert, Finset.ext_iff.mp H.edges_covered e,
      Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
    have hroot : wireEdges (H.outgroupWire ρ ℓ [true]) =
        insert (ρ, N.root) (wireEdges H.rootWire) := by
      change wireEdges (ρ :: H.rootWire) = _
      rw [H.rootWire_eq_cons]
      simp [wireEdges]
    have hleaf : wireEdges (H.outgroupWire ρ ℓ [false]) = {(ρ, ℓ)} := by
      simp [outgroupWire, wireEdges]
    have htrue : [true] ∈ ((PhyloTree.fork (.leaf z) t).nodes.erase []) :=
      Finset.mem_erase.mpr ⟨by simp,
        PhyloTree.mem_outgroup_nodes.mpr (Or.inr (Or.inr ⟨[], t.root_mem_nodes, rfl⟩))⟩
    have hfalse : [false] ∈ ((PhyloTree.fork (.leaf z) t).nodes.erase []) :=
      Finset.mem_erase.mpr ⟨by simp, PhyloTree.mem_outgroup_nodes.mpr (Or.inr (Or.inl rfl))⟩
    constructor
    · rintro (rfl | rfl | (⟨p, hp, he⟩ | he))
      · exact ⟨[true], htrue, by rw [hroot]; exact Finset.mem_insert_self _ _⟩
      · exact ⟨[false], hfalse, by rw [hleaf]; exact Finset.mem_singleton_self _⟩
      · obtain ⟨hp0, hp⟩ := Finset.mem_erase.mp hp
        refine ⟨true :: p, Finset.mem_erase.mpr ⟨by simp,
          PhyloTree.mem_outgroup_nodes.mpr (Or.inr (Or.inr ⟨p, hp, rfl⟩))⟩, ?_⟩
        rw [H.outgroupWire_cons_true ρ ℓ hp0]
        exact he
      · exact ⟨[true], htrue, by rw [hroot]; exact Finset.mem_insert_of_mem he⟩
    · rintro ⟨p, hp, he⟩
      obtain ⟨hp0, hp⟩ := Finset.mem_erase.mp hp
      rcases PhyloTree.mem_outgroup_nodes.mp hp with rfl | rfl | ⟨p', hp', rfl⟩
      · exact absurd rfl hp0
      · rw [hleaf, Finset.mem_singleton] at he
        exact Or.inr (Or.inl he)
      · by_cases hp'0 : p' = []
        · subst hp'0
          rw [hroot, Finset.mem_insert] at he
          rcases he with he | he
          · exact Or.inl he
          · exact Or.inr (Or.inr (Or.inr he))
        · rw [H.outgroupWire_cons_true ρ ℓ hp'0] at he
          exact Or.inr (Or.inr (Or.inl ⟨p', Finset.mem_erase.mpr ⟨hp'0, hp'⟩, he⟩))
  switching := RootedNetwork.withOutgroup_switching hN hρ hℓ H.switching

/-- The pairs extracted from `N⁺` through `H.toOutgroup` (the pairs `(u, w)` of vertices of `T⁺`
directly below the two ends of its non-tree edges) are pairs `(true :: u, true :: w)` of vertices
of `T` below `[true]`. Each end of a non-tree edge lies inside the wire of its anchor, and the
wire above the leaf `z` has no interior vertex. -/
theorem outgroup_extracted_mem (H : DisplayedSubdivision t N S) (hN : N.RootedBinaryLevelOne)
    {z ρ ℓ : ℕ} (hρ : ρ ∉ N.vertices) (hℓ : ℓ ∉ N.vertices) (hρℓ : ρ ≠ ℓ) (hz : z ∉ t.taxa)
    {e : Address × Address} (he : e ∈ (H.toOutgroup hN hρ hℓ hρℓ hz).extracted) :
    ∃ u ∈ t.nodes, ∃ w ∈ t.nodes, e = (true :: u, true :: w) := by
  classical
  have hzN : z ∉ N.taxa := H.taxa_preserved ▸ hz
  have hN' := RootedNetwork.withOutgroup_levelOne hN hρ hℓ hρℓ hzN
  set H' := H.toOutgroup hN hρ hℓ hρℓ hz with hH'
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
  -- the anchor of a vertex inside a wire is not the leaf `z`, whose wire has no interior vertex
  have hanchor : ∀ v, H'.anchor v ∈ (PhyloTree.fork (.leaf z) t).nodes → H'.anchor v ≠ [] →
      v ∈ wireInterior (H'.wire (H'.anchor v)) → ∃ u ∈ t.nodes, H'.anchor v = true :: u := by
    intro v hv hv0 hint
    rcases PhyloTree.mem_outgroup_nodes.mp hv with h | h | h
    · exact absurd h hv0
    · rw [h] at hint
      change v ∈ wireInterior (H.outgroupWire ρ ℓ [false]) at hint
      simp [outgroupWire, wireInterior] at hint
    · exact h
  obtain ⟨hs1, hs2, hs3⟩ := H'.deleted_source_anchor_spec hN' hd
  obtain ⟨ht1, ht2, ht3⟩ := H'.deleted_target_anchor_spec hN' hd
  obtain ⟨u, hu, hequ⟩ := hanchor _ hs1 hs2 hs3
  obtain ⟨w, hw, heqw⟩ := hanchor _ ht1 ht2 ht3
  exact ⟨u, hu, w, hw, Prod.ext hequ heqw⟩

end DisplayedSubdivision

end Camus
