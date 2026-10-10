module

public import Camus.Network.RootAbove.RootWire

/-!
# Gluing displayed subdivisions

A displayed subdivision of `T` in `N` (`DisplayedSubdivision`) presents a switching of `N` as `T`
with each edge replaced by a directed path (a wire), below a directed path from the root of `N`
to the root of `T` (the root wire). This file builds such presentations from smaller ones, in the
three ways a switching branches at a vertex `v`: `v` is a labelled leaf
(`DisplayedSubdivision.single`); `v` has one child, and the root wire grows by `v`
(`DisplayedSubdivision.extendRoot`); `v` has two children, below which lie the trees `T₁` and
`T₂`, and `v` becomes the root of `fork T₁ T₂`, with the root wires of `T₁` and `T₂`, preceded by
`v`, as the wires above the roots of `T₁` and `T₂` (`DisplayedSubdivision.join`). The networks are
arbitrary: the hypotheses say how the vertices, the edges of the switching and the taxa of the
glued network are made of those of the parts. `DisplayedSubdivision.congr` transports a displayed
subdivision along equalities of the data of the networks.

## Main results

* `DisplayedSubdivision.single`: the one-leaf tree.
* `DisplayedSubdivision.extendRoot`: a vertex with one child, added above the root wire.
* `DisplayedSubdivision.join`: a vertex with two children, the root of `fork T₁ T₂`.
* `DisplayedSubdivision.congr`: transport along equal data.
-/

@[expose] public section

namespace Camus

/-- The parent of `b :: p` is `b :: parent p` when `p` is not the root. -/
theorem parent_cons_of_ne_nil (b : Bool) {p : Address} (hp : p ≠ []) :
    parent (b :: p) = b :: parent p := by
  cases p with
  | nil => exact absurd rfl hp
  | cons c p => simp [parent]

namespace PhyloTree

/-- The vertices of `fork l r`: the root, `false :: q` for the vertices `q` of `l`, and
`true :: q` for the vertices `q` of `r`. -/
theorem mem_fork_nodes {l r : PhyloTree} {p : Address} :
    p ∈ (PhyloTree.fork l r).nodes ↔
      p = [] ∨ (∃ q ∈ l.nodes, p = false :: q) ∨ ∃ q ∈ r.nodes, p = true :: q := by
  simp only [nodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
    · exact Or.inr (Or.inr ⟨q, hq, rfl⟩)
  · rintro (h | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
    · exact Or.inr (Or.inr ⟨q, hq, rfl⟩)

/-- The vertices of `fork l r` other than the root: `false :: q` for the vertices `q` of `l`, and
`true :: q` for the vertices `q` of `r`. -/
theorem mem_fork_nodes_erase {l r : PhyloTree} {p : Address} :
    p ∈ (PhyloTree.fork l r).nodes.erase [] ↔
      (∃ q ∈ l.nodes, p = false :: q) ∨ ∃ q ∈ r.nodes, p = true :: q := by
  rw [Finset.mem_erase, mem_fork_nodes]
  constructor
  · rintro ⟨hp, h | h | h⟩
    · exact absurd h hp
    · exact Or.inl h
    · exact Or.inr h
  · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact ⟨List.cons_ne_nil _ _, Or.inr (Or.inl ⟨q, hq, rfl⟩)⟩
    · exact ⟨List.cons_ne_nil _ _, Or.inr (Or.inr ⟨q, hq, rfl⟩)⟩

end PhyloTree

namespace DisplayedSubdivision

/-- The vertex of the glued network at the vertex `p` of `fork T₁ T₂`: the root `v` at the root,
`o₁ q` at `false :: q` and `o₂ q` at `true :: q`. -/
def forkOriginal (v : ℕ) (o₁ o₂ : Address → ℕ) : Address → ℕ
  | [] => v
  | false :: p => o₁ p
  | true :: p => o₂ p

/-- The wire of the glued network above the vertex `p` of `fork T₁ T₂`: above the roots of `T₁`
and `T₂`, the root `v` followed by the root wires `r₁` and `r₂`; below, the wires `w₁` and
`w₂`. -/
def forkWire (v : ℕ) (r₁ r₂ : List ℕ) (w₁ w₂ : Address → List ℕ) : Address → List ℕ
  | [] => []
  | [false] => v :: r₁
  | false :: b :: p => w₁ (b :: p)
  | [true] => v :: r₂
  | true :: b :: p => w₂ (b :: p)

/-- Below the root of `T₁`, the wires of the glued network are those of `T₁`. -/
theorem forkWire_false {v : ℕ} {r₁ r₂ : List ℕ} {w₁ w₂ : Address → List ℕ} {p : Address}
    (hp : p ≠ []) : forkWire v r₁ r₂ w₁ w₂ (false :: p) = w₁ p := by
  cases p with
  | nil => exact absurd rfl hp
  | cons b p => rfl

/-- Below the root of `T₂`, the wires of the glued network are those of `T₂`. -/
theorem forkWire_true {v : ℕ} {r₁ r₂ : List ℕ} {w₁ w₂ : Address → List ℕ} {p : Address}
    (hp : p ≠ []) : forkWire v r₁ r₂ w₁ w₂ (true :: p) = w₂ p := by
  cases p with
  | nil => exact absurd rfl hp
  | cons b p => rfl

/-- The images of the vertices of `fork T₁ T₂`: the root `v` and the images of the vertices of
`T₁` and `T₂`. -/
theorem forkImage_eq (t₁ t₂ : PhyloTree) (v : ℕ) (o₁ o₂ : Address → ℕ) :
    (PhyloTree.fork t₁ t₂).nodes.image (forkOriginal v o₁ o₂) =
      insert v (t₁.nodes.image o₁ ∪ t₂.nodes.image o₂) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_union, PhyloTree.mem_fork_nodes]
  constructor
  · rintro ⟨p, rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
    · exact Or.inr (Or.inr ⟨q, hq, rfl⟩)
  · rintro (rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact ⟨[], Or.inl rfl, rfl⟩
    · exact ⟨false :: q, Or.inr (Or.inl ⟨q, hq, rfl⟩), rfl⟩
    · exact ⟨true :: q, Or.inr (Or.inr ⟨q, hq, rfl⟩), rfl⟩

/-- A union over the wires of the glued network splits into the wires above the roots of `T₁` and
`T₂` and the wires of `T₁` and `T₂`. -/
theorem mem_forkWire_biUnion {α : Type*} [DecidableEq α] (G : List ℕ → Finset α)
    {t₁ t₂ : PhyloTree} {v : ℕ} {r₁ r₂ : List ℕ} {w₁ w₂ : Address → List ℕ} {x : α} :
    x ∈ ((PhyloTree.fork t₁ t₂).nodes.erase []).biUnion
        (fun p => G (forkWire v r₁ r₂ w₁ w₂ p)) ↔
      x ∈ G (v :: r₁) ∨ x ∈ (t₁.nodes.erase []).biUnion (fun p => G (w₁ p)) ∨
        x ∈ G (v :: r₂) ∨ x ∈ (t₂.nodes.erase []).biUnion (fun p => G (w₂ p)) := by
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, hx⟩
    rcases PhyloTree.mem_fork_nodes_erase.mp hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · by_cases hq0 : q = []
      · subst hq0
        exact Or.inl hx
      · rw [forkWire_false hq0] at hx
        exact Or.inr (Or.inl ⟨q, Finset.mem_erase.mpr ⟨hq0, hq⟩, hx⟩)
    · by_cases hq0 : q = []
      · subst hq0
        exact Or.inr (Or.inr (Or.inl hx))
      · rw [forkWire_true hq0] at hx
        exact Or.inr (Or.inr (Or.inr ⟨q, Finset.mem_erase.mpr ⟨hq0, hq⟩, hx⟩))
  · rintro (hx | ⟨q, hq, hx⟩ | hx | ⟨q, hq, hx⟩)
    · exact ⟨[false], PhyloTree.mem_fork_nodes_erase.mpr (Or.inl ⟨[], t₁.root_mem_nodes, rfl⟩),
        hx⟩
    · obtain ⟨hq0, hq⟩ := Finset.mem_erase.mp hq
      exact ⟨false :: q, PhyloTree.mem_fork_nodes_erase.mpr (Or.inl ⟨q, hq, rfl⟩),
        by rw [forkWire_false hq0]; exact hx⟩
    · exact ⟨[true], PhyloTree.mem_fork_nodes_erase.mpr (Or.inr ⟨[], t₂.root_mem_nodes, rfl⟩),
        hx⟩
    · obtain ⟨hq0, hq⟩ := Finset.mem_erase.mp hq
      exact ⟨true :: q, PhyloTree.mem_fork_nodes_erase.mpr (Or.inr ⟨q, hq, rfl⟩),
        by rw [forkWire_true hq0]; exact hx⟩

/-- The interior vertices of the path `v, L` are the vertices of `L` but its last one. -/
theorem wireInterior_cons (v : ℕ) (L : List ℕ) : wireInterior (v :: L) = L.dropLast.toFinset :=
  rfl

/-- A path with one vertex has no edge. -/
theorem wireEdges_singleton (v : ℕ) : wireEdges [v] = ∅ := by
  simp [wireEdges]

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- The images of the vertices of `T` are vertices of `N`. -/
theorem image_subset (H : DisplayedSubdivision t N S) : t.nodes.image H.original ⊆ N.vertices := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact H.original_mem hp

/-- The vertices of the root wire other than its last one are vertices of `N`. -/
theorem rootWire_dropLast_mem (H : DisplayedSubdivision t N S) {x : ℕ}
    (hx : x ∈ H.rootWire.dropLast.toFinset) : x ∈ N.vertices :=
  H.rootWire_mem (List.dropLast_subset _ (List.mem_toFinset.mp hx))

/-- The root wire preceded by a new vertex `v` keeps its last vertex. -/
theorem getLast?_cons_rootWire (H : DisplayedSubdivision t N S) (v : ℕ) :
    (v :: H.rootWire).getLast? = some (H.original []) := by
  rw [List.getLast?_cons, H.rootWire_laws.2.2.1]
  rfl

/-- The root wire preceded by a new vertex `v`, without its last vertex, is `v` followed by the
root wire without its last vertex. -/
theorem dropLast_cons_rootWire (H : DisplayedSubdivision t N S) (v : ℕ) :
    (v :: H.rootWire).dropLast = v :: H.rootWire.dropLast :=
  List.dropLast_cons_of_ne_nil H.rootWire_ne_nil

/-- The edges of the root wire preceded by a new vertex `v`: the edge from `v` to the root of `N`
and the edges of the root wire. -/
theorem wireEdges_cons_rootWire (H : DisplayedSubdivision t N S) (v : ℕ) :
    wireEdges (v :: H.rootWire) = insert (v, N.root) (wireEdges H.rootWire) := by
  rw [H.rootWire_eq_cons, Realization.wireEdges_cons_cons]

/-- The root wire preceded by a vertex `v` outside `N` is a wire from `v` to the image of the root
of `T`, whose interior vertices are not `v` and are not images of vertices of `T` or vertices of a
set `Y` disjoint from the vertices of `N`. -/
theorem topWire_laws (H : DisplayedSubdivision t N S) {v : ℕ} (hv : v ∉ N.vertices)
    {Y : Finset ℕ} (hY : Disjoint N.vertices Y) :
    2 ≤ (v :: H.rootWire).length ∧ (v :: H.rootWire).Nodup ∧
      (v :: H.rootWire).head? = some v ∧ (v :: H.rootWire).getLast? = some (H.original []) ∧
      Disjoint (wireInterior (v :: H.rootWire)) (insert v (t.nodes.image H.original ∪ Y)) := by
  have hpos : 0 < H.rootWire.length := List.length_pos_iff.mpr H.rootWire_ne_nil
  refine ⟨by simp only [List.length_cons]; omega,
    List.nodup_cons.mpr ⟨fun h => hv (H.rootWire_mem h), H.rootWire_laws.1⟩, rfl,
    H.getLast?_cons_rootWire v, ?_⟩
  change Disjoint H.rootWire.dropLast.toFinset _
  refine Finset.disjoint_left.mpr fun x hx hx' => ?_
  have hxN := H.rootWire_dropLast_mem hx
  rcases Finset.mem_insert.mp hx' with rfl | hx'
  · exact hv hxN
  rcases Finset.mem_union.mp hx' with h | h
  · exact Finset.disjoint_left.mp H.rootWire_laws.2.2.2 hx h
  · exact Finset.disjoint_left.mp hY hxN h

/-- The interior vertices of the wire above a non-root vertex of `T` are not a vertex `v` outside
`N`, not images of vertices of `T`, and not vertices of a set `Y` disjoint from the vertices of
`N`. -/
theorem innerWire_disjoint (H : DisplayedSubdivision t N S) {p : Address} (hp : p ∈ t.nodes)
    (hp0 : p ≠ []) {v : ℕ} (hv : v ∉ N.vertices) {Y : Finset ℕ} (hY : Disjoint N.vertices Y) :
    Disjoint (wireInterior (H.wire p)) (insert v (t.nodes.image H.original ∪ Y)) := by
  refine Finset.disjoint_left.mpr fun x hx hx' => ?_
  have hxN := H.interior_mem hp hp0 hx
  rcases Finset.mem_insert.mp hx' with rfl | hx'
  · exact hv hxN
  rcases Finset.mem_union.mp hx' with h | h
  · exact Finset.disjoint_left.mp (H.wire_laws p hp hp0).2.2.2.2 hx h
  · exact Finset.disjoint_left.mp hY hxN h

/-- A displayed subdivision of the one-leaf tree `leaf a` in a network with one vertex, the root,
which is the leaf of `a`, and no edge. -/
def single (a : ℕ) {N : RootedNetwork} {S : Finset (ℕ × ℕ)}
    (hvert : N.vertices = {N.root}) (hedges : S = ∅) (htaxa : N.taxa = {a})
    (hleaf : N.leaf a = N.root) (hsw : N.Switching S) :
    DisplayedSubdivision (.leaf a) N S where
  original := fun _ => N.root
  wire := fun _ => []
  rootWire := [N.root]
  original_injective := by
    intro p hp q hq _
    simp only [PhyloTree.nodes, Finset.coe_singleton, Set.mem_singleton_iff] at hp hq
    rw [hp, hq]
  taxa_preserved := by
    rw [htaxa]
    rfl
  leaves_preserved := by
    intro p hp b hb
    simp only [PhyloTree.nodes, Finset.mem_singleton] at hp
    subst hp
    simp only [PhyloTree.nodeAt, Option.some.injEq, PhyloTree.leaf.injEq] at hb
    subst hb
    exact hleaf.symm
  rootWire_laws := ⟨List.nodup_singleton _, rfl, rfl, by simp⟩
  wire_laws := by
    intro p hp hp0
    simp only [PhyloTree.nodes, Finset.mem_singleton] at hp
    exact absurd hp hp0
  interiors_disjoint := by
    intro p hp
    simp [PhyloTree.nodes] at hp
  rootWire_disjoint := by
    intro p hp hp0
    simp only [PhyloTree.nodes, Finset.mem_singleton] at hp
    exact absurd hp hp0
  vertices_covered := by
    rw [hvert]
    simp [PhyloTree.nodes]
  edges_covered := by
    rw [hedges]
    simp [PhyloTree.nodes, wireEdges]
  switching := hsw

/-- A displayed subdivision of `T` in `N₁` extends to the network `N₀` with one more vertex, the
root of `N₀`, whose only edge in the switching goes to the root of `N₁`: the root wire is
preceded by the root of `N₀`. -/
def extendRoot {N₀ N₁ : RootedNetwork} {S₀ S₁ : Finset (ℕ × ℕ)}
    (H : DisplayedSubdivision t N₁ S₁) (hroot : N₀.root ∉ N₁.vertices)
    (hvert : N₀.vertices = insert N₀.root N₁.vertices)
    (hedges : S₀ = insert (N₀.root, N₁.root) S₁) (htaxa : N₀.taxa = N₁.taxa)
    (hleaf : ∀ a, N₁.leaf a = N₀.leaf a) (hsw : N₀.Switching S₀) :
    DisplayedSubdivision t N₀ S₀ where
  original := H.original
  wire := H.wire
  rootWire := N₀.root :: H.rootWire
  original_injective := H.original_injective
  taxa_preserved := htaxa.trans H.taxa_preserved
  leaves_preserved := fun p hp a h => (H.leaves_preserved p hp a h).trans (hleaf a)
  rootWire_laws := by
    refine ⟨List.nodup_cons.mpr ⟨fun h => hroot (H.rootWire_mem h), H.rootWire_laws.1⟩, rfl,
      H.getLast?_cons_rootWire _, ?_⟩
    rw [H.dropLast_cons_rootWire, List.toFinset_cons, Finset.disjoint_insert_left]
    exact ⟨fun h => hroot (H.image_subset h), H.rootWire_laws.2.2.2⟩
  wire_laws := H.wire_laws
  interiors_disjoint := H.interiors_disjoint
  rootWire_disjoint := by
    intro p hp hp0
    rw [H.dropLast_cons_rootWire, List.toFinset_cons, Finset.disjoint_insert_left]
    exact ⟨fun h => hroot (H.interior_mem hp hp0 h), H.rootWire_disjoint p hp hp0⟩
  vertices_covered := by
    rw [hvert, H.dropLast_cons_rootWire, List.toFinset_cons]
    ext x
    have h := Finset.ext_iff.mp H.vertices_covered x
    simp only [Finset.mem_union] at h
    simp only [Finset.mem_insert, Finset.mem_union, h]
    tauto
  edges_covered := by
    rw [hedges, H.wireEdges_cons_rootWire]
    ext e
    have h := Finset.ext_iff.mp H.edges_covered e
    simp only [Finset.mem_union] at h
    simp only [Finset.mem_insert, Finset.mem_union, h]
    tauto
  switching := hsw

/-- Two displayed subdivisions, of `T₁` in `N₁` and of `T₂` in `N₂`, glue to a displayed
subdivision of `fork T₁ T₂` in the network `N₀` whose vertices are its root and the disjoint
vertices of `N₁` and `N₂`, and whose switching has the edges from its root to the roots of `N₁` and
`N₂` and the edges of the two switchings. The root of `N₀` is the root of `fork T₁ T₂`, and the
wires above the roots of `T₁` and `T₂` are their root wires, preceded by the root of `N₀`. -/
def join {t₁ t₂ : PhyloTree} {N₀ N₁ N₂ : RootedNetwork} {S₀ S₁ S₂ : Finset (ℕ × ℕ)}
    (H₁ : DisplayedSubdivision t₁ N₁ S₁) (H₂ : DisplayedSubdivision t₂ N₂ S₂)
    (hdisj : Disjoint N₁.vertices N₂.vertices)
    (hroot₁ : N₀.root ∉ N₁.vertices) (hroot₂ : N₀.root ∉ N₂.vertices)
    (hvert : N₀.vertices = insert N₀.root (N₁.vertices ∪ N₂.vertices))
    (hedges : S₀ = insert (N₀.root, N₁.root) (insert (N₀.root, N₂.root) (S₁ ∪ S₂)))
    (htaxa : N₀.taxa = N₁.taxa ∪ N₂.taxa)
    (hleaf₁ : ∀ a, N₁.leaf a = N₀.leaf a) (hleaf₂ : ∀ a, N₂.leaf a = N₀.leaf a)
    (hsw : N₀.Switching S₀) :
    DisplayedSubdivision (.fork t₁ t₂) N₀ S₀ where
  original := forkOriginal N₀.root H₁.original H₂.original
  wire := forkWire N₀.root H₁.rootWire H₂.rootWire H₁.wire H₂.wire
  rootWire := [N₀.root]
  original_injective := by
    intro p hp q hq hpq
    rcases PhyloTree.mem_fork_nodes.mp hp with rfl | ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩ <;>
      rcases PhyloTree.mem_fork_nodes.mp hq with rfl | ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩ <;>
      simp only [forkOriginal] at hpq
    · rfl
    · exact absurd (hpq ▸ H₁.original_mem hq') hroot₁
    · exact absurd (hpq ▸ H₂.original_mem hq') hroot₂
    · exact absurd (hpq.symm ▸ H₁.original_mem hp') hroot₁
    · rw [H₁.original_injective hp' hq' hpq]
    · exact absurd (hpq ▸ H₂.original_mem hq')
        (Finset.disjoint_left.mp hdisj (H₁.original_mem hp'))
    · exact absurd (hpq.symm ▸ H₂.original_mem hp') hroot₂
    · exact absurd (hpq.symm ▸ H₂.original_mem hp')
        (Finset.disjoint_left.mp hdisj (H₁.original_mem hq'))
    · rw [H₂.original_injective hp' hq' hpq]
  taxa_preserved := by
    rw [htaxa, H₁.taxa_preserved, H₂.taxa_preserved]
    simp [PhyloTree.taxa, PhyloTree.labels, List.toFinset_append]
  leaves_preserved := by
    intro p hp a hleaf
    rcases PhyloTree.mem_fork_nodes.mp hp with rfl | ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩
    · simp [PhyloTree.nodeAt] at hleaf
    · exact (H₁.leaves_preserved p' hp' a hleaf).trans (hleaf₁ a)
    · exact (H₂.leaves_preserved p' hp' a hleaf).trans (hleaf₂ a)
  rootWire_laws := ⟨List.nodup_singleton _, rfl, rfl, by simp⟩
  wire_laws := by
    intro p hp hp0
    rw [forkImage_eq]
    have hY₁ : Disjoint N₁.vertices (t₂.nodes.image H₂.original) :=
      Finset.disjoint_of_subset_right H₂.image_subset hdisj
    have hY₂ : Disjoint N₂.vertices (t₁.nodes.image H₁.original) :=
      Finset.disjoint_of_subset_right H₁.image_subset hdisj.symm
    rcases PhyloTree.mem_fork_nodes.mp hp with rfl | ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩
    · exact absurd rfl hp0
    · by_cases hp'0 : p' = []
      · subst hp'0
        exact H₁.topWire_laws hroot₁ hY₁
      · rw [forkWire_false hp'0, parent_cons_of_ne_nil false hp'0]
        obtain ⟨l1, l2, l3, l4, _⟩ := H₁.wire_laws p' hp' hp'0
        exact ⟨l1, l2, l3, l4, H₁.innerWire_disjoint hp' hp'0 hroot₁ hY₁⟩
    · rw [Finset.union_comm]
      by_cases hp'0 : p' = []
      · subst hp'0
        exact H₂.topWire_laws hroot₂ hY₂
      · rw [forkWire_true hp'0, parent_cons_of_ne_nil true hp'0]
        obtain ⟨l1, l2, l3, l4, _⟩ := H₂.wire_laws p' hp' hp'0
        exact ⟨l1, l2, l3, l4, H₂.innerWire_disjoint hp' hp'0 hroot₂ hY₂⟩
  interiors_disjoint := by
    -- the interiors of the wires on the side of `T₁` lie in `N₁`, those on the side of `T₂` in `N₂`
    have hside₁ : ∀ p ∈ t₁.nodes, ∀ x ∈ wireInterior
        (forkWire N₀.root H₁.rootWire H₂.rootWire H₁.wire H₂.wire (false :: p)),
        x ∈ N₁.vertices := by
      intro p hp x hx
      by_cases hp0 : p = []
      · subst hp0
        exact H₁.rootWire_dropLast_mem hx
      · rw [forkWire_false hp0] at hx
        exact H₁.interior_mem hp hp0 hx
    have hside₂ : ∀ p ∈ t₂.nodes, ∀ x ∈ wireInterior
        (forkWire N₀.root H₁.rootWire H₂.rootWire H₁.wire H₂.wire (true :: p)),
        x ∈ N₂.vertices := by
      intro p hp x hx
      by_cases hp0 : p = []
      · subst hp0
        exact H₂.rootWire_dropLast_mem hx
      · rw [forkWire_true hp0] at hx
        exact H₂.interior_mem hp hp0 hx
    intro p hp q hq hpq
    rcases PhyloTree.mem_fork_nodes_erase.mp hp with ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩ <;>
      rcases PhyloTree.mem_fork_nodes_erase.mp hq with ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
    · have hpq' : p' ≠ q' := fun h => hpq (h ▸ rfl)
      by_cases hp'0 : p' = [] <;> by_cases hq'0 : q' = []
      · exact absurd (hp'0.trans hq'0.symm) hpq'
      · subst hp'0
        rw [forkWire_false hq'0]
        exact H₁.rootWire_disjoint q' hq' hq'0
      · subst hq'0
        rw [forkWire_false hp'0]
        exact (H₁.rootWire_disjoint p' hp' hp'0).symm
      · rw [forkWire_false hp'0, forkWire_false hq'0]
        exact H₁.interiors_disjoint (Finset.mem_erase.mpr ⟨hp'0, hp'⟩)
          (Finset.mem_erase.mpr ⟨hq'0, hq'⟩) hpq'
    · exact Finset.disjoint_left.mpr fun x hx hx' =>
        Finset.disjoint_left.mp hdisj (hside₁ p' hp' x hx) (hside₂ q' hq' x hx')
    · exact Finset.disjoint_left.mpr fun x hx hx' =>
        Finset.disjoint_left.mp hdisj (hside₁ q' hq' x hx') (hside₂ p' hp' x hx)
    · have hpq' : p' ≠ q' := fun h => hpq (h ▸ rfl)
      by_cases hp'0 : p' = [] <;> by_cases hq'0 : q' = []
      · exact absurd (hp'0.trans hq'0.symm) hpq'
      · subst hp'0
        rw [forkWire_true hq'0]
        exact H₂.rootWire_disjoint q' hq' hq'0
      · subst hq'0
        rw [forkWire_true hp'0]
        exact (H₂.rootWire_disjoint p' hp' hp'0).symm
      · rw [forkWire_true hp'0, forkWire_true hq'0]
        exact H₂.interiors_disjoint (Finset.mem_erase.mpr ⟨hp'0, hp'⟩)
          (Finset.mem_erase.mpr ⟨hq'0, hq'⟩) hpq'
  rootWire_disjoint := fun _ _ _ => by simp
  vertices_covered := by
    rw [hvert, forkImage_eq]
    ext x
    have h₁ := Finset.ext_iff.mp H₁.vertices_covered x
    have h₂ := Finset.ext_iff.mp H₂.vertices_covered x
    simp only [Finset.mem_union] at h₁ h₂
    simp only [Finset.mem_insert, Finset.mem_union, mem_forkWire_biUnion, List.dropLast_singleton,
      List.toFinset_nil, Finset.notMem_empty, or_false, h₁, h₂, wireInterior_cons]
    simp only [or_assoc, or_left_comm, or_comm]
  edges_covered := by
    rw [hedges]
    ext e
    have h₁ := Finset.ext_iff.mp H₁.edges_covered e
    have h₂ := Finset.ext_iff.mp H₂.edges_covered e
    simp only [Finset.mem_union] at h₁ h₂
    simp only [Finset.mem_insert, Finset.mem_union, mem_forkWire_biUnion, h₁, h₂,
      H₁.wireEdges_cons_rootWire, H₂.wireEdges_cons_rootWire, wireEdges_singleton,
      Finset.notMem_empty, or_false]
    simp only [or_assoc, or_left_comm, or_comm]
  switching := hsw

/-- A displayed subdivision of `T` in `N'` through `S'` is one in `N` through `S` when the two
networks have the same vertices, root, taxa and leaves, `S' = S`, and `S` is a switching of `N`. -/
def congr {N' : RootedNetwork} {S' : Finset (ℕ × ℕ)} (H : DisplayedSubdivision t N' S')
    (hvert : N'.vertices = N.vertices) (hroot : N'.root = N.root) (htaxa : N'.taxa = N.taxa)
    (hleaf : ∀ a, N'.leaf a = N.leaf a) (hedges : S' = S) (hsw : N.Switching S) :
    DisplayedSubdivision t N S where
  original := H.original
  wire := H.wire
  rootWire := H.rootWire
  original_injective := H.original_injective
  taxa_preserved := htaxa ▸ H.taxa_preserved
  leaves_preserved := fun p hp a h => (H.leaves_preserved p hp a h).trans (hleaf a)
  rootWire_laws := hroot ▸ H.rootWire_laws
  wire_laws := H.wire_laws
  interiors_disjoint := H.interiors_disjoint
  rootWire_disjoint := H.rootWire_disjoint
  vertices_covered := hvert ▸ H.vertices_covered
  edges_covered := hedges ▸ H.edges_covered
  switching := hsw

end DisplayedSubdivision

end Camus
