module

public import Camus.Galled.TreeIsomorphism

/-!
# Networks built on trees equal up to the order of the children

A `PhyloTree` is a plane tree: the two children of each vertex are ordered, and a vertex is its
address, the path of left and right steps from the root. The paper's trees are unordered, and two
`PhyloTree`s that differ in the order of the children at some vertices (`PhyloTree.RootedIso`)
stand for the same tree. For well-labelled trees, this is having the same clades
(`PhyloTree.ClusterEq`; `PhyloTree.rootedIso_of_clusterEq` in `Camus/Pipelines/AstralTree.lean`).
This file shows that the networks built on two such trees are the same networks. A
rooted isomorphism from `t` to `t'` maps the addresses of `t` onto those of `t'`, keeping the root,
the parent of each vertex and the labels of the leaves (`PhyloTree.AddressMap`,
`PhyloTree.RootedIso.addressMap`), so that a subdivision of `t'` in a network `N`, read through this
map, is a subdivision of `t` in `N` (`SupportSubdivision.comap`, `DisplayedSubdivision.comap`).
Hence `N` is built on `t` if and only if it is built on `t'`, with the root kept
(`PhyloTree.RootedIso.anchoredExtension_iff`) or in the sense of Definition 1
(`PhyloTree.RootedIso.builtOn_iff`). So CAMUS's problem is the same on `t` and on `t'`: the same
networks are feasible, with the same displayed quartets and the same reticulations.

## Main results

* `PhyloTree.AddressMap`: a map of the addresses of `t` onto those of `t'` that keeps the tree.
* `PhyloTree.RootedIso.addressMap`: a rooted isomorphism has one.
* `PhyloTree.RootedIso.anchoredExtension_iff`: a network is built on `t` if and only if it is
  built on `t'`.
* `PhyloTree.RootedIso.builtOn_iff`: the same for networks built on a tree in the sense of
  Definition 1.
-/

@[expose] public section

namespace Camus

namespace PhyloTree

/-- A map `φ` of the addresses of `t` onto those of `t'` that keeps the tree: it is injective,
keeps the length of an address and commutes with taking the first `k` steps (so it keeps the
root, the parent of each vertex and the ancestor order), maps the vertices of `t` onto those of
`t'`, and maps the leaf of `t` labelled `a` to the leaf of `t'` labelled `a`; the two trees have
the same taxa. -/
structure AddressMap (t t' : PhyloTree) where
  toFun : Address → Address
  injective : Function.Injective toFun
  length_eq : ∀ p, (toFun p).length = p.length
  take_eq : ∀ p k, toFun (p.take k) = (toFun p).take k
  nodes_eq : t'.nodes = t.nodes.image toFun
  leaf : ∀ p a, t.nodeAt p = some (.leaf a) → t'.nodeAt (toFun p) = some (.leaf a)
  taxa_eq : t.taxa = t'.taxa

namespace AddressMap

variable {t t' : PhyloTree} (φ : AddressMap t t')

/-- The root is mapped to the root. -/
theorem map_root : φ.toFun [] = [] :=
  List.eq_nil_of_length_eq_zero (φ.length_eq [])

/-- Only the root is mapped to the root. -/
theorem map_ne_root {p : Address} (hp : p ≠ []) : φ.toFun p ≠ [] := by
  intro h
  exact hp (List.eq_nil_of_length_eq_zero ((φ.length_eq p).symm.trans (by rw [h]; rfl)))

/-- The parent of the image of `p` is the image of the parent of `p`. -/
theorem map_parent (p : Address) : parent (φ.toFun p) = φ.toFun (parent p) := by
  unfold parent
  rw [φ.take_eq, φ.length_eq]

/-- A vertex of `t` is mapped to a vertex of `t'`. -/
theorem map_mem {p : Address} (hp : p ∈ t.nodes) : φ.toFun p ∈ t'.nodes := by
  rw [φ.nodes_eq]
  exact Finset.mem_image_of_mem _ hp

/-- The non-root vertices of `t` are mapped onto those of `t'`. -/
theorem nodes_erase_eq : t'.nodes.erase [] = (t.nodes.erase []).image φ.toFun := by
  rw [φ.nodes_eq, Finset.image_erase φ.injective, φ.map_root]

end AddressMap

/-- The map of addresses of `fork l r` that sends the addresses of `l` through `φ₁` below the
child `c` and those of `r` through `φ₂` below the other child: for `c = false` it keeps the order
of the two children, and for `c = true` it swaps them. -/
def forkMap (c : Bool) (φ₁ φ₂ : Address → Address) : Address → Address
  | [] => []
  | false :: p => c :: φ₁ p
  | true :: p => (!c) :: φ₂ p

/-- `forkMap` is injective if `φ₁` and `φ₂` are. -/
theorem forkMap_injective (c : Bool) {φ₁ φ₂ : Address → Address}
    (h₁ : Function.Injective φ₁) (h₂ : Function.Injective φ₂) :
    Function.Injective (forkMap c φ₁ φ₂) := by
  intro p q h
  match p, q with
  | [], [] => rfl
  | [], false :: q => simp [forkMap] at h
  | [], true :: q => simp [forkMap] at h
  | false :: p, [] => simp [forkMap] at h
  | true :: p, [] => simp [forkMap] at h
  | false :: p, false :: q =>
    simp only [forkMap, List.cons.injEq, true_and] at h
    rw [h₁ h]
  | true :: p, true :: q =>
    simp only [forkMap, List.cons.injEq, true_and] at h
    rw [h₂ h]
  | false :: p, true :: q =>
    simp only [forkMap, List.cons.injEq] at h
    cases c <;> simp at h
  | true :: p, false :: q =>
    simp only [forkMap, List.cons.injEq] at h
    cases c <;> simp at h

/-- `forkMap` keeps lengths if `φ₁` and `φ₂` do. -/
theorem forkMap_length (c : Bool) {φ₁ φ₂ : Address → Address}
    (h₁ : ∀ p, (φ₁ p).length = p.length) (h₂ : ∀ p, (φ₂ p).length = p.length) :
    ∀ p, (forkMap c φ₁ φ₂ p).length = p.length
  | [] => rfl
  | false :: p => by simp [forkMap, h₁]
  | true :: p => by simp [forkMap, h₂]

/-- `forkMap` commutes with taking the first `k` steps if `φ₁` and `φ₂` do. -/
theorem forkMap_take (c : Bool) {φ₁ φ₂ : Address → Address}
    (h₁ : ∀ p k, φ₁ (p.take k) = (φ₁ p).take k) (h₂ : ∀ p k, φ₂ (p.take k) = (φ₂ p).take k) :
    ∀ p k, forkMap c φ₁ φ₂ (p.take k) = (forkMap c φ₁ φ₂ p).take k
  | [], k => by simp [forkMap]
  | _ :: _, 0 => by simp [forkMap]
  | false :: p, k + 1 => by simp [forkMap, h₁]
  | true :: p, k + 1 => by simp [forkMap, h₂]

/-- A rooted isomorphism from `t` to `t'` has a map of addresses that keeps the tree: at a vertex
where the isomorphism swaps the two children, the map swaps the first step below that vertex. -/
theorem RootedIso.addressMap {t t' : PhyloTree} (h : RootedIso t t') :
    Nonempty (AddressMap t t') := by
  induction h with
  | leaf a =>
    exact ⟨⟨id, Function.injective_id, fun _ => rfl, fun _ _ => rfl, by simp, fun _ _ h => h,
      rfl⟩⟩
  | @fork l₁ r₁ l₂ r₂ hl hr ihl ihr =>
    obtain ⟨φ₁⟩ := ihl
    obtain ⟨φ₂⟩ := ihr
    refine ⟨⟨forkMap false φ₁.toFun φ₂.toFun, forkMap_injective false φ₁.injective φ₂.injective,
      forkMap_length false φ₁.length_eq φ₂.length_eq, forkMap_take false φ₁.take_eq φ₂.take_eq,
      ?_, ?_, (RootedIso.fork hl hr).taxa_eq⟩⟩
    · simp only [nodes, Finset.image_insert, Finset.image_union, Finset.image_image, φ₁.nodes_eq,
        φ₂.nodes_eq]
      rfl
    · intro p a hp
      match p with
      | [] => simp [nodeAt] at hp
      | false :: p => exact φ₁.leaf p a hp
      | true :: p => exact φ₂.leaf p a hp
  | @swap l₁ r₁ l₂ r₂ hl hr ihl ihr =>
    obtain ⟨φ₁⟩ := ihl
    obtain ⟨φ₂⟩ := ihr
    refine ⟨⟨forkMap true φ₁.toFun φ₂.toFun, forkMap_injective true φ₁.injective φ₂.injective,
      forkMap_length true φ₁.length_eq φ₂.length_eq, forkMap_take true φ₁.take_eq φ₂.take_eq,
      ?_, ?_, (RootedIso.swap hl hr).taxa_eq⟩⟩
    · simp only [nodes, Finset.image_insert, Finset.image_union, Finset.image_image, φ₁.nodes_eq,
        φ₂.nodes_eq]
      rw [Finset.union_comm]
      rfl
    · intro p a hp
      match p with
      | [] => simp [nodeAt] at hp
      | false :: p => exact φ₁.leaf p a hp
      | true :: p => exact φ₂.leaf p a hp

end PhyloTree

namespace SupportSubdivision

variable {t t' : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- A subdivision of `t'` in `N`, read through a map of addresses `φ` from `t` to `t'`, is a
subdivision of `t` in `N`: the vertex `p` of `t` is the vertex `φ p` of `t'`, and the edge of `t`
above `p` is the edge of `t'` above `φ p`. -/
def comap (φ : PhyloTree.AddressMap t t') (H : SupportSubdivision t' N S) :
    SupportSubdivision t N S where
  original := H.original ∘ φ.toFun
  wire := H.wire ∘ φ.toFun
  original_injective := fun p hp q hq h =>
    φ.injective (H.original_injective (φ.map_mem hp) (φ.map_mem hq) h)
  root_preserved := by
    simp only [Function.comp_apply, φ.map_root, H.root_preserved]
  taxa_preserved := H.taxa_preserved.trans φ.taxa_eq.symm
  leaves_preserved := fun p hp a hpa => H.leaves_preserved _ (φ.map_mem hp) a (φ.leaf p a hpa)
  wire_laws := by
    intro p hp hp0
    have himage : t.nodes.image (H.original ∘ φ.toFun) = t'.nodes.image H.original := by
      rw [φ.nodes_eq, Finset.image_image]
    obtain ⟨h1, h2, h3, h4, h5⟩ := H.wire_laws _ (φ.map_mem hp) (φ.map_ne_root hp0)
    refine ⟨h1, h2, ?_, h4, ?_⟩
    · rw [φ.map_parent] at h3
      exact h3
    · rw [himage]
      exact h5
  interiors_disjoint := by
    intro p hp q hq hpq
    obtain ⟨hp0, hpn⟩ := Finset.mem_erase.mp hp
    obtain ⟨hq0, hqn⟩ := Finset.mem_erase.mp hq
    exact H.interiors_disjoint (Finset.mem_erase.mpr ⟨φ.map_ne_root hp0, φ.map_mem hpn⟩)
      (Finset.mem_erase.mpr ⟨φ.map_ne_root hq0, φ.map_mem hqn⟩)
      (fun h => hpq (φ.injective h))
  vertices_covered := by
    rw [H.vertices_covered, φ.nodes_erase_eq, φ.nodes_eq, Finset.image_image,
      Finset.image_biUnion]
    rfl
  edges_covered := by
    refine H.edges_covered.trans ?_
    rw [φ.nodes_erase_eq, Finset.image_biUnion]
    rfl
  switching := H.switching

end SupportSubdivision

namespace DisplayedSubdivision

variable {t t' : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- A displayed subdivision of `t'` in `N`, read through a map of addresses `φ` from `t` to `t'`,
is a displayed subdivision of `t` in `N`, with the same root wire. -/
def comap (φ : PhyloTree.AddressMap t t') (H : DisplayedSubdivision t' N S) :
    DisplayedSubdivision t N S where
  original := H.original ∘ φ.toFun
  wire := H.wire ∘ φ.toFun
  rootWire := H.rootWire
  original_injective := fun p hp q hq h =>
    φ.injective (H.original_injective (φ.map_mem hp) (φ.map_mem hq) h)
  taxa_preserved := H.taxa_preserved.trans φ.taxa_eq.symm
  leaves_preserved := fun p hp a hpa => H.leaves_preserved _ (φ.map_mem hp) a (φ.leaf p a hpa)
  rootWire_laws := by
    have himage : t.nodes.image (H.original ∘ φ.toFun) = t'.nodes.image H.original := by
      rw [φ.nodes_eq, Finset.image_image]
    obtain ⟨h1, h2, h3, h4⟩ := H.rootWire_laws
    refine ⟨h1, h2, ?_, ?_⟩
    · simp only [Function.comp_apply, φ.map_root, h3]
    · rw [himage]
      exact h4
  wire_laws := by
    intro p hp hp0
    have himage : t.nodes.image (H.original ∘ φ.toFun) = t'.nodes.image H.original := by
      rw [φ.nodes_eq, Finset.image_image]
    obtain ⟨h1, h2, h3, h4, h5⟩ := H.wire_laws _ (φ.map_mem hp) (φ.map_ne_root hp0)
    refine ⟨h1, h2, ?_, h4, ?_⟩
    · rw [φ.map_parent] at h3
      exact h3
    · rw [himage]
      exact h5
  interiors_disjoint := by
    intro p hp q hq hpq
    obtain ⟨hp0, hpn⟩ := Finset.mem_erase.mp hp
    obtain ⟨hq0, hqn⟩ := Finset.mem_erase.mp hq
    exact H.interiors_disjoint (Finset.mem_erase.mpr ⟨φ.map_ne_root hp0, φ.map_mem hpn⟩)
      (Finset.mem_erase.mpr ⟨φ.map_ne_root hq0, φ.map_mem hqn⟩)
      (fun h => hpq (φ.injective h))
  rootWire_disjoint := fun p hp hp0 =>
    H.rootWire_disjoint _ (φ.map_mem hp) (φ.map_ne_root hp0)
  vertices_covered := by
    rw [H.vertices_covered, φ.nodes_erase_eq, φ.nodes_eq, Finset.image_image,
      Finset.image_biUnion]
    rfl
  edges_covered := by
    refine H.edges_covered.trans ?_
    rw [φ.nodes_erase_eq, Finset.image_biUnion]
    rfl
  switching := H.switching

end DisplayedSubdivision

namespace PhyloTree

variable {t t' : PhyloTree}

/-- A network is built on `t` (with the root kept) if and only if it is built on a tree `t'` equal
to `t` up to the order of the children (`RootedIso`). For well-labelled trees with the same clades,
see `ClusterEq.anchoredExtension_iff`. -/
theorem RootedIso.anchoredExtension_iff (h : RootedIso t t') (N : RootedNetwork) :
    N.AnchoredExtension t ↔ N.AnchoredExtension t' := by
  obtain ⟨φ⟩ := h.addressMap
  obtain ⟨ψ⟩ := h.symm.addressMap
  constructor
  · rintro ⟨hN, S, ⟨H⟩⟩
    exact ⟨hN, S, ⟨H.comap ψ⟩⟩
  · rintro ⟨hN, S, ⟨H⟩⟩
    exact ⟨hN, S, ⟨H.comap φ⟩⟩

/-- A network is built on `t` in the sense of Definition 1 (`RootedNetwork.BuiltOn`) if and only
if it is built on a tree `t'` equal to `t` up to the order of the children (`RootedIso`). -/
theorem RootedIso.builtOn_iff (h : RootedIso t t') (N : RootedNetwork) :
    N.BuiltOn t ↔ N.BuiltOn t' := by
  obtain ⟨φ⟩ := h.addressMap
  obtain ⟨ψ⟩ := h.symm.addressMap
  constructor
  · rintro ⟨hN, S, ⟨H⟩⟩
    exact ⟨hN, S, ⟨H.comap ψ⟩⟩
  · rintro ⟨hN, S, ⟨H⟩⟩
    exact ⟨hN, S, ⟨H.comap φ⟩⟩

end PhyloTree

end Camus
