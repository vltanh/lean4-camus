module

public import Camus.Network.Cuts

/-!
# Networks built on `T` in the sense of Definition 1

Definition 1 says that a rooted binary level-1 network `N` is built on `t` when `t` is one of
the trees of `N`: delete one of the two edges into each reticulation, in each of the possible
ways, then clean up. The library's `RootedNetwork.AnchoredExtension` reads "built on `T`" with
the root of `T` at the root of `N`, the class over which the dynamic program of Section 2.2
optimizes ("we cannot add an edge to T that begins above the root of T"). Definition 1 also
allows networks whose root lies above the root of `T`: the root of `N` has the root of `T` and a
reticulation as children, and deleting the edge into the reticulation leaves a root with one
child, which the clean-up suppresses. This file defines Definition 1's class,
`RootedNetwork.BuiltOn`, proves the fact on switchings that the definition relies on (a switching
of a rooted binary level-1 network has no unlabelled leaf), and shows that the class contains the
anchored extensions.

## Main definitions

* `DisplayedSubdivision`: the switching `S` of `N` is a subdivision of `T` below a directed path
  from the root of `N` to the root of `T`.
* `RootedNetwork.BuiltOn`: `N` is built on `T` (Definition 1).

## Main results

* `RootedNetwork.switching_leaf_of_childless`: in a switching of a rooted binary level-1
  network, a vertex without children is a labelled leaf.
* `SupportSubdivision.toDisplayed`, `RootedNetwork.AnchoredExtension.builtOn`: a network built on
  `T` with the root of `T` at its root is built on `T` in the sense of Definition 1.
-/

@[expose] public section

namespace Camus

/-- The switching `S` of `N` gives the tree `T` of Definition 1, with the root of `N` at or above
the root of `T`. Deleting the edges of `N` outside `S` deletes one of the two edges into each
reticulation. The clean-up of Definition 1 then deletes unlabelled leaves, of which there are none
(`RootedNetwork.switching_leaf_of_childless`), and suppresses the vertices with one child, a root
with one child included. `DisplayedSubdivision t N S` says that the result is `T`: `S` is `T` with
each edge replaced by a directed path, below a directed path from the root of `N` to the root of
`T`. The map `original` sends the vertices of `T` injectively to vertices of `N`; for each
non-root vertex `p` of `T`, `wire p` is the directed path of `N` that replaces the edge of `T`
from `parent p` to `p`; and `rootWire` is the directed path from `N.root` to `original []`, which
is `[N.root]` when the root of `T` is the root of `N` (`SupportSubdivision.toDisplayed`). The
laws:
* `original` sends the leaf of `T` labelled `a` to `N.leaf a`, and `N` has the taxa of `T`;
* the root wire runs from `N.root` to `original []` without repeating a vertex, and its vertices
  other than `original []` are not images of vertices of `T`;
* each wire runs from `original (parent p)` to `original p` without repeating a vertex, and its
  interior vertices are not images of vertices of `T`;
* the interiors of distinct wires are disjoint, and they avoid the vertices of the root wire;
* the vertices of `N` are the images of the vertices of `T`, the interior vertices of the wires
  and the vertices of the root wire, and `S` is the set of the edges of the wires and of the root
  wire;
* `S` is a switching of `N`.

`SupportSubdivision` is the case `rootWire = [N.root]`. -/
structure DisplayedSubdivision (t : PhyloTree) (N : RootedNetwork)
    (S : Finset (ℕ × ℕ)) where
  original : Address → ℕ
  wire : Address → List ℕ
  rootWire : List ℕ
  original_injective : Set.InjOn original t.nodes
  taxa_preserved : N.taxa = t.taxa
  leaves_preserved : ∀ p ∈ t.nodes, ∀ a, t.nodeAt p = some (.leaf a) →
    original p = N.leaf a
  rootWire_laws : rootWire.Nodup ∧ rootWire.head? = some N.root ∧
    rootWire.getLast? = some (original []) ∧
    Disjoint rootWire.dropLast.toFinset (t.nodes.image original)
  wire_laws : ∀ p ∈ t.nodes, p ≠ [] →
    2 ≤ (wire p).length ∧ (wire p).Nodup ∧
    (wire p).head? = some (original (parent p)) ∧
    (wire p).getLast? = some (original p) ∧
    Disjoint (wireInterior (wire p)) (t.nodes.image original)
  interiors_disjoint :
    ((t.nodes.erase []) : Set Address).Pairwise
      (fun p q => Disjoint (wireInterior (wire p)) (wireInterior (wire q)))
  rootWire_disjoint : ∀ p ∈ t.nodes, p ≠ [] →
    Disjoint rootWire.dropLast.toFinset (wireInterior (wire p))
  vertices_covered : N.vertices = t.nodes.image original ∪
    (t.nodes.erase []).biUnion (fun p => wireInterior (wire p)) ∪ rootWire.dropLast.toFinset
  edges_covered : S = (t.nodes.erase []).biUnion (fun p => wireEdges (wire p)) ∪
    wireEdges rootWire
  switching : N.Switching S

/-- **Definition 1** (`mthst1`). `N` is built on `T`: `N` is a rooted binary level-1 network and
`T` is one of its trees, the trees obtained by deleting one of the two edges into each reticulation
and cleaning up (`DisplayedSubdivision`). The root of `T` need not be the root of `N`; with the
root of `T` at the root of `N`, this is `RootedNetwork.AnchoredExtension`. -/
def RootedNetwork.BuiltOn (N : RootedNetwork) (t : PhyloTree) : Prop :=
  N.RootedBinaryLevelOne ∧ ∃ S, Nonempty (DisplayedSubdivision t N S)

namespace RootedNetwork

/-- In a switching `S` of a rooted binary level-1 network `N`, a vertex with no child is a
labelled leaf: deleting the edges outside `S` creates no unlabelled leaf. Otherwise the vertex
`v` would have an edge out of it outside `S`. If `v` is the root or a tree vertex, both edges out
of `v` lie outside `S`; if `v` is a reticulation, so does one of the two edges into `v`. Either
way `v` lies on the cycles of two non-tree edges, which are vertex-disjoint since `N` is level-1
(`RootedNetwork.fundamentalCycles_disjoint`). -/
theorem switching_leaf_of_childless {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) {v : ℕ} (hv : v ∈ N.vertices)
    (hchild : ∀ w, (v, w) ∉ S) : ∃ a ∈ N.taxa, N.leaf a = v := by
  classical
  by_contra hleaf
  have hout : N.outdegree v ≠ 0 := fun h => hleaf ((hN.2.2.2.2.2.2.2.2.1 v hv).mp h)
  -- every edge out of `v` is a non-tree edge
  have hdel : ∀ e ∈ N.edges.filter (fun e => e.1 = v), e ∈ N.edges \ S := by
    intro e he
    obtain ⟨heN, hev⟩ := Finset.mem_filter.mp he
    refine Finset.mem_sdiff.mpr ⟨heN, fun heS => hchild e.2 ?_⟩
    rw [← hev]
    exact heS
  -- two distinct edges out of `v` would put `v` on two disjoint cycles
  have htwo : N.outdegree v = 2 → False := by
    intro h2
    obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp (show 1 < N.outdegree v by omega)
    have hev := (Finset.mem_filter.mp he).2
    have hfv := (Finset.mem_filter.mp hf).2
    have hve := fundamentalCycle_source_mem hN hS (hdel e he)
    have hvf : e.1 ∈ (fundamentalCycle hN hS (hdel f hf)).support := by
      rw [hev, ← hfv]
      exact fundamentalCycle_source_mem hN hS (hdel f hf)
    exact Finset.disjoint_left.mp (fundamentalCycles_disjoint hN hS (hdel e he) (hdel f hf) hef)
      (List.mem_toFinset.mpr hve) (List.mem_toFinset.mpr hvf)
  by_cases hr : v = N.root
  · rcases hN.2.2.2.2.1 with h | h
    · exact hout (hr ▸ h)
    · exact htwo (hr ▸ h)
  · rcases hN.2.2.2.2.2.2.2.2.2.1 v hv hr with h | h | h
    · exact hout h.2
    · exact htwo h.2
    -- a reticulation: its edge out and one edge in are non-tree edges, both at `v`
    · obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < N.outdegree v by omega)
      obtain ⟨d, hd, hdv⟩ := deleted_incoming_of_reticulation hN hS v h.1
      have hev := (Finset.mem_filter.mp he).2
      have hed : e ≠ d := by
        intro hed
        have hloop : e = (v, v) := Prod.ext hev (by rw [hed]; exact hdv)
        exact edge_ne hN (hloop ▸ (Finset.mem_filter.mp he).1) rfl
      have hve := fundamentalCycle_source_mem hN hS (hdel e he)
      have hvd : e.1 ∈ (fundamentalCycle hN hS hd).support := by
        rw [hev, ← hdv]
        exact fundamentalCycle_target_mem hN hS hd
      exact Finset.disjoint_left.mp (fundamentalCycles_disjoint hN hS (hdel e he) hd hed)
        (List.mem_toFinset.mpr hve) (List.mem_toFinset.mpr hvd)

end RootedNetwork

namespace SupportSubdivision

/-- A support subdivision of `T` in `N`, which keeps the root, is a displayed subdivision whose
root wire is the root of `N` alone. -/
def toDisplayed {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}
    (H : SupportSubdivision t N S) : DisplayedSubdivision t N S where
  original := H.original
  wire := H.wire
  rootWire := [N.root]
  original_injective := H.original_injective
  taxa_preserved := H.taxa_preserved
  leaves_preserved := H.leaves_preserved
  rootWire_laws := ⟨List.nodup_singleton _, rfl, by simp [H.root_preserved], by simp⟩
  wire_laws := H.wire_laws
  interiors_disjoint := H.interiors_disjoint
  rootWire_disjoint := fun _ _ _ => by simp
  vertices_covered := by rw [H.vertices_covered]; simp
  edges_covered := by
    rw [show wireEdges [N.root] = ∅ by simp [wireEdges], Finset.union_empty]
    exact H.edges_covered
  switching := H.switching

end SupportSubdivision

/-- A network built on `T` with the root of `T` at its root (`RootedNetwork.AnchoredExtension`)
is built on `T` in the sense of Definition 1. -/
theorem RootedNetwork.AnchoredExtension.builtOn {N : RootedNetwork} {t : PhyloTree}
    (hN : N.AnchoredExtension t) : N.BuiltOn t := by
  obtain ⟨hbin, S, ⟨H⟩⟩ := hN
  exact ⟨hbin, S, ⟨H.toDisplayed⟩⟩

end Camus
