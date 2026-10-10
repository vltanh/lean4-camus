module

public import Camus.Network.Realization.Support

/-!
# The canonical network of an edge family: subdivision of the tree

With no added edge, the canonical network `Realization.graph t ∅` is `T` itself
(`Realization.baseline_edges`). This file proves that the support of `Realization.graph t E`,
the network without its added edges, is a subdivision of `T` (`GraphSubdivision`): every vertex
of `T` is kept, and the edge from `parent(p)` to `p` is replaced by the wire above `p`. It is used
to show that the quartets displayed by `T` are displayed by `Realization.graph t E`, and it is
the starting point of the single-edge reduction `T + e`
(`Realization.singletonSupportSubdivision`).

## Main results

* `Realization.addressOf_code`: `Realization.addressOf` decodes the codes of vertices of `T`.
* `Realization.baseline_edges`: the edges of `Realization.graph t ∅` are the edges of `T`.
* `Realization.supportGraphSubdivision`: the support of `Realization.graph t E` is a subdivision
  of `T`.
-/

@[expose] public section

namespace Camus.Realization

/-- The address with code `n`: the inverse of `Address.code`, with value the root `[]` when
`n` is not a code. -/
noncomputable def addressOf (n : ℕ) : Address := by
  classical
  exact if h : ∃ p, Address.code p = n then h.choose else []

/-- `Realization.addressOf` inverts `Address.code`. -/
theorem addressOf_code (p : Address) : addressOf (Address.code p) = p := by
  classical
  unfold addressOf
  have hex : ∃ q, Address.code q = Address.code p := ⟨p, rfl⟩
  simp only [dite_eq_left hex]
  exact Address.code_injective hex.choose_spec

/-- With no added edge, the canonical network is `T`: the edges of `Realization.graph t ∅` are
the edges from `parent(p)` to `p`, for the non-root vertices `p` of `T`. -/
theorem baseline_edges (t : PhyloTree) :
    (graph t ∅).edges = (t.nodes.erase []).image
      (fun p => (Address.code (parent p), Address.code p)) := by
  classical
  simp only [graph, Finset.image_empty, Finset.union_empty, supportEdges,
    wire, outerEndpoints, ghostEndpoints, Finset.toList_empty,
    List.flatMap_nil, List.append_nil, wireEdges]
  simpa using Finset.biUnion_singleton

/-- For a family of admissible pairs, the support of `Realization.graph t E` (the network
without its added edges) is a subdivision of `T`, given as `Realization.graph t ∅`. The vertex
map is the identity, and the edge from `parent(p)` to `p` is replaced by the wire above `p`. -/
noncomputable def supportGraphSubdivision (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) :
    GraphSubdivision (graph t ∅) {graph t E with edges := supportEdges t E} := by
  classical
  refine
    { original := id
      wire := fun e => wire t E (addressOf e.2)
      original_injective := Function.injective_id.injOn
      root_left := by exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨[], t.root_mem_nodes, rfl⟩)
      root_preserved := rfl
      taxa_preserved := rfl
      leaves_left := by
        intro a ha
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨leafAddress t a, leafAddress_mem_nodes ha, rfl⟩)
      leaves_preserved := fun a ha => rfl
      edge_endpoints := ?_
      wire_laws := ?_
      interiors_disjoint := ?_
      vertices_covered := ?_
      edges_covered := ?_ }
  · intro e he
    rw [baseline_edges] at he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    have hp' := Finset.mem_erase.mp hp
    exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨parent p,
      t.nodes_prefix_closed hp'.2 (parent_prefix p), rfl⟩),
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp'.2, rfl⟩)⟩
  · intro e he
    rw [baseline_edges] at he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    have hp' := Finset.mem_erase.mp hp
    simp only [addressOf_code, id_eq]
    exact ⟨wire_length t E p, wire_nodup t E hE hp'.2 hp'.1,
      wire_head t E p, wire_last t E p,
      by simpa [graph] using wireInterior_disjoint_original t E p⟩
  · intro e he f hf hef
    rw [baseline_edges] at he hf
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hf
    have hpq : p ≠ q := by
      intro h
      subst q
      exact hef rfl
    simpa only [addressOf_code] using interiors_disjoint t E hE hpq
  · change (graph t E).vertices = (graph t ∅).vertices.image id ∪ _
    rw [baseline_edges, Finset.image_biUnion]
    simp only [addressOf_code, Finset.image_id]
    simpa only [graph, Finset.biUnion_empty, Finset.union_empty] using vertices_covered t E hE
  · simp only [baseline_edges, Finset.image_biUnion, addressOf_code]
    rfl

end Camus.Realization
