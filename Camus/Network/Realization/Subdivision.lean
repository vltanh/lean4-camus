module

public import Camus.Network.Realization.Support

@[expose] public section

namespace Camus.Realization

noncomputable def addressOf (n : ℕ) : Address := by
  classical
  exact if h : ∃ p, Address.code p = n then h.choose else []

theorem addressOf_code (p : Address) : addressOf (Address.code p) = p := by
  classical
  unfold addressOf
  have hex : ∃ q, Address.code q = Address.code p := ⟨p, rfl⟩
  simp only [dite_eq_left hex]
  exact Address.code_injective hex.choose_spec

theorem baseline_edges (t : PhyloTree) :
    (graph t ∅).edges = (t.nodes.erase []).image
      (fun p => (Address.code (parent p), Address.code p)) := by
  classical
  simp only [graph, Finset.image_empty, Finset.union_empty, supportEdges,
    wire, outerEndpoints, ghostEndpoints, Finset.toList_empty,
    List.flatMap_nil, List.append_nil, wireEdges]
  simpa using Finset.biUnion_singleton

/-- Subdivision preserves the rooted support tree before the reticulation arcs
are inserted. The construction follows the actual canonical wires. -/
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
