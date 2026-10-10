module

public import Camus.Network.Completeness.Transport

/-!
# Adding an edge to a subdivision

If `N` is a subdivision of `P` that keeps the names of the vertices of `P`, adding an edge
`e ∉ P.edges` between two distinct vertices of `P` to both networks gives a subdivision again;
the wire of `e` is `e` itself. The single-edge reduction
(`SupportSubdivision.single_edge_reduction`) uses it to add the retained non-tree edge.

## Main results

* `GraphSubdivision.addEdge`: the subdivision with the edge added.
-/

@[expose] public section

namespace Camus.GraphSubdivision

/-- Let `N` be a subdivision of `P` whose vertex map is the identity, and let `e ∉ P.edges` join
two distinct vertices of `P`. Adding `e` to the edges of `P` and of `N` gives a subdivision, in
which the wire of `e` is `[e.1, e.2]` and the other wires are unchanged. -/
noncomputable def addEdge {P N : RootedNetwork} (H : GraphSubdivision P N)
    (hid : H.original = id) (e : ℕ × ℕ) (he : e ∉ P.edges)
    (hends : e.1 ∈ P.vertices ∧ e.2 ∈ P.vertices) (hne : e.1 ≠ e.2) :
    GraphSubdivision {P with edges := insert e P.edges}
      {N with edges := insert e N.edges} := by
  classical
  let W : (ℕ × ℕ) → List ℕ := fun f => if f = e then [e.1,e.2] else H.wire f
  have hnew : W e = [e.1,e.2] := by simp [W]
  have hold : ∀ f ∈ P.edges, W f = H.wire f := by
    intro f hf
    simp only [W,ite_eq_right (show f ≠ e from fun h => he (h ▸ hf))]
  have hi : wireInterior [e.1,e.2] = ∅ := by simp [wireInterior]
  have hed : wireEdges [e.1,e.2] = {e} := by simp [wireEdges]
  refine
    { original := id
      wire := W
      original_injective := Function.injective_id.injOn
      root_left := H.root_left
      root_preserved := by simpa only [hid,id_eq] using H.root_preserved
      taxa_preserved := H.taxa_preserved
      leaves_left := H.leaves_left
      leaves_preserved := by simpa only [hid,id_eq] using H.leaves_preserved
      edge_endpoints := ?_
      wire_laws := ?_
      interiors_disjoint := ?_
      vertices_covered := ?_
      edges_covered := ?_ }
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact hends
    · exact H.edge_endpoints f hf
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · rw [hnew]
      refine ⟨by simp,by simpa using hne,by simp,by simp,?_⟩
      rw [hi]
      exact Finset.disjoint_empty_left _
    · rw [hold f hf]
      simpa only [hid,id_eq,Finset.image_id] using H.wire_laws f hf
  · intro f hf g hg hfg
    rcases Finset.mem_insert.mp hf with rfl | hf
    · rw [hnew,hi]
      exact Finset.disjoint_empty_left _
    · rcases Finset.mem_insert.mp hg with rfl | hg
      · rw [hnew,hi]
        exact Finset.disjoint_empty_right _
      · rw [hold f hf,hold g hg]
        exact H.interiors_disjoint hf hg hfg
  · have hrest : P.edges.biUnion (fun f => wireInterior (W f)) =
        P.edges.biUnion (fun f => wireInterior (H.wire f)) := by
      apply Finset.biUnion_congr rfl
      intro f hf
      rw [hold f hf]
    change N.vertices = P.vertices.image id ∪ _
    rw [Finset.biUnion_insert,hnew,hi,Finset.empty_union,hrest]
    simpa only [hid,Finset.image_id] using H.vertices_covered
  · have hrest : P.edges.biUnion (fun f => wireEdges (W f)) =
        P.edges.biUnion (fun f => wireEdges (H.wire f)) := by
      apply Finset.biUnion_congr rfl
      intro f hf
      rw [hold f hf]
    change insert e N.edges = _
    rw [Finset.biUnion_insert,hnew,hed,hrest,←H.edges_covered]
    simp

end Camus.GraphSubdivision
