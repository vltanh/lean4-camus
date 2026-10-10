module

public import Camus.Network.Completeness.Decode
public import Camus.Network.Completeness.AddEdge

/-!
# The single-edge network T + e

For a non-tree edge `d`, Section 2.1 defines `T + d` as the subnetwork of `N` obtained by
removing all other non-tree edges and then suppressing the vertices of indegree and outdegree
one. `SupportSubdivision.single_edge_reduction` states it as a subdivision: `N` restricted to the
edges `S ∪ {d}` is a subdivision of the canonical network `Realization.graph t {H.pairOf d}`.
This file reduces that statement to a subdivision between the supports of two canonical networks:
add the edge of `H.pairOf d` to both (`GraphSubdivision.addEdge`), then move the result to `N`
along the decoding (`GraphSubdivision.map_target`).

## Main results

* `SupportSubdivision.transport_single_refinement`: the reduction step.
-/

@[expose] public section

namespace Camus.SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- Let `d` be a non-tree edge, and let `R` show that the support of
`Realization.graph t H.extracted` is a subdivision of the support of
`Realization.graph t {H.pairOf d}`, with the identity as vertex map. Then `N` restricted to the
edges `S ∪ {d}` is a subdivision of `Realization.graph t {H.pairOf d}`. The proof adds the edge
from the donor to the recipient of `H.pairOf d` to both supports and transports the result along
the decoding. -/
theorem transport_single_refinement (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne)
    (hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)))
    (hsep : EdgeAbove.CycleSeparated t H.extracted)
    {e : ℕ × ℕ} (he : e ∈ N.edges \ S)
    (R : GraphSubdivision
      {Realization.graph t {H.pairOf e} with edges := Realization.supportEdges t {H.pairOf e}}
      {Realization.graph t H.extracted with edges := Realization.supportEdges t H.extracted})
    (hid : R.original = id) :
    Nonempty (GraphSubdivision (Realization.graph t {H.pairOf e})
      {N with edges := insert e S}) := by
  classical
  have hpair : H.pairOf e ∈ H.extracted := Finset.mem_image.mpr ⟨e,he,rfl⟩
  have hcand : {H.pairOf e} ⊆ EdgeAbove.candidates t :=
    Finset.singleton_subset_iff.mpr (hsep.1 hpair)
  have hends : Realization.donor t (H.pairOf e) ∈
      (Realization.graph t {H.pairOf e}).vertices ∧
      Realization.recipient t (H.pairOf e) ∈
      (Realization.graph t {H.pairOf e}).vertices := by
    simp [Realization.graph]
  let R' := R.addEdge hid
    (Realization.donor t (H.pairOf e),Realization.recipient t (H.pairOf e))
    (Realization.added_edge_not_support hcand (Finset.mem_singleton_self _))
    hends (Realization.donor_ne_recipient t _ _)
  have hsource :
      {Realization.graph t {H.pairOf e} with
        edges := insert (Realization.donor t (H.pairOf e),Realization.recipient t (H.pairOf e))
          (Realization.supportEdges t {H.pairOf e})} =
      Realization.graph t {H.pairOf e} := by
    simp [Realization.graph,Finset.union_comm]
  have R'' : GraphSubdivision (Realization.graph t {H.pairOf e})
      {Realization.graph t H.extracted with
        edges := insert (Realization.donor t (H.pairOf e),Realization.recipient t (H.pairOf e))
          (Realization.supportEdges t H.extracted)} := by
    simpa only [hsource] using R'
  exact ⟨R''.map_target (H.decode hN hpairs)
    (H.decode_injective hN hpairs) (H.decode_vertices_image hN hpairs)
    (H.decode_single_edges_image hN hpairs hsep he) (H.decode_root hN hpairs)
    H.taxa_preserved (fun a ha => H.decode_leaf hN hpairs ha)⟩

end Camus.SupportSubdivision
