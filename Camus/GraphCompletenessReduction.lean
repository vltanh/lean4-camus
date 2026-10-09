module

public import Camus.GraphCompletenessDecode
public import Camus.GraphCompletenessAddEdge

@[expose] public section

namespace Camus.SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- Transport the canonical selected-edge subdivision to the original graph.
The input is the concrete refinement of canonical support wires. -/
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
