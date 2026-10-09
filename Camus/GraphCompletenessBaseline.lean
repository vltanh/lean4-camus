module

public import Camus.GraphCompletenessWires
public import Camus.GraphRealizationSubdivision

@[expose] public section

namespace Camus.SupportSubdivision

/-- The arbitrary support switching is a graph subdivision of the canonically
encoded constraint tree. This is a construction from its original wire data. -/
noncomputable def baseline_subdivision {t : PhyloTree} {N : RootedNetwork}
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) :
    GraphSubdivision (Realization.graph t ∅) {N with edges := S} := by
  classical
  let f : ℕ → ℕ := fun n => H.original (Realization.addressOf n)
  have hverts : (Realization.graph t ∅).vertices = t.nodes.image Address.code := by
    simp [Realization.graph]
  have hinj : Set.InjOn f (Realization.graph t ∅).vertices := by
    intro u hu v hv huv
    rw [hverts] at hu hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
    simp only [f, Realization.addressOf_code] at huv
    exact congrArg Address.code (H.original_injective hp hq huv)
  refine
    { original := f
      wire := fun e => H.wire (Realization.addressOf e.2)
      original_injective := hinj
      root_left := ?_
      root_preserved := ?_
      taxa_preserved := H.taxa_preserved
      leaves_left := ?_
      leaves_preserved := ?_
      edge_endpoints := ?_
      wire_laws := ?_
      interiors_disjoint := ?_
      vertices_covered := ?_
      edges_covered := ?_ }
  · rw [hverts]
    exact Finset.mem_image.mpr ⟨[],t.root_mem_nodes,rfl⟩
  · change H.original (Realization.addressOf (Address.code [])) = N.root
    rw [Realization.addressOf_code]
    exact H.root_preserved
  · intro a ha
    rw [hverts]
    exact Finset.mem_image.mpr ⟨Realization.leafAddress t a,
      Realization.leafAddress_mem_nodes ha,rfl⟩
  · intro a ha
    change H.original (Realization.addressOf (Address.code (Realization.leafAddress t a))) = N.leaf a
    rw [Realization.addressOf_code]
    exact H.leaves_preserved _ (Realization.leafAddress_mem_nodes ha) a
      (Realization.leafAddress_nodeAt ha)
  · intro e he
    rw [Realization.baseline_edges] at he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    have hp' := Finset.mem_erase.mp hp
    rw [hverts]
    exact ⟨Finset.mem_image.mpr ⟨parent p,
      t.nodes_prefix_closed hp'.2 (parent_prefix p),rfl⟩,
      Finset.mem_image.mpr ⟨p,hp'.2,rfl⟩⟩
  · intro e he
    rw [Realization.baseline_edges] at he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    have hp' := Finset.mem_erase.mp hp
    simp only [Realization.addressOf_code, f]
    rw [hverts, Finset.image_image]
    simp only [Function.comp_def, Realization.addressOf_code]
    exact H.wire_laws p hp'.2 hp'.1
  · intro e he g hg heg
    rw [Realization.baseline_edges] at he hg
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hg
    have hpq : p ≠ q := by
      intro h
      subst q
      exact heg rfl
    simpa only [Realization.addressOf_code] using H.interiors_disjoint hp hq hpq
  · change N.vertices = (Realization.graph t ∅).vertices.image f ∪ _
    rw [hverts, Finset.image_image, Realization.baseline_edges, Finset.image_biUnion]
    simp only [Function.comp_def, f, Realization.addressOf_code]
    exact H.vertices_covered
  · change S = _
    rw [Realization.baseline_edges, Finset.image_biUnion]
    simp only [Realization.addressOf_code]
    exact H.edges_covered

end Camus.SupportSubdivision
