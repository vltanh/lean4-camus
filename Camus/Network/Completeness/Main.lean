module

public import Camus.Network.Realization.Construction
public import Camus.Network.Baseline.Main
public import Camus.Network.Completeness.Footprints
public import Camus.Network.Completeness.Iso
public import Camus.Network.Completeness.Reduction
public import Camus.Network.Realization.Refinement
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace Camus

namespace SupportSubdivision

/-- Completeness, part 1: extract admissible pairs whose original cycle
footprints are disjoint from every actual rooted level-1 support extension. -/
theorem extracted_separated {t : PhyloTree}
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) :
    EdgeAbove.CycleSeparated t H.extracted := by
  classical
  refine ⟨H.extracted_subset_candidates hN, ?_⟩
  intro p hp q hq hpq
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
  have hef : e ≠ f := by
    intro hef
    subst f
    exact hpq rfl
  apply Finset.disjoint_left.mpr
  intro x hxe hxf
  exact Finset.disjoint_left.mp
    (RootedNetwork.fundamentalCycles_disjoint hN H.switching he hf hef)
    (List.mem_toFinset.mpr (H.footprint_mem_fundamentalCycle hN he hxe))
    (List.mem_toFinset.mpr (H.footprint_mem_fundamentalCycle hN hf hxf))

/-- Distinct deleted edges cannot contract to the same ordered pair. -/
theorem pairOf_injective {t : PhyloTree}
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) :
    Set.InjOn H.pairOf (N.edges \ S) := by
  classical
  intro e he f hf hpair
  have he' : e ∈ (N.edges \ S : Finset (ℕ × ℕ)) := by simpa using he
  have hf' : f ∈ (N.edges \ S : Finset (ℕ × ℕ)) := by simpa using hf
  by_contra hef
  have hmem := EdgeAbove.target_mem_footprint t (H.pairOf e)
    (H.deleted_pair_admissible hN he')
  have hmem' : EdgeAbove.target (H.pairOf e) ∈ EdgeAbove.footprint t (H.pairOf f) := by
    rw [← hpair]
    exact hmem
  exact Finset.disjoint_left.mp
    (RootedNetwork.fundamentalCycles_disjoint hN H.switching he' hf' hef)
    (List.mem_toFinset.mpr (H.footprint_mem_fundamentalCycle hN he' hmem))
    (List.mem_toFinset.mpr (H.footprint_mem_fundamentalCycle hN hf' hmem'))

/-- Completeness, part 2: canonical realization recovers the arbitrary graph,
including the forced order on any shared subdivided wire. -/
theorem canonical_iso {t : PhyloTree}
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S) :
    Nonempty (N.Iso (Realization.graph t H.extracted)) := by
  have hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)) := by
    simpa using pairOf_injective hN H
  exact ⟨H.canonicalIso hN hpairs (extracted_separated hN H)⟩

/-- Definition 1's deletion/suppression bridge: retain the selected non-tree
edge, delete the others, then suppress their unary endpoints. -/
theorem single_edge_reduction {t : PhyloTree}
    {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (H : SupportSubdivision t N S)
    {e : ℕ × ℕ} (he : e ∈ N.edges \ S) :
    Nonempty (GraphSubdivision (Realization.graph t {H.pairOf e})
      {N with edges := insert e S}) := by
  classical
  have hpairs : Set.InjOn H.pairOf (N.edges \ S : Finset (ℕ × ℕ)) := by
    simpa using pairOf_injective hN H
  have hsep := extracted_separated hN H
  have hpair : H.pairOf e ∈ H.extracted := Finset.mem_image.mpr ⟨e,he,rfl⟩
  exact H.transport_single_refinement hN hpairs hsep he
    (Realization.singletonSupportSubdivision hsep hpair)
    (Realization.singletonSupportSubdivision_original hsep hpair)

end SupportSubdivision

end Camus
