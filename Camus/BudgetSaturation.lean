module

public import Camus.ReticulationBudget

@[expose] public section

namespace Camus.EdgeAbove

theorem footprint_internal {t : PhyloTree} {e : Address × Address}
    (he : Admissible t e) : footprint t e ⊆ t.internalNodes := by
  intro p hp
  obtain ⟨hp,hcond⟩ := Finset.mem_filter.mp hp
  obtain ⟨s,hs⟩ := (t.mem_nodes_iff p).mp hp
  rw [PhyloTree.mem_internalNodes_iff]
  cases s with
  | fork l r => exact ⟨l,r,hs⟩
  | leaf a =>
    rcases hcond.2 with ⟨hu,hne⟩ | ⟨hw,hne⟩
    · exact (hne (PhyloTree.leaf_no_descendant hs he.1 hu)).elim
    · exact (hne (PhyloTree.leaf_no_descendant hs he.2.1 hw)).elim

/-- Saturation at n−1 reticulations leaves exactly one original branching
vertex in each cycle. This follows from disjoint footprints, not a bound alone. -/
theorem saturated_footprint {t : PhyloTree} {E : Finset (Address × Address)}
    (hE : CycleSeparated t E) (hcard : E.card = t.internalNodes.card)
    {e : Address × Address} (he : e ∈ E) : footprint t e = {target e} := by
  classical
  have hsub : E.image target ⊆ t.internalNodes := by
    intro p hp
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hp
    exact target_mem_internalNodes (Finset.mem_filter.mp (hE.1 hf)).2
  have hinj : Set.InjOn target E := fun e he f hf h => target_unique t E hE he hf h
  have hall : E.image target = t.internalNodes := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_image_of_injOn hinj,hcard])
  have hae := (Finset.mem_filter.mp (hE.1 he)).2
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨target_mem_footprint t e hae,?_⟩
  intro p hp
  have hpi := footprint_internal hae hp
  rw [←hall] at hpi
  obtain ⟨f,hf,hfp⟩ := Finset.mem_image.mp hpi
  have hpf : p ∈ footprint t f := hfp ▸ target_mem_footprint t f (Finset.mem_filter.mp (hE.1 hf)).2
  have hef : e = f := by
    by_contra hn
    exact Finset.disjoint_left.mp (hE.2 he hf hn) hp hpf
  exact hfp.symm.trans (congrArg target hef).symm

end Camus.EdgeAbove
