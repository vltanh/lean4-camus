module

public import Camus.Network.Completeness.Splitting

/-!
# Order of endpoints on a shared wire

Non-tree edges with disjoint cycles may have endpoints inside the same wire. On the wire above
`p`, the canonical network places the endpoint of an outer cycle before the donor of a ghost pair
with target `p` (`Realization.outerEndpoints`, `Realization.ghostEndpoints`); a pair `(u, w)` is a
ghost pair when `u = lca(u, w)`. This file shows that `N` has the same order. If the ghost donor
`u'` came first, the cycle of its edge, which runs from `u'` down the wire to `H.original p`,
would pass through the later endpoint, which lies on another cycle.

## Main results

* `SupportSubdivision.no_ghost_before_endpoint`: the wire of `p` is not
  `[H.original (parent p), u', v, H.original p]` with `u'` the ghost donor of an edge with target
  `p` and `v` an endpoint of another non-tree edge.
-/

@[expose] public section

namespace Camus.SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- Let `d` be a non-tree edge whose pair has target `p`, and let `v` be an endpoint of another
non-tree edge `f`. Then the wire of `p` is not `[H.original (parent p), d.1, v, H.original p]`.
Otherwise the tail of `d` lies inside the wire of `p`, so its pair `(u, w)` has `u = p = lca(u, w)`
(a ghost pair) and `p` lies on `γ(u, w)`. The cycle of `d` then contains the switching path from
`H.original p` to `d.1`, which passes through `v`, and `v` lies on the cycle of `f`. -/
theorem no_ghost_before_endpoint (H : SupportSubdivision t N S)
    (hN : N.RootedBinaryLevelOne) {e f : ℕ × ℕ}
    (he : e ∈ N.edges \ S) (hf : f ∈ N.edges \ S) (hef : e ≠ f)
    {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ [])
    (hghost : EdgeAbove.target (H.pairOf e) = p) {v : ℕ}
    (hv : v = f.1 ∨ v = f.2)
    (hwire : H.wire p = [H.original (parent p),e.1,v,H.original p]) : False := by
  classical
  have he₁ : (e.1,v) ∈ S := H.wire_edge_mem_support hp hp0
    (by rw [hwire]; simp [wireEdges])
  have he₂ : (v,H.original p) ∈ S := H.wire_edge_mem_support hp hp0
    (by rw [hwire]; simp [wireEdges])
  have hne₁ : H.original p ≠ v := (RootedNetwork.edge_ne hN (H.switching.1 he₂)).symm
  have hne₂ : H.original p ≠ e.1 := by
    intro h
    exact H.deleted_source_not_original hN he (Finset.mem_image.mpr ⟨p,hp,h⟩)
  have hne₃ : v ≠ e.1 := (RootedNetwork.edge_ne hN (H.switching.1 he₁)).symm
  let z : ({N with edges := S}).underlying.Walk (H.original p) e.1 :=
    .cons ⟨hne₁,Or.inr he₂⟩ (.cons ⟨hne₃,Or.inr he₁⟩ .nil)
  have hz : z.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    change [H.original p,v,e.1].Nodup
    simp [hne₁,hne₂,hne₃]
  have hfoot : p ∈ EdgeAbove.footprint t (H.pairOf e) := by
    rw [← hghost]
    exact EdgeAbove.target_mem_footprint t _ (H.deleted_pair_admissible hN he)
  have hcycle := H.footprint_mem_fundamentalCycle hN he hfoot
  let a := (RootedNetwork.supportPath hN H.switching he).val
  have ha : H.original p ∈ a.support := by
    change H.original p ∈ e.1 :: (a.mapLe _).support at hcycle
    rw [SimpleGraph.Walk.support_mapLe_eq_support,List.mem_cons] at hcycle
    rcases hcycle with hcycle | hcycle
    · exact False.elim (hne₂ hcycle)
    · exact hcycle
  let b := a.dropUntil (H.original p) ha
  have hb : b.IsPath := SimpleGraph.Walk.isPath_of_isSubwalk
    (a.isSubwalk_dropUntil ha) (RootedNetwork.supportPath hN H.switching he).isPath
  have hzb : z = b := Subtype.mk.inj
    ((RootedNetwork.switching_acyclic hN H.switching).subsingleton_path _ _ |>.elim ⟨z,hz⟩ ⟨b,hb⟩)
  have hvb : v ∈ b.support := by
    rw [← hzb]
    change v ∈ [H.original p,v,e.1]
    simp
  have hva : v ∈ a.support := a.support_dropUntil_subset_support ha hvb
  have hvce : v ∈ (RootedNetwork.fundamentalCycle hN H.switching he).support := by
    change v ∈ e.1 :: (a.mapLe _).support
    rw [SimpleGraph.Walk.support_mapLe_eq_support]
    exact List.mem_cons_of_mem _ hva
  have hvcf : v ∈ (RootedNetwork.fundamentalCycle hN H.switching hf).support := by
    rcases hv with h | h
    · rw [h]
      exact RootedNetwork.fundamentalCycle_source_mem hN H.switching hf
    · rw [h]
      exact RootedNetwork.fundamentalCycle_target_mem hN H.switching hf
  exact Finset.disjoint_left.mp (RootedNetwork.fundamentalCycles_disjoint hN H.switching he hf hef)
    (List.mem_toFinset.mpr hvce) (List.mem_toFinset.mpr hvcf)

end Camus.SupportSubdivision
