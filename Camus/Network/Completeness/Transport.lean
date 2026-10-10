module

public import Camus.Network.Subdivision.Incoming
public import Camus.Network.Completeness.Iso

/-!
# Transporting a subdivision along an isomorphism

`GraphSubdivision P Q` says that `Q` is obtained from `P` by subdividing edges. If a map `f` is
injective on the vertices of `Q` and maps the vertices, edges, root and labelled leaves of `Q`
onto those of `M`, then `M` is a subdivision of `P` too. The single-edge reduction
(`SupportSubdivision.single_edge_reduction`) uses this to move a subdivision of a canonical
network to `N` along the decoding.

## Main results

* `GraphSubdivision.map_target`: the transported subdivision.
-/

@[expose] public section

namespace Camus

/-- The interior of the image of a wire under `f` is the image of its interior. -/
theorem wireInterior_map (l : List ℕ) (f : ℕ → ℕ) :
    wireInterior (l.map f) = (wireInterior l).image f := by
  classical
  ext v
  simp only [wireInterior,← List.map_tail,← List.map_dropLast,
    List.mem_toFinset,List.mem_map,Finset.mem_image]

namespace GraphSubdivision

variable {P Q M : RootedNetwork}

/-- The vertices of the wire of an edge of `P` are vertices of `Q`. -/
theorem wire_mem_vertices (R : GraphSubdivision P Q) {e : ℕ × ℕ}
    (he : e ∈ P.edges) {v : ℕ} (hv : v ∈ R.wire e) : v ∈ Q.vertices := by
  rcases wire_vertex_cases hv with hh | hl | hi
  · have hveq : v = R.original e.1 := Option.some.inj
      (hh.symm.trans (R.wire_laws e he).2.2.1)
    rw [hveq]
    exact R.original_mem_vertices (R.edge_endpoints e he).1
  · have hveq : v = R.original e.2 := Option.some.inj
      (hl.symm.trans (R.wire_laws e he).2.2.2.1)
    rw [hveq]
    exact R.original_mem_vertices (R.edge_endpoints e he).2
  · exact R.interior_mem_vertices he hi

/-- Let `R` show that `Q` is a subdivision of `P`, and let `f` be injective on the vertices of
`Q` and map the vertices, edges, root and labelled leaves of `Q` onto those of `M`. Then `M` is a
subdivision of `P`, with vertex map `f ∘ R.original` and wires mapped by `f`. -/
noncomputable def map_target (R : GraphSubdivision P Q) (f : ℕ → ℕ)
    (hinj : Set.InjOn f Q.vertices)
    (hverts : Q.vertices.image f = M.vertices)
    (hedges : Q.edges.image (Prod.map f f) = M.edges)
    (hroot : f Q.root = M.root) (htaxa : M.taxa = Q.taxa)
    (hleaves : ∀ a ∈ Q.taxa, f (Q.leaf a) = M.leaf a) :
    GraphSubdivision P M := by
  classical
  refine
    { original := fun v => f (R.original v)
      wire := fun e => (R.wire e).map f
      original_injective := ?_
      root_left := R.root_left
      root_preserved := ?_
      taxa_preserved := htaxa.trans R.taxa_preserved
      leaves_left := R.leaves_left
      leaves_preserved := ?_
      edge_endpoints := R.edge_endpoints
      wire_laws := ?_
      interiors_disjoint := ?_
      vertices_covered := ?_
      edges_covered := ?_ }
  · intro u hu v hv huv
    exact R.original_injective hu hv (hinj
      (R.original_mem_vertices hu) (R.original_mem_vertices hv) huv)
  · rw [R.root_preserved]
    exact hroot
  · intro a ha
    rw [R.leaves_preserved a ha]
    exact hleaves a (R.taxa_preserved.symm ▸ ha)
  · intro e he
    have hw := R.wire_laws e he
    refine ⟨by simpa only [List.length_map] using hw.1,
      hw.2.1.map_on (fun u hu v hv huv => hinj (R.wire_mem_vertices he hu)
        (R.wire_mem_vertices he hv) huv), ?_, ?_, ?_⟩
    · simp only [List.head?_map,hw.2.2.1,Option.map_some]
    · simp only [List.getLast?_map,hw.2.2.2.1,Option.map_some]
    · rw [wireInterior_map]
      apply Finset.disjoint_left.mpr
      intro v hv ho
      obtain ⟨u,hu,huf⟩ := Finset.mem_image.mp hv
      obtain ⟨w,hwP,hwf⟩ := Finset.mem_image.mp ho
      have huw : u = R.original w := hinj (R.interior_mem_vertices he hu)
        (R.original_mem_vertices hwP) (huf.trans hwf.symm)
      exact Finset.disjoint_left.mp hw.2.2.2.2 hu
        (Finset.mem_image.mpr ⟨w,hwP,huw.symm⟩)
  · intro e he g hg heg
    rw [wireInterior_map,wireInterior_map]
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨u,hu,huf⟩ := Finset.mem_image.mp hv
    obtain ⟨w,hw,hwf⟩ := Finset.mem_image.mp hw
    have huw := hinj (R.interior_mem_vertices he hu) (R.interior_mem_vertices hg hw)
      (huf.trans hwf.symm)
    exact Finset.disjoint_left.mp (R.interiors_disjoint he hg heg) hu (huw.symm ▸ hw)
  · rw [← hverts,R.vertices_covered,Finset.image_union,Finset.image_image,Finset.biUnion_image]
    simp only [Function.comp_def,wireInterior_map]
  · rw [← hedges,R.edges_covered,Finset.biUnion_image]
    simp only [wireEdges_map]

end GraphSubdivision
end Camus
