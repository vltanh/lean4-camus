module

public import Camus.Network.Realization.Subdivision
public import Camus.Network.Completeness.Splitting

/-!
# The canonical network of an edge family: splitting wires, and `T + e`

Section 2.1 defines `T + e`, for a non-tree edge `e` of a network built on `T`: delete the other
non-tree edges, then suppress the vertices of indegree and outdegree one. For the canonical
network this reduction amounts to splitting wires. Let `(u, w)` be a pair of a cycle-separated
family `E`. The support of `Realization.graph t E` is a subdivision of the support of
`Realization.graph t {(u, w)}`, which is `T` with the edges above `u` and `w` subdivided by `u′`
and `w′` (`Realization.singletonSupportSubdivision`). It is obtained from the subdivision of `T`
in `Realization.supportGraphSubdivision` by splitting the wire above `u` at `u′`, then the wire
above `w` at `w′` (`GraphSubdivision.splitIdentity`). `SupportSubdivision.single_edge_reduction`
uses it to show that for a non-tree edge `e` with pair `(u, w)` of a network built on `T`, the
network with its other non-tree edges removed is a subdivision of `Realization.graph t {(u, w)}`.
Suppressing its vertices of indegree and outdegree one therefore gives
`Realization.graph t {(u, w)}`: this is `T + e`, in the form in which Lemma 1 uses it.

## Main results

* `RootedNetwork.splitAt`: subdivide one edge of a network by a vertex.
* `GraphSubdivision.splitIdentity`: if a subdivision has the identity as vertex map, cutting the
  wire of an edge at an interior vertex `k` gives a subdivision of the coarse network with that
  edge subdivided by `k`.
* `Realization.singleton_support_split`: for `e = (u, w)`, the support of
  `Realization.graph t {e}` is `T` with the edges above `u` and `w` subdivided by `u′` and `w′`.
* `Realization.singletonSupportSubdivision`: for `e ∈ E`, the support of `Realization.graph t E`
  is a subdivision of the support of `Realization.graph t {e}`, with the identity as vertex map
  (`Realization.singletonSupportSubdivision_original`).
-/

@[expose] public section

namespace Camus

namespace WireSplit

/-- The upper part of a split wire runs from its first vertex to the splitting vertex; its
interior is contained in the interior of the wire. -/
theorem upper_interior_subset {l : List ℕ} {v : ℕ} (W : WireSplit l v) :
    wireInterior W.upper ⊆ wireInterior l := by
  rw [W.interior_covered]
  exact Finset.subset_union_right.trans (Finset.subset_union_left)

/-- The lower part of a split wire runs from the splitting vertex to its last vertex; its
interior is contained in the interior of the wire. -/
theorem lower_interior_subset {l : List ℕ} {v : ℕ} (W : WireSplit l v) :
    wireInterior W.lower ⊆ wireInterior l := by
  rw [W.interior_covered]
  exact Finset.subset_union_right

/-- For a wire without repetition, the splitting vertex is not inside the upper part. -/
theorem upper_interior_not_marker {l : List ℕ} {v : ℕ} (W : WireSplit l v) (hl : l.Nodup) :
    v ∉ wireInterior W.upper := by
  obtain ⟨a,b,heq,ha,hb⟩ := W
  have hn := List.nodup_append.mp (heq ▸ hl)
  have hva : v ∉ a := fun hv => hn.2.2 v hv v List.mem_cons_self rfl
  intro hv
  have hmem : v ∈ (a ++ [v]).tail.dropLast := List.mem_toFinset.mp hv
  have hdrop : (a ++ [v]).dropLast = a := by simp
  have hvs : v ∈ (a ++ [v]).dropLast := List.mem_of_mem_tail (by
    simpa only [List.tail_dropLast] using hmem)
  exact hva (hdrop ▸ hvs)

/-- For a wire without repetition, the splitting vertex is not inside the lower part. -/
theorem lower_interior_not_marker {l : List ℕ} {v : ℕ} (W : WireSplit l v) (hl : l.Nodup) :
    v ∉ wireInterior W.lower := by
  have hn := List.nodup_cons.mp (W.lower_nodup hl)
  intro hv
  exact hn.1 (List.mem_of_mem_dropLast (List.mem_toFinset.mp hv))

/-- For a wire without repetition, the two parts of a split have disjoint interiors. -/
theorem interiors_disjoint {l : List ℕ} {v : ℕ} (W : WireSplit l v) (hl : l.Nodup) :
    Disjoint (wireInterior W.upper) (wireInterior W.lower) := by
  obtain ⟨a,b,heq,ha,hb⟩ := W
  have hn := List.nodup_append.mp (heq ▸ hl)
  rw [Finset.disjoint_left]
  intro w hu hlower
  have huppermem : w ∈ a := by
    have hu' : w ∈ (a ++ [v]).tail.dropLast := List.mem_toFinset.mp hu
    have hmem := List.mem_of_mem_tail (by
      simpa only [←List.tail_dropLast] using hu')
    simpa using hmem
  have hlowermem : w ∈ b := List.mem_of_mem_dropLast (List.mem_toFinset.mp hlower)
  exact hn.2.2 w huppermem w (List.mem_cons_of_mem v hlowermem) rfl

end WireSplit

namespace RootedNetwork

/-- The network `P` with its edge `e = (a, b)` subdivided by the vertex `k`: `k` is added, and
the edge `a → b` is replaced by `a → k` and `k → b`. -/
noncomputable def splitAt (P : RootedNetwork) (e : ℕ × ℕ) (k : ℕ) : RootedNetwork :=
  { vertices := insert k P.vertices
    edges := P.edges.erase e ∪ {(e.1,k),(k,e.2)}
    root := P.root
    taxa := P.taxa
    leaf := P.leaf }

end RootedNetwork

namespace GraphSubdivision

/-- The wires of a subdivision after the wire of `e = (a, b)` is split at `k`: the edge
`a → k` gets the upper part, the edge `k → b` the lower part, and every other edge keeps its
wire. -/
noncomputable def splitWire {P N : RootedNetwork} (H : GraphSubdivision P N)
    (e : ℕ × ℕ) (k : ℕ) (W : WireSplit (H.wire e) k) (f : ℕ × ℕ) : List ℕ :=
  if f = (e.1,k) then W.upper else if f = (k,e.2) then W.lower else H.wire f

/-- If `k` is not a vertex of `P`, every edge of `P` keeps its wire. -/
theorem splitWire_old {P N : RootedNetwork} (H : GraphSubdivision P N)
    (e : ℕ × ℕ) {k : ℕ} (hk : k ∉ P.vertices) (W : WireSplit (H.wire e) k)
    {f : ℕ × ℕ} (hf : f ∈ P.edges) : H.splitWire e k W f = H.wire f := by
  have hends := H.edge_endpoints f hf
  have hu : f ≠ (e.1,k) := by
    intro h
    exact hk (by simpa only [h] using hends.2)
  have hl : f ≠ (k,e.2) := by
    intro h
    exact hk (by simpa only [h] using hends.1)
  simp [splitWire,hu,hl]

/-- The edge `a → k` gets the upper part of the split wire. -/
theorem splitWire_upper {P N : RootedNetwork} (H : GraphSubdivision P N)
    (e : ℕ × ℕ) (k : ℕ) (W : WireSplit (H.wire e) k) :
    H.splitWire e k W (e.1,k) = W.upper := by simp [splitWire]

/-- The edge `k → b` gets the lower part of the split wire. -/
theorem splitWire_lower {P N : RootedNetwork} (H : GraphSubdivision P N)
    {e : ℕ × ℕ} (he : e ∈ P.edges) {k : ℕ} (hk : k ∉ P.vertices)
    (W : WireSplit (H.wire e) k) : H.splitWire e k W (k,e.2) = W.lower := by
  have hke : k ≠ e.1 := fun h => hk (h ▸ (H.edge_endpoints e he).1)
  simp [splitWire,hke]

/-- Let `H` be a subdivision of `P` in `N` whose vertex map is the identity, `e` an edge of
`P`, and `k` a vertex inside the wire of `e`. Then `N` is a subdivision of `P` with `e`
subdivided by `k`: the wire of `e` is cut at `k` into the wires of the two edges through `k`. -/
noncomputable def splitIdentity {P N : RootedNetwork} (H : GraphSubdivision P N)
    (hid : H.original = id) (e : ℕ × ℕ) (he : e ∈ P.edges) (k : ℕ)
    (hmark : k ∈ wireInterior (H.wire e)) (W : WireSplit (H.wire e) k) :
    GraphSubdivision (P.splitAt e k) N := by
  classical
  have hwl := H.wire_laws e he
  have hk : k ∉ P.vertices := by
    intro hk
    exact Finset.disjoint_left.mp hwl.2.2.2.2 hmark
      (by simpa only [hid,Finset.image_id] using hk)
  have he1 := (H.edge_endpoints e he).1
  have he2 := (H.edge_endpoints e he).2
  have hk1 : k ≠ e.1 := fun h => hk (h ▸ he1)
  have hk2 : k ≠ e.2 := fun h => hk (h ▸ he2)
  have hlw := H.splitWire_lower he hk W
  have huw := H.splitWire_upper e k W
  have hold : ∀ f ∈ P.edges.erase e, H.splitWire e k W f = H.wire f :=
    fun f hf => H.splitWire_old e hk W (Finset.mem_erase.mp hf).2
  have hdisOld (f : ℕ × ℕ) (hf : f ∈ P.edges.erase e) :
      Disjoint (wireInterior (H.wire e)) (wireInterior (H.wire f)) :=
    H.interiors_disjoint he (Finset.mem_erase.mp hf).2 (Ne.symm (Finset.mem_erase.mp hf).1)
  have hnotOld (f : ℕ × ℕ) (hf : f ∈ P.edges.erase e) : k ∉ wireInterior (H.wire f) :=
    fun h => Finset.disjoint_left.mp (hdisOld f hf) hmark h
  refine
    { original := id
      wire := H.splitWire e k W
      original_injective := Function.injective_id.injOn
      root_left := Finset.mem_insert_of_mem H.root_left
      root_preserved := by simpa only [hid,id_eq,RootedNetwork.splitAt] using H.root_preserved
      taxa_preserved := H.taxa_preserved
      leaves_left := fun a ha => Finset.mem_insert_of_mem (H.leaves_left a ha)
      leaves_preserved := by simpa only [hid,id_eq,RootedNetwork.splitAt] using H.leaves_preserved
      edge_endpoints := ?_
      wire_laws := ?_
      interiors_disjoint := ?_
      vertices_covered := ?_
      edges_covered := ?_ }
  · intro f hf
    rcases Finset.mem_union.mp hf with hold | hnew
    · have hends := H.edge_endpoints f (Finset.mem_erase.mp hold).2
      exact ⟨Finset.mem_insert_of_mem hends.1,Finset.mem_insert_of_mem hends.2⟩
    · rcases Finset.mem_insert.mp hnew with rfl | hlast
      · exact ⟨Finset.mem_insert_of_mem he1,Finset.mem_insert_self _ _⟩
      · rw [Finset.mem_singleton.mp hlast]
        exact ⟨Finset.mem_insert_self _ _,Finset.mem_insert_of_mem he2⟩
  · intro f hf
    rcases Finset.mem_union.mp hf with hfold | hnew
    · rw [hold f hfold]
      have hf := (Finset.mem_erase.mp hfold).2
      have hlaws := H.wire_laws f hf
      refine ⟨hlaws.1,hlaws.2.1,?_,?_,?_⟩
      · simpa only [hid,id_eq] using hlaws.2.2.1
      · simpa only [hid,id_eq] using hlaws.2.2.2.1
      · simpa only [RootedNetwork.splitAt,Finset.image_id,Finset.disjoint_insert_right] using
          And.intro (hnotOld f hfold) (by simpa only [hid,Finset.image_id] using hlaws.2.2.2.2)
    · rcases Finset.mem_insert.mp hnew with rfl | hlast
      · rw [huw]
        refine ⟨W.upper_length,W.upper_nodup hwl.2.1,?_,W.upper_last,?_⟩
        · simpa only [hid,id_eq] using W.upper_head.trans hwl.2.2.1
        · simp only [RootedNetwork.splitAt,Finset.image_id,Finset.disjoint_insert_right]
          exact ⟨W.upper_interior_not_marker hwl.2.1,
            Finset.disjoint_of_subset_left W.upper_interior_subset
              (by simpa only [hid,Finset.image_id] using hwl.2.2.2.2)⟩
      · rw [Finset.mem_singleton.mp hlast,hlw]
        refine ⟨W.lower_length,W.lower_nodup hwl.2.1,W.lower_head,?_,?_⟩
        · simpa only [hid,id_eq] using W.lower_last.trans hwl.2.2.2.1
        · simp only [RootedNetwork.splitAt,Finset.image_id,Finset.disjoint_insert_right]
          exact ⟨W.lower_interior_not_marker hwl.2.1,
            Finset.disjoint_of_subset_left W.lower_interior_subset
              (by simpa only [hid,Finset.image_id] using hwl.2.2.2.2)⟩
  · intro f hf g hg hfg
    rcases Finset.mem_union.mp hf with hf | hf <;> rcases Finset.mem_union.mp hg with hg | hg
    · rw [hold f hf,hold g hg]
      exact H.interiors_disjoint (Finset.mem_erase.mp hf).2 (Finset.mem_erase.mp hg).2 hfg
    · rw [hold f hf]
      rcases Finset.mem_insert.mp hg with rfl | hlast
      · rw [huw]
        exact Finset.disjoint_of_subset_right W.upper_interior_subset (hdisOld f hf).symm
      · rw [Finset.mem_singleton.mp hlast,hlw]
        exact Finset.disjoint_of_subset_right W.lower_interior_subset (hdisOld f hf).symm
    · rw [hold g hg]
      rcases Finset.mem_insert.mp hf with rfl | hlast
      · rw [huw]
        exact Finset.disjoint_of_subset_left W.upper_interior_subset (hdisOld g hg)
      · rw [Finset.mem_singleton.mp hlast,hlw]
        exact Finset.disjoint_of_subset_left W.lower_interior_subset (hdisOld g hg)
    · rcases Finset.mem_insert.mp hf with rfl | hfl <;> rcases Finset.mem_insert.mp hg with rfl | hgl
      · exact False.elim (hfg rfl)
      · rw [Finset.mem_singleton.mp hgl,huw,hlw]
        exact W.interiors_disjoint hwl.2.1
      · rw [Finset.mem_singleton.mp hfl,hlw,huw]
        exact (W.interiors_disjoint hwl.2.1).symm
      · exact False.elim (hfg ((Finset.mem_singleton.mp hfl).trans (Finset.mem_singleton.mp hgl).symm))
  · rw [H.vertices_covered]
    have hsource : P.edges = insert e (P.edges.erase e) := (Finset.insert_erase he).symm
    rw [hsource,Finset.biUnion_insert]
    simp only [hid,Finset.image_id,RootedNetwork.splitAt,Finset.union_biUnion,
      Finset.biUnion_insert,Finset.singleton_biUnion,huw,hlw]
    have hrest : (P.edges.erase e).biUnion (fun f => wireInterior (H.splitWire e k W f)) =
        (P.edges.erase e).biUnion (fun f => wireInterior (H.wire f)) := by
      apply Finset.biUnion_congr rfl
      intro f hf
      rw [hold f hf]
    rw [hrest,W.interior_covered]
    simp [Finset.union_assoc,Finset.union_comm ]
  · rw [H.edges_covered]
    have hsource : P.edges = insert e (P.edges.erase e) := (Finset.insert_erase he).symm
    rw [hsource,Finset.biUnion_insert]
    simp only [RootedNetwork.splitAt,Finset.union_biUnion,Finset.biUnion_insert,
      Finset.singleton_biUnion,huw,hlw]
    have hrest : (P.edges.erase e).biUnion (fun f => wireEdges (H.splitWire e k W f)) =
        (P.edges.erase e).biUnion (fun f => wireEdges (H.wire f)) := by
      apply Finset.biUnion_congr rfl
      intro f hf
      rw [hold f hf]
    rw [hrest,W.edges_covered]
    simp [Finset.union_assoc,Finset.union_comm ]

/-- `GraphSubdivision.splitIdentity` keeps the identity as vertex map. -/
theorem splitIdentity_original {P N : RootedNetwork} (H : GraphSubdivision P N)
    (hid : H.original = id) (e : ℕ × ℕ) (he : e ∈ P.edges) (k : ℕ)
    (hmark : k ∈ wireInterior (H.wire e)) (W : WireSplit (H.wire e) k) :
    (H.splitIdentity hid e he k hmark W).original = id := rfl

/-- Transporting a subdivision along an equality of coarse networks keeps its vertex map. -/
theorem original_transport {P Q N : RootedNetwork} (h : P = Q)
    (H : GraphSubdivision P N) : (h ▸ H).original = H.original := by
  cases h
  rfl

end GraphSubdivision

namespace Realization

/-- The edge of `T` above `p`, from `parent(p)` to `p`. -/
def originalEdge (p : Address) : ℕ × ℕ := (Address.code (parent p), Address.code p)

/-- Distinct addresses have distinct edges above them. -/
theorem originalEdge_injective : Function.Injective originalEdge := by
  intro p q h
  exact Address.code_injective (congrArg Prod.snd h)

/-- The wires of `Realization.graph t {e}`, for an admissible pair `e = (u, w)`: the wire above
`u` is `parent(u), u′, u`, the wire above `w` is `parent(w), w′, w`, and every other wire is a
single edge. -/
theorem singleton_wire {t : PhyloTree} {e : Pair} (he : EdgeAbove.Admissible t e)
    (p : Address) : wire t {e} p =
      if p = e.1 then [Address.code (parent p),donor t e,Address.code p]
      else if p = e.2 then [Address.code (parent p),recipient t e,Address.code p]
      else [Address.code (parent p),Address.code p] := by
  classical
  have hne : e.1 ≠ e.2 := fun h => he.2.2.2.2 (h ▸ List.prefix_refl e.1)
  by_cases hu : p = e.1
  · subst p
    by_cases ht : EdgeAbove.target e = e.1 <;>
      simp [wire,outerEndpoints,ghostEndpoints,Ne.symm hne,ht]
  · by_cases hw : p = e.2
    · subst p
      simp [wire,outerEndpoints,ghostEndpoints,hne,hu]
    · simp [wire,outerEndpoints,ghostEndpoints,hu,hw,Ne.symm hu,Ne.symm hw]

/-- The support edges of `Realization.graph t {e}`, for an admissible pair `e = (u, w)`: the
edges of `T`, with the edges above `u` and `w` replaced by the paths through `u′` and `w′`. -/
theorem singleton_support {t : PhyloTree} {e : Pair} (he : EdgeAbove.Admissible t e) :
    supportEdges t {e} =
      (((graph t ∅).edges.erase (originalEdge e.1)).erase (originalEdge e.2)) ∪
        {(Address.code (parent e.1),donor t e),(donor t e,Address.code e.1)} ∪
        {(Address.code (parent e.2),recipient t e),(recipient t e,Address.code e.2)} := by
  classical
  let J := t.nodes.erase []
  have hu : e.1 ∈ J := Finset.mem_erase.mpr ⟨he.2.2.1,he.1⟩
  have hw : e.2 ∈ J := Finset.mem_erase.mpr ⟨he.2.2.2.1,he.2.1⟩
  have hne : e.1 ≠ e.2 := fun h => he.2.2.2.2 (h ▸ List.prefix_refl e.1)
  have hJ : J = insert e.1 (insert e.2 ((J.erase e.1).erase e.2)) := by
    ext p
    simp only [Finset.mem_insert,Finset.mem_erase]
    by_cases hpu : p = e.1 <;> by_cases hpw : p = e.2 <;> simp_all
  have hrest : ((J.erase e.1).erase e.2).biUnion (fun p => wireEdges (wire t {e} p)) =
      ((J.erase e.1).erase e.2).image originalEdge := by
    rw [←Finset.biUnion_singleton]
    apply Finset.biUnion_congr rfl
    intro p hp
    have hpw := (Finset.mem_erase.mp hp).1
    have hpu := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
    simp [singleton_wire he p,hpu,hpw,wireEdges,originalEdge]
  change J.biUnion _ = _
  rw [hJ,Finset.biUnion_insert,Finset.biUnion_insert,hrest]
  rw [Finset.image_erase originalEdge_injective,Finset.image_erase originalEdge_injective]
  have hb : J.image originalEdge = (graph t ∅).edges := (baseline_edges t).symm
  rw [hb]
  simp [singleton_wire he e.1,singleton_wire he e.2,Ne.symm hne,wireEdges,
    Finset.union_comm,Finset.insert_comm]

/-- The support of `Realization.graph t {e}`, for an admissible pair `e = (u, w)`, is `T` with
the edge above `u` subdivided by `u′`, then the edge above `w` subdivided by `w′`. -/
theorem singleton_support_split {t : PhyloTree} {e : Pair}
    (he : EdgeAbove.Admissible t e) :
    {graph t {e} with edges := supportEdges t {e}} =
      ((graph t ∅).splitAt (originalEdge e.1) (donor t e)).splitAt
        (originalEdge e.2) (recipient t e) := by
  classical
  have hne : e.1 ≠ e.2 := fun h => he.2.2.2.2 (h ▸ List.prefix_refl e.1)
  have hdw := donor_ne_code e he.2.1
  have hdpw := donor_ne_code e (t.nodes_prefix_closed he.2.1 (parent_prefix e.2))
  have hnew : originalEdge e.2 ∉
      ({(Address.code (parent e.1),donor t e),(donor t e,Address.code e.1)} : Finset (ℕ×ℕ)) := by
    simp only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,originalEdge]
    intro h
    rcases h with h | h
    · exact hdw h.2.symm
    · exact hdpw h.1.symm
  simp only [graph,RootedNetwork.splitAt,RootedNetwork.mk.injEq]
  refine ⟨?_,?_,trivial,trivial,trivial⟩
  · simp [Finset.insert_comm,Finset.union_comm]
  · change supportEdges t {e} =
      (((graph t ∅).splitAt (originalEdge e.1) (donor t e)).splitAt
        (originalEdge e.2) (recipient t e)).edges
    rw [singleton_support he]
    simp only [RootedNetwork.splitAt]
    ext f
    simp only [Finset.mem_union,Finset.mem_erase]
    by_cases hf : f = originalEdge e.2
    · subst f
      simp [originalEdge,Ne.symm hdw,Ne.symm hdpw]
    · simp only [originalEdge] at hf
      simp [hf,originalEdge]

/-- For `e = (u, w)` in a cycle-separated family `E`, the support of `Realization.graph t E` is
a subdivision of the support of `Realization.graph t {e}`. It refines the subdivision of `T` in
`Realization.supportGraphSubdivision` by splitting the wire above `u` at `u′` and the wire above
`w` at `w′`. -/
noncomputable def singletonSupportSubdivision {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) :
    GraphSubdivision {graph t {e} with edges := supportEdges t {e}}
      {graph t E with edges := supportEdges t E} := by
  classical
  let H := supportGraphSubdivision t E hE.1
  have hae := (Finset.mem_filter.mp (hE.1 he)).2
  have hune : e.1 ≠ e.2 := fun h => hae.2.2.2.2 (h ▸ List.prefix_refl e.1)
  have hu : originalEdge e.1 ∈ (graph t ∅).edges := by
    rw [baseline_edges]
    exact Finset.mem_image.mpr ⟨e.1,Finset.mem_erase.mpr ⟨hae.2.2.1,hae.1⟩,rfl⟩
  have hw : originalEdge e.2 ∈ (graph t ∅).edges := by
    rw [baseline_edges]
    exact Finset.mem_image.mpr ⟨e.2,Finset.mem_erase.mpr ⟨hae.2.2.2.1,hae.2.1⟩,rfl⟩
  have huw : originalEdge e.2 ≠ originalEdge e.1 :=
    fun h => hune (originalEdge_injective h).symm
  have hd : donor t e ∈ wireInterior (H.wire (originalEdge e.1)) := by
    change donor t e ∈ wireInterior (wire t E (addressOf (Address.code e.1)))
    rw [addressOf_code]
    exact mem_wireInterior.mpr ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
  -- Split the wire above `u` at `u′`.
  let W := Classical.choice (exists_wireSplit (H.wire_laws _ hu).2.1 hd)
  let H₁ := H.splitIdentity rfl (originalEdge e.1) hu (donor t e) hd W
  have hd0 : donor t e ∉ (graph t ∅).vertices := by
    simp only [graph,Finset.biUnion_empty,Finset.union_empty,Finset.mem_image]
    rintro ⟨p,hp,hpEq⟩
    exact donor_ne_code e hp hpEq.symm
  have hw₁ : originalEdge e.2 ∈ ((graph t ∅).splitAt (originalEdge e.1) (donor t e)).edges :=
    Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨huw,hw⟩)
  have hr : recipient t e ∈ wireInterior (H₁.wire (originalEdge e.2)) := by
    change recipient t e ∈ wireInterior (H.splitWire (originalEdge e.1) (donor t e) W (originalEdge e.2))
    rw [H.splitWire_old _ hd0 W hw]
    change recipient t e ∈ wireInterior (wire t E (addressOf (Address.code e.2)))
    rw [addressOf_code]
    exact mem_wireInterior.mpr ⟨e,he,Or.inr ⟨rfl,rfl⟩⟩
  -- Then split the wire above `w` at `w′`.
  let W₂ := Classical.choice (exists_wireSplit (H₁.wire_laws _ hw₁).2.1 hr)
  let H₂ := H₁.splitIdentity rfl (originalEdge e.2) hw₁ (recipient t e) hr W₂
  -- The coarse network obtained is the support of `Realization.graph t {e}`.
  exact (singleton_support_split hae).symm ▸ H₂

/-- The vertex map of `Realization.singletonSupportSubdivision` is the identity. -/
theorem singletonSupportSubdivision_original {t : PhyloTree} {E : Finset Pair}
    (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) :
    (singletonSupportSubdivision hE he).original = id := by
  classical
  unfold singletonSupportSubdivision
  rw [GraphSubdivision.original_transport]
  rfl


end Realization
end Camus
