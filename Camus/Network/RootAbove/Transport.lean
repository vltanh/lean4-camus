module

public import Camus.Network.Completeness.Transport
public import Camus.Network.Completeness.Wires

/-!
# Networks built on `T` with the root kept, up to isomorphism

`RootedNetwork.AnchoredExtension` speaks of a network with its vertex names. This file shows that
it depends only on the network up to isomorphism (`RootedNetwork.AnchoredExtension.of_iso`): a
support subdivision of `T` in `P` is carried to `N` along a map that is injective on the vertices
of `P` and maps the vertices, edges, root and labelled leaves of `P` onto those of `N`
(`SupportSubdivision.map_target`). So a network is built on `T` with the root kept exactly when it
is isomorphic to the canonical network of a cycle-separated family of pairs, as CAMUS outputs.

## Main results

* `SupportSubdivision.map_target`: the transported support subdivision.
* `RootedNetwork.AnchoredExtension.of_iso`: a network isomorphic to a network built on `T` with
  the root kept is built on `T` with the root kept.
-/

@[expose] public section

namespace Camus

namespace SupportSubdivision

variable {t : PhyloTree} {P N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- The vertices of a wire of a support subdivision are vertices of the network. -/
theorem wire_mem (H : SupportSubdivision t P S) {p : Address} (hp : p ∈ t.nodes) (hp0 : p ≠ [])
    {v : ℕ} (hv : v ∈ H.wire p) : v ∈ P.vertices := by
  obtain ⟨_, _, hhead, hlast, _⟩ := H.wire_laws p hp hp0
  rcases wire_vertex_cases hv with h | h | h
  · rw [hhead, Option.some.injEq] at h
    rw [← h]
    exact H.original_mem_vertices (t.nodes_prefix_closed hp (parent_prefix p))
  · rw [hlast, Option.some.injEq] at h
    rw [← h]
    exact H.original_mem_vertices hp
  · exact H.interior_mem_vertices hp hp0 h

/-- Two sets of vertices of `P` that are disjoint have disjoint images under a map injective on
the vertices of `P`. -/
theorem disjoint_image_of_injOn {f : ℕ → ℕ} (hinj : Set.InjOn f P.vertices) {X Y : Finset ℕ}
    (hX : ∀ v ∈ X, v ∈ P.vertices) (hY : ∀ v ∈ Y, v ∈ P.vertices) (hXY : Disjoint X Y) :
    Disjoint (X.image f) (Y.image f) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hwX hwY
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hwX
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hwY
  have := hinj (hY y hy) (hX x hx) hxy
  subst this
  exact Finset.disjoint_left.mp hXY hx hy

/-- A support subdivision of `T` in `P`, carried to `N` along a map `f` that is injective on the
vertices of `P` and maps the vertices, edges, root and labelled leaves of `P` onto those of `N`.
The images of the vertices of `T` are mapped by `f`, and so are the wires and the switching. -/
noncomputable def map_target (H : SupportSubdivision t P S) (hP : ∀ e ∈ P.edges,
      e.1 ∈ P.vertices ∧ e.2 ∈ P.vertices) (f : ℕ → ℕ)
    (hinj : Set.InjOn f P.vertices) (hverts : P.vertices.image f = N.vertices)
    (hedges : P.edges.image (Prod.map f f) = N.edges) (hroot : f P.root = N.root)
    (htaxa : N.taxa = P.taxa) (hleaves : ∀ a ∈ P.taxa, f (P.leaf a) = N.leaf a) :
    SupportSubdivision t N (S.image (Prod.map f f)) := by
  classical
  have hSP := H.switching.1
  -- the vertices of the edges of `S`
  have hSv : ∀ e ∈ S, e.1 ∈ P.vertices ∧ e.2 ∈ P.vertices := fun e he => hP e (hSP he)
  have himg : ∀ v ∈ t.nodes.image H.original, v ∈ P.vertices := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact H.original_mem_vertices hp
  have hint : ∀ p ∈ t.nodes, p ≠ [] → ∀ v ∈ wireInterior (H.wire p), v ∈ P.vertices :=
    fun p hp hp0 v hv => H.interior_mem_vertices hp hp0 hv
  refine
    { original := fun p => f (H.original p)
      wire := fun p => (H.wire p).map f
      original_injective := ?_
      root_preserved := ?_
      taxa_preserved := htaxa.trans H.taxa_preserved
      leaves_preserved := ?_
      wire_laws := ?_
      interiors_disjoint := ?_
      vertices_covered := ?_
      edges_covered := ?_
      switching := ?_ }
  · intro p hp q hq hpq
    exact H.original_injective hp hq
      (hinj (H.original_mem_vertices hp) (H.original_mem_vertices hq) hpq)
  · rw [H.root_preserved, hroot]
  · intro p hp a ha
    have hat : a ∈ P.taxa := by
      rw [H.taxa_preserved]
      exact List.mem_toFinset.mpr (PhyloTree.leaf_label_mem ha)
    rw [H.leaves_preserved p hp a ha, hleaves a hat]
  · intro p hp hp0
    obtain ⟨hlen, hnd, hhead, hlast, hdis⟩ := H.wire_laws p hp hp0
    refine ⟨by rw [List.length_map]; exact hlen, ?_, ?_, ?_, ?_⟩
    · exact hnd.map_on (fun x hx y hy hxy => hinj (H.wire_mem hp hp0 hx) (H.wire_mem hp hp0 hy) hxy)
    · rw [List.head?_map, hhead]
      rfl
    · rw [List.getLast?_map, hlast]
      rfl
    · have himage : t.nodes.image (fun p => f (H.original p)) =
          (t.nodes.image H.original).image f := by
        rw [Finset.image_image]
        rfl
      change Disjoint (wireInterior ((H.wire p).map f)) (t.nodes.image (fun p => f (H.original p)))
      rw [wireInterior_map, himage]
      exact disjoint_image_of_injOn hinj (hint p hp hp0) himg hdis
  · intro p hp q hq hpq
    rw [wireInterior_map, wireInterior_map]
    obtain ⟨hp0, hp'⟩ := Finset.mem_erase.mp hp
    obtain ⟨hq0, hq'⟩ := Finset.mem_erase.mp hq
    exact disjoint_image_of_injOn hinj (hint p hp' hp0) (hint q hq' hq0)
      (H.interiors_disjoint hp hq hpq)
  · rw [← hverts, H.vertices_covered, Finset.image_union, Finset.image_image,
      Finset.biUnion_image]
    congr 1
    apply Finset.biUnion_congr rfl
    intro p _
    exact (wireInterior_map _ f).symm
  · refine (congrArg (Finset.image (Prod.map f f)) H.edges_covered).trans ?_
    rw [Finset.biUnion_image]
    apply Finset.biUnion_congr rfl
    intro p _
    exact (wireEdges_map _ f).symm
  · constructor
    · rw [← hedges]
      exact Finset.image_subset_image hSP
    · intro v hv hvr
      rw [← hverts] at hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      have hur : u ≠ P.root := fun h => hvr (by rw [h, hroot])
      -- the edges of the image into `f u` are the images of the edges of `S` into `u`
      have hfilter : (S.image (Prod.map f f)).filter (fun e => e.2 = f u) =
          (S.filter (fun e => e.2 = u)).image (Prod.map f f) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_image, Prod.map]
        constructor
        · rintro ⟨⟨d, hd, rfl⟩, he⟩
          exact ⟨d, ⟨hd, hinj (hSv d hd).2 hu he⟩, rfl⟩
        · rintro ⟨d, ⟨hd, hdu⟩, rfl⟩
          exact ⟨⟨d, hd, rfl⟩, by rw [hdu]⟩
      rw [hfilter, Finset.card_image_of_injOn, H.switching.2 u hu hur]
      intro d hd d' hd' hdd'
      simp only [Prod.map, Prod.mk.injEq] at hdd'
      have hd1 := hSv d (Finset.mem_filter.mp hd).1
      have hd'1 := hSv d' (Finset.mem_filter.mp hd').1
      exact Prod.ext (hinj hd1.1 hd'1.1 hdd'.1) (hinj hd1.2 hd'1.2 hdd'.2)

end SupportSubdivision

/-- A network isomorphic to a network built on `T` with the root kept is built on `T` with the
root kept: the support subdivision is carried along the inverse of the isomorphism. -/
theorem RootedNetwork.AnchoredExtension.of_iso {t : PhyloTree} {N P : RootedNetwork}
    (hN : N.RootedBinaryLevelOne) (i : N.Iso P) (hP : P.AnchoredExtension t) :
    N.AnchoredExtension t := by
  classical
  obtain ⟨hPbin, S, ⟨H⟩⟩ := hP
  -- the inverse of the isomorphism, on the vertices of `P`
  let f : ℕ → ℕ := fun v => if h : v ∈ P.vertices then (i.vertices.symm ⟨v, h⟩).val else v
  have hf : ∀ v (h : v ∈ P.vertices), f v = (i.vertices.symm ⟨v, h⟩).val :=
    fun v h => dite_eq_left h
  have hfN : ∀ w (h : w ∈ N.vertices), f (i.vertices ⟨w, h⟩).val = w := by
    intro w h
    rw [hf _ (i.vertices ⟨w, h⟩).property]
    simp
  have hinj : Set.InjOn f P.vertices := by
    intro u hu v hv huv
    rw [hf u hu, hf v hv] at huv
    have := i.vertices.symm.injective (Subtype.ext huv)
    exact congrArg Subtype.val this
  have hverts : P.vertices.image f = N.vertices := by
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      rw [hf v hv]
      exact (i.vertices.symm ⟨v, hv⟩).property
    · intro hw
      exact Finset.mem_image.mpr ⟨_, (i.vertices ⟨w, hw⟩).property, hfN w hw⟩
  have hedges : P.edges.image (Prod.map f f) = N.edges := by
    ext e
    constructor
    · intro he
      obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hu, hv⟩ := hPbin.2.1 _ huv
      have h := (i.edges (i.vertices.symm ⟨u, hu⟩) (i.vertices.symm ⟨v, hv⟩)).mpr
        (by simpa using huv)
      simpa [Prod.map, hf u hu, hf v hv] using h
    · intro he
      obtain ⟨hu, hv⟩ := hN.2.1 e he
      have h := (i.edges ⟨e.1, hu⟩ ⟨e.2, hv⟩).mp he
      refine Finset.mem_image.mpr ⟨_, h, ?_⟩
      simp only [Prod.map, hfN e.1 hu, hfN e.2 hv]
  have hroot : f P.root = N.root := by
    rw [hf _ i.root_right, ← i.root_preserved]
    simp
  have hleaves : ∀ a ∈ P.taxa, f (P.leaf a) = N.leaf a := by
    intro a ha
    have haN : a ∈ N.taxa := i.taxa_preserved ▸ ha
    rw [hf _ (i.leaves_right a haN), ← i.leaves_preserved a haN]
    simp
  exact ⟨hN, _, ⟨H.map_target hPbin.2.1 f hinj hverts hedges hroot i.taxa_preserved hleaves⟩⟩

end Camus
