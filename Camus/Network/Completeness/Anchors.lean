module

public import Camus.Defs
public import Camus.Tree.Forest
public import Mathlib.Data.Fintype.Card

/-!
# Anchors of the vertices inside wires

This file starts the completeness proof, which shows that every network built on `T` is a
canonical network (`SupportSubdivision.canonical_iso`, outlined in
`Camus/Network/Completeness/Main.lean`). Fix a support subdivision `H` of `T` in `N`. A vertex of
`N` is either an original vertex `H.original p` or lies inside the wire of exactly one non-root
vertex `p` of `T`, the wire that subdivides the edge of `T` above `p`. In the second case its
anchor `H.anchor v` is `p`, the vertex of `T` directly below it. So the pair
`H.pairOf d = (u, w)` of a non-tree edge `d = (u', w')` is the pair of Definition 2. The file
also shows that the switching `S` reaches every vertex from the root.

## Main results

* `SupportSubdivision.interior_unique`: a vertex lies inside at most one wire.
* `SupportSubdivision.anchor_eq`: the anchor of a vertex inside the wire of `p` is `p`.
* `SupportSubdivision.vertex_cases`: every vertex of `N` is original or lies inside the wire of
  its anchor.
* `RootedNetwork.switching_reachable`: every vertex of `N` is reachable from the root along
  switching edges.
-/

@[expose] public section

namespace Camus
namespace SupportSubdivision

variable {t : PhyloTree} {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- A vertex lies inside at most one wire: if `v` lies inside the wires of the non-root vertices
`p` and `q` of `T`, then `p = q`. -/
theorem interior_unique (H : SupportSubdivision t N S) {p q : Address}
    (hp : p ∈ t.nodes) (hp0 : p ≠ []) (hq : q ∈ t.nodes) (hq0 : q ≠ [])
    {v : ℕ} (hvp : v ∈ wireInterior (H.wire p))
    (hvq : v ∈ wireInterior (H.wire q)) : p = q := by
  by_contra hpq
  have hd := H.interiors_disjoint
    (Finset.mem_erase.mpr ⟨hp0, hp⟩)
    (Finset.mem_erase.mpr ⟨hq0, hq⟩) hpq
  exact Finset.disjoint_left.mp hd hvp hvq

/-- If `v` lies inside the wire of the non-root vertex `p`, its anchor `H.anchor v` is `p`. -/
theorem anchor_eq (H : SupportSubdivision t N S) {p : Address}
    (hp : p ∈ t.nodes) (hp0 : p ≠ []) {v : ℕ}
    (hv : v ∈ wireInterior (H.wire p)) : H.anchor v = p := by
  classical
  have hex : ∃ q ∈ t.nodes, q ≠ [] ∧ v ∈ wireInterior (H.wire q) :=
    ⟨p, hp, hp0, hv⟩
  unfold anchor
  rw [dite_eq_left hex]
  obtain ⟨hq, hq0, hvq⟩ := Classical.choose_spec hex
  exact H.interior_unique hq hq0 hp hp0 hvq hv

/-- A vertex inside some wire lies inside the wire of its anchor, a non-root vertex of `T`. -/
theorem anchor_spec (H : SupportSubdivision t N S) {v : ℕ}
    (hv : v ∈ (t.nodes.erase []).biUnion (fun p => wireInterior (H.wire p))) :
    H.anchor v ∈ t.nodes ∧ H.anchor v ≠ [] ∧
      v ∈ wireInterior (H.wire (H.anchor v)) := by
  classical
  obtain ⟨p, hp, hv⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨hp0, hp⟩ := Finset.mem_erase.mp hp
  rw [H.anchor_eq hp hp0 hv]
  exact ⟨hp, hp0, hv⟩

/-- A vertex inside a wire is not an original vertex. -/
theorem interior_not_original (H : SupportSubdivision t N S) {p : Address}
    (hp : p ∈ t.nodes) (hp0 : p ≠ []) {v : ℕ}
    (hv : v ∈ wireInterior (H.wire p)) : v ∉ t.nodes.image H.original := by
  exact fun ho => Finset.disjoint_left.mp (H.wire_laws p hp hp0).2.2.2.2 hv ho

/-- Original vertices are vertices of `N`. -/
theorem original_mem_vertices (H : SupportSubdivision t N S) {p : Address}
    (hp : p ∈ t.nodes) : H.original p ∈ N.vertices := by
  classical
  rw [H.vertices_covered]
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

/-- Vertices inside wires are vertices of `N`. -/
theorem interior_mem_vertices (H : SupportSubdivision t N S) {p : Address}
    (hp : p ∈ t.nodes) (hp0 : p ≠ []) {v : ℕ}
    (hv : v ∈ wireInterior (H.wire p)) : v ∈ N.vertices := by
  classical
  rw [H.vertices_covered]
  exact Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨p, Finset.mem_erase.mpr ⟨hp0, hp⟩, hv⟩)

/-- Every vertex of `N` is an original vertex `H.original p`, or lies inside the wire of its
anchor, a non-root vertex of `T`. -/
theorem vertex_cases (H : SupportSubdivision t N S) {v : ℕ} (hv : v ∈ N.vertices) :
    (∃ p ∈ t.nodes, H.original p = v) ∨
      (H.anchor v ∈ t.nodes ∧ H.anchor v ≠ [] ∧
        v ∈ wireInterior (H.wire (H.anchor v))) := by
  classical
  rw [H.vertices_covered] at hv
  rcases Finset.mem_union.mp hv with ho | hi
  · exact Or.inl (Finset.mem_image.mp ho)
  · exact Or.inr (H.anchor_spec hi)

end SupportSubdivision

namespace RootedNetwork

/-- Every vertex of `N` is reachable from the root along the edges of a switching `S`. The proof
is by induction along the strict-ancestor relation of `N`, well-founded since `N` is finite and
acyclic: the switching edge into a non-root vertex comes from a strict ancestor. -/
theorem switching_reachable {N : RootedNetwork} (hN : N.RootedBinaryLevelOne)
    {S : Finset (ℕ × ℕ)} (hS : N.Switching S) {v : ℕ} (hv : v ∈ N.vertices) :
    Relation.ReflTransGen (fun u w => (u,w) ∈ S) N.root v := by
  classical
  let R : N.vertices → N.vertices → Prop := fun u w =>
    Relation.TransGen (fun x y => (x,y) ∈ N.edges) u.val w.val
  have : IsTrans N.vertices R := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
  have : Std.Irrefl R := ⟨fun u => hN.2.2.1 u.val⟩
  have hwf : WellFounded R := Finite.wellFounded_of_trans_of_irrefl R
  have all : ∀ w : N.vertices,
      Relation.ReflTransGen (fun u z => (u,z) ∈ S) N.root w.val := by
    intro w
    induction w using hwf.induction with
    | h w ih =>
      by_cases hr : w.val = N.root
      · rw [hr]
      · have hc := hS.2 w.val w.property hr
        have hn : (S.filter (fun e => e.2 = w.val)).Nonempty :=
          Finset.card_pos.mp (by omega)
        obtain ⟨e, he⟩ := hn
        obtain ⟨heS, hew⟩ := Finset.mem_filter.mp he
        have heN := hS.1 heS
        have heu := (hN.2.1 e heN).1
        change (e.1,e.2) ∈ N.edges at heN
        change (e.1,e.2) ∈ S at heS
        rw [hew] at heN heS
        have hprev := ih ⟨e.1, heu⟩ (Relation.TransGen.single heN)
        exact hprev.tail heS
  exact all ⟨v, hv⟩

end RootedNetwork
end Camus
