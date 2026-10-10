module

public import Camus.Network.Subdivision.Wires
public import Camus.Network.Completeness.Reachability

/-!
# Reachability through a subdivision

Auxiliary to `GraphSubdivision.displays_iff`. Let `N` be a subdivision of `P`
(`H : GraphSubdivision P N`): each edge `e` of `P` is replaced by a directed path of `N`, its wire
`H.wire e`, from `H.original e.1` to `H.original e.2`. For a set `B` of arcs of `N`, call an edge of
`P` active if its whole wire lies in `B` (`GraphSubdivision.active`). Then two vertices of `P` are
connected by active edges if and only if their images are connected in the underlying undirected
graph of `B`. One direction follows each wire. For the other, colour the vertices of `P` by the
connected components of the active edges and extend the colouring to `N` wire by wire
(`exists_wire_coloring`), so that no arc of `B` joins two colours.

## Main results

* `GraphSubdivision.active`: the edges of `P` whose wire lies in `B`.
* `GraphSubdivision.reachable_iff`: connectivity of images in `B` is connectivity by active edges.
-/

@[expose] public section

namespace Camus.GraphSubdivision

variable {P N : RootedNetwork}

/-- Wire interiors are disjoint: a vertex interior to the wires of two edges `e`, `f` of `P` forces
`e = f`. -/
theorem interior_unique (H : GraphSubdivision P N) {e f : ℕ × ℕ}
    (he : e ∈ P.edges) (hf : f ∈ P.edges) {v : ℕ}
    (hv : v ∈ wireInterior (H.wire e)) (hw : v ∈ wireInterior (H.wire f)) : e = f := by
  by_contra hne
  exact Finset.disjoint_left.mp (H.interiors_disjoint he hf hne) hv hw

/-- A vertex interior to a wire is not the image of a vertex of `P`. -/
theorem interior_not_original (H : GraphSubdivision P N) {e : ℕ × ℕ}
    (he : e ∈ P.edges) {v u : ℕ} (hv : v ∈ wireInterior (H.wire e))
    (hu : u ∈ P.vertices) : v ≠ H.original u := by
  intro h
  exact Finset.disjoint_left.mp (H.wire_laws e he).2.2.2.2 hv
    (Finset.mem_image.mpr ⟨u, hu, h.symm⟩)

/-- A left inverse of `H.original` on the vertices of `P`; it returns the root of `P` on vertices of
`N` that are not images. -/
noncomputable def originalOf (H : GraphSubdivision P N) (v : ℕ) : ℕ :=
  if h : ∃ u ∈ P.vertices, H.original u = v then h.choose else P.root

theorem originalOf_eq (H : GraphSubdivision P N) {u : ℕ} (hu : u ∈ P.vertices) :
    H.originalOf (H.original u) = u := by
  classical
  have hex : ∃ w ∈ P.vertices, H.original w = H.original u := ⟨u, hu, rfl⟩
  simp only [originalOf, dite_eq_left hex]
  exact H.original_injective hex.choose_spec.1 hu hex.choose_spec.2

/-- Gluing the wire colourings. Let `B ⊆ N.edges` and let `C` colour the vertices of `P` so that the
two ends of every edge of `P` whose whole wire lies in `B` have the same colour. Then some colouring
of `N` gives each image `H.original u` the colour `C u` and both ends of every arc of `B` the same
colour. Each wire is coloured by `exists_wire_coloring`; the wire interiors are disjoint, so these
colourings combine. -/
theorem exists_subdivision_coloring {β : Type*} (H : GraphSubdivision P N)
    (B : Finset (ℕ × ℕ)) (hB : B ⊆ N.edges) (C : ℕ → β)
    (hC : ∀ e ∈ P.edges, wireEdges (H.wire e) ⊆ B → C e.1 = C e.2) :
    ∃ color : ℕ → β, (∀ u ∈ P.vertices, color (H.original u) = C u) ∧
      ∀ e ∈ B, color e.1 = color e.2 := by
  classical
  have hex e (he : e ∈ P.edges) : ∃ c : ℕ → β,
      c (H.original e.1) = C e.1 ∧ c (H.original e.2) = C e.2 ∧
      ∀ f ∈ wireEdges (H.wire e), f ∈ B → c f.1 = c f.2 := by
    have hl := H.wire_laws e he
    exact exists_wire_coloring (H.wire e) hl.2.1 hl.2.2.1 hl.2.2.2.1 B (C e.1) (C e.2) (hC e he)
  let cw := fun e => if h : e ∈ P.edges then Classical.choose (hex e h) else fun _ => C P.root
  have hcw e (he : e ∈ P.edges) :
      cw e (H.original e.1) = C e.1 ∧ cw e (H.original e.2) = C e.2 ∧
        ∀ f ∈ wireEdges (H.wire e), f ∈ B → cw e f.1 = cw e f.2 := by
    simpa only [cw, dite_eq_left he] using Classical.choose_spec (hex e he)
  let owner := fun v => if h : ∃ e ∈ P.edges, v ∈ wireInterior (H.wire e) then h.choose else (0,0)
  let color := fun v => if h : ∃ u ∈ P.vertices, H.original u = v then C (H.originalOf v)
    else cw (owner v) v
  have horig (u : ℕ) (hu : u ∈ P.vertices) : color (H.original u) = C u := by
    have h : ∃ w ∈ P.vertices, H.original w = H.original u := ⟨u, hu, rfl⟩
    simp only [color, dite_eq_left h, H.originalOf_eq hu]
  have hinterior e (he : e ∈ P.edges) v (hv : v ∈ wireInterior (H.wire e)) : color v = cw e v := by
    have hnot : ¬∃ u ∈ P.vertices, H.original u = v := by
      rintro ⟨u, hu, h⟩
      exact H.interior_not_original he hv hu h.symm
    have hexowner : ∃ f ∈ P.edges, v ∈ wireInterior (H.wire f) := ⟨e, he, hv⟩
    have howner : owner v = e := by
      simp only [owner, dite_eq_left hexowner]
      exact H.interior_unique hexowner.choose_spec.1 he hexowner.choose_spec.2 hv
    simp only [color, dite_eq_right hnot, howner]
  have hwire e (he : e ∈ P.edges) v (hv : v ∈ H.wire e) : color v = cw e v := by
    rcases wire_vertex_cases hv with hhead | hlast | hv
    · have hv : v = H.original e.1 := Option.some.inj
        (hhead.symm.trans (H.wire_laws e he).2.2.1)
      rw [hv, horig _ (H.edge_endpoints e he).1, (hcw e he).1]
    · have hv : v = H.original e.2 := Option.some.inj
        (hlast.symm.trans (H.wire_laws e he).2.2.2.1)
      rw [hv, horig _ (H.edge_endpoints e he).2, (hcw e he).2.1]
    · exact hinterior e he v hv
  refine ⟨color, horig, ?_⟩
  intro f hf
  have hfN := hB hf
  rw [H.edges_covered] at hfN
  obtain ⟨e, he, hfe⟩ := Finset.mem_biUnion.mp hfN
  rw [hwire e he f.1 (List.mem_of_mem_dropLast (wire_edge_source_mem hfe)),
    hwire e he f.2 (List.mem_of_mem_tail (wire_edge_target_mem hfe))]
  exact (hcw e he).2.2 f hfe hf

/-- The active edges of `P` for a set `B` of arcs of `N`: the edges of `P` whose whole wire lies in
`B`. -/
def active (H : GraphSubdivision P N) (B : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := by
  classical
  exact P.edges.filter (fun e => wireEdges (H.wire e) ⊆ B)

/-- Contracting the wires. Let `B ⊆ N.edges` and let `u`, `v` be vertices of `P`. If their images
are connected in the underlying graph of `B`, then `u` and `v` are connected by active edges. The
connected components of the active edges, extended to `N` by `exists_subdivision_coloring`, are
constant along every walk in `B`. -/
theorem reachable_contract (H : GraphSubdivision P N) {B : Finset (ℕ × ℕ)}
    (hB : B ⊆ N.edges) {u v : ℕ} (hu : u ∈ P.vertices) (hv : v ∈ P.vertices) :
    ({N with edges := B}).underlying.Reachable (H.original u) (H.original v) →
      ({P with edges := H.active B}).underlying.Reachable u v := by
  classical
  let G := ({P with edges := H.active B}).underlying
  have hc : ∀ e ∈ P.edges, wireEdges (H.wire e) ⊆ B → G.connectedComponentMk e.1 = G.connectedComponentMk e.2 := by
    intro e he hfull
    by_cases hneq : e.1 = e.2
    · rw [hneq]
    · exact SimpleGraph.ConnectedComponent.sound
        (show G.Adj e.1 e.2 from ⟨hneq, Or.inl (Finset.mem_filter.mpr ⟨he, hfull⟩)⟩).reachable
  obtain ⟨color, horig, hedge⟩ := H.exists_subdivision_coloring B hB G.connectedComponentMk hc
  intro hreach
  have preserve {a b : ℕ} (walk : ({N with edges := B}).underlying.Walk a b) : color a = color b := by
    induction walk with
    | nil => rfl
    | @cons a b c hadj walk ih =>
      have hstep : color a = color b := by
        rcases hadj.2 with he | he
        · exact hedge _ he
        · exact (hedge _ he).symm
      exact hstep.trans ih
  obtain ⟨walk⟩ := hreach
  have heq := preserve walk
  rw [horig _ hu, horig _ hv] at heq
  exact SimpleGraph.ConnectedComponent.exact heq

/-- If the whole wire of an edge `e` of `P` lies in `B`, its two ends are connected in the
underlying graph of `B`. -/
theorem wire_reachable (H : GraphSubdivision P N) {B : Finset (ℕ × ℕ)}
    {e : ℕ × ℕ} (he : e ∈ P.edges) (hwire : wireEdges (H.wire e) ⊆ B) :
    ({N with edges := B}).underlying.Reachable (H.original e.1) (H.original e.2) := by
  let : Trans (({N with edges := B}).underlying.Reachable)
      (({N with edges := B}).underlying.Reachable) (({N with edges := B}).underlying.Reachable) :=
    ⟨fun h₁ h₂ => h₁.trans h₂⟩
  let : Std.Refl (({N with edges := B}).underlying.Reachable) := ⟨fun v => .refl v⟩
  have hl := H.wire_laws e he
  have hpairs : (H.wire e).Pairwise (({N with edges := B}).underlying.Reachable) := by
    apply List.isChain_iff_pairwise.mp
    apply wire_chain
    intro f hf
    have hidx := wire_edge_idxOf hl.2.1 hf
    have hneq : f.1 ≠ f.2 := by intro h; rw [h] at hidx; omega
    exact (show ({N with edges := B}).underlying.Adj f.1 f.2 from ⟨hneq, Or.inl (hwire hf)⟩).reachable
  have hne : H.wire e ≠ [] := by intro h; simp [h] at hl
  have hhead : (H.wire e).head hne = H.original e.1 :=
    Option.some.inj ((List.head?_eq_some_head hne).symm.trans hl.2.2.1)
  have hlast : (H.wire e).getLast hne = H.original e.2 :=
    Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hl.2.2.2.1)
  simpa only [hhead, hlast] using hpairs.rel_head (List.getLast_mem hne)

/-- Following the wires. If `u` and `v` are connected by active edges of `P`, their images are
connected in the underlying graph of `B`. -/
theorem reachable_expand (H : GraphSubdivision P N) {B : Finset (ℕ × ℕ)} {u v : ℕ} :
    ({P with edges := H.active B}).underlying.Reachable u v →
      ({N with edges := B}).underlying.Reachable (H.original u) (H.original v) := by
  have lift {a b : ℕ} (walk : ({P with edges := H.active B}).underlying.Walk a b) :
      ({N with edges := B}).underlying.Reachable (H.original a) (H.original b) := by
    induction walk with
    | nil => exact .refl _
    | @cons a b c hadj walk ih =>
      have hstep : ({N with edges := B}).underlying.Reachable (H.original a) (H.original b) := by
        rcases hadj.2 with he | he
        · obtain ⟨heP, hfull⟩ := Finset.mem_filter.mp he
          exact H.wire_reachable heP hfull
        · obtain ⟨heP, hfull⟩ := Finset.mem_filter.mp he
          exact (H.wire_reachable heP hfull).symm
      exact hstep.trans ih
  rintro ⟨walk⟩
  exact lift walk

/-- Let `B ⊆ N.edges` and let `u`, `v` be vertices of `P`. The images of `u` and `v` are connected
in the underlying graph of `B` if and only if `u` and `v` are connected by active edges of `P`. -/
theorem reachable_iff (H : GraphSubdivision P N) {B : Finset (ℕ × ℕ)}
    (hB : B ⊆ N.edges) {u v : ℕ} (hu : u ∈ P.vertices) (hv : v ∈ P.vertices) :
    ({N with edges := B}).underlying.Reachable (H.original u) (H.original v) ↔
      ({P with edges := H.active B}).underlying.Reachable u v :=
  ⟨H.reachable_contract hB hu hv, H.reachable_expand⟩

end Camus.GraphSubdivision
