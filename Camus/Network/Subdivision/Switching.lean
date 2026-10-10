module

public import Camus.Network.Subdivision.Incoming

/-!
# Switchings of `P` lift to a subdivision

Auxiliary to `GraphSubdivision.displays_iff`. Let `N` be a subdivision of `P`. A switching `R` of
`P` lifts to the switching of `N` that keeps every arc entering a vertex interior to a wire and the
terminal arcs of the edges in `R`. Its active edges are `R` again. With
`GraphSubdivision.active_switching`, the switchings of `P` are thus the sets of active edges of the
switchings of `N`.

## Main results

* `GraphSubdivision.liftSwitching`: the lift of a set of edges of `P`.
* `GraphSubdivision.lift_switching`: the lift of a switching of `P` is a switching of `N`.
* `GraphSubdivision.active_lift`: the active edges of the lift of a switching `R` are `R`.
-/

@[expose] public section

namespace Camus.GraphSubdivision

variable {P N : RootedNetwork}

/-- The lift of a set `R` of edges of `P` to `N`: the arcs of `N` entering a vertex that is not the
image of a vertex of `P` (that is, a vertex interior to a wire), together with the terminal arcs of
the edges in `R`. -/
noncomputable def liftSwitching (H : GraphSubdivision P N) (R : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  N.edges.filter (fun arc => arc.2 ∉ P.vertices.image H.original ∨ arc ∈ R.image H.terminal)

/-- For `R ⊆ P.edges`, the terminal arc of an edge `e` of `P` lies in the lift of `R` if and only if
`e ∈ R`. -/
theorem terminal_mem_lift (H : GraphSubdivision P N) {R : Finset (ℕ × ℕ)}
    (hR : R ⊆ P.edges) {e : ℕ × ℕ} (he : e ∈ P.edges) :
    H.terminal e ∈ H.liftSwitching R ↔ e ∈ R := by
  classical
  have hspec := H.terminal_spec he
  have htermN : H.terminal e ∈ N.edges := by
    rw [H.edges_covered]
    exact Finset.mem_biUnion.mpr ⟨e, he, hspec.1⟩
  have horig : (H.terminal e).2 ∈ P.vertices.image H.original := by
    rw [hspec.2]
    exact Finset.mem_image.mpr ⟨e.2, (H.edge_endpoints e he).2, rfl⟩
  simp only [liftSwitching, Finset.mem_filter, htermN, not_true_eq_false, horig, false_or, true_and]
  constructor
  · intro h
    obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp h
    exact H.terminal_injective (hR hf) he heq ▸ hf
  · intro heR
    exact Finset.mem_image.mpr ⟨e, heR, rfl⟩

/-- For `R ⊆ P.edges`, the edges of `P` whose terminal arc lies in the lift of `R` are those of
`R`. -/
theorem retained_lift (H : GraphSubdivision P N) {R : Finset (ℕ × ℕ)}
    (hR : R ⊆ P.edges) : H.retained (H.liftSwitching R) = R := by
  classical
  ext e
  simp only [retained, Finset.mem_filter]
  constructor
  · rintro ⟨he, hterm⟩
    exact (H.terminal_mem_lift hR he).mp hterm
  · intro he
    exact ⟨hR he, (H.terminal_mem_lift hR (hR he)).mpr he⟩

/-- The lift of a switching of `P` is a switching of `N`: an image `H.original u` keeps as many
incoming arcs as `u` keeps incoming edges, and a vertex interior to a wire keeps its only incoming
arc. -/
theorem lift_switching (H : GraphSubdivision P N) {R : Finset (ℕ × ℕ)}
    (hR : P.Switching R) : N.Switching (H.liftSwitching R) := by
  classical
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro v hv hvroot
  rw [H.vertices_covered] at hv
  rcases Finset.mem_union.mp hv with horig | hinterior
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp horig
    have hB : H.liftSwitching R ⊆ N.edges := Finset.filter_subset _ _
    rw [← H.original_incoming_card hB hu, H.retained_lift hR.1]
    apply hR.2 u hu
    exact fun h => hvroot (h ▸ H.root_preserved)
  · obtain ⟨e, he, hv⟩ := Finset.mem_biUnion.mp hinterior
    have hnot : v ∉ P.vertices.image H.original := by
      rintro h
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp h
      exact H.interior_not_original he hv hu heq.symm
    have hfilter : (H.liftSwitching R).filter (fun arc => arc.2 = v) =
        N.edges.filter (fun arc => arc.2 = v) := by
      ext arc
      simp only [liftSwitching, Finset.mem_filter]
      constructor
      · rintro ⟨⟨ha, _⟩, hav⟩
        exact ⟨ha, hav⟩
      · rintro ⟨ha, hav⟩
        exact ⟨⟨ha, Or.inl (hav ▸ hnot)⟩, hav⟩
    rw [hfilter]
    exact H.interior_incoming_card he hv

/-- The active edges of the lift of a switching `R` of `P` are the edges of `R`. -/
theorem active_lift (H : GraphSubdivision P N) {R : Finset (ℕ × ℕ)}
    (hR : P.Switching R) : H.active (H.liftSwitching R) = R := by
  rw [H.active_eq_retained (H.lift_switching hR), H.retained_lift hR.1]

end Camus.GraphSubdivision
