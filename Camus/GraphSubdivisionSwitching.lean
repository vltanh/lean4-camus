module

public import Camus.GraphSubdivisionIncoming

@[expose] public section

namespace Camus.GraphSubdivision

variable {P N : RootedNetwork}

noncomputable def liftSwitching (H : GraphSubdivision P N) (R : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  N.edges.filter (fun arc => arc.2 ∉ P.vertices.image H.original ∨ arc ∈ R.image H.terminal)

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

theorem active_lift (H : GraphSubdivision P N) {R : Finset (ℕ × ℕ)}
    (hR : P.Switching R) : H.active (H.liftSwitching R) = R := by
  rw [H.active_eq_retained (H.lift_switching hR), H.retained_lift hR.1]

end Camus.GraphSubdivision
