module

public import Camus.Network.SingleEdge
public import Camus.Network.Reticulations

/-!
# Moving the donor down the tree

Let `(u, w)` be an admissible cross pair of a well-labelled tree `T` (its target lca(u, w) is not
`u`, so `u` and `w` are incomparable), and let `u₂` be a vertex of `T` strictly below `u`. Moving
the donor end of the added edge from above `u` to above `u₂` keeps every displayed quartet: every
quartet displayed by `T + (u, w)` is displayed by `T + (u₂, w)`
(`Realization.deeper_donor_displays`). In clades: the tree `T'₂` displayed by `T + (u₂, w)`
through its added edge has the clades of the tree `T'` displayed by `T + (u, w)`, except that the
clade of a vertex `p` on the path from `u` down to `u₂` (`u₂` excluded) gains `T_w`; the clade
`T_u ∪ T_w` of u′ in `T'` is that of `u` in `T'₂`, and the clade `T_p` of such a `p` in `T'` is a
clade of `T`. So whenever the deeper network displays a quartet that the first does not, the
first is not identifiable under inclusion, the hypothesis of `recovery`
(`Realization.deeper_donor_not_identifiable`). `Counterexamples.shallow_not_identifiable` is an
instance.

The statement fails for ghost pairs. In `Counterexamples.donorTree` `((A,B),(C,(F,(D,E))))`, the
network `T + ((C,(F,(D,E))), (D,E))` displays `AD|CF` and `T + (C, (D,E))` does not
(`Counterexamples.ghost_deeper_donor`).

## Main results

* `Realization.deeper_donor_displays`: the deeper network displays every quartet of the first.
* `Realization.deeper_donor_not_identifiable`: the first is then not identifiable under inclusion,
  unless the two display the same quartets.
* `Realization.cycleVertices_card`: the cycle of `T + e` has the vertices of its footprint and the
  two new vertices.
-/

@[expose] public section

namespace Camus.Realization

/-- Moving the donor of a cross pair down the tree keeps the displayed quartets. Let `T` be
well-labelled, `(u, w)` an admissible pair whose target lca(u, w) is not `u` (a cross pair: `u` is
not an ancestor of `w`), and `u₂` a vertex of `T` strictly below `u`. Then `(u₂, w)` is admissible,
and every quartet displayed by `T + (u, w)` is displayed by `T + (u₂, w)`.

The proof compares clades (`Realization.single_displays_iff`). The clade `T_u ∪ T_w` of u′ in `T'`
is the clade of `u` in `T'₂`; the clade of a vertex `p` of `T` is the same in `T'` and `T'₂` unless
`p` lies on the path from `u` to `u₂`, `u₂` excluded, and then its clade in `T'` is its clade in
`T`. The statement fails for ghost pairs (`u` an ancestor of `w`):
`Counterexamples.ghost_deeper_donor`. -/
theorem deeper_donor_displays {t : PhyloTree} (ht : t.WellLabelled) {u w u₂ : Address}
    (he : (u, w) ∈ EdgeAbove.candidates t) (hcross : EdgeAbove.target (u, w) ≠ u)
    (hu₂ : u₂ ∈ t.nodes) (hbelow : u <+: u₂) (hne : u ≠ u₂) :
    (u₂, w) ∈ EdgeAbove.candidates t ∧
      ∀ q, (graph t {(u, w)}).DisplaysQuartet q → (graph t {(u₂, w)}).DisplaysQuartet q := by
  have hadm : EdgeAbove.Admissible t (u, w) := (Finset.mem_filter.mp he).2
  obtain ⟨hu, hw, hu0, hw0, hwu⟩ := hadm
  change ¬w <+: u at hwu
  -- `u` is not an ancestor of `w`
  have huw : ¬u <+: w := fun h => hcross ((lca_eq_left_iff u w).mpr h)
  -- `(u₂, w)` is admissible
  have hu₂0 : u₂ ≠ [] := by
    rintro rfl
    exact hu0 (List.prefix_nil.mp hbelow)
  have hwu₂ : ¬w <+: u₂ := by
    intro h
    rcases List.prefix_or_prefix_of_prefix hbelow h with h' | h'
    · exact huw h'
    · exact hwu h'
  have hadm₂ : EdgeAbove.Admissible t (u₂, w) := ⟨hu₂, hw, hu₂0, hw0, hwu₂⟩
  have he₂ : (u₂, w) ∈ EdgeAbove.candidates t :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu₂, hw⟩, hadm₂⟩
  refine ⟨he₂, ?_⟩
  intro q hq
  rw [single_displays_iff ht he] at hq
  rw [single_displays_iff ht he₂]
  obtain ⟨hqt, hind | ⟨C, hC, hcut⟩⟩ := hq
  · exact ⟨hqt, Or.inl hind⟩
  refine ⟨hqt, ?_⟩
  -- `u` is a strict ancestor of `u₂`, and not one of `w`
  have hsu : u <+: u₂ ∧ u ≠ u₂ := ⟨hbelow, hne⟩
  have hnsw : ¬(u <+: w ∧ u ≠ w) := fun h => huw h.1
  simp only [EdgeAbove.switchedClades, Finset.mem_insert, Finset.mem_image] at hC
  rcases hC with rfl | rfl | ⟨p, hp, rfl⟩
  · -- the clade of u′ in `T'` is the clade of `u` in `T'₂`
    refine Or.inr ⟨EdgeAbove.switchedClade t (u₂, w) u, ?_, ?_⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hu))
    · have hC : EdgeAbove.switchedClade t (u, w) u ∪ t.taxaAt w =
          EdgeAbove.switchedClade t (u₂, w) u := by
        simp only [EdgeAbove.switchedClade, hnsw, hsu, ne_eq, not_true_eq_false, and_false,
          ite_false, ite_true, not_false_eq_true, and_self, Finset.union_empty]
      rw [← hC]
      exact hcut
  · -- the clade `T_w` of w′ is the same in both
    exact Or.inr ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), hcut⟩
  · by_cases hpath : (p <+: u₂ ∧ p ≠ u₂) ∧ ¬(p <+: u ∧ p ≠ u)
    · -- `p` lies on the path from `u` to `u₂`: its clade in `T'` is its clade in `T`
      have hup : u <+: p := by
        rcases List.prefix_or_prefix_of_prefix hbelow hpath.1.1 with h | h
        · exact h
        · by_cases hpu : p = u
          · exact hpu ▸ List.prefix_refl _
          · exact absurd ⟨h, hpu⟩ hpath.2
      have hpw : ¬(p <+: w ∧ p ≠ w) := fun h => huw (hup.trans h.1)
      have hp0 : p ≠ [] := by
        rintro rfl
        exact hu0 (List.prefix_nil.mp hup)
      have hclade : EdgeAbove.switchedClade t (u, w) p = t.taxaAt p := by
        simp only [EdgeAbove.switchedClade, hpw, hpath.2, ite_false, Finset.union_empty]
      rw [hclade] at hcut
      exact Or.inl ((Quartet.induced_iff_taxaAt q t).mpr ⟨hqt, p, hp, hp0, hcut⟩)
    · -- otherwise the clade of `p` is the same in `T'` and `T'₂`
      have hiff : (p <+: u ∧ p ≠ u) ↔ (p <+: u₂ ∧ p ≠ u₂) := by
        constructor
        · rintro ⟨h, hpu⟩
          refine ⟨h.trans hbelow, ?_⟩
          rintro rfl
          exact hpu (h.eq_of_length_le hbelow.length_le)
        · intro h
          by_contra h'
          exact hpath ⟨h, h'⟩
      have hclade : EdgeAbove.switchedClade t (u, w) p = EdgeAbove.switchedClade t (u₂, w) p := by
        unfold EdgeAbove.switchedClade
        simp only [hiff]
      refine Or.inr ⟨EdgeAbove.switchedClade t (u₂, w) p, ?_, hclade ▸ hcut⟩
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp))

/-- A network with one added edge, above a cross pair `(u, w)`, is not identifiable under
inclusion (the hypothesis `identifiable` of `recovery`) as soon as moving the donor to a vertex
`u₂` strictly below `u` displays a quartet more: `T + (u₂, w)` is built on `T`, displays every
quartet of `T + (u, w)` (`Realization.deeper_donor_displays`), has one reticulation as well, and
is not isomorphic to `T + (u, w)`, since isomorphic networks display the same quartets. -/
theorem deeper_donor_not_identifiable {t : PhyloTree} (ht : t.WellLabelled) {u w u₂ : Address}
    (he : (u, w) ∈ EdgeAbove.candidates t) (hcross : EdgeAbove.target (u, w) ≠ u)
    (hu₂ : u₂ ∈ t.nodes) (hbelow : u <+: u₂) (hne : u ≠ u₂) {q : Quartet}
    (hq : (graph t {(u₂, w)}).DisplaysQuartet q) (hnq : ¬(graph t {(u, w)}).DisplaysQuartet q) :
    ¬ ∀ P : RootedNetwork, P.AnchoredExtension t →
      (∀ q, (graph t {(u, w)}).DisplaysQuartet q → P.DisplaysQuartet q) →
      P.reticulationCount ≤ (graph t {(u, w)}).reticulationCount →
      Nonempty (P.Iso (graph t {(u, w)})) := by
  obtain ⟨he₂, hdisplays⟩ := deeper_donor_displays ht he hcross hu₂ hbelow hne
  have hsep : EdgeAbove.CycleSeparated t {(u, w)} :=
    ⟨Finset.singleton_subset_iff.mpr he, by simp⟩
  have hsep₂ : EdgeAbove.CycleSeparated t {(u₂, w)} :=
    ⟨Finset.singleton_subset_iff.mpr he₂, by simp⟩
  have hN := levelOne t ht _ hsep
  have hN₂ := levelOne t ht _ hsep₂
  intro h
  obtain ⟨i⟩ := h (graph t {(u₂, w)})
    ⟨hN₂, ⟨_, ⟨support t ht _ hsep₂⟩⟩⟩ hdisplays
    (by rw [reticulationCount_eq_card t _ hsep, reticulationCount_eq_card t _ hsep₂,
      Finset.card_singleton, Finset.card_singleton])
  exact hnq ((i.displays_iff hN₂ hN q).mp hq)

/-- The cycle γ(u, w) of `T + e` has as many vertices as the footprint of `e` (its vertices in `T`)
plus two, the new vertices u′ and w′. -/
theorem cycleVertices_card (t : PhyloTree) (e : Pair) :
    (cycleVertices t e).card = (EdgeAbove.footprint t e).card + 2 := by
  unfold cycleVertices
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ Address.code_injective,
    Finset.card_pair (donor_ne_recipient t e e)]
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  have hpt : p ∈ t.nodes := (Finset.mem_filter.mp hp).1
  rcases Finset.mem_insert.mp hv' with h | h
  · exact donor_ne_code e hpt h.symm
  · exact recipient_ne_code e hpt (Finset.mem_singleton.mp h).symm

end Camus.Realization
