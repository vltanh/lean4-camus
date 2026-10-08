module

public import Camus.Definitions

public import Camus.TreeGeometry
public import Mathlib.Data.Nat.Find

@[expose] public section

namespace Camus

theorem parent_prefix (p : Address) : parent p <+: p := List.take_prefix _ _

theorem prefix_parent_of_ne {p q : Address} (hp : p <+: q) (hne : p ≠ q) :
    p <+: parent q := by
  have hlt : p.length < q.length := by
    have hle := hp.length_le
    by_contra h
    exact hne (hp.eq_of_length_le (by omega))
  rw [List.prefix_iff_eq_take.mp hp]
  exact List.take_prefix_take_left (by omega)

theorem EdgeAbove.footprint_region (t : PhyloTree) (e : Address × Address)
    (he : EdgeAbove.Admissible t e) :
    TreeRegion t (EdgeAbove.target e) (EdgeAbove.footprint t e) := by
  refine ⟨EdgeAbove.target_mem_footprint t e he, Finset.filter_subset _ _, ?_⟩
  intro x hx
  obtain ⟨hxnode, hpx, hxbranch⟩ := Finset.mem_filter.mp hx
  refine ⟨hpx, ?_⟩
  intro y hpy hyx
  refine Finset.mem_filter.mpr ⟨t.nodes_prefix_closed hxnode hyx, hpy, ?_⟩
  rcases hxbranch with ⟨hxu, hne⟩ | ⟨hxw, hne⟩
  · exact Or.inl ⟨hyx.trans hxu, fun h => hne
      ((hxu.eq_of_length_le (h ▸ hyx.length_le)).symm.symm)⟩
  · exact Or.inr ⟨hyx.trans hxw, fun h => hne
      ((hxw.eq_of_length_le (h ▸ hyx.length_le)).symm.symm)⟩

theorem frontier_below {t : PhyloTree} {p : Address} {S : Finset Address}
    (hS : TreeRegion t p S) {r : Address} (hr : r ∈ frontier t S) :
    p <+: r ∧ p ≠ r := by
  obtain ⟨_, _, hpar, hnot⟩ := Finset.mem_filter.mp hr
  exact ⟨(hS.2.2 _ hpar).1.trans (parent_prefix r),
    fun h => hnot (h ▸ hS.1)⟩

theorem frontier_cone_disjoint {t : PhyloTree} {p : Address} {S : Finset Address}
    (hS : TreeRegion t p S) {r x : Address} (hr : r ∈ frontier t S)
    (hrx : r <+: x) : x ∉ S := by
  intro hx
  have hp := (frontier_below hS hr).1
  exact (Finset.mem_filter.mp hr).2.2.2 ((hS.2.2 x hx).2 r hp hrx)

/-- Distinct hanging-subtree roots are incomparable in the ancestor order. -/
theorem frontier_antichain {t : PhyloTree} {p : Address} {S : Finset Address}
    (hS : TreeRegion t p S) {r s : Address} (hr : r ∈ frontier t S)
    (hs : s ∈ frontier t S) (hrs : r <+: s) : r = s := by
  by_contra hne
  have hrpar := prefix_parent_of_ne hrs hne
  have hparent := (Finset.mem_filter.mp hs).2.2.1
  exact frontier_cone_disjoint hS hr hrpar hparent

/-- Every original vertex outside the connected cycle region lies in exactly
one hanging subtree. This proves the partition rather than assuming it in a
network or DP structure. -/
theorem exists_unique_frontier {t : PhyloTree} {p x : Address} {S : Finset Address}
    (hS : TreeRegion t p S) (hx : x ∈ t.nodes) (hpx : p <+: x) (hxS : x ∉ S) :
    ∃! r, r ∈ frontier t S ∧ r <+: x := by
  have hlt : p.length < x.length := by
    have hle := hpx.length_le
    by_contra h
    have heq := hpx.eq_of_length_le (by omega)
    exact hxS (heq ▸ hS.1)
  let P := fun i : ℕ => p.length < i ∧ i ≤ x.length ∧ x.take i ∉ S
  have hex : ∃ i, P i := ⟨x.length, hlt, le_rfl, by simpa using hxS⟩
  let i := Nat.find hex
  have hi : P i := Nat.find_spec hex
  have hprev : x.take (i - 1) ∈ S := by
    by_cases hp : i - 1 = p.length
    · rw [hp, ← List.prefix_iff_eq_take.mp hpx]
      exact hS.1
    · by_contra hn
      have hpred : P (i - 1) := ⟨by omega, by omega, hn⟩
      have hm := Nat.find_min' hex hpred
      change i ≤ i - 1 at hm
      omega
  let r := x.take i
  have hrx : r <+: x := List.take_prefix _ _
  have hr : r ∈ frontier t S := by
    refine Finset.mem_filter.mpr ⟨t.nodes_prefix_closed hx hrx, ?_, ?_, hi.2.2⟩
    · have hrlen : r.length = i := by simp [r, Nat.min_eq_left hi.2.1]
      intro hn
      simp only [hn, List.length_nil] at hrlen
      omega
    · simpa only [parent, r, List.length_take, Nat.min_eq_left hi.2.1,
        List.take_take, Nat.min_eq_left (Nat.sub_le i 1)] using hprev
  refine ⟨r, ⟨hr, hrx⟩, ?_⟩
  intro s hs
  rcases List.prefix_or_prefix_of_prefix hs.2 hrx with hsr | hrs
  · exact frontier_antichain hS hs.1 hr hsr
  · exact (frontier_antichain hS hr hs.1 hrs).symm

end Camus
