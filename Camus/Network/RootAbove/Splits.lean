module

public import Camus.Network.RootAbove.Pairs
public import Camus.Network.RootAbove.Subdivision

/-!
# The splits displayed through a moved edge

The tree `T'` displayed by `T + e` through the added edge `e = (u, w)` is `T` with `T_w` pruned
and regrafted on the edge above `u`; its clades are `EdgeAbove.switchedClades t e`
(`Realization.single_displays_iff`). This file compares these clades, as cuts of quartets on the
taxa of `T`, in two situations.

* The outgroup: the pair `(true :: u, true :: w)` of `T⁺ = fork (leaf z) T` and the pair `(u, w)`
  of `T` cut the same quartets (`EdgeAbove.cuts_outgroup_iff`). The two extra clades of `T⁺` are
  the whole set of taxa and `{z}`, which cut no quartet on the taxa of `T`.
* The moved donor: an edge from above the root of `T` to above `w` (the pair `([], w)`) and the
  edge of `EdgeAbove.lowerPair` cut the same quartets (`EdgeAbove.cuts_lowerPair_iff`). As
  unrooted trees, attaching `T_w` above the root of `T ∖ T_w` or on the edge above the child of
  the root that contains `w` is the same. The clades differ only by complements within the taxa
  of `T`, which cut the same quartets (`Quartet.cutBy_complement`), and by clades containing all
  the taxa of `T`, which cut none.

## Main results

* `EdgeAbove.cuts_outgroup_iff`: the outgroup changes no split.
* `EdgeAbove.cuts_lowerPair_iff`: moving the donor below the root changes no split.
-/

@[expose] public section

namespace Camus

namespace EdgeAbove

/-- The clade of the vertex `p` of `T` with the taxa of `T_w` removed if `p` is a strict ancestor
of `w`: the clade of `p` in `T` with `T_w` pruned. -/
def prunedClade (t : PhyloTree) (w p : Address) : Finset ℕ :=
  if p <+: w ∧ p ≠ w then t.taxaAt p \ t.taxaAt w else t.taxaAt p

/-- The clade of `p` in `T'`: the pruned clade, together with `T_w` if `p` is a strict ancestor of
the donor. -/
theorem switchedClade_eq_prunedClade (t : PhyloTree) (e : Address × Address) (p : Address) :
    switchedClade t e p =
      prunedClade t e.2 p ∪ (if p <+: e.1 ∧ p ≠ e.1 then t.taxaAt e.2 else ∅) := rfl

/-- If the donor is the root or a child of the root, a vertex other than the root is not a strict
ancestor of the donor, and its clade in `T'` is the pruned clade. -/
theorem switchedClade_of_short {t : PhyloTree} {d w p : Address} (hd : d.length ≤ 1)
    (hp : p ≠ []) : switchedClade t (d, w) p = prunedClade t w p := by
  have hnot : ¬(p <+: d ∧ p ≠ d) := by
    rintro ⟨h1, h2⟩
    have hlt : p.length < d.length := by
      by_contra hle
      exact h2 (h1.eq_of_length_le (by omega))
    exact hp (List.eq_nil_of_length_eq_zero (by omega))
  rw [switchedClade_eq_prunedClade, ite_eq_right hnot, Finset.union_empty]

/-- In `T⁺ = fork (leaf z) T`, the clade of `true :: p` in the tree displayed through the pair
`(true :: u, true :: w)` is the clade of `p` in the tree displayed through `(u, w)`. -/
theorem switchedClade_outgroup (t : PhyloTree) (z : ℕ) (u w p : Address) :
    switchedClade (PhyloTree.fork (.leaf z) t) (true :: u, true :: w) (true :: p) =
      switchedClade t (u, w) p := by
  simp only [switchedClade, prefix_ne_of_cons_true, PhyloTree.outgroup_taxaAt_true]

/-- In `T⁺ = fork (leaf z) T`, the root's clade in the tree displayed through a pair below the
root of `T` contains all taxa of `T⁺`. -/
theorem switchedClade_outgroup_root (t : PhyloTree) (z : ℕ) (u w : Address) :
    (PhyloTree.fork (.leaf z) t).taxa ⊆
      switchedClade (PhyloTree.fork (.leaf z) t) (true :: u, true :: w) [] := by
  have h1 : ([] : Address) <+: true :: w ∧ ([] : Address) ≠ true :: w := ⟨List.nil_prefix, by simp⟩
  have h2 : ([] : Address) <+: true :: u ∧ ([] : Address) ≠ true :: u := ⟨List.nil_prefix, by simp⟩
  rw [switchedClade_eq_prunedClade, prunedClade, ite_eq_left h1, ite_eq_left h2,
    Finset.sdiff_union_self_eq_union, PhyloTree.taxaAt_root]
  exact Finset.subset_union_left

/-- In `T⁺ = fork (leaf z) T`, the clade of the leaf `z` in the tree displayed through a pair below
the root of `T` is `{z}`. -/
theorem switchedClade_outgroup_leaf (t : PhyloTree) (z : ℕ) (u w : Address) :
    switchedClade (PhyloTree.fork (.leaf z) t) (true :: u, true :: w) [false] = {z} := by
  have h1 : ¬([false] <+: true :: w ∧ [false] ≠ true :: w) := by simp [List.cons_prefix_cons]
  have h2 : ¬([false] <+: true :: u ∧ [false] ≠ true :: u) := by simp [List.cons_prefix_cons]
  rw [switchedClade_eq_prunedClade, prunedClade, ite_eq_right h1, ite_eq_right h2,
    Finset.union_empty, PhyloTree.outgroup_taxaAt_false]

/-- The outgroup changes no split on the taxa of `T`: for a quartet `q` on taxa of `T`, the tree
displayed through the pair `(true :: u, true :: w)` of `T⁺ = fork (leaf z) T` cuts `q` if and only
if the tree displayed through the pair `(u, w)` of `T` does. -/
theorem cuts_outgroup_iff {t : PhyloTree} {z : ℕ} (hz : z ∉ t.taxa) {q : Quartet}
    (hq : q.taxa ⊆ t.taxa) (u w : Address) :
    (∃ C ∈ switchedClades (PhyloTree.fork (.leaf z) t) (true :: u, true :: w),
        q.cutBy C = true) ↔
      ∃ C ∈ switchedClades t (u, w), q.cutBy C = true := by
  have hfirst : switchedClade (PhyloTree.fork (.leaf z) t) (true :: u, true :: w) (true :: u) ∪
      (PhyloTree.fork (.leaf z) t).taxaAt (true :: w) = switchedClade t (u, w) u ∪ t.taxaAt w := by
    rw [switchedClade_outgroup, PhyloTree.outgroup_taxaAt_true]
  simp only [switchedClades, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨C, hC | hC | ⟨p, hp, rfl⟩, hcut⟩
    · exact ⟨C, Or.inl (hC.trans hfirst), hcut⟩
    · exact ⟨C, Or.inr (Or.inl hC), hcut⟩
    · rcases PhyloTree.mem_outgroup_nodes.mp hp with rfl | rfl | ⟨p', hp', rfl⟩
      -- the root of `T⁺` cuts nothing: its clade contains all the taxa
      · have hsub : q.taxa ⊆ switchedClade (PhyloTree.fork (.leaf z) t)
            (true :: u, true :: w) [] := by
          refine (hq.trans ?_).trans (switchedClade_outgroup_root t z u w)
          rw [PhyloTree.outgroup_taxa]
          exact Finset.subset_insert _ _
        rw [q.cutBy_false_of_taxa_subset hsub] at hcut
        exact absurd hcut (by simp)
      -- the leaf `z` cuts nothing: `z` is not a taxon of `q`
      · rw [switchedClade_outgroup_leaf] at hcut
        have hdis : Disjoint q.taxa {z} :=
          Finset.disjoint_singleton_right.mpr (fun h => hz (hq h))
        rw [q.cutBy_false_of_taxa_disjoint hdis] at hcut
        exact absurd hcut (by simp)
      · exact ⟨_, Or.inr (Or.inr ⟨p', hp', (switchedClade_outgroup t z u w p').symm⟩), hcut⟩
  · rintro ⟨C, hC | hC | ⟨p, hp, rfl⟩, hcut⟩
    · exact ⟨C, Or.inl (hC.trans hfirst.symm), hcut⟩
    · exact ⟨C, Or.inr (Or.inl hC), hcut⟩
    · refine ⟨_, Or.inr (Or.inr ⟨true :: p, ?_, switchedClade_outgroup t z u w p⟩), hcut⟩
      exact PhyloTree.mem_outgroup_nodes.mpr (Or.inr (Or.inr ⟨p, hp, rfl⟩))

/-- The splits displayed through an edge from above the root of `T` to above `w`: `T_w`, and the
pruned clades of the vertices of `T` other than the root. -/
theorem cuts_rootPair_iff {t : PhyloTree} {w : Address} (hw : w ∈ t.nodes) (hw0 : w ≠ [])
    {q : Quartet} (hq : q.taxa ⊆ t.taxa) :
    (∃ C ∈ switchedClades t ([], w), q.cutBy C = true) ↔
      q.cutBy (t.taxaAt w) = true ∨
        ∃ p ∈ t.nodes, p ≠ [] ∧ q.cutBy (prunedClade t w p) = true := by
  have hTw := PhyloTree.taxaAt_subset_taxa hw
  have hroot : ([] : Address) <+: w ∧ ([] : Address) ≠ w := ⟨List.nil_prefix, Ne.symm hw0⟩
  have hnil : ¬(([] : Address) <+: [] ∧ ([] : Address) ≠ []) := by simp
  -- the clade of the root of `T` is the complement of `T_w`
  have hrootClade : switchedClade t ([], w) [] = t.taxa \ t.taxaAt w := by
    rw [switchedClade_eq_prunedClade, prunedClade, ite_eq_left hroot, ite_eq_right hnil,
      Finset.union_empty, PhyloTree.taxaAt_root]
  have hcompl : q.cutBy (t.taxa \ t.taxaAt w) = q.cutBy (t.taxaAt w) := by
    apply q.cutBy_complement
    · rw [Finset.sdiff_union_self_eq_union, Finset.union_eq_left.mpr hTw]
      exact hq
    · exact Finset.sdiff_disjoint
  simp only [switchedClades, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨C, hC | hC | ⟨p, hp, rfl⟩, hcut⟩
    -- the clade of the new vertex above the root contains all the taxa of `T`
    · rw [hC, hrootClade, Finset.sdiff_union_self_eq_union] at hcut
      rw [q.cutBy_false_of_taxa_subset (hq.trans Finset.subset_union_left)] at hcut
      exact absurd hcut (by simp)
    · exact Or.inl (hC ▸ hcut)
    · by_cases hp0 : p = []
      · subst hp0
        rw [hrootClade, hcompl] at hcut
        exact Or.inl hcut
      · rw [switchedClade_of_short (by simp) hp0] at hcut
        exact Or.inr ⟨p, hp, hp0, hcut⟩
  · rintro (hcut | ⟨p, hp, hp0, hcut⟩)
    · exact ⟨_, Or.inr (Or.inl rfl), hcut⟩
    · exact ⟨_, Or.inr (Or.inr ⟨p, hp, switchedClade_of_short (by simp) hp0⟩), hcut⟩

/-- The splits displayed through the edge of the moved pair `(rootDonor w, w)`: the same as for
the edge from above the root (`EdgeAbove.cuts_rootPair_iff`). The new vertex on the edge above the
moved donor `x` has the clade of `x` in `T`, the complement of the clade of the other child of the
root, or all the taxa of `T` if `x` is the sibling of `w`. -/
theorem cuts_rootDonor_iff {t : PhyloTree} (ht : t.WellLabelled) {w : Address}
    (hw : w ∈ t.nodes) (hw0 : w ≠ []) {q : Quartet} (hq : q.taxa ⊆ t.taxa) :
    (∃ C ∈ switchedClades t (rootDonor w, w), q.cutBy C = true) ↔
      q.cutBy (t.taxaAt w) = true ∨
        ∃ p ∈ t.nodes, p ≠ [] ∧ q.cutBy (prunedClade t w p) = true := by
  have hTw := PhyloTree.taxaAt_subset_taxa hw
  obtain ⟨hd, hd0, hwd⟩ := rootDonor_spec hw hw0
  have hdlen := rootDonor_length hw0
  have hroot : ([] : Address) <+: w ∧ ([] : Address) ≠ w := ⟨List.nil_prefix, Ne.symm hw0⟩
  have hrootd : ([] : Address) <+: rootDonor w ∧ ([] : Address) ≠ rootDonor w :=
    ⟨List.nil_prefix, Ne.symm hd0⟩
  -- the clade of the root of `T` contains all the taxa of `T`
  have hrootClade : t.taxa ⊆ switchedClade t (rootDonor w, w) [] := by
    rw [switchedClade_eq_prunedClade, prunedClade, ite_eq_left hroot, ite_eq_left hrootd,
      Finset.sdiff_union_self_eq_union, PhyloTree.taxaAt_root]
    exact Finset.subset_union_left
  -- the clade of the new vertex above the moved donor
  have hfirst : q.cutBy (switchedClade t (rootDonor w, w) (rootDonor w) ∪ t.taxaAt w) = true →
      ∃ p ∈ t.nodes, p ≠ [] ∧ q.cutBy (prunedClade t w p) = true := by
    intro hcut
    have hnd : ¬(rootDonor w <+: rootDonor w ∧ rootDonor w ≠ rootDonor w) := by simp
    rw [switchedClade_eq_prunedClade, ite_eq_right hnd, Finset.union_empty] at hcut
    match w, hw, hw0, hd, hTw, hwd, hroot with
    | [b], hw, _, hd, hTw, _, _ =>
      -- `w` is a child of the root: the new vertex has all the taxa of `T`
      exfalso
      have hns : ¬([!b] <+: [b] ∧ [!b] ≠ [b]) := by simp [List.cons_prefix_cons]
      change q.cutBy (prunedClade t [b] [!b] ∪ t.taxaAt [b]) = true at hcut
      rw [prunedClade, ite_eq_right hns] at hcut
      have hall : t.taxa ⊆ t.taxaAt [!b] ∪ t.taxaAt [b] := by
        rw [Finset.union_comm, (PhyloTree.root_children_taxaAt ht hw).1]
      rw [q.cutBy_false_of_taxa_subset (hq.trans hall)] at hcut
      exact absurd hcut (by simp)
    | b :: c :: w', hw, _, hd, hTw, _, _ =>
      -- the new vertex has the clade of `[b]`, the complement of the clade of `[!b]`
      have hbw : [b] <+: b :: c :: w' ∧ [b] ≠ b :: c :: w' := by simp [List.cons_prefix_cons]
      change q.cutBy (prunedClade t (b :: c :: w') [b] ∪ t.taxaAt (b :: c :: w')) = true at hcut
      rw [prunedClade, ite_eq_left hbw, Finset.sdiff_union_self_eq_union,
        Finset.union_eq_left.mpr (PhyloTree.taxaAt_subset_of_prefix hbw.1 hw)] at hcut
      have hpart := PhyloTree.root_children_taxaAt ht hd
      have hsib := PhyloTree.root_sibling_mem_nodes hd
      have hcompl : q.cutBy (t.taxaAt [b]) = q.cutBy (t.taxaAt [!b]) :=
        q.cutBy_complement (hq.trans hpart.1.ge) hpart.2
      have hns : ¬([!b] <+: b :: c :: w' ∧ [!b] ≠ b :: c :: w') := by
        simp [List.cons_prefix_cons]
      refine ⟨[!b], hsib, by simp, ?_⟩
      rw [prunedClade, ite_eq_right hns, ← hcompl]
      exact hcut
  simp only [switchedClades, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨C, hC | hC | ⟨p, hp, rfl⟩, hcut⟩
    · exact Or.inr (hfirst (hC ▸ hcut))
    · exact Or.inl (hC ▸ hcut)
    · by_cases hp0 : p = []
      · subst hp0
        rw [q.cutBy_false_of_taxa_subset (hq.trans hrootClade)] at hcut
        exact absurd hcut (by simp)
      · rw [switchedClade_of_short (by omega) hp0] at hcut
        exact Or.inr ⟨p, hp, hp0, hcut⟩
  · rintro (hcut | ⟨p, hp, hp0, hcut⟩)
    · exact ⟨_, Or.inr (Or.inl rfl), hcut⟩
    · exact ⟨_, Or.inr (Or.inr ⟨p, hp, switchedClade_of_short (by omega) hp0⟩), hcut⟩

/-- Moving the donor below the root changes no split: for a pair `(u, w)` of vertices of `T` with
`w` neither an ancestor of `u` nor `u` itself, the trees displayed through `(u, w)` (an edge from
above the root of `T` if `u = []`) and through `lowerPair (u, w)` cut the same quartets on the taxa
of `T`. -/
theorem cuts_lowerPair_iff {t : PhyloTree} (ht : t.WellLabelled) {f : Address × Address}
    (hw : f.2 ∈ t.nodes) (hwu : ¬f.2 <+: f.1) {q : Quartet} (hq : q.taxa ⊆ t.taxa) :
    (∃ C ∈ switchedClades t f, q.cutBy C = true) ↔
      ∃ C ∈ switchedClades t (lowerPair f), q.cutBy C = true := by
  obtain ⟨u, w⟩ := f
  have hw0 : w ≠ [] := fun h => hwu (h ▸ List.nil_prefix)
  by_cases hu0 : u = []
  · subst hu0
    have hl : lowerPair ([], w) = (rootDonor w, w) := by simp [lowerPair]
    rw [hl, cuts_rootPair_iff hw hw0 hq, cuts_rootDonor_iff ht hw hw0 hq]
  · have hl : lowerPair (u, w) = (u, w) := by simp [lowerPair, hu0]
    rw [hl]

end EdgeAbove

end Camus
