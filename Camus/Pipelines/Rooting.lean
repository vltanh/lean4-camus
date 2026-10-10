module

public import Camus.Pipelines.Astral
public import Camus.Network.RootAbove.Pairs

/-!
# Rooting a tree at an outgroup

ASTRAL returns an unrooted tree, and the pipelines of Section 3 root it "on the edge leading to the
outgroup". The library's trees are rooted (`PhyloTree`) and stand for their unrooted forms: the
quartets `Q(T)` that a tree induces (`Quartet.induced`) are those of its unrooted form. This file
roots a tree `T` on the edge leading to its leaf `z` (`PhyloTree.reroot`): the root of the rooted
tree has the leaf `z` and the rest of `T` as children, and the rooted tree has the taxa and the
induced quartets of `T` (`PhyloTree.reroot_spec`), hence its quartet support score
(`PhyloTree.quartetSupport_reroot`). The clade of a vertex on the path from `z` to the root of `T`
is replaced by its complement in the taxa, which cuts the same quartets
(`Quartet.cutBy_complement`); the other clades stay.

## Main results

* `PhyloTree.hang`, `PhyloTree.reroot`: the tree rooted at the outgroup.
* `PhyloTree.reroot_spec`: rooting keeps the taxa, the well-labelledness and the induced quartets.
* `PhyloTree.reroot_eq_fork`: the root of the rooted tree has the outgroup leaf as a child.
* `PhyloTree.exists_wellLabelled`: every nonempty finite set of taxa is the set of taxa of a
  well-labelled tree.
-/

@[expose] public section

namespace Camus

namespace PhyloTree

/-- A taxon is a taxon of `t` iff it labels a leaf of `t`. -/
theorem mem_taxa {t : PhyloTree} {a : ℕ} : a ∈ t.taxa ↔ a ∈ t.labels := List.mem_toFinset

/-- The taxa of `fork l r` are those of `l` and `r`. -/
theorem taxa_fork (l r : PhyloTree) : (PhyloTree.fork l r).taxa = l.taxa ∪ r.taxa := by
  simp [taxa, labels, List.toFinset_append]

/-- The caterpillar `(a₀,(a₁,(…,aₖ)))` on the labels `a₀, a₁, …, aₖ`. -/
def caterpillar : ℕ → List ℕ → PhyloTree
  | a, [] => .leaf a
  | a, b :: l => .fork (.leaf a) (caterpillar b l)

/-- The leaf labels of the caterpillar on `a, l` are `a, l`. -/
theorem caterpillar_labels (a : ℕ) (l : List ℕ) : (caterpillar a l).labels = a :: l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp [caterpillar, labels, ih]

/-- Every nonempty finite set `X` of taxa is the set of taxa of a well-labelled tree, a caterpillar
on `X`. -/
theorem exists_wellLabelled {X : Finset ℕ} (hX : X.Nonempty) :
    ∃ t : PhyloTree, t.WellLabelled ∧ t.taxa = X := by
  obtain ⟨a, l, hl⟩ : ∃ a l, X.toList = a :: l := by
    cases h : X.toList with
    | nil => exact absurd (Finset.toList_eq_nil.mp h) hX.ne_empty
    | cons a l => exact ⟨a, l, rfl⟩
  refine ⟨caterpillar a l, ?_, ?_⟩
  · change (caterpillar a l).labels.Nodup
    rw [caterpillar_labels, ← hl]
    exact X.nodup_toList
  · change (caterpillar a l).labels.toFinset = X
    rw [caterpillar_labels, ← hl, Finset.toList_toFinset]

/-- The tree `s` with the tree `A` hung above its root, rooted at its leaf `z`, with the leaf `z`
removed. On the path from `z` up to the root of `s`, each vertex gets as children its child off the
path and the tree above it; the tree above the root of `s` is `A`. So `fork (leaf z) (hang z s A)`
is `fork s A` rooted on the edge leading to `z`, as unrooted trees the same. -/
def hang (z : ℕ) : PhyloTree → PhyloTree → PhyloTree
  | .leaf _, A => A
  | .fork l r, A => if z ∈ l.taxa then hang z l (.fork r A) else hang z r (.fork l A)

/-- The tree `t` rooted on the edge leading to its leaf `z`: the root has the leaf `z` and the rest
of `t` as children. The root of `t`, a vertex with two neighbours in the unrooted form of `t`, is
suppressed. -/
def reroot (z : ℕ) : PhyloTree → PhyloTree
  | .leaf a => .leaf a
  | .fork l r =>
    if z ∈ l.taxa then .fork (.leaf z) (hang z l r) else .fork (.leaf z) (hang z r l)

/-- The root of `t`, rooted at `z`, has the leaf `z` as a child, unless `t` is a single leaf. -/
theorem reroot_eq_fork (z : ℕ) (l r : PhyloTree) :
    ∃ R, reroot z (.fork l r) = .fork (.leaf z) R := by
  by_cases h : z ∈ l.taxa
  · exact ⟨hang z l r, by simp [reroot, h]⟩
  · exact ⟨hang z r l, by simp [reroot, h]⟩

/-- The leaf labels of `hang z s A` are those of `s` and `A`, without `z`. -/
theorem hang_labels_perm {z : ℕ} {s : PhyloTree} (hz : z ∈ s.labels) (A : PhyloTree) :
    (hang z s A).labels.Perm (s.labels.erase z ++ A.labels) := by
  induction s generalizing A with
  | leaf a =>
    simp only [labels, List.mem_singleton] at hz
    subst hz
    simp [hang, labels]
  | fork l r ihl ihr =>
    by_cases hl : z ∈ l.taxa
    · have hl' : z ∈ l.labels := mem_taxa.mp hl
      simp only [hang, hl, ↓reduceIte, labels, List.erase_append_left _ hl']
      simpa [labels, List.append_assoc] using ihl hl' (.fork r A)
    · have hl' : z ∉ l.labels := fun h => hl (mem_taxa.mpr h)
      have hr' : z ∈ r.labels := by
        simp only [labels, List.mem_append] at hz
        exact hz.resolve_left hl'
      simp only [hang, hl, ↓reduceIte, labels, List.erase_append_right _ hl']
      refine (ihr hr' (.fork l A)).trans ?_
      simp only [labels, ← List.append_assoc]
      exact List.perm_append_comm.append_right _

/-- The leaf labels of `fork (leaf z) (hang z s A)` are those of `fork s A`. -/
theorem fork_hang_labels_perm {z : ℕ} {s : PhyloTree} (hz : z ∈ s.labels) (A : PhyloTree) :
    (PhyloTree.fork (.leaf z) (hang z s A)).labels.Perm (PhyloTree.fork s A).labels := by
  simp only [labels, List.singleton_append]
  refine ((hang_labels_perm hz A).cons z).trans ?_
  rw [← List.erase_append_left _ hz]
  exact (List.perm_cons_erase (List.mem_append_left _ hz)).symm

/-- Two lists without common elements have disjoint sets of elements. -/
theorem disjoint_toFinset_of_nodup {l₁ l₂ : List ℕ} (h : (l₁ ++ l₂).Nodup) :
    Disjoint l₁.toFinset l₂.toFinset :=
  Finset.disjoint_left.mpr fun _ ha hb =>
    List.disjoint_of_nodup_append h (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)

/-- A leaf label `z` of `t` gives the clade `{z}`. -/
theorem leaf_clade_mem {t : PhyloTree} {z : ℕ} (hz : z ∈ t.labels) : {z} ∈ t.clades := by
  induction t with
  | leaf a =>
    simp only [labels, List.mem_singleton] at hz
    subst hz
    simp [clades]
  | fork l r ihl ihr =>
    simp only [labels, List.mem_append] at hz
    simp only [clades, List.mem_cons, List.mem_append]
    rcases hz with h | h
    · exact Or.inr (Or.inl (ihl h))
    · exact Or.inr (Or.inr (ihr h))

/-- The clades of `hang z s A`: clades of `A`, clades of `s`, and the complements in the taxa of
`s` and `A` of the clades of `s` that contain `z`. -/
theorem clades_hang {z : ℕ} {s : PhyloTree} (hz : z ∈ s.labels) {A : PhyloTree}
    (hnd : (s.labels ++ A.labels).Nodup) :
    ∀ C ∈ (hang z s A).clades, C ∈ A.clades ∨ C ∈ s.clades ∨
      ∃ D ∈ s.clades, z ∈ D ∧ C = (s.taxa ∪ A.taxa) \ D := by
  induction s generalizing A with
  | leaf a =>
    intro C hC
    exact Or.inl hC
  | fork l r ihl ihr =>
    intro C hC
    simp only [labels, List.append_assoc] at hnd
    by_cases hl : z ∈ l.taxa
    · simp only [hang, hl, ↓reduceIte] at hC
      rcases ihl (mem_taxa.mp hl) (A := .fork r A) hnd C hC with h | h | ⟨D, hD, hzD, rfl⟩
      · simp only [clades, List.mem_cons, List.mem_append] at h
        rcases h with rfl | h | h
        -- the clade of the old root's other side is the complement of the clade of `l`
        · refine Or.inr (Or.inr ⟨l.taxa, ?_, hl, ?_⟩)
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ (taxa_mem_clades l))
          · have hd := disjoint_toFinset_of_nodup hnd
            simp only [List.toFinset_append] at hd
            change Disjoint l.taxa (r.taxa ∪ A.taxa) at hd
            rw [taxa_fork, Finset.union_assoc, Finset.union_sdiff_cancel_left hd]
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_append_right _ h)))
        · exact Or.inl h
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
      · refine Or.inr (Or.inr ⟨D, List.mem_cons_of_mem _ (List.mem_append_left _ hD), hzD, ?_⟩)
        rw [taxa_fork, taxa_fork, Finset.union_assoc]
    · have hr : z ∈ r.labels := by
        simp only [labels, List.mem_append] at hz
        exact hz.resolve_left fun h => hl (mem_taxa.mpr h)
      have hnd' : (r.labels ++ (l.labels ++ A.labels)).Nodup := by
        refine (List.Perm.nodup_iff ?_).mp hnd
        rw [← List.append_assoc, ← List.append_assoc]
        exact List.perm_append_comm.append_right _
      simp only [hang, hl, ↓reduceIte] at hC
      rcases ihr hr (A := .fork l A) hnd' C hC with h | h | ⟨D, hD, hzD, rfl⟩
      · simp only [clades, List.mem_cons, List.mem_append] at h
        rcases h with rfl | h | h
        · refine Or.inr (Or.inr ⟨r.taxa, ?_, mem_taxa.mpr hr, ?_⟩)
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ (taxa_mem_clades r))
          · have hd := disjoint_toFinset_of_nodup hnd'
            simp only [List.toFinset_append] at hd
            change Disjoint r.taxa (l.taxa ∪ A.taxa) at hd
            rw [taxa_fork, Finset.union_comm l.taxa r.taxa, Finset.union_assoc,
              Finset.union_sdiff_cancel_left hd]
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
        · exact Or.inl h
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_append_right _ h)))
      · refine Or.inr (Or.inr ⟨D, List.mem_cons_of_mem _ (List.mem_append_right _ hD), hzD, ?_⟩)
        rw [taxa_fork, taxa_fork, Finset.union_comm l.taxa r.taxa, Finset.union_assoc]

/-- The clades of `A`, the clades of `s` without `z`, and the complements of the clades of `s`
with `z` in the taxa of `s` and `A`, are clades of `hang z s A`. -/
theorem mem_clades_hang {z : ℕ} {s : PhyloTree} (hz : z ∈ s.labels) {A : PhyloTree}
    (hnd : (s.labels ++ A.labels).Nodup) :
    (∀ C ∈ A.clades, C ∈ (hang z s A).clades) ∧
      (∀ D ∈ s.clades, z ∉ D → D ∈ (hang z s A).clades) ∧
      (∀ D ∈ s.clades, z ∈ D → (s.taxa ∪ A.taxa) \ D ∈ (hang z s A).clades) := by
  induction s generalizing A with
  | leaf a =>
    simp only [labels, List.mem_singleton] at hz
    subst hz
    refine ⟨fun C hC => hC, ?_, ?_⟩
    · intro D hD hzD
      simp only [clades, List.mem_singleton] at hD
      subst hD
      exact absurd (Finset.mem_singleton_self _) hzD
    · intro D hD _
      simp only [clades, List.mem_singleton] at hD
      subst hD
      have hd := disjoint_toFinset_of_nodup hnd
      change Disjoint (leaf z).taxa A.taxa at hd
      change ((leaf z).taxa ∪ A.taxa) \ (leaf z).taxa ∈ (hang z (leaf z) A).clades
      rw [Finset.union_sdiff_cancel_left hd]
      exact taxa_mem_clades A
  | fork l r ihl ihr =>
    simp only [labels, List.append_assoc] at hnd
    have hd₀ := disjoint_toFinset_of_nodup hnd
    have hlr := disjoint_toFinset_of_nodup (List.nodup_append.mp hnd).2.1
    simp only [List.toFinset_append] at hd₀
    change Disjoint l.taxa (r.taxa ∪ A.taxa) at hd₀
    change Disjoint r.taxa A.taxa at hlr
    by_cases hl : z ∈ l.taxa
    · obtain ⟨h1, h2, h3⟩ := ihl (mem_taxa.mp hl) (A := .fork r A) hnd
      simp only [hang, hl, ↓reduceIte]
      have hA : ∀ C ∈ A.clades, C ∈ (hang z l (.fork r A)).clades :=
        fun C hC => h1 C (List.mem_cons_of_mem _ (List.mem_append_right _ hC))
      refine ⟨hA, ?_, ?_⟩
      · intro D hD hzD
        simp only [clades, List.mem_cons, List.mem_append] at hD
        rcases hD with rfl | hD | hD
        · exact absurd (Finset.mem_union_left _ hl) hzD
        · exact h2 D hD hzD
        · exact h1 D (List.mem_cons_of_mem _ (List.mem_append_left _ hD))
      · intro D hD hzD
        simp only [clades, List.mem_cons, List.mem_append] at hD
        rcases hD with rfl | hD | hD
        -- the complement of the whole of `s` is the clade of `A`
        · have hd : Disjoint (l.taxa ∪ r.taxa) A.taxa := by
            rw [Finset.disjoint_union_left]
            exact ⟨Finset.disjoint_of_subset_right Finset.subset_union_right hd₀, hlr⟩
          rw [taxa_fork, Finset.union_sdiff_cancel_left hd]
          exact hA _ (taxa_mem_clades A)
        · have := h3 D hD hzD
          rw [taxa_fork] at this
          rw [taxa_fork, Finset.union_assoc]
          exact this
        · exact absurd (Finset.mem_union_left _ (r.clade_subset_taxa D hD hzD))
            (Finset.disjoint_left.mp hd₀ hl)
    · have hr : z ∈ r.labels := by
        simp only [labels, List.mem_append] at hz
        exact hz.resolve_left fun h => hl (mem_taxa.mpr h)
      have hnd' : (r.labels ++ (l.labels ++ A.labels)).Nodup := by
        refine (List.Perm.nodup_iff ?_).mp hnd
        rw [← List.append_assoc, ← List.append_assoc]
        exact List.perm_append_comm.append_right _
      obtain ⟨h1, h2, h3⟩ := ihr hr (A := .fork l A) hnd'
      simp only [hang, hl, ↓reduceIte]
      have hA : ∀ C ∈ A.clades, C ∈ (hang z r (.fork l A)).clades :=
        fun C hC => h1 C (List.mem_cons_of_mem _ (List.mem_append_right _ hC))
      refine ⟨hA, ?_, ?_⟩
      · intro D hD hzD
        simp only [clades, List.mem_cons, List.mem_append] at hD
        rcases hD with rfl | hD | hD
        · exact absurd (Finset.mem_union_right _ (mem_taxa.mpr hr)) hzD
        · exact h1 D (List.mem_cons_of_mem _ (List.mem_append_left _ hD))
        · exact h2 D hD hzD
      · intro D hD hzD
        simp only [clades, List.mem_cons, List.mem_append] at hD
        rcases hD with rfl | hD | hD
        · have hd : Disjoint (l.taxa ∪ r.taxa) A.taxa := by
            rw [Finset.disjoint_union_left]
            exact ⟨Finset.disjoint_of_subset_right Finset.subset_union_right hd₀, hlr⟩
          rw [taxa_fork, Finset.union_sdiff_cancel_left hd]
          exact hA _ (taxa_mem_clades A)
        · exact absurd (l.clade_subset_taxa D hD hzD) hl
        · have := h3 D hD hzD
          rw [taxa_fork] at this
          rw [taxa_fork, Finset.union_comm l.taxa r.taxa, Finset.union_assoc]
          exact this

/-- `fork (leaf z) (hang z s A)`, the tree `fork s A` rooted at its leaf `z`, induces the quartets
of `fork s A`. -/
theorem induced_fork_hang {z : ℕ} {s : PhyloTree} (hz : z ∈ s.labels) {A : PhyloTree}
    (hnd : (s.labels ++ A.labels).Nodup) (q : Quartet) :
    q.induced (.fork (.leaf z) (hang z s A)) = q.induced (.fork s A) := by
  have htaxa : (PhyloTree.fork (.leaf z) (hang z s A)).taxa = (PhyloTree.fork s A).taxa :=
    List.toFinset_eq_of_perm _ _ (fork_hang_labels_perm hz A)
  have hX : (PhyloTree.fork s A).taxa = s.taxa ∪ A.taxa := taxa_fork s A
  unfold Quartet.induced
  rw [htaxa]
  by_cases hq : q.taxa ⊆ (PhyloTree.fork s A).taxa
  swap
  · simp [hq]
  simp only [hq, decide_true, Bool.true_and]
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  have hd := disjoint_toFinset_of_nodup hnd
  -- complements in the taxa cut the same quartets
  have hcompl : ∀ D ⊆ (PhyloTree.fork s A).taxa,
      q.cutBy ((s.taxa ∪ A.taxa) \ D) = q.cutBy D := by
    intro D hD
    rw [← hX]
    refine q.cutBy_complement ?_ Finset.sdiff_disjoint
    rw [Finset.sdiff_union_of_subset hD]
    exact hq
  obtain ⟨hA, hs₁, hs₂⟩ := mem_clades_hang hz hnd
  constructor
  · rintro ⟨C, hC, hcut⟩
    simp only [clades, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hC
    rcases hC with rfl | rfl | hC
    -- the root clade contains all the taxa and cuts no quartet
    · rw [← taxa_fork, htaxa] at hcut
      exact absurd hcut (by simp [q.cutBy_false_of_taxa_subset hq])
    · exact ⟨{z}, List.mem_cons_of_mem _ (List.mem_append_left _ (leaf_clade_mem hz)),
        hcut⟩
    · rcases clades_hang hz hnd C hC with h | h | ⟨D, hD, _, rfl⟩
      · exact ⟨C, List.mem_cons_of_mem _ (List.mem_append_right _ h), hcut⟩
      · exact ⟨C, List.mem_cons_of_mem _ (List.mem_append_left _ h), hcut⟩
      · refine ⟨D, List.mem_cons_of_mem _ (List.mem_append_left _ hD), ?_⟩
        rw [← hcompl D (hX ▸ (s.clade_subset_taxa D hD).trans Finset.subset_union_left)]
        exact hcut
  · rintro ⟨C, hC, hcut⟩
    simp only [clades, List.mem_cons, List.mem_append] at hC
    have hin : ∀ C ∈ (hang z s A).clades, C ∈ (PhyloTree.fork (.leaf z) (hang z s A)).clades :=
      fun C hC => List.mem_cons_of_mem _ (List.mem_append_right _ hC)
    rcases hC with rfl | hC | hC
    · exact absurd hcut (by simp [q.cutBy_false_of_taxa_subset (hX ▸ hq)])
    · by_cases hzC : z ∈ C
      · refine ⟨_, hin _ (hs₂ C hC hzC), ?_⟩
        rw [hcompl C (hX ▸ (s.clade_subset_taxa C hC).trans Finset.subset_union_left)]
        exact hcut
      · exact ⟨C, hin _ (hs₁ C hC hzC), hcut⟩
    · exact ⟨C, hin _ (hA C hC), hcut⟩

/-- Exchanging the children of the root changes no induced quartet. -/
theorem induced_fork_comm (l r : PhyloTree) (q : Quartet) :
    q.induced (.fork r l) = q.induced (.fork l r) := by
  simp only [Quartet.induced, taxa_fork, Finset.union_comm r.taxa l.taxa, clades,
    List.any_cons, List.any_append, Bool.or_comm (r.clades.any q.cutBy)]

/-- Rooting a well-labelled tree `t` at its leaf `z` keeps the taxa and the induced quartets: the
rooted tree is the same unrooted tree. -/
theorem reroot_spec {t : PhyloTree} (ht : t.WellLabelled) {z : ℕ} (hz : z ∈ t.taxa) :
    (reroot z t).WellLabelled ∧ (reroot z t).taxa = t.taxa ∧
      ∀ q : Quartet, q.induced (reroot z t) = q.induced t := by
  cases t with
  | leaf a => exact ⟨ht, rfl, fun _ => rfl⟩
  | fork l r =>
    have hnd : (l.labels ++ r.labels).Nodup := ht
    by_cases hl : z ∈ l.taxa
    · simp only [reroot, hl, ↓reduceIte]
      have hp := fork_hang_labels_perm (mem_taxa.mp hl) r
      exact ⟨(hp.nodup_iff).mpr ht, List.toFinset_eq_of_perm _ _ hp,
        induced_fork_hang (mem_taxa.mp hl) hnd⟩
    · have hr : z ∈ r.labels := by
        have hz' := mem_taxa.mp hz
        simp only [labels, List.mem_append] at hz'
        exact hz'.resolve_left fun h => hl (mem_taxa.mpr h)
      simp only [reroot, hl, ↓reduceIte]
      have hswap : (PhyloTree.fork r l).labels.Perm (PhyloTree.fork l r).labels :=
        List.perm_append_comm
      have hp := (fork_hang_labels_perm hr l).trans hswap
      have hnd' : (r.labels ++ l.labels).Nodup := (hswap.nodup_iff).mpr ht
      exact ⟨(hp.nodup_iff).mpr ht, List.toFinset_eq_of_perm _ _ hp,
        fun q => (induced_fork_hang hr hnd' q).trans (induced_fork_comm l r q)⟩

/-- Rooting a well-labelled tree at one of its leaves keeps its quartet support score. -/
theorem quartetSupport_reroot (Q : Multiset Quartet) {t : PhyloTree} (ht : t.WellLabelled)
    {z : ℕ} (hz : z ∈ t.taxa) : quartetSupport Q (reroot z t) = quartetSupport Q t := by
  unfold quartetSupport
  congr 1
  exact Finset.filter_congr fun q _ => by rw [(reroot_spec ht hz).2.2 q]

end PhyloTree

end Camus
