module

public import Camus.Pipelines.Coalescent.Sampling
public import Camus.Network.RootedIso
public import ADR11.External.Quartets.Steel

/-!
# Section 3.2: the quartets of a binary tree determine it

Section 3.2 of the paper concludes from the comparison of quartet support scores that "ASTRAL will
return t", and that "this tree will be rooted using the outgroup and then passed to CAMUS". The
comparison shows that every tree of maximum score induces the quartets of `t`
(`astral_maximizer_tendsto`); the conclusion uses the classical fact that the quartets of a binary
tree determine its unrooted topology (Steel 1992), and that rooting it at the outgroup gives back
the rooted tree. This file proves both, from Steel's reconstruction of the splits of a tree from
its quartets as formalized in lean4-adr11 (`ADR11.mem_unroot_iff_quartets`). Two well-labelled
trees on the same taxa that induce the same quartets have the same splits
(`PhyloTree.splits_eq_of_induced_eq`); if moreover the leaf of the same outgroup is a child of the
root of both, they have the same clades (`PhyloTree.clusterEq_of_induced_eq`), and so they are
equal up to the order of the children (`PhyloTree.rootedIso_of_induced_eq`), which leaves the
networks built on them unchanged (`PhyloTree.RootedIso.anchoredExtension_iff`). Every tree with at
least two taxa can be rooted at the outgroup without changing its quartets (`PhyloTree.reroot`,
`PhyloTree.induced_reroot`, `PhyloTree.rootedAt_reroot`).

## Main results

* `PhyloTree.splits`, `PhyloTree.RootedAt`: the splits of the unrooted form of a tree, and a tree
  rooted at an outgroup.
* `Quartet.exists_hasSplit`: four distinct taxa carry the quartet tree of each of their splits.
* `Coalescent.unroot_eq_of_induced_eq`: species trees whose topologies induce the same quartets
  have the same unrooted topology.
* `PhyloTree.splits_eq_of_induced_eq`: the quartets of a binary tree determine its splits.
* `PhyloTree.rootedIso_of_clusterEq`: well-labelled trees with the same clades are equal up to
  the order of the children.
* `PhyloTree.rootedIso_of_induced_eq`: the quartets of a binary tree rooted at an outgroup
  determine it, up to the order of the children.
* `PhyloTree.reroot`, `PhyloTree.induced_reroot`, `PhyloTree.rootedAt_reroot`: rooting a tree at
  the outgroup keeps its quartets.

## Proof

The paper uses these facts without proof; the proof here is Steel's reconstruction, from
lean4-adr11. The bridge `Coalescent.HasTopology` reads a tree `t` as a species tree `σ` of
lean4-adr11, whose unrooted topology `unroot σ.clusters` is the set of the splits of `t`
(`PhyloTree.mem_splits_iff`). A bipartition `A | Aᶜ` with two taxa on each side is a split of `σ`
if and only if every quartet tree `aa'|bb'` with `a, a' ∈ A` and `b, b' ∉ A` is induced by `σ`
(`ADR11.mem_unroot_iff_quartets`), and `σ` induces `aa'|bb'` if and only if `t` does
(`Coalescent.separates_iff_induced`, through `Coalescent.induces_iff_induced`). So trees with the
same quartets have the same splits (`Coalescent.unroot_subset_of_induced`). If the outgroup `o` is
a child of the root, the clades of the tree are the set of all taxa, `{o}`, and the sides of its
splits that do not contain `o` (`PhyloTree.mem_clades_iff_of_rootedAt`). Rooting at the outgroup
moves the root down the path to `o`, one rotation `((a, b), c) ↦ (a, (b, c))` at a time, and a
rotation keeps the quartets (`PhyloTree.induced_rotate`).
-/

@[expose] public section

namespace Camus

namespace PhyloTree

/-- The splits of the unrooted form of `t`, as the set of their sides: the clades of `t` other
than `t.taxa`, and their complements in `t.taxa`. Deleting an edge of the unrooted tree separates
one side of its split from the other; the two edges below the root give the same split. -/
def splits (t : PhyloTree) : Finset (Finset ℕ) :=
  t.clades.toFinset.erase t.taxa ∪ (t.clades.toFinset.erase t.taxa).image (t.taxa \ ·)

/-- The tree `t` is rooted at the outgroup `o` (Section 3.2: the tree "will be rooted using the
outgroup"): the leaf labelled `o` is a child of the root of `t`. -/
def RootedAt (t : PhyloTree) (o : ℕ) : Prop := ∃ b : Bool, t.nodeAt [b] = some (.leaf o)

/-- A tree rooted at the outgroup `o` is `(o, r)` or `(r, o)`. -/
theorem rootedAt_iff {t : PhyloTree} {o : ℕ} :
    t.RootedAt o ↔ ∃ r, t = .fork (.leaf o) r ∨ t = .fork r (.leaf o) := by
  constructor
  · rintro ⟨b, hb⟩
    cases t with
    | leaf a => simp [nodeAt] at hb
    | fork l r =>
      cases b
      · simp only [nodeAt, Option.some.injEq] at hb
        exact ⟨r, Or.inl (by rw [hb])⟩
      · simp only [nodeAt, Option.some.injEq] at hb
        exact ⟨l, Or.inr (by rw [hb])⟩
  · rintro ⟨r, rfl | rfl⟩
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

/-- The taxa of a fork are the taxa of its two subtrees. -/
theorem taxa_fork (l r : PhyloTree) : (fork l r).taxa = l.taxa ∪ r.taxa := by
  simp [taxa, labels, List.toFinset_append]

/-- The taxa of a leaf. -/
theorem taxa_leaf (a : ℕ) : (leaf a).taxa = {a} := by
  simp [taxa, labels]

/-- The clades of a fork: the taxa of the fork, and the clades of its two subtrees. -/
theorem mem_clades_fork {l r : PhyloTree} {C : Finset ℕ} :
    C ∈ (fork l r).clades ↔ C = l.taxa ∪ r.taxa ∨ C ∈ l.clades ∨ C ∈ r.clades := by
  simp [clades]

/-- A tree has at least one taxon. -/
theorem taxa_nonempty (t : PhyloTree) : t.taxa.Nonempty :=
  t.clade_nonempty t.taxa t.taxa_mem_clades

/-- The two subtrees of a well-labelled fork are well-labelled and have disjoint taxa. -/
theorem wellLabelled_fork {l r : PhyloTree} (h : (fork l r).WellLabelled) :
    l.WellLabelled ∧ r.WellLabelled ∧ Disjoint l.taxa r.taxa := by
  have hnd : (l.labels ++ r.labels).Nodup := h
  obtain ⟨hl, hr, hlr⟩ := List.nodup_append.mp hnd
  refine ⟨hl, hr, Finset.disjoint_left.mpr fun a ha hb => ?_⟩
  exact hlr a (List.mem_toFinset.mp ha) a (List.mem_toFinset.mp hb) rfl

/-- A nonempty set is not contained in two disjoint sets. -/
private theorem not_subset_disjoint {A B C : Finset ℕ} (hA : A.Nonempty) (hB : A ⊆ B) (hC : A ⊆ C)
    (hBC : Disjoint B C) : False := by
  obtain ⟨a, ha⟩ := hA
  exact Finset.disjoint_left.mp hBC (hB ha) (hC ha)

/-- In a well-labelled fork, the clades contained in the taxa of the left subtree are the clades
of the left subtree. -/
theorem clades_filter_left {l r : PhyloTree} (h : (fork l r).WellLabelled) :
    (fork l r).clades.toFinset.filter (· ⊆ l.taxa) = l.clades.toFinset := by
  obtain ⟨-, -, hlr⟩ := wellLabelled_fork h
  ext C
  simp only [Finset.mem_filter, List.mem_toFinset, mem_clades_fork]
  constructor
  · rintro ⟨rfl | hC | hC, hsub⟩
    · exact (not_subset_disjoint r.taxa_nonempty Finset.Subset.rfl
        (Finset.subset_union_right.trans hsub) hlr.symm).elim
    · exact hC
    · exact (not_subset_disjoint (r.clade_nonempty C hC) (r.clade_subset_taxa C hC) hsub
        hlr.symm).elim
  · intro hC
    exact ⟨Or.inr (Or.inl hC), l.clade_subset_taxa C hC⟩

/-- In a well-labelled fork, the clades contained in the taxa of the right subtree are the clades
of the right subtree. -/
theorem clades_filter_right {l r : PhyloTree} (h : (fork l r).WellLabelled) :
    (fork l r).clades.toFinset.filter (· ⊆ r.taxa) = r.clades.toFinset := by
  obtain ⟨-, -, hlr⟩ := wellLabelled_fork h
  ext C
  simp only [Finset.mem_filter, List.mem_toFinset, mem_clades_fork]
  constructor
  · rintro ⟨rfl | hC | hC, hsub⟩
    · exact (not_subset_disjoint l.taxa_nonempty Finset.Subset.rfl
        (Finset.subset_union_left.trans hsub) hlr).elim
    · exact (not_subset_disjoint (l.clade_nonempty C hC) (l.clade_subset_taxa C hC) hsub
        hlr).elim
    · exact hC
  · intro hC
    exact ⟨Or.inr (Or.inr hC), r.clade_subset_taxa C hC⟩

/-- A leaf and a well-labelled fork do not have the same clades: the fork has two disjoint
clades, the taxa of its subtrees. -/
theorem not_clusterEq_leaf_fork {a : ℕ} {l r : PhyloTree} (h : (fork l r).WellLabelled) :
    ¬ ClusterEq (leaf a) (fork l r) := by
  obtain ⟨-, -, hlr⟩ := wellLabelled_fork h
  intro heq
  have hmem : ∀ C ∈ (fork l r).clades, C = {a} := by
    intro C hC
    have := List.mem_toFinset.mpr hC
    rw [← heq.2] at this
    simpa [clades] using this
  have hl := hmem _ (mem_clades_fork.mpr (Or.inr (Or.inl l.taxa_mem_clades)))
  have hr := hmem _ (mem_clades_fork.mpr (Or.inr (Or.inr r.taxa_mem_clades)))
  rw [hl, hr] at hlr
  exact (Finset.disjoint_singleton.mp hlr) rfl

/-- Well-labelled trees with the same clades are equal up to the order of the children: the
children of the root are the maximal clades other than the set of all taxa, and the clades below
a child are the clades contained in its taxa. -/
theorem rootedIso_of_clusterEq {t t' : PhyloTree} (ht : t.WellLabelled) (ht' : t'.WellLabelled)
    (h : ClusterEq t t') : RootedIso t t' := by
  induction t generalizing t' with
  | leaf a =>
    cases t' with
    | leaf a' =>
      have := h.1
      rw [taxa_leaf, taxa_leaf, Finset.singleton_inj] at this
      subst this
      exact .leaf a
    | fork l' r' => exact (not_clusterEq_leaf_fork ht' h).elim
  | fork l r ihl ihr =>
    cases t' with
    | leaf a' => exact (not_clusterEq_leaf_fork ht h.symm).elim
    | fork l' r' =>
      obtain ⟨hl, hr, hlr⟩ := wellLabelled_fork ht
      obtain ⟨hl', hr', hlr'⟩ := wellLabelled_fork ht'
      have htaxa : l.taxa ∪ r.taxa = l'.taxa ∪ r'.taxa := by
        rw [← taxa_fork, ← taxa_fork]
        exact h.1
      have hmem : ∀ C, C ∈ (fork l r).clades ↔ C ∈ (fork l' r').clades := by
        intro C
        rw [← List.mem_toFinset, ← List.mem_toFinset, h.2]
      -- a clade of one tree other than the set of all taxa lies below a child of the root of
      -- the other tree
      have hbelow : ∀ {A B C D : PhyloTree}, (fork A B).WellLabelled →
          (fork C D).WellLabelled → A.taxa ∪ B.taxa = C.taxa ∪ D.taxa →
          (∀ X, X ∈ (fork A B).clades ↔ X ∈ (fork C D).clades) →
          A.taxa ⊆ C.taxa ∨ A.taxa ⊆ D.taxa := by
        intro A B C D hAB _ hun hiff
        obtain ⟨-, -, hAB'⟩ := wellLabelled_fork hAB
        have hA := (hiff A.taxa).mp (mem_clades_fork.mpr (Or.inr (Or.inl A.taxa_mem_clades)))
        rcases mem_clades_fork.mp hA with hA | hA | hA
        · rw [← hun] at hA
          exact (not_subset_disjoint B.taxa_nonempty (hA ▸ Finset.subset_union_right)
            Finset.Subset.rfl hAB').elim
        · exact Or.inl (C.clade_subset_taxa _ hA)
        · exact Or.inr (D.clade_subset_taxa _ hA)
      -- the complement of the taxa of one child in the set of all taxa
      have hcompl : ∀ {A B : PhyloTree}, Disjoint A.taxa B.taxa →
          B.taxa = (A.taxa ∪ B.taxa) \ A.taxa := by
        intro A B hAB
        rw [Finset.union_sdiff_left, Finset.sdiff_eq_self_of_disjoint hAB.symm]
      rcases hbelow ht ht' htaxa hmem with h1 | h1
      · -- the left children have the same taxa, and so do the right children
        rcases hbelow ht' ht htaxa.symm (fun X => (hmem X).symm) with h2 | h2
        · have hll : l.taxa = l'.taxa := Finset.Subset.antisymm h1 h2
          have hrr : r.taxa = r'.taxa := by rw [hcompl hlr, hcompl hlr', htaxa, hll]
          refine .fork (ihl hl hl' ⟨hll, ?_⟩) (ihr hr hr' ⟨hrr, ?_⟩)
          · rw [← clades_filter_left ht, ← clades_filter_left ht', h.2, hll]
          · rw [← clades_filter_right ht, ← clades_filter_right ht', h.2, hrr]
        · exact (not_subset_disjoint l.taxa_nonempty Finset.Subset.rfl (h1.trans h2) hlr).elim
      · -- the left child of one tree has the taxa of the right child of the other
        have h2 : r'.taxa ⊆ l.taxa ∨ r'.taxa ⊆ r.taxa := by
          have hswap : (fork r' l').WellLabelled := by
            change (r'.labels ++ l'.labels).Nodup
            exact List.nodup_append_comm.mp ht'
          exact hbelow hswap ht (by rw [Finset.union_comm, htaxa]) (fun X => by
            rw [← List.mem_toFinset, ← List.mem_toFinset, (ClusterEq.fork_swap r' l').2, ← h.2])
        rcases h2 with h2 | h2
        · have hlr2 : l.taxa = r'.taxa := Finset.Subset.antisymm h1 h2
          have hrl : r.taxa = l'.taxa := by
            rw [hcompl hlr, htaxa, hlr2, Finset.union_comm,
              ← hcompl (A := r') (B := l') hlr'.symm]
          refine .swap (ihl hl hr' ⟨hlr2, ?_⟩) (ihr hr hl' ⟨hrl, ?_⟩)
          · rw [← clades_filter_left ht, ← clades_filter_right ht', h.2, hlr2]
          · rw [← clades_filter_right ht, ← clades_filter_left ht', h.2, hrl]
        · exact (not_subset_disjoint l.taxa_nonempty Finset.Subset.rfl (h1.trans h2) hlr).elim

/-- A network is built on a well-labelled tree `t` (with the root kept) if and only if it is built
on a well-labelled tree `t'` with the same clades. -/
theorem ClusterEq.anchoredExtension_iff {t t' : PhyloTree} (ht : t.WellLabelled)
    (ht' : t'.WellLabelled) (h : ClusterEq t t') (N : RootedNetwork) :
    N.AnchoredExtension t ↔ N.AnchoredExtension t' :=
  (rootedIso_of_clusterEq ht ht' h).anchoredExtension_iff N

end PhyloTree

namespace Quartet

/-- The quartet tree `q` is x₁x₂|y₁y₂: its taxa are `x₁, x₂, y₁, y₂`, and a set of taxa cuts it
if and only if it contains `x₁` and `x₂` and neither `y₁` nor `y₂`, or the reverse. -/
def HasSplit (q : Quartet) (x₁ x₂ y₁ y₂ : ℕ) : Prop :=
  q.taxa = {x₁, x₂, y₁, y₂} ∧ ∀ S : Finset ℕ, q.cutBy S = true ↔
    (x₁ ∈ S ∧ x₂ ∈ S ∧ y₁ ∉ S ∧ y₂ ∉ S) ∨ (y₁ ∈ S ∧ y₂ ∈ S ∧ x₁ ∉ S ∧ x₂ ∉ S)

namespace HasSplit

variable {q : Quartet} {x₁ x₂ y₁ y₂ : ℕ}

/-- x₁x₂|y₁y₂ is x₂x₁|y₁y₂. -/
theorem swap_left (h : q.HasSplit x₁ x₂ y₁ y₂) : q.HasSplit x₂ x₁ y₁ y₂ := by
  refine ⟨by rw [h.1, Finset.insert_comm], fun S => (h.2 S).trans ?_⟩
  tauto

/-- x₁x₂|y₁y₂ is x₁x₂|y₂y₁. -/
theorem swap_right (h : q.HasSplit x₁ x₂ y₁ y₂) : q.HasSplit x₁ x₂ y₂ y₁ := by
  refine ⟨by rw [h.1, Finset.pair_comm y₁ y₂], fun S => (h.2 S).trans ?_⟩
  tauto

/-- x₁x₂|y₁y₂ is y₁y₂|x₁x₂. -/
theorem swap (h : q.HasSplit x₁ x₂ y₁ y₂) : q.HasSplit y₁ y₂ x₁ x₂ := by
  refine ⟨?_, fun S => (h.2 S).trans ?_⟩
  · rw [h.1]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · tauto

end HasSplit

/-- A set of taxa cuts `q` iff it contains one side of `q` and avoids the other. -/
theorem cutBy_iff (q : Quartet) (S : Finset ℕ) : q.cutBy S = true ↔
    q.sides.1 ⊆ S ∧ Disjoint q.sides.2 S ∨ q.sides.2 ⊆ S ∧ Disjoint q.sides.1 S := by
  simp [cutBy]

/-- The quartet tree x₁x₂|y₁y₂ for `x₁ < x₂`, `y₁ < y₂` and `x₁ < y₁`: with its taxa
`a < b < c < d`, it is ab|cd if `x₂ < y₁`, ac|bd if `y₁ < x₂ < y₂`, and ad|bc if `y₂ < x₂`. -/
theorem exists_hasSplit_of_lt {x₁ x₂ y₁ y₂ : ℕ} (h12 : x₁ < x₂) (h34 : y₁ < y₂) (h13 : x₁ < y₁)
    (h23 : x₂ ≠ y₁) (h24 : x₂ ≠ y₂) : ∃ q : Quartet, q.HasSplit x₁ x₂ y₁ y₂ := by
  rcases lt_or_gt_of_ne h23 with h | h
  · -- `x₁ < x₂ < y₁ < y₂`: ab|cd
    refine ⟨⟨x₁, x₂, y₁, y₂, h12, h, h34, 0⟩, rfl, fun S => ?_⟩
    rw [cutBy_iff]
    simp [sides, Finset.insert_subset_iff, Finset.disjoint_insert_left, and_assoc]
  · rcases lt_or_gt_of_ne h24 with h' | h'
    · -- `x₁ < y₁ < x₂ < y₂`: ac|bd
      refine ⟨⟨x₁, y₁, x₂, y₂, h13, h, h', 1⟩, ?_, fun S => ?_⟩
      · simp only [taxa]
        rw [Finset.insert_comm y₁ x₂]
      · rw [cutBy_iff]
        simp [sides, Finset.insert_subset_iff, Finset.disjoint_insert_left, and_assoc]
    · -- `x₁ < y₁ < y₂ < x₂`: ad|bc
      refine ⟨⟨x₁, y₁, y₂, x₂, h13, h34, h', 2⟩, ?_, fun S => ?_⟩
      · simp only [taxa]
        ext z
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · rw [cutBy_iff]
        simp only [sides, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
          ite_false]
        simp [Finset.insert_subset_iff, Finset.disjoint_insert_left]
        tauto

/-- Four distinct taxa `x₁, x₂, y₁, y₂` carry a quartet tree x₁x₂|y₁y₂. -/
theorem exists_hasSplit {x₁ x₂ y₁ y₂ : ℕ} (h12 : x₁ ≠ x₂) (h34 : y₁ ≠ y₂) (h13 : x₁ ≠ y₁)
    (h14 : x₁ ≠ y₂) (h23 : x₂ ≠ y₁) (h24 : x₂ ≠ y₂) : ∃ q : Quartet, q.HasSplit x₁ x₂ y₁ y₂ := by
  -- the case of increasing pairs, with the smaller pair first
  have hinc : ∀ {x₁ x₂ y₁ y₂ : ℕ}, x₁ < x₂ → y₁ < y₂ → x₁ ≠ y₁ → x₁ ≠ y₂ → x₂ ≠ y₁ →
      x₂ ≠ y₂ → ∃ q : Quartet, q.HasSplit x₁ x₂ y₁ y₂ := by
    intro x₁ x₂ y₁ y₂ h12 h34 h13 _ h23 h24
    rcases lt_or_gt_of_ne h13 with h | h
    · exact exists_hasSplit_of_lt h12 h34 h h23 h24
    · obtain ⟨q, hq⟩ := exists_hasSplit_of_lt h34 h12 h (Ne.symm (by omega)) (Ne.symm h24)
      exact ⟨q, hq.swap⟩
  rcases lt_or_gt_of_ne h12 with ha | ha <;> rcases lt_or_gt_of_ne h34 with hb | hb
  · exact hinc ha hb h13 h14 h23 h24
  · obtain ⟨q, hq⟩ := hinc ha hb h14 h13 h24 h23
    exact ⟨q, hq.swap_right⟩
  · obtain ⟨q, hq⟩ := hinc ha hb h23 h24 h13 h14
    exact ⟨q, hq.swap_left⟩
  · obtain ⟨q, hq⟩ := hinc ha hb h24 h23 h14 h13
    exact ⟨q, hq.swap_left.swap_right⟩

end Quartet

namespace Coalescent

open Finset ADR11

variable {L : Finset ℕ}

/-- A taxon of `L` is in a set `A` of taxa iff its label is in the labels of `A`. -/
theorem val_mem_map_label {A : Finset L} {x : L} : (x : ℕ) ∈ A.map (label L) ↔ x ∈ A :=
  mem_map' (label L)

/-- The labels of all the taxa of `L` are `L`. -/
theorem map_label_univ : (univ : Finset L).map (label L) = L := by
  rw [univ_eq_attach]
  exact attach_map_val

/-- The labels of the complement of `A` are the taxa of `L` that are not labels of `A`. -/
theorem map_label_compl (A : Finset L) : Aᶜ.map (label L) = L \ A.map (label L) := by
  ext n
  simp only [mem_map, mem_compl, mem_sdiff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, fun ⟨y, hy, hyx⟩ => hx ?_⟩
    rwa [← Subtype.ext hyx]
  · rintro ⟨hn, hnot⟩
    exact ⟨⟨n, hn⟩, fun h => hnot ⟨⟨n, hn⟩, h, rfl⟩, rfl⟩

/-- The sides of the splits of the unrooted topology of a species tree are nonempty. -/
theorem nonempty_of_mem_unroot (σ : SpeciesTree L) {A : Finset L} (h : A ∈ unroot σ.clusters) :
    A.Nonempty := by
  rcases mem_unroot.1 h with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact σ.nonempty_of_mem A h1
  · rw [nonempty_iff_ne_empty]
    rintro rfl
    exact h2 compl_empty

/-- Through the topology `t` of the species tree `σ`: a split of the unrooted topology of `σ`
separates `a, a'` from `b, b'` iff `t` induces the quartet tree `aa'|bb'`. -/
theorem separates_iff_induced {σ : SpeciesTree L} {t : PhyloTree} (h : HasTopology σ t)
    {a a' b b' : L} {q : Quartet} (hq : q.HasSplit a a' b b') :
    (∃ C ∈ unroot σ.clusters, a ∈ C ∧ a' ∈ C ∧ b ∉ C ∧ b' ∉ C) ↔ q.induced t = true := by
  rw [← induces_iff_induced h q]
  have htaxa : q.taxa ⊆ L := by
    rw [hq.1]
    intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl
    exacts [a.2, a'.2, b.2, b'.2]
  simp only [Induces, htaxa, true_and, hq.2, val_mem_map_label]
  constructor
  · rintro ⟨C, hC, ha, ha', hb, hb'⟩
    exact ⟨C, hC, Or.inl ⟨ha, ha', hb, hb'⟩⟩
  · rintro ⟨C, hC, ⟨ha, ha', hb, hb'⟩ | ⟨hb, hb', ha, ha'⟩⟩
    · exact ⟨C, hC, ha, ha', hb, hb'⟩
    · refine ⟨Cᶜ, compl_mem_unroot.mpr hC, ?_, ?_, ?_, ?_⟩ <;> simpa [mem_compl]

/-- If every quartet tree induced by the topology `t` of `σ` is induced by the topology `t'` of
`σ'`, every split of the unrooted topology of `σ` is a split of that of `σ'`: a split with one
taxon on a side is a split of every tree, and a split with two taxa on each side is determined by
the quartet trees `aa'|bb'` across it (Steel's reconstruction, `ADR11.mem_unroot_iff_quartets`). -/
theorem unroot_subset_of_induced {σ σ' : SpeciesTree L} {t t' : PhyloTree}
    (h : HasTopology σ t) (h' : HasTopology σ' t')
    (hq : ∀ q : Quartet, q.induced t = true → q.induced t' = true) :
    unroot σ.clusters ⊆ unroot σ'.clusters := by
  intro A hA
  have hAne := nonempty_of_mem_unroot σ hA
  have hAcne := nonempty_of_mem_unroot σ (compl_mem_unroot.mpr hA)
  -- a side with one taxon
  by_cases h1 : #A ≤ 1
  · obtain ⟨x, rfl⟩ := card_eq_one.1 (le_antisymm h1 (card_pos.2 hAne))
    refine mem_unroot.2 (Or.inl ⟨σ'.singleton_mem x, ?_⟩)
    intro hu
    rw [hu, compl_univ] at hAcne
    exact not_nonempty_empty hAcne
  by_cases h2 : #Aᶜ ≤ 1
  · obtain ⟨x, hx⟩ := card_eq_one.1 (le_antisymm h2 (card_pos.2 hAcne))
    refine mem_unroot.2 (Or.inr ⟨hx ▸ σ'.singleton_mem x, ?_⟩)
    intro hu
    have : A = ∅ := by rw [← compl_compl A, hu, compl_univ]
    exact hAne.ne_empty this
  -- two taxa on each side: the quartet trees across the split
  rw [mem_unroot_iff_quartets σ' (by omega) (by omega)]
  intro a ha a' ha' b hb b' hb' haa hbb
  rw [mem_compl] at hb hb'
  have hab : a ≠ b := by rintro rfl; exact hb ha
  have hab' : a ≠ b' := by rintro rfl; exact hb' ha
  have ha'b : a' ≠ b := by rintro rfl; exact hb ha'
  have ha'b' : a' ≠ b' := by rintro rfl; exact hb' ha'
  have hval : ∀ {x y : L}, x ≠ y → (x : ℕ) ≠ y := fun hxy hv => hxy (Subtype.ext hv)
  obtain ⟨q, hqs⟩ := Quartet.exists_hasSplit (hval haa) (hval hbb) (hval hab) (hval hab')
    (hval ha'b) (hval ha'b')
  exact (separates_iff_induced h' hqs).2
    (hq q ((separates_iff_induced h hqs).1 ⟨A, hA, ha, ha', hb, hb'⟩))

/-- Section 3.2, through lean4-adr11: species trees whose topologies induce the same quartet trees
have the same unrooted topology. -/
theorem unroot_eq_of_induced_eq {σ σ' : SpeciesTree L} {t t' : PhyloTree}
    (h : HasTopology σ t) (h' : HasTopology σ' t')
    (hq : ∀ q : Quartet, q.induced t = q.induced t') :
    unroot σ.clusters = unroot σ'.clusters :=
  Subset.antisymm (unroot_subset_of_induced h h' fun q hq' => (hq q) ▸ hq')
    (unroot_subset_of_induced h' h fun q hq' => (hq q).symm ▸ hq')

/-- Every well-labelled tree is the topology of a species tree on any set of taxa equal to its
taxa. -/
theorem exists_hasTopology_of_taxa (t : PhyloTree) (ht : t.WellLabelled) (hL : t.taxa = L) :
    ∃ σ : SpeciesTree L, HasTopology σ t := by
  subst hL
  exact exists_hasTopology t ht

end Coalescent

namespace PhyloTree

open Finset ADR11 Coalescent

/-- The splits of the topology `t` of a species tree `σ` are the labels of the splits of the
unrooted topology of `σ`. -/
theorem mem_splits_iff {L : Finset ℕ} {σ : SpeciesTree L} {t : PhyloTree} (h : HasTopology σ t)
    (A : Finset ℕ) : A ∈ t.splits ↔ ∃ B ∈ unroot σ.clusters, B.map (label L) = A := by
  have htaxa := taxa_eq_of_hasTopology h
  have hne : ∀ {B : Finset L}, B.map (label L) = L ↔ B = univ := by
    intro B
    constructor
    · intro hB
      apply map_injective (label L)
      rw [hB, map_label_univ]
    · rintro rfl
      exact map_label_univ
  simp only [splits, mem_union, mem_erase, List.mem_toFinset, mem_image, htaxa]
  constructor
  · rintro (⟨hAL, hA⟩ | ⟨C, ⟨hCL, hC⟩, rfl⟩)
    · obtain ⟨B, hB, rfl⟩ := (h A).1 hA
      exact ⟨B, mem_unroot.2 (Or.inl ⟨hB, fun hu => hAL (hne.2 hu)⟩), rfl⟩
    · obtain ⟨B, hB, rfl⟩ := (h C).1 hC
      refine ⟨Bᶜ, compl_mem_unroot.2 (mem_unroot.2 (Or.inl ⟨hB, fun hu => hCL (hne.2 hu)⟩)),
        map_label_compl B⟩
  · rintro ⟨B, hB, rfl⟩
    rcases mem_unroot.1 hB with ⟨hB, hBu⟩ | ⟨hB, hBu⟩
    · exact Or.inl ⟨fun hu => hBu (hne.1 hu), (h _).2 ⟨B, hB, rfl⟩⟩
    · refine Or.inr ⟨Bᶜ.map (label L), ⟨fun hu => hBu (hne.1 hu), (h _).2 ⟨Bᶜ, hB, rfl⟩⟩, ?_⟩
      rw [map_label_compl, Finset.sdiff_sdiff_eq_self]
      intro n hn
      obtain ⟨x, -, rfl⟩ := mem_map.1 hn
      exact x.2

/-- Section 3.2: two well-labelled trees on the same taxa that induce the same quartets have the
same splits, that is, the same unrooted topology (Steel 1992, through lean4-adr11's
`ADR11.mem_unroot_iff_quartets`). -/
theorem splits_eq_of_induced_eq {t t' : PhyloTree} (ht : t.WellLabelled) (ht' : t'.WellLabelled)
    (htaxa : t.taxa = t'.taxa) (hq : ∀ q : Quartet, q.induced t = q.induced t') :
    t.splits = t'.splits := by
  obtain ⟨σ, hσ⟩ := exists_hasTopology t ht
  obtain ⟨σ', hσ'⟩ := exists_hasTopology_of_taxa t' ht' htaxa.symm
  have hU := unroot_eq_of_induced_eq hσ hσ' hq
  ext A
  rw [mem_splits_iff hσ, mem_splits_iff hσ', hU]

/-- The clades of a well-labelled tree rooted at the outgroup `o`: the set of all taxa, `{o}`,
and the sides of its splits that do not contain `o`. -/
theorem mem_clades_iff_of_rootedAt {t : PhyloTree} (ht : t.WellLabelled) {o : ℕ}
    (hto : t.RootedAt o) (C : Finset ℕ) :
    C ∈ t.clades.toFinset ↔ C = t.taxa ∨ C = {o} ∨ (C ∈ t.splits ∧ o ∉ C) := by
  -- the case `t = (o, r)`
  have hcase : ∀ r : PhyloTree, (fork (leaf o) r).WellLabelled →
      ∀ C, C ∈ (fork (leaf o) r).clades.toFinset ↔ C = (fork (leaf o) r).taxa ∨ C = {o} ∨
        (C ∈ (fork (leaf o) r).splits ∧ o ∉ C) := by
    intro r hr C
    obtain ⟨-, -, hor⟩ := wellLabelled_fork hr
    rw [taxa_leaf, Finset.disjoint_singleton_left] at hor
    have hT : (fork (leaf o) r).taxa = insert o r.taxa := by
      rw [taxa_fork, taxa_leaf, Finset.insert_eq]
    have hclades : ∀ C, C ∈ (fork (leaf o) r).clades ↔
        C = insert o r.taxa ∨ C = {o} ∨ C ∈ r.clades := by
      intro C
      rw [mem_clades_fork, taxa_leaf, ← Finset.insert_eq]
      simp [clades]
    have hro : ∀ D ∈ r.clades, o ∉ D := fun D hD hoD => hor (r.clade_subset_taxa D hD hoD)
    simp only [splits, mem_union, mem_erase, List.mem_toFinset, mem_image, hT, hclades]
    constructor
    · rintro (rfl | rfl | hC)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · refine Or.inr (Or.inr ⟨Or.inl ⟨fun h => hro C hC (h ▸ Finset.mem_insert_self o _),
          Or.inr (Or.inr hC)⟩, hro C hC⟩)
    · rintro (rfl | rfl | ⟨⟨-, hC⟩ | ⟨D, ⟨hD, hD'⟩, rfl⟩, hoC⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact hC
      · rcases hD' with rfl | rfl | hD'
        · exact absurd rfl hD
        · refine Or.inr (Or.inr ?_)
          rw [Finset.insert_sdiff_of_mem _ (Finset.mem_singleton_self o),
            Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem hor]
          exact r.taxa_mem_clades
        · exact absurd (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self o _, hro D hD'⟩) hoC
  obtain ⟨r, rfl | rfl⟩ := rootedAt_iff.mp hto
  · exact hcase r ht C
  · -- `t = (r, o)` has the clades, taxa and splits of `(o, r)`
    have hswap := ClusterEq.fork_swap r (leaf o)
    have hwl : (fork (leaf o) r).WellLabelled := by
      change ((leaf o).labels ++ r.labels).Nodup
      exact List.nodup_append_comm.mp ht
    have hsplits : (fork r (leaf o)).splits = (fork (leaf o) r).splits := by
      simp only [splits, hswap.1, hswap.2]
    rw [hswap.2, hswap.1, hsplits]
    exact hcase r hwl C

/-- Section 3.2: two well-labelled trees on the same taxa that induce the same quartets and are
rooted at the same outgroup have the same clades. -/
theorem clusterEq_of_induced_eq {t t' : PhyloTree} (ht : t.WellLabelled) (ht' : t'.WellLabelled)
    (htaxa : t.taxa = t'.taxa) (hq : ∀ q : Quartet, q.induced t = q.induced t') {o : ℕ}
    (hto : t.RootedAt o) (hto' : t'.RootedAt o) : ClusterEq t t' := by
  refine ⟨htaxa, ?_⟩
  ext C
  rw [mem_clades_iff_of_rootedAt ht hto, mem_clades_iff_of_rootedAt ht' hto', htaxa,
    splits_eq_of_induced_eq ht ht' htaxa hq]

/-- Section 3.2: "ASTRAL will return t", and "this tree will be rooted using the outgroup". Two
well-labelled trees on the same taxa that induce the same quartets and are rooted at the same
outgroup are equal up to the order of the children. So the networks built on them are the same
(`RootedIso.anchoredExtension_iff`). -/
theorem rootedIso_of_induced_eq {t t' : PhyloTree} (ht : t.WellLabelled) (ht' : t'.WellLabelled)
    (htaxa : t.taxa = t'.taxa) (hq : ∀ q : Quartet, q.induced t = q.induced t') {o : ℕ}
    (hto : t.RootedAt o) (hto' : t'.RootedAt o) : RootedIso t t' :=
  rootedIso_of_clusterEq ht ht' (clusterEq_of_induced_eq ht ht' htaxa hq hto hto')

end PhyloTree

namespace Quartet

/-- A set of taxa `S` and its complement in a set `L` of taxa cut the same quartet trees on taxa
of `L`. -/
theorem cutBy_sdiff {q : Quartet} {L : Finset ℕ} (hq : q.taxa ⊆ L) (S : Finset ℕ) :
    q.cutBy (L \ S) = q.cutBy S := by
  obtain ⟨h1, h2⟩ := q.sides_subset_taxa
  have hsub : ∀ A ⊆ q.taxa, A ⊆ L \ S ↔ Disjoint A S := fun A hA => by
    rw [Finset.subset_sdiff]
    exact and_iff_right (hA.trans hq)
  have hdisj : ∀ A ⊆ q.taxa, Disjoint A (L \ S) ↔ A ⊆ S := fun A hA => by
    simp only [Finset.disjoint_left, Finset.mem_sdiff, not_and, not_not]
    exact ⟨fun h x hx => h hx (hA.trans hq hx), fun h x hx _ => h hx⟩
  rw [Bool.eq_iff_iff, cutBy_iff, cutBy_iff, hsub _ h1, hsub _ h2, hdisj _ h1, hdisj _ h2]
  tauto

end Quartet

/-! ### Rooting a tree at the outgroup -/

namespace PhyloTree

/-- The tree `s`, with the tree `up` hanging from the edge above its root, rooted on the edge to the
leaf `o` of `s`: the subtrees met on the path from the root of `s` down to `o` are hung, in reverse
order, on the path from the new root up to `up`. -/
def graftAt (o : ℕ) : PhyloTree → PhyloTree → PhyloTree
  | .leaf a, up => .fork (.leaf a) up
  | .fork a b, up => if o ∈ a.taxa then graftAt o a (.fork b up) else graftAt o b (.fork a up)

/-- Section 3.2: the tree `t` "rooted using the outgroup" `o`, the same unrooted tree rooted on the
edge to the leaf `o` (`induced_reroot`, `rootedAt_reroot`). A leaf is left as it is. -/
def reroot (o : ℕ) : PhyloTree → PhyloTree
  | .leaf a => .leaf a
  | .fork a b => if o ∈ a.taxa then graftAt o a b else graftAt o b a

/-- Rotating a well-labelled tree at its root keeps its quartets: `(a, (b, c))` and `((a, b), c)`
are the same unrooted tree. The clade `b ∪ c` of the first is the complement of the clade `a`,
and the clade `a ∪ b` of the second is the complement of the clade `c`. -/
theorem induced_rotate {a b c : PhyloTree} (h : (fork a (fork b c)).WellLabelled) (q : Quartet) :
    q.induced (fork a (fork b c)) = q.induced (fork (fork a b) c) := by
  obtain ⟨-, hbc, habc⟩ := wellLabelled_fork h
  obtain ⟨-, -, hbc'⟩ := wellLabelled_fork hbc
  rw [taxa_fork] at habc
  have htaxa : (fork (fork a b) c).taxa = (fork a (fork b c)).taxa := by
    simp only [taxa_fork, Finset.union_assoc]
  have hL : (fork a (fork b c)).taxa = a.taxa ∪ (b.taxa ∪ c.taxa) := by
    rw [taxa_fork, taxa_fork]
  -- the two clades that differ are complements of clades of both trees
  have hBC : b.taxa ∪ c.taxa = (fork a (fork b c)).taxa \ a.taxa := by
    rw [hL, Finset.union_sdiff_left, Finset.sdiff_eq_self_of_disjoint habc.symm]
  have hAB : a.taxa ∪ b.taxa = (fork a (fork b c)).taxa \ c.taxa := by
    rw [hL, ← Finset.union_assoc, Finset.union_sdiff_right,
      Finset.sdiff_eq_self_of_disjoint]
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_of_subset_right Finset.subset_union_right habc, hbc'⟩
  unfold Quartet.induced
  rw [htaxa]
  by_cases hq : q.taxa ⊆ (fork a (fork b c)).taxa
  · simp only [hq, decide_true, Bool.true_and]
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨C, hC, hcut⟩
      rcases mem_clades_fork.mp hC with rfl | hC | hC
      · refine ⟨_, mem_clades_fork.mpr (Or.inl rfl), ?_⟩
        rw [taxa_fork] at hcut ⊢
        rwa [Finset.union_assoc]
      · exact ⟨C, mem_clades_fork.mpr (Or.inr (Or.inl (mem_clades_fork.mpr
          (Or.inr (Or.inl hC))))), hcut⟩
      · rcases mem_clades_fork.mp hC with rfl | hC | hC
        · refine ⟨a.taxa, mem_clades_fork.mpr (Or.inr (Or.inl (mem_clades_fork.mpr
            (Or.inr (Or.inl a.taxa_mem_clades))))), ?_⟩
          rw [hBC, Quartet.cutBy_sdiff hq] at hcut
          exact hcut
        · exact ⟨C, mem_clades_fork.mpr (Or.inr (Or.inl (mem_clades_fork.mpr
            (Or.inr (Or.inr hC))))), hcut⟩
        · exact ⟨C, mem_clades_fork.mpr (Or.inr (Or.inr hC)), hcut⟩
    · rintro ⟨C, hC, hcut⟩
      rcases mem_clades_fork.mp hC with rfl | hC | hC
      · refine ⟨_, mem_clades_fork.mpr (Or.inl rfl), ?_⟩
        rw [taxa_fork] at hcut ⊢
        rwa [← Finset.union_assoc]
      · rcases mem_clades_fork.mp hC with rfl | hC | hC
        · refine ⟨c.taxa, mem_clades_fork.mpr (Or.inr (Or.inr (mem_clades_fork.mpr
            (Or.inr (Or.inr c.taxa_mem_clades))))), ?_⟩
          rw [hAB, Quartet.cutBy_sdiff hq] at hcut
          exact hcut
        · exact ⟨C, mem_clades_fork.mpr (Or.inr (Or.inl hC)), hcut⟩
        · exact ⟨C, mem_clades_fork.mpr (Or.inr (Or.inr (mem_clades_fork.mpr
            (Or.inr (Or.inl hC))))), hcut⟩
      · exact ⟨C, mem_clades_fork.mpr (Or.inr (Or.inr (mem_clades_fork.mpr
          (Or.inr (Or.inr hC))))), hcut⟩
  · simp [hq]

/-- `graftAt o s up` has the leaves of `s` and of `up`. -/
theorem graftAt_labels_perm (o : ℕ) :
    ∀ s up : PhyloTree, (graftAt o s up).labels.Perm (s.labels ++ up.labels)
  | .leaf a, up => by simp [graftAt, labels]
  | .fork a b, up => by
    unfold graftAt
    split_ifs
    · refine (graftAt_labels_perm o a (.fork b up)).trans ?_
      simp only [labels, List.append_assoc]
      exact List.Perm.refl _
    · refine (graftAt_labels_perm o b (.fork a up)).trans ?_
      simp only [labels, ← List.append_assoc]
      exact List.perm_append_comm.append_right _

/-- `graftAt o s up` is the unrooted tree `(s, up)`: it induces the same quartets. -/
theorem induced_graftAt (o : ℕ) :
    ∀ s up : PhyloTree, (fork s up).WellLabelled →
      ∀ q : Quartet, q.induced (graftAt o s up) = q.induced (fork s up)
  | .leaf a, up, _, q => rfl
  | .fork a b, up, h, q => by
    unfold graftAt
    split_ifs
    · have h' : (fork a (fork b up)).WellLabelled := by
        change (a.labels ++ (b.labels ++ up.labels)).Nodup
        rw [← List.append_assoc]
        exact h
      rw [induced_graftAt o a (.fork b up) h' q, induced_rotate h' q]
    · have h' : (fork b (fork a up)).WellLabelled := by
        change (b.labels ++ (a.labels ++ up.labels)).Nodup
        refine (List.Perm.nodup_iff ?_).mpr h
        rw [← List.append_assoc]
        exact List.perm_append_comm.append_right _
      rw [induced_graftAt o b (.fork a up) h' q, induced_rotate h' q]
      exact (ClusterEq.fork (ClusterEq.fork_swap b a) (ClusterEq.refl up)).induced_eq q

/-- `graftAt o s up` is rooted at `o`, a taxon of `s`. -/
theorem rootedAt_graftAt (o : ℕ) : ∀ s up : PhyloTree, o ∈ s.taxa → (graftAt o s up).RootedAt o
  | .leaf a, up, h => by
    rw [taxa_leaf, Finset.mem_singleton] at h
    subst h
    exact ⟨false, rfl⟩
  | .fork a b, up, h => by
    unfold graftAt
    split_ifs with ho
    · exact rootedAt_graftAt o a _ ho
    · rw [taxa_fork, Finset.mem_union] at h
      exact rootedAt_graftAt o b _ (h.resolve_left ho)

/-- Rooting at the outgroup keeps the leaves. -/
theorem reroot_labels_perm (o : ℕ) (t : PhyloTree) : (t.reroot o).labels.Perm t.labels := by
  cases t with
  | leaf a => exact List.Perm.refl _
  | fork a b =>
    simp only [reroot]
    split_ifs
    · exact graftAt_labels_perm o a b
    · exact (graftAt_labels_perm o b a).trans List.perm_append_comm

/-- Rooting at the outgroup keeps the taxa. -/
theorem taxa_reroot (o : ℕ) (t : PhyloTree) : (t.reroot o).taxa = t.taxa :=
  List.toFinset_eq_of_perm _ _ (reroot_labels_perm o t)

/-- Rooting a well-labelled tree at the outgroup gives a well-labelled tree. -/
theorem wellLabelled_reroot (o : ℕ) {t : PhyloTree} (ht : t.WellLabelled) :
    (t.reroot o).WellLabelled :=
  (List.Perm.nodup_iff (reroot_labels_perm o t)).mpr ht

/-- Section 3.2: rooting a well-labelled tree at the outgroup keeps its unrooted form: the rooted
tree induces the same quartets. -/
theorem induced_reroot (o : ℕ) {t : PhyloTree} (ht : t.WellLabelled) (q : Quartet) :
    q.induced (t.reroot o) = q.induced t := by
  cases t with
  | leaf a => rfl
  | fork a b =>
    simp only [reroot]
    split_ifs
    · exact induced_graftAt o a b ht q
    · have h' : (fork b a).WellLabelled := by
        change (b.labels ++ a.labels).Nodup
        exact List.nodup_append_comm.mp ht
      rw [induced_graftAt o b a h' q]
      exact (ClusterEq.fork_swap b a).induced_eq q

/-- Section 3.2: "we have an outgroup and hence can root the tree returned by ASTRAL". Rooting at
`o` a tree with at least two taxa, one of which is `o`, gives a tree rooted at `o`. -/
theorem rootedAt_reroot {o : ℕ} {t : PhyloTree} (ho : o ∈ t.taxa) (h2 : 2 ≤ t.taxa.card) :
    (t.reroot o).RootedAt o := by
  cases t with
  | leaf a =>
    rw [taxa_leaf, Finset.card_singleton] at h2
    omega
  | fork a b =>
    simp only [reroot]
    split_ifs with hoa
    · exact rootedAt_graftAt o a b hoa
    · rw [taxa_fork, Finset.mem_union] at ho
      exact rootedAt_graftAt o b a (ho.resolve_left hoa)

/-! ### Trees on a set of taxa -/

/-- The caterpillar `(a₀, (a₁, (…, aₖ)))` on the labels `a₀, a₁, …, aₖ`. -/
def caterpillar : ℕ → List ℕ → PhyloTree
  | a, [] => .leaf a
  | a, b :: l => .fork (.leaf a) (caterpillar b l)

/-- The leaves of the caterpillar on `a :: l` are labelled `a :: l`, in order. -/
theorem labels_caterpillar : ∀ (a : ℕ) (l : List ℕ), (caterpillar a l).labels = a :: l
  | a, [] => rfl
  | a, b :: l => by simp [caterpillar, labels, labels_caterpillar b l]

/-- Every nonempty set of taxa is the set of taxa of some well-labelled tree. -/
theorem exists_wellLabelled {X : Finset ℕ} (hX : X.Nonempty) :
    ∃ t : PhyloTree, t.WellLabelled ∧ t.taxa = X := by
  obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil (Finset.toList_eq_nil.not.mpr hX.ne_empty)
  refine ⟨caterpillar a l, ?_, ?_⟩
  · change (caterpillar a l).labels.Nodup
    rw [labels_caterpillar, ← hal]
    exact X.nodup_toList
  · unfold taxa
    rw [labels_caterpillar, ← hal, Finset.toList_toFinset]

end PhyloTree

end Camus
