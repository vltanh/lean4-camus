module

public import Camus.Network.SingleEdge

/-!
# Moving a donor from above the root of `T`

A network built on `T` in the sense of Definition 1 whose root lies above the root of `T` may
have an added edge that starts above the root of `T` and ends above a vertex `w` of `T`. Write
such an edge as the pair `([], w)`: its donor end lies on the edge above the root `[]`, which only
exists in the network. Its cycle meets `T` in the vertices strictly above `w`
(`EdgeAbove.footprint t ([], w)`). This file moves the donor below the root: to the child `x` of
the root that is an ancestor of `w` if `x ≠ w`, and to the other child of the root if `w` is a
child of the root (`EdgeAbove.rootDonor`). The pair `EdgeAbove.lowerPair ([], w)` so obtained is
admissible, and its cycle meets `T` in a subset of the vertices of the old cycle; so moving the
donors keeps the cycles disjoint (`EdgeAbove.RootSeparated.image_lowerPair`). The tree displayed
through the moved edge has the same splits (`Camus/Network/RootAbove/Splits.lean`).

The file also passes from the tree `T⁺ = fork (leaf z) T` with an outgroup to `T`: the pairs
`(true :: u, true :: w)` of `T⁺` are the pairs `(u, w)` of `T`, with the same cycle; the donor
`[true]`, the root of `T` in `T⁺`, becomes the donor `[]` (`EdgeAbove.outgroup_rootSeparated`).

## Main results

* `EdgeAbove.RootSeparated`: the families of pairs of `T` in which a donor may lie above the root,
  with vertex-disjoint cycles.
* `EdgeAbove.RootSeparated.image_lowerPair`, `EdgeAbove.RootSeparated.card_image_lowerPair`:
  moving the donors below the root gives a cycle-separated family with as many pairs.
* `EdgeAbove.outgroup_rootSeparated`, `EdgeAbove.outgroup_card_image`: the pairs of a
  cycle-separated family of `T⁺` below the root of `T` give such a family of `T`.
* `Quartet.cutBy_eq_of_compl`: complementary sets cut the same quartets.
-/

@[expose] public section

namespace Camus

/-- `true :: p` is a strict ancestor of `true :: q` if and only if `p` is a strict ancestor of
`q`. -/
theorem prefix_ne_of_cons_true {p q : Address} :
    (true :: p <+: true :: q ∧ true :: p ≠ true :: q) ↔ (p <+: q ∧ p ≠ q) := by
  simp [List.cons_prefix_cons]

namespace PhyloTree

/-- The clade of a vertex lies in the clade of each of its ancestors. -/
theorem taxaAt_mono {t : PhyloTree} {x y : Address} (hxy : x <+: y) (hy : y ∈ t.nodes) :
    t.taxaAt y ⊆ t.taxaAt x := by
  obtain ⟨r, rfl⟩ := hxy
  obtain ⟨s, hs⟩ := (t.mem_nodes_iff _).mp hy
  rw [nodeAt_append] at hs
  cases hx : t.nodeAt x with
  | none => rw [hx] at hs; exact absurd hs (by simp)
  | some sx =>
    rw [hx, Option.bind_some] at hs
    have hy' : t.nodeAt (x ++ r) = some s := by rw [nodeAt_append, hx, Option.bind_some, hs]
    simp only [taxaAt, hy', hx]
    exact subtree_taxa_subset hs

/-- The clade of the root is the set of taxa. -/
theorem taxaAt_nil (t : PhyloTree) : t.taxaAt [] = t.taxa := by
  cases t <;> rfl

/-- The clade of a vertex is a set of taxa of `T`. -/
theorem taxaAt_subset {t : PhyloTree} {p : Address} (hp : p ∈ t.nodes) :
    t.taxaAt p ⊆ t.taxa := by
  rw [← taxaAt_nil]
  exact taxaAt_mono List.nil_prefix hp

/-- In `T⁺ = fork (leaf z) T`, the clade of the leaf `z` is `{z}`. -/
theorem outgroup_taxaAt_false (t : PhyloTree) (z : ℕ) :
    (PhyloTree.fork (.leaf z) t).taxaAt [false] = {z} := by
  simp [taxaAt, nodeAt, taxa, labels]

/-- In `T⁺ = fork (leaf z) T`, the clade of `true :: p` is the clade of `p` in `T`. -/
theorem outgroup_taxaAt_true (t : PhyloTree) (z : ℕ) (p : Address) :
    (PhyloTree.fork (.leaf z) t).taxaAt (true :: p) = t.taxaAt p := rfl

/-- A tree with a vertex `[b]` is a fork, and `[!b]` is a vertex too. -/
theorem sibling_mem_nodes {t : PhyloTree} {b : Bool} (h : [b] ∈ t.nodes) : [!b] ∈ t.nodes := by
  cases t with
  | leaf a => simp [nodes] at h
  | fork l r => cases b <;> simp [nodes, root_mem_nodes]

/-- In a well-labelled fork, the clades of the two children of the root partition the taxa. -/
theorem children_taxaAt {t : PhyloTree} (ht : t.WellLabelled) {b : Bool} (h : [b] ∈ t.nodes) :
    t.taxaAt [b] ∪ t.taxaAt [!b] = t.taxa ∧ Disjoint (t.taxaAt [b]) (t.taxaAt [!b]) := by
  cases t with
  | leaf a => simp [nodes] at h
  | fork l r =>
    have hd : Disjoint l.taxa r.taxa := by
      have hnd : (l.labels ++ r.labels).Nodup := ht
      rw [Finset.disjoint_left]
      intro a hal har
      exact List.disjoint_of_nodup_append hnd (List.mem_toFinset.mp hal)
        (List.mem_toFinset.mp har)
    cases b
    · refine ⟨?_, ?_⟩
      · simp [taxaAt, nodeAt, taxa, labels]
      · simpa [taxaAt, nodeAt] using hd
    · refine ⟨?_, ?_⟩
      · simp [taxaAt, nodeAt, taxa, labels, Finset.union_comm]
      · simpa [taxaAt, nodeAt] using hd.symm

end PhyloTree

namespace Quartet

/-- A set containing the four taxa of `q` does not cut `q`. -/
theorem cutBy_eq_false_of_superset (q : Quartet) {C : Finset ℕ} (h : q.taxa ⊆ C) :
    q.cutBy C = false := by
  have := q.cutBy_not_whole C h
  simpa using this

/-- A set disjoint from the four taxa of `q` does not cut `q`. -/
theorem cutBy_eq_false_of_disjoint (q : Quartet) {C : Finset ℕ} (h : Disjoint q.taxa C) :
    q.cutBy C = false := by
  simp only [cutBy, decide_eq_false_iff_not, not_or, not_and]
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := q.sides_nonempty
  refine ⟨fun hs _ => ?_, fun hs _ => ?_⟩
  · exact Finset.disjoint_left.mp h (q.sides_subset_taxa.1 ha) (hs ha)
  · exact Finset.disjoint_left.mp h (q.sides_subset_taxa.2 hb) (hs hb)

/-- Complementary sets cut the same quartets: if `A` and `B` are disjoint and together contain the
four taxa of `q`, then `A` cuts `q` if and only if `B` does. -/
theorem cutBy_eq_of_compl (q : Quartet) {A B : Finset ℕ} (hAB : q.taxa ⊆ A ∪ B)
    (hd : Disjoint A B) : q.cutBy A = q.cutBy B := by
  have h1 : q.sides.1 ⊆ A ∪ B := q.sides_subset_taxa.1.trans hAB
  have h2 : q.sides.2 ⊆ A ∪ B := q.sides_subset_taxa.2.trans hAB
  -- a part of `A ∪ B` lies in `A` if and only if it avoids `B`
  have key : ∀ s : Finset ℕ, s ⊆ A ∪ B → (s ⊆ A ↔ Disjoint s B) := by
    intro s hs
    constructor
    · intro hsA
      exact Finset.disjoint_of_subset_left hsA hd
    · intro hsB x hx
      rcases Finset.mem_union.mp (hs hx) with h | h
      · exact h
      · exact absurd h (Finset.disjoint_left.mp hsB hx)
  have key' : ∀ s : Finset ℕ, s ⊆ A ∪ B → (s ⊆ B ↔ Disjoint s A) := by
    intro s hs
    rw [Finset.union_comm] at hs
    constructor
    · intro hsB
      exact Finset.disjoint_of_subset_left hsB hd.symm
    · intro hsA x hx
      rcases Finset.mem_union.mp (hs hx) with h | h
      · exact h
      · exact absurd h (Finset.disjoint_left.mp hsA hx)
  simp only [cutBy, Bool.decide_or, Bool.decide_and]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rw [key _ h1, key _ h2, key' _ h1, key' _ h2]
  tauto

end Quartet

namespace EdgeAbove

/-- The donor that replaces a donor above the root of `T`, for a recipient `w` other than the root:
the child of the root that is an ancestor of `w` if it is not `w` itself, and the other child of
the root if `w` is a child of the root. -/
def rootDonor : Address → Address
  | [] => []
  | [b] => [!b]
  | b :: _ :: _ => [b]

/-- The pair that replaces the pair `e`: for a donor `[]` above the root of `T`, the pair
`(rootDonor w, w)`; any other pair is kept. -/
def lowerPair (e : Address × Address) : Address × Address :=
  if e.1 = [] then (rootDonor e.2, e.2) else e

/-- The families of pairs of `T` of a network built on `T` in the sense of Definition 1, whose root
may lie above the root of `T`: a donor `[]` stands for a donor above the root of `T`. The pairs
`(u, w)` are pairs of vertices of `T` with `w` neither an ancestor of `u` nor `u` itself (so
`w ≠ []`), and their cycles meet `T` in pairwise disjoint sets of vertices
(`EdgeAbove.footprint`; for a pair `([], w)`, the vertices strictly above `w`). -/
def RootSeparated (t : PhyloTree) (F : Finset (Address × Address)) : Prop :=
  (∀ f ∈ F, f.1 ∈ t.nodes ∧ f.2 ∈ t.nodes ∧ ¬f.2 <+: f.1) ∧
    (F : Set (Address × Address)).Pairwise (fun e f => Disjoint (footprint t e) (footprint t f))

/-- The moved donor is a non-root vertex of `T`, and `w` is neither an ancestor of it nor equal
to it. -/
theorem rootDonor_spec {t : PhyloTree} {w : Address} (hw : w ∈ t.nodes) (hw0 : w ≠ []) :
    rootDonor w ∈ t.nodes ∧ rootDonor w ≠ [] ∧ ¬w <+: rootDonor w := by
  match w, hw, hw0 with
  | [b], hw, _ =>
    refine ⟨PhyloTree.sibling_mem_nodes hw, List.cons_ne_nil _ _, ?_⟩
    simp [rootDonor, List.cons_prefix_cons]
  | b :: c :: w', hw, _ =>
    refine ⟨t.nodes_prefix_closed hw (by simp [rootDonor]), List.cons_ne_nil _ _, ?_⟩
    intro h
    have := h.length_le
    simp [rootDonor] at this

/-- The moved pair is admissible. -/
theorem lowerPair_mem_candidates {t : PhyloTree} {f : Address × Address}
    (hf : f.1 ∈ t.nodes ∧ f.2 ∈ t.nodes ∧ ¬f.2 <+: f.1) : lowerPair f ∈ candidates t := by
  obtain ⟨hu, hw, hwu⟩ := hf
  have hw0 : f.2 ≠ [] := by
    intro h
    exact hwu (h ▸ List.nil_prefix)
  unfold lowerPair
  split_ifs with hu0
  · obtain ⟨hd, hd0, hwd⟩ := rootDonor_spec hw hw0
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hd, hw⟩, hd, hw, hd0, hw0, hwd⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hw⟩, hu, hw, hu0, hw0, hwu⟩

/-- The moved donor is a child of the root. -/
theorem rootDonor_length {w : Address} (hw0 : w ≠ []) : (rootDonor w).length = 1 := by
  match w, hw0 with
  | [b], _ => rfl
  | b :: c :: w', _ => rfl

/-- A strict ancestor of a child of the root is the root. -/
theorem eq_nil_of_strict_prefix {x d : Address} (h : x <+: d) (hne : x ≠ d)
    (hd : d.length = 1) : x = [] := by
  have hlt : x.length < d.length := by
    by_contra hle
    exact hne (h.eq_of_length_le (by omega))
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- The cycle of the moved pair meets `T` in a subset of the vertices of the old cycle. -/
theorem footprint_lowerPair_subset {t : PhyloTree} {f : Address × Address}
    (hw : f.2 ∈ t.nodes) (hwu : ¬f.2 <+: f.1) : footprint t (lowerPair f) ⊆ footprint t f := by
  obtain ⟨u, w⟩ := f
  have hw0 : w ≠ [] := fun h => hwu (h ▸ List.nil_prefix)
  by_cases hu0 : u = []
  · subst hu0
    have hl : lowerPair ([], w) = (rootDonor w, w) := by simp [lowerPair]
    rw [hl]
    intro x hx
    obtain ⟨hxt, _, hx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxt, List.nil_prefix, Or.inr ?_⟩
    rcases hx with ⟨hxd, hxd'⟩ | hxw
    -- a strict ancestor of the moved donor is the root, strictly above `w`
    · rw [eq_nil_of_strict_prefix hxd hxd' (rootDonor_length hw0)]
      exact ⟨List.nil_prefix, Ne.symm hw0⟩
    · exact hxw
  · have hl : lowerPair (u, w) = (u, w) := by simp [lowerPair, hu0]
    rw [hl]

/-- For a family of pairs of a network built on `T` in the sense of Definition 1, moving the
donors from above the root to below it is injective. A moved pair `(rootDonor w, w)` cannot equal
another pair of the family: that pair would have target `lca (rootDonor w) w`, which lies strictly
above `w`, on the cycle of `([], w)`. -/
theorem RootSeparated.lowerPair_injOn {t : PhyloTree} {F : Finset (Address × Address)}
    (hF : RootSeparated t F) : Set.InjOn lowerPair F := by
  intro e he f hf hef
  by_contra hne
  have hdis := hF.2 he hf hne
  obtain ⟨heu, hew, hewu⟩ := hF.1 e he
  obtain ⟨hfu, hfw, hfwu⟩ := hF.1 f hf
  have hnil : ∀ g : Address × Address, g.2 ∈ t.nodes → ¬g.2 <+: g.1 → g.2 ≠ [] := by
    intro g _ h h0
    exact h (h0 ▸ List.nil_prefix)
  -- the target of `lowerPair g` lies on the cycle of `([], w)`
  have hcross : ∀ g h : Address × Address, g ∈ F → h ∈ F → g.1 = [] → h.1 ≠ [] →
      lowerPair g = lowerPair h → False := by
    intro g h hg hh hg0 hh0 hgh
    have hdis := hF.2 hg hh (fun heq => hh0 (heq ▸ hg0))
    obtain ⟨_, hgw, hgwu⟩ := hF.1 g hg
    obtain ⟨hhu, hhw, hhwu⟩ := hF.1 h hh
    have hh' : lowerPair h = h := by simp [lowerPair, hh0]
    have hg' : lowerPair g = (rootDonor g.2, g.2) := by simp [lowerPair, hg0]
    rw [hh', hg'] at hgh
    have hadm : Admissible t h := ⟨hhu, hhw, hh0, hnil h hhw hhwu, hhwu⟩
    have htarget := target_mem_footprint t h hadm
    rw [← hgh] at htarget
    -- the target `lca (rootDonor w) w` is strictly above `w`
    have hw0 := hnil g hgw hgwu
    obtain ⟨_, _, hwd⟩ := rootDonor_spec hgw hw0
    have hlca : lca (rootDonor g.2) g.2 <+: g.2 ∧ lca (rootDonor g.2) g.2 ≠ g.2 := by
      refine ⟨lca_prefix_right _ _, fun heq => hwd ?_⟩
      have h := lca_prefix_left (rootDonor g.2) g.2
      rwa [heq] at h
    have hmem : lca (rootDonor g.2) g.2 ∈ footprint t g := by
      refine Finset.mem_filter.mpr ⟨t.nodes_prefix_closed hgw hlca.1, ?_, Or.inr hlca⟩
      rw [target, hg0]
      exact List.nil_prefix
    rw [← hgh] at hdis
    exact Finset.disjoint_left.mp hdis hmem htarget
  by_cases he0 : e.1 = [] <;> by_cases hf0 : f.1 = []
  · -- two donors above the root: equal recipients
    have h2 : e.2 = f.2 := by
      have := congrArg Prod.snd hef
      simpa [lowerPair, he0, hf0] using this
    exact hne (Prod.ext (he0.trans hf0.symm) h2)
  · exact hcross e f he hf he0 hf0 hef
  · exact hcross f e hf he hf0 he0 hef.symm
  · exact hne (by simpa [lowerPair, he0, hf0] using hef)

/-- Moving the donors below the root gives a cycle-separated family of pairs of `T`
(`EdgeAbove.CycleSeparated`): the moved pairs are admissible, and their cycles meet `T` in
subsets of the old, pairwise disjoint, cycles. -/
theorem RootSeparated.image_lowerPair {t : PhyloTree} {F : Finset (Address × Address)}
    (hF : RootSeparated t F) : CycleSeparated t (F.image lowerPair) := by
  refine ⟨?_, ?_⟩
  · intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact lowerPair_mem_candidates (hF.1 f hf)
  · intro e he e' he' hee'
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp he'
    have hff' : f ≠ f' := fun h => hee' (h ▸ rfl)
    exact Finset.disjoint_of_subset_left
      (footprint_lowerPair_subset (hF.1 f hf).2.1 (hF.1 f hf).2.2)
      (Finset.disjoint_of_subset_right
        (footprint_lowerPair_subset (hF.1 f' hf').2.1 (hF.1 f' hf').2.2) (hF.2 hf hf' hff'))

/-- Moving the donors below the root keeps the number of pairs. -/
theorem RootSeparated.card_image_lowerPair {t : PhyloTree} {F : Finset (Address × Address)}
    (hF : RootSeparated t F) : (F.image lowerPair).card = F.card :=
  Finset.card_image_of_injOn hF.lowerPair_injOn

/-- The cycle of the pair `(true :: u, true :: w)` of `T⁺ = fork (leaf z) T` meets `T⁺` in the
vertices `true :: x` for the vertices `x` of the cycle of `(u, w)` in `T`. -/
theorem mem_footprint_outgroup {t : PhyloTree} {z : ℕ} {u w x : Address}
    (hx : x ∈ footprint t (u, w)) :
    true :: x ∈ footprint (PhyloTree.fork (.leaf z) t) (true :: u, true :: w) := by
  obtain ⟨hxt, htx, hx⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
  · simp [PhyloTree.nodes, hxt]
  · simp only [target, lca, ite_true, List.cons_prefix_cons, true_and]
    exact htx
  · simpa [List.cons_prefix_cons] using hx

/-- The pairs `(u, w)` of `T` for the pairs `(true :: u, true :: w)` of a cycle-separated family
`E` of `T⁺ = fork (leaf z) T` form a family of pairs of a network built on `T` in the sense of
Definition 1: a donor `[true]` becomes the donor `[]`, above the root of `T`. -/
theorem outgroup_rootSeparated {t : PhyloTree} {z : ℕ} {E : Finset (Address × Address)}
    (hE : CycleSeparated (PhyloTree.fork (.leaf z) t) E)
    (hform : ∀ e ∈ E, ∃ u ∈ t.nodes, ∃ w ∈ t.nodes, e = (true :: u, true :: w)) :
    RootSeparated t (E.image (fun e => (e.1.tail, e.2.tail))) := by
  refine ⟨?_, ?_⟩
  · intro f hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨u, hu, w, hw, rfl⟩ := hform e he
    have hadm := (Finset.mem_filter.mp (hE.1 he)).2
    refine ⟨hu, hw, fun h => hadm.2.2.2.2 ?_⟩
    exact List.cons_prefix_cons.mpr ⟨rfl, h⟩
  · intro f hf f' hf' hff'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hf'
    have hee' : e ≠ e' := fun h => hff' (h ▸ rfl)
    have hdis := hE.2 he he' hee'
    obtain ⟨u, _, w, _, rfl⟩ := hform e he
    obtain ⟨u', _, w', _, rfl⟩ := hform e' he'
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact Finset.disjoint_left.mp hdis (mem_footprint_outgroup hx) (mem_footprint_outgroup hx')

/-- Passing from the pairs `(true :: u, true :: w)` of `T⁺` to the pairs `(u, w)` of `T` keeps the
number of pairs. -/
theorem outgroup_card_image {t : PhyloTree} {E : Finset (Address × Address)}
    (hform : ∀ e ∈ E, ∃ u ∈ t.nodes, ∃ w ∈ t.nodes, e = (true :: u, true :: w)) :
    (E.image (fun e => (e.1.tail, e.2.tail))).card = E.card := by
  apply Finset.card_image_of_injOn
  intro e he e' he' h
  obtain ⟨u, _, w, _, rfl⟩ := hform e he
  obtain ⟨u', _, w', _, rfl⟩ := hform e' he'
  simp only [List.tail_cons, Prod.mk.injEq] at h
  rw [h.1, h.2]

end EdgeAbove

end Camus
