module

public import Camus.Pipelines.NMSC.GraphTrees

/-!
# Every displayed tree of a network of the NMSC is a tree of its graph

(module docstring to be written)
-/

@[expose] public section

namespace Camus

namespace NMSC

open Finset Realization

variable {L : Finset ℕ}

/-! ### The clades of the vertices with a modification -/

/-- The clades of the tree of the switching keeping the added edges of `F`, with the clade of each
vertex `y` of `s` transformed by `f y`, and the clades of the donor vertices of `F`. -/
def nodeClades (s : PhyloTree) (F : Finset Pair) (f : Address → Finset ℕ → Finset ℕ) :
    Finset (Finset ℕ) :=
  s.nodes.image (fun y => f y (keptClade s F y)) ∪
    F.image fun e => keptClade s F e.1 ∪ s.taxaAt e.2

theorem keptClades_eq_nodeClades (s : PhyloTree) (F : Finset Pair) :
    keptClades s F = nodeClades s F fun _ C => C := rfl

/-! ### Lifting to a child of the root -/

theorem movesOut_lift {b c : Bool} (hbc : b ≠ c) (F F' : Finset Pair) (y : Address) :
    movesOut (liftPairs b F ∪ liftPairs c F') (b :: y) = liftPairs b (movesOut F y) := by
  ext e
  simp only [movesOut, Finset.mem_filter, Finset.mem_union, mem_liftPairs]
  constructor
  · rintro ⟨⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩, h1, h2⟩
    · exact ⟨f, ⟨hf, by simpa using h1, by simpa using h2⟩, rfl⟩
    · simp [hbc] at h1
  · rintro ⟨f, ⟨hf, h1, h2⟩, rfl⟩
    exact ⟨Or.inl ⟨f, hf, rfl⟩, by simpa using h1, by simpa using h2⟩

theorem movesIn_lift {b c : Bool} (hbc : b ≠ c) (F F' : Finset Pair) (y : Address) :
    movesIn (liftPairs b F ∪ liftPairs c F') (b :: y) = liftPairs b (movesIn F y) := by
  ext e
  simp only [movesIn, Finset.mem_filter, Finset.mem_union, mem_liftPairs]
  constructor
  · rintro ⟨⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩, h1, h2⟩
    · exact ⟨f, ⟨hf, by simpa using h1, by simpa using h2⟩, rfl⟩
    · simp [hbc] at h1
  · rintro ⟨f, ⟨hf, h1, h2⟩, rfl⟩
    exact ⟨Or.inl ⟨f, hf, rfl⟩, by simpa using h1, by simpa using h2⟩

theorem biUnion_liftPairs {t s : PhyloTree} {b : Bool} (h : t.nodeAt [b] = some s)
    (F : Finset Pair) :
    (liftPairs b F).biUnion (fun e => t.taxaAt e.2) = F.biUnion fun e => s.taxaAt e.2 := by
  rw [liftPairs, Finset.image_biUnion]
  exact Finset.biUnion_congr rfl fun e _ => taxaAt_cons h e.2

/-- The clade of a vertex of a child of the root, for pairs lifted to the two children. -/
theorem keptClade_cons {t s : PhyloTree} {b c : Bool} (hbc : b ≠ c) (h : t.nodeAt [b] = some s)
    (F F' : Finset Pair) (y : Address) :
    keptClade t (liftPairs b F ∪ liftPairs c F') (b :: y) = keptClade s F y := by
  simp only [keptClade, movesOut_lift hbc, movesIn_lift hbc, biUnion_liftPairs h,
    taxaAt_cons h]

/-- The clade of the root, for pairs whose ends are not the root. -/
theorem keptClade_nil (t : PhyloTree) {F : Finset Pair} (hF : ∀ e ∈ F, e.1 ≠ [] ∧ e.2 ≠ []) :
    keptClade t F [] = t.taxa := by
  have h1 : movesOut F [] = ∅ := Finset.filter_false_of_mem fun e he h =>
    h.2 ⟨List.nil_prefix, (hF e he).1.symm⟩
  have h2 : movesIn F [] = ∅ := Finset.filter_false_of_mem fun e he h =>
    h.2 ⟨List.nil_prefix, (hF e he).2.symm⟩
  simp [keptClade, h1, h2, PhyloTree.taxaAt_nil]

theorem liftPairs_ne_nil {b : Bool} {F : Finset Pair} :
    ∀ e ∈ liftPairs b F, e.1 ≠ [] ∧ e.2 ≠ [] := by
  intro e he
  obtain ⟨f, -, rfl⟩ := mem_liftPairs.1 he
  exact ⟨List.cons_ne_nil _ _, List.cons_ne_nil _ _⟩

/-- **The fork lemma.** For pairs lifted to the two children of the root, the clades of the tree of
the switching are the set of all taxa and the clades for the two children. -/
theorem nodeClades_fork (l r : PhyloTree) (F₁ F₂ : Finset Pair)
    (f : Address → Finset ℕ → Finset ℕ) :
    nodeClades (.fork l r) (liftPairs false F₁ ∪ liftPairs true F₂) f =
      insert (f [] (l.taxa ∪ r.taxa))
        (nodeClades l F₁ (fun y => f (false :: y)) ∪ nodeClades r F₂ (fun y => f (true :: y))) := by
  have hl := nodeAt_fork_false l r
  have hr := nodeAt_fork_true l r
  have hne : ∀ e ∈ liftPairs false F₁ ∪ liftPairs true F₂, e.1 ≠ [] ∧ e.2 ≠ [] := by
    intro e he
    rcases Finset.mem_union.1 he with he | he <;> exact liftPairs_ne_nil e he
  have kl := keptClade_cons (b := false) (c := true) (by decide) hl F₁ F₂
  have kr : ∀ y, keptClade (.fork l r) (liftPairs false F₁ ∪ liftPairs true F₂) (true :: y) =
      keptClade r F₂ y := fun y => by
    rw [Finset.union_comm]
    exact keptClade_cons (b := true) (c := false) (by decide) hr F₂ F₁ y
  ext C
  simp only [nodeClades, Finset.mem_union, Finset.mem_image, Finset.mem_insert]
  constructor
  · rintro (⟨y, hy, rfl⟩ | ⟨e, he, rfl⟩)
    · rcases (mem_nodes_fork.1 hy) with rfl | ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
      · left
        rw [keptClade_nil _ hne, taxa_fork]
      · exact Or.inr (Or.inl (Or.inl ⟨z, hz, by rw [kl]⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨z, hz, by rw [kr]⟩))
    · rcases he with he | he <;> obtain ⟨g, hg, rfl⟩ := mem_liftPairs.1 he
      · exact Or.inr (Or.inl (Or.inr ⟨g, hg, by rw [kl, taxaAt_cons hl]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨g, hg, by rw [kr, taxaAt_cons hr]⟩))
  · rintro (rfl | (⟨z, hz, rfl⟩ | ⟨g, hg, rfl⟩) | (⟨z, hz, rfl⟩ | ⟨g, hg, rfl⟩))
    · refine Or.inl ⟨[], PhyloTree.root_mem_nodes _, ?_⟩
      rw [keptClade_nil _ hne, taxa_fork]
    · exact Or.inl ⟨false :: z, (mem_nodes_cons hl z).2 hz, by rw [kl]⟩
    · exact Or.inr ⟨(false :: g.1, false :: g.2),
        Or.inl (mem_liftPairs.2 ⟨g, hg, rfl⟩), by rw [kl, taxaAt_cons hl]⟩
    · exact Or.inl ⟨true :: z, (mem_nodes_cons hr z).2 hz, by rw [kr]⟩
    · exact Or.inr ⟨(true :: g.1, true :: g.2),
        Or.inr (mem_liftPairs.2 ⟨g, hg, rfl⟩), by rw [kr, taxaAt_cons hr]⟩


/-! ### One more kept added edge -/

theorem keptClade_insert_out {t : PhyloTree} {F : Finset Pair} {e : Pair} {p : Address}
    (h1 : p <+: e.2 ∧ p ≠ e.2) (h2 : ¬(p <+: e.1 ∧ p ≠ e.1)) (hin : movesIn F p = ∅) :
    keptClade t (insert e F) p = keptClade t F p \ t.taxaAt e.2 := by
  have ho : movesOut (insert e F) p = insert e (movesOut F p) := by
    unfold movesOut
    rw [Finset.filter_insert, ite_eq_left ⟨h1, h2⟩]
  have hi : movesIn (insert e F) p = movesIn F p := by
    unfold movesIn
    rw [Finset.filter_insert, ite_eq_right (fun h => h.2 h1)]
  rw [keptClade, keptClade, ho, hi, hin, Finset.biUnion_insert]
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.biUnion_empty, Finset.notMem_empty]
  tauto

theorem keptClade_insert_in {t : PhyloTree} {F : Finset Pair} {e : Pair} {p : Address}
    (h1 : p <+: e.1 ∧ p ≠ e.1) (h2 : ¬(p <+: e.2 ∧ p ≠ e.2)) :
    keptClade t (insert e F) p = keptClade t F p ∪ t.taxaAt e.2 := by
  have ho : movesOut (insert e F) p = movesOut F p := by
    unfold movesOut
    rw [Finset.filter_insert, ite_eq_right (fun h => h.2 h1)]
  have hi : movesIn (insert e F) p = insert e (movesIn F p) := by
    unfold movesIn
    rw [Finset.filter_insert, ite_eq_left ⟨h1, h2⟩]
  rw [keptClade, keptClade, ho, hi, Finset.biUnion_insert]
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

theorem keptClade_insert_none {t : PhyloTree} {F : Finset Pair} {e : Pair} {p : Address}
    (h1 : ¬((p <+: e.2 ∧ p ≠ e.2) ∧ ¬(p <+: e.1 ∧ p ≠ e.1)))
    (h2 : ¬((p <+: e.1 ∧ p ≠ e.1) ∧ ¬(p <+: e.2 ∧ p ≠ e.2))) :
    keptClade t (insert e F) p = keptClade t F p := by
  have ho : movesOut (insert e F) p = movesOut F p := by
    unfold movesOut
    rw [Finset.filter_insert, ite_eq_right h1]
  have hi : movesIn (insert e F) p = movesIn F p := by
    unfold movesIn
    rw [Finset.filter_insert, ite_eq_right h2]
  rw [keptClade, keptClade, ho, hi]

/-- Remove `Y` from the clades of the strict ancestors of `w`. -/
def dropOn (w : Address) (Y : Finset ℕ) : Address → Finset ℕ → Finset ℕ :=
  fun y C => if y <+: w ∧ y ≠ w then C \ Y else C

/-- Add `Y` to the clades of the strict ancestors of `u`. -/
def addOn (u : Address) (Y : Finset ℕ) : Address → Finset ℕ → Finset ℕ :=
  fun y C => if y <+: u ∧ y ≠ u then C ∪ Y else C

/-- **The cross lemma.** With the added edge `(true :: u, false :: w)` from the right child of the
root to the left one kept, the clades of the tree of the switching are the set of all taxa, the
clades for the left child with the subtree at `w` removed from the strict ancestors of `w`, those
for the right child with it added to the strict ancestors of `u`, and the clade of the donor
vertex. The pairs kept inside the children do not cross the strict ancestors of `w` and have no
donor end on the paths to `w` and to `u`. -/
theorem keptClades_cross (l r : PhyloTree) (F₁ F₂ : Finset Pair) (u w : Address)
    (h1 : ∀ e ∈ F₁, ∀ y, (y <+: w ∧ y ≠ w) →
      ((y <+: e.1 ∧ y ≠ e.1) ↔ (y <+: e.2 ∧ y ≠ e.2)))
    (h2 : ∀ e ∈ F₁, ¬(e.1 <+: w ∧ e.1 ≠ w)) (h3 : ∀ e ∈ F₂, ¬(e.1 <+: u ∧ e.1 ≠ u)) :
    keptClades (.fork l r) (insert (true :: u, false :: w)
        (liftPairs false F₁ ∪ liftPairs true F₂)) =
      insert (l.taxa ∪ r.taxa) (nodeClades l F₁ (dropOn w (l.taxaAt w)) ∪
        nodeClades r F₂ (addOn u (l.taxaAt w)) ∪ {keptClade r F₂ u ∪ l.taxaAt w}) := by
  have hl := nodeAt_fork_false l r
  have hr := nodeAt_fork_true l r
  set G := liftPairs false F₁ ∪ liftPairs true F₂ with hG
  have hne : ∀ e ∈ insert (true :: u, false :: w) G, e.1 ≠ [] ∧ e.2 ≠ [] := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact ⟨List.cons_ne_nil _ _, List.cons_ne_nil _ _⟩
    · rcases Finset.mem_union.1 he with he | he <;> exact liftPairs_ne_nil e he
  have kl : ∀ y, keptClade (.fork l r) G (false :: y) = keptClade l F₁ y :=
    keptClade_cons (b := false) (c := true) (by decide) hl F₁ F₂
  have kr : ∀ y, keptClade (.fork l r) G (true :: y) = keptClade r F₂ y := fun y => by
    rw [hG, Finset.union_comm]
    exact keptClade_cons (b := true) (c := false) (by decide) hr F₂ F₁ y
  have hW : (PhyloTree.fork l r).taxaAt (false :: w) = l.taxaAt w := taxaAt_cons hl w
  -- the clades of the vertices of the left child
  have cl : ∀ y, keptClade (.fork l r) (insert (true :: u, false :: w) G) (false :: y) =
      dropOn w (l.taxaAt w) y (keptClade l F₁ y) := by
    intro y
    unfold dropOn
    by_cases hy : y <+: w ∧ y ≠ w
    · have hin : movesIn G (false :: y) = ∅ := by
        rw [hG, movesIn_lift (by decide)]
        refine Finset.eq_empty_of_forall_notMem fun e he => ?_
        obtain ⟨f, hf, rfl⟩ := mem_liftPairs.1 he
        obtain ⟨hf, hf1, hf2⟩ := Finset.mem_filter.1 hf
        exact hf2 ((h1 f hf y hy).1 hf1)
      have hno : keptClade l F₁ y = l.taxaAt y := by
        have h1' : movesOut F₁ y = ∅ := Finset.filter_false_of_mem fun e he h =>
          h.2 ((h1 e he y hy).2 h.1)
        have h2' : movesIn F₁ y = ∅ := Finset.filter_false_of_mem fun e he h =>
          h.2 ((h1 e he y hy).1 h.1)
        simp [keptClade, h1', h2']
      rw [ite_eq_left hy, keptClade_insert_out (by simpa using hy) (by simp) hin, hW, kl]
    · rw [ite_eq_right hy, keptClade_insert_none (by simpa using hy) (by simp), kl]
  -- the clades of the vertices of the right child
  have cr : ∀ y, keptClade (.fork l r) (insert (true :: u, false :: w) G) (true :: y) =
      addOn u (l.taxaAt w) y (keptClade r F₂ y) := by
    intro y
    unfold addOn
    by_cases hy : y <+: u ∧ y ≠ u
    · rw [ite_eq_left hy, keptClade_insert_in (by simpa using hy) (by simp), hW, kr]
    · rw [ite_eq_right hy, keptClade_insert_none (by simp) (by simpa using hy), kr]
  have cl0 : ∀ y, ¬(y <+: w ∧ y ≠ w) →
      keptClade (.fork l r) (insert (true :: u, false :: w) G) (false :: y) =
        keptClade l F₁ y := fun y hy => by rw [cl, dropOn, ite_eq_right hy]
  have cr0 : ∀ y, ¬(y <+: u ∧ y ≠ u) →
      keptClade (.fork l r) (insert (true :: u, false :: w) G) (true :: y) =
        keptClade r F₂ y := fun y hy => by rw [cr, addOn, ite_eq_right hy]
  ext C
  simp only [keptClades, nodeClades, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (⟨y, hy, rfl⟩ | ⟨e, he, rfl⟩)
    · rcases (mem_nodes_fork.1 hy) with rfl | ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
      · left
        rw [keptClade_nil _ hne, taxa_fork]
      · exact Or.inr (Or.inl (Or.inl (Or.inl ⟨z, hz, (cl z).symm⟩)))
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨z, hz, (cr z).symm⟩)))
    · rcases he with rfl | he
      · refine Or.inr (Or.inr ?_)
        rw [cr0 u (by simp), hW]
      · rcases Finset.mem_union.1 he with he | he <;> obtain ⟨g, hg, rfl⟩ := mem_liftPairs.1 he
        · exact Or.inr (Or.inl (Or.inl (Or.inr ⟨g, hg, by
            rw [cl0 g.1 (h2 g hg), taxaAt_cons hl]⟩)))
        · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨g, hg, by
            rw [cr0 g.1 (h3 g hg), taxaAt_cons hr]⟩)))
  · rintro (rfl | ((⟨z, hz, rfl⟩ | ⟨g, hg, rfl⟩) | (⟨z, hz, rfl⟩ | ⟨g, hg, rfl⟩)) | rfl)
    · refine Or.inl ⟨[], PhyloTree.root_mem_nodes _, ?_⟩
      rw [keptClade_nil _ hne, taxa_fork]
    · exact Or.inl ⟨false :: z, (mem_nodes_cons hl z).2 hz, cl z⟩
    · exact Or.inr ⟨(false :: g.1, false :: g.2),
        Or.inr (Finset.mem_union_left _ (mem_liftPairs.2 ⟨g, hg, rfl⟩)), by
          rw [cl0 g.1 (h2 g hg), taxaAt_cons hl]⟩
    · exact Or.inl ⟨true :: z, (mem_nodes_cons hr z).2 hz, cr z⟩
    · exact Or.inr ⟨(true :: g.1, true :: g.2),
        Or.inr (Finset.mem_union_right _ (mem_liftPairs.2 ⟨g, hg, rfl⟩)), by
          rw [cr0 g.1 (h3 g hg), taxaAt_cons hr]⟩
    · exact Or.inr ⟨(true :: u, false :: w), Or.inl rfl, by
        rw [cr0 u (by simp), hW]⟩


/-! ### The pairs along the sides of a cycle -/

/-- The pairs `P` of the tree hanging from the hybrid edge of a side, moved to its address in the
tree of the side with this tree attached. -/
def liftHang : Brooqs.Side L → Finset Pair → Finset Pair
  | .hyb _, P => P
  | .node _ _ _ S, P => liftPairs true (liftHang S P)

theorem liftPairs_union (b : Bool) (A B : Finset Pair) :
    liftPairs b (A ∪ B) = liftPairs b A ∪ liftPairs b B := Finset.image_union _ _

theorem attachPairs_eq : ∀ (S : Brooqs.Side L) (P : Finset Pair),
    attachPairs S P = attachPairs S ∅ ∪ liftHang S P
  | .hyb _, P => by simp [attachPairs, liftHang]
  | .node _ _ M S, P => by
      simp only [attachPairs, liftHang]
      rw [attachPairs_eq S P, liftPairs_union, Finset.union_assoc]

theorem liftHang_subset : ∀ (S : Brooqs.Side L) {P Q : Finset Pair}, P ⊆ Q →
    liftHang S P ⊆ liftHang S Q
  | .hyb _, _, _, h => h
  | .node _ _ _ S, _, _, h => Finset.image_subset_image (liftHang_subset S h)

/-- No pair of the tree of a side with a tree attached crosses a strict ancestor of the address of
the attached tree: the pairs lie in the pendant networks or in the attached tree. -/
theorem attachPairs_noncross : ∀ (S : Brooqs.Side L) (P : Finset Pair), ∀ e ∈ attachPairs S P,
    ∀ y, (y <+: hangAddr S ∧ y ≠ hangAddr S) →
      ((y <+: e.1 ∧ y ≠ e.1) ↔ (y <+: e.2 ∧ y ≠ e.2))
  | .hyb _, _, _, _, y, hy => by
      simp only [hangAddr, Brooqs.Side.nodes, List.length_nil, List.replicate_zero,
        List.prefix_nil] at hy
      exact absurd hy.1 hy.2
  | .node _ _ M S, P, e, he, y, hy => by
      rw [hangAddr_node] at hy
      simp only [attachPairs, Finset.mem_union] at he
      rcases y with _ | ⟨c, y⟩
      · rcases he with he | he <;> obtain ⟨f, -, rfl⟩ := mem_liftPairs.1 he <;> simp
      · obtain ⟨rfl, hy'⟩ := List.cons_prefix_cons.1 hy.1
        have hy'' : y ≠ hangAddr S := fun h => hy.2 (by rw [h])
        rcases he with he | he <;> obtain ⟨f, hf, rfl⟩ := mem_liftPairs.1 he
        · simp
        · simpa using attachPairs_noncross S P f hf y ⟨hy', hy''⟩

/-- No pair of the tree of a side with a tree attached has its donor end strictly above the
address of the attached tree. -/
theorem attachPairs_donor : ∀ (S : Brooqs.Side L) (P : Finset Pair), ∀ e ∈ attachPairs S P,
    ¬(e.1 <+: hangAddr S ∧ e.1 ≠ hangAddr S)
  | .hyb _, _, _, _, h => by
      simp only [hangAddr, Brooqs.Side.nodes, List.length_nil, List.replicate_zero,
        List.prefix_nil] at h
      exact h.2 h.1
  | .node _ _ M S, P, e, he, h => by
      rw [hangAddr_node] at h
      simp only [attachPairs, Finset.mem_union] at he
      rcases he with he | he <;> obtain ⟨f, hf, rfl⟩ := mem_liftPairs.1 he
      · simp at h
      · simp only [List.cons_prefix_cons, true_and, ne_eq, List.cons.injEq] at h
        exact attachPairs_donor S P f hf h

/-- No pair of the tree of a side with its hybrid edge deleted has its donor end strictly above
the address of the last pendant network. -/
theorem detachPairs_donor : ∀ (S : Brooqs.Side L), ∀ e ∈ detachPairs S,
    ¬(e.1 <+: lastAddr S ∧ e.1 ≠ lastAddr S)
  | .hyb _, _, he, _ => by simp [detachPairs] at he
  | .node _ _ M (.hyb _), e, _, h => by
      rw [lastAddr_single, List.prefix_nil] at h
      exact h.2 h.1
  | .node _ _ M (.node ℓ' b' M' S), e, he, h => by
      rw [lastAddr_node] at h
      rw [detachPairs_node] at he
      rcases Finset.mem_union.1 he with he | he <;> obtain ⟨f, hf, rfl⟩ := mem_liftPairs.1 he
      · simp at h
      · simp only [List.cons_prefix_cons, true_and, ne_eq, List.cons.injEq] at h
        exact detachPairs_donor _ f hf h


/-! ### The displayed trees are trees of the graph -/

theorem keptClades_fork (l r : PhyloTree) (F₁ F₂ : Finset Pair) :
    keptClades (.fork l r) (liftPairs false F₁ ∪ liftPairs true F₂) =
      insert (l.taxa ∪ r.taxa) (keptClades l F₁ ∪ keptClades r F₂) :=
  nodeClades_fork l r F₁ F₂ fun _ C => C

theorem pairs_ne_nil {N : Brooqs.Net L} {e : Pair} (he : e ∈ pairs N) : e.1 ≠ [] ∧ e.2 ≠ [] :=
  ⟨(admissible_of_mem (separated_pairs N) he).2.2.1,
    (admissible_of_mem (separated_pairs N) he).2.2.2.1⟩

/-- The cycle case: the hybrid component hangs from the side `Sa` in the base tree, the side `Sd`
has its hybrid edge deleted. The displayed tree that hangs it from `Sa` is the tree of the
switching that keeps the added edges inside the pendant networks and the hybrid component, and
the one that hangs it from `Sd` also keeps the added edge of the cycle. -/
theorem cycle_kept {Sa Sd : Brooqs.Side L} {H : Brooqs.Net L} (hSa : Sa.IsMetric)
    (hSd : Sd.IsMetric) (hd : hasNode Sd) (hH : H.IsMetric) (hdisj : Disjoint Sa.taxa H.taxa)
    {KH Ka Kd : Finset (Finset L)} {Ta Td : Finset L}
    (hT : (Ta = H.taxa ∧ Td = ∅) ∨ (Ta = ∅ ∧ Td = H.taxa))
    {FH : Finset Pair} (hFH : FH ⊆ pairs H)
    (hKH : keptClades (baseTree H) FH = KH.image (Finset.map (Coalescent.label L)))
    {Ga : Finset Pair} (hGa : Ga ⊆ attachPairs Sa ∅)
    (hA : ∀ (X : PhyloTree) (FX : Finset Pair) (Y : Finset ℕ),
      Disjoint Y (Sa.taxa.map (Coalescent.label L)) → X.taxa \ Y = Ta.map (Coalescent.label L) →
      nodeClades (attachTree Sa X) (Ga ∪ liftHang Sa FX) (dropOn (hangAddr Sa) Y) =
        Ka.image (Finset.map (Coalescent.label L)) ∪ keptClades X FX)
    {Gd : Finset Pair} (hGd : Gd ⊆ detachPairs Sd)
    (hD : ∀ Y : Finset ℕ, Y = Td.map (Coalescent.label L) →
      nodeClades (detachTree Sd) Gd (addOn (lastAddr Sd) Y) ∪
        {keptClade (detachTree Sd) Gd (lastAddr Sd) ∪ Y} =
          Kd.image (Finset.map (Coalescent.label L))) :
    ∃ F ⊆ insert (true :: lastAddr Sd, false :: hangAddr Sa)
        (liftPairs false (attachPairs Sa (pairs H)) ∪ liftPairs true (detachPairs Sd)),
      keptClades (.fork (attachTree Sa (baseTree H)) (detachTree Sd)) F =
        (insert (Sa.taxa ∪ Sd.taxa ∪ H.taxa) (KH ∪ Ka ∪ Kd)).image
          (Finset.map (Coalescent.label L)) := by
  have hX : (baseTree H).taxa = H.taxa.map (Coalescent.label L) := taxa_baseTree hH
  have hne : Sd.nodes ≠ [] := by
    cases Sd with
    | hyb _ => simp at hd
    | node _ _ _ _ => simp [Brooqs.Side.nodes]
  have hAt := taxa_attachTree hSa (baseTree H)
  have hDt := taxa_detachTree hSd hne
  have hFA : Ga ∪ liftHang Sa FH ⊆ attachPairs Sa (pairs H) := by
    rw [attachPairs_eq Sa (pairs H)]
    exact Finset.union_subset_union hGa (liftHang_subset Sa hFH)
  have hu : lastAddr Sd ∈ (detachTree Sd).nodes := lastAddr_mem_nodes Sd
  have htop : (insert (Sa.taxa ∪ Sd.taxa ∪ H.taxa) (KH ∪ Ka ∪ Kd)).image
      (Finset.map (Coalescent.label L)) =
      insert ((attachTree Sa (baseTree H)).taxa ∪ (detachTree Sd).taxa)
        (Ka.image (Finset.map (Coalescent.label L)) ∪ KH.image (Finset.map (Coalescent.label L)) ∪
          Kd.image (Finset.map (Coalescent.label L))) := by
    rw [hAt, hDt, hX, Finset.image_insert, Finset.image_union, Finset.image_union,
      Finset.map_union, Finset.map_union]
    congr 1
    · ext a
      simp only [Finset.mem_union]
      tauto
    · ext C
      simp only [Finset.mem_union]
      tauto
  rcases hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  -- the hybrid component hangs from `Sa`: no added edge of the cycle is kept
  · refine ⟨liftPairs false (Ga ∪ liftHang Sa FH) ∪ liftPairs true Gd,
      (Finset.union_subset_union (Finset.image_subset_image hFA)
        (Finset.image_subset_image hGd)).trans (Finset.subset_insert _ _), ?_⟩
    have h1 : keptClades (attachTree Sa (baseTree H)) (Ga ∪ liftHang Sa FH) =
        Ka.image (Finset.map (Coalescent.label L)) ∪ KH.image (Finset.map (Coalescent.label L)) := by
      rw [← hKH, ← hA (baseTree H) FH ∅ (Finset.disjoint_empty_left _)
        (by rw [Finset.sdiff_empty, hX]), keptClades_eq_nodeClades]
      congr 1
      funext y C
      simp [dropOn]
    have h2 : keptClades (detachTree Sd) Gd = Kd.image (Finset.map (Coalescent.label L)) := by
      rw [← hD ∅ (by simp), keptClades_eq_nodeClades]
      have hf : (fun (_ : Address) (C : Finset ℕ) => C) = addOn (lastAddr Sd) ∅ := by
        funext y C
        simp [addOn]
      rw [hf, Finset.union_empty]
      refine (Finset.union_eq_left.2 fun C hC => ?_).symm
      rw [Finset.mem_singleton] at hC
      subst hC
      exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨_, hu, by simp [addOn]⟩)
    rw [keptClades_fork, h1, h2, htop]
  -- the hybrid component hangs from `Sd`: the added edge of the cycle is kept
  · refine ⟨insert (true :: lastAddr Sd, false :: hangAddr Sa)
      (liftPairs false (Ga ∪ liftHang Sa FH) ∪ liftPairs true Gd),
      Finset.insert_subset_insert _ (Finset.union_subset_union (Finset.image_subset_image hFA)
        (Finset.image_subset_image hGd)), ?_⟩
    rw [keptClades_cross _ _ _ _ _ _
      (fun e he => attachPairs_noncross Sa (pairs H) e (hFA he))
      (fun e he => attachPairs_donor Sa (pairs H) e (hFA he))
      (fun e he => detachPairs_donor Sd e (hGd he)),
      PhyloTree.taxaAt_eq (nodeAt_hangAddr Sa (baseTree H)),
      hA (baseTree H) FH (baseTree H).taxa (by rw [hX, Finset.disjoint_map]; exact hdisj.symm)
        (by rw [Finset.sdiff_self, Finset.map_empty]),
      hKH, Finset.union_assoc (Ka.image _ ∪ KH.image _), hD _ (by rw [hX]), htop]


mutual
/-- **Every displayed tree of `N` is the tree of a switching of its graph.** For a metric network
`N` with distinct leaf labels and a displayed tree `K` of `N`, the switching of the graph of `N`
that keeps the added edges of a set `F` of pairs of `N` has the clusters of `K` as its clades. -/
theorem exists_kept_net : ∀ (N : Brooqs.Net L), N.WellFormed → ∀ K ∈ N.displayed,
    ∃ F ⊆ pairs N, keptClades (baseTree N) F = K.image (Finset.map (Coalescent.label L))
  | .leaf x, _, K, hK => by
      simp only [Brooqs.Net.displayed, List.mem_singleton] at hK
      subst hK
      refine ⟨∅, Finset.empty_subset _, ?_⟩
      ext C
      simp [keptClades, keptClade, movesOut, movesIn, baseTree, PhyloTree.nodes,
        PhyloTree.taxaAt, PhyloTree.nodeAt, PhyloTree.taxa, PhyloTree.labels, Coalescent.label]
  | .tree _ N₁ _ N₂, h, K, hK => by
      have h₁ : N₁.WellFormed := ⟨h.1.2.2.1, (List.nodup_append.1 h.2).1⟩
      have h₂ : N₂.WellFormed := ⟨h.1.2.2.2, (List.nodup_append.1 h.2).2.1⟩
      simp only [Brooqs.Net.displayed, List.mem_flatMap, List.mem_map] at hK
      obtain ⟨K₁, hK₁, K₂, hK₂, rfl⟩ := hK
      obtain ⟨F₁, hF₁, e₁⟩ := exists_kept_net N₁ h₁ K₁ hK₁
      obtain ⟨F₂, hF₂, e₂⟩ := exists_kept_net N₂ h₂ K₂ hK₂
      refine ⟨liftPairs false F₁ ∪ liftPairs true F₂, Finset.union_subset_union
        (Finset.image_subset_image hF₁) (Finset.image_subset_image hF₂), ?_⟩
      change keptClades (.fork (baseTree N₁) (baseTree N₂)) _ = _
      rw [keptClades_fork, e₁, e₂, taxa_baseTree h₁.1, taxa_baseTree h₂.1, Finset.image_insert,
        Finset.image_union, Finset.map_union]
  | .cycle _ S₁ S₂ _ H, h, K, hK => by
      have hS₁ : S₁.IsMetric := h.1.2.2.2.1
      have hS₂ : S₂.IsMetric := h.1.2.2.2.2.1
      have hH : H.IsMetric := h.1.2.2.2.2.2.1
      obtain ⟨hn₁, hn₂, hnH, hd₁, hd₂⟩ := nodup_cycle h.2
      simp only [Brooqs.Net.displayed, List.mem_flatMap, List.mem_append, List.mem_map] at hK
      obtain ⟨KH, hKH, hK⟩ := hK
      obtain ⟨FH, hFH, eH⟩ := exists_kept_net H ⟨hH, hnH⟩ KH hKH
      cases S₂ with
      | hyb ℓ' =>
        have h1 : S₁.nodes ≠ [] := h.1.2.2.2.2.2.2.resolve_right (by simp [Brooqs.Side.nodes])
        have hd : hasNode S₁ := by
          cases S₁ with
          | hyb _ => simp [Brooqs.Side.nodes] at h1
          | node _ _ _ _ => rfl
        rw [baseTree_cycle_hyb, pairs_cycle_hyb]
        rcases hK with ⟨K₁, hK₁, K₂, hK₂, rfl⟩ | ⟨K₁, hK₁, K₂, hK₂, rfl⟩
        -- the hybrid component hangs from `S₁`: the added edge of the cycle is kept
        · obtain ⟨Gd, hGd, eD⟩ := exists_kept_detach S₁ hS₁ hn₁ hd H.taxa K₁ hK₁
          obtain ⟨Ga, hGa, eA⟩ := exists_kept_attach (.hyb ℓ') hS₂ hn₂ ∅ K₂ hK₂
          obtain ⟨F, hF, eF⟩ := cycle_kept hS₂ hS₁ hd hH hd₂ (Or.inr ⟨rfl, rfl⟩) hFH eH hGa eA
            hGd eD
          refine ⟨F, hF, eF.trans ?_⟩
          congr 1
          rw [Finset.union_comm (Brooqs.Side.hyb ℓ').taxa S₁.taxa, Finset.union_right_comm KH]
        -- the hybrid component hangs from `S₂`, the direct edge: no added edge of the cycle
        · obtain ⟨Gd, hGd, eD⟩ := exists_kept_detach S₁ hS₁ hn₁ hd ∅ K₁ hK₁
          obtain ⟨Ga, hGa, eA⟩ := exists_kept_attach (.hyb ℓ') hS₂ hn₂ H.taxa K₂ hK₂
          obtain ⟨F, hF, eF⟩ := cycle_kept hS₂ hS₁ hd hH hd₂ (Or.inl ⟨rfl, rfl⟩) hFH eH hGa eA
            hGd eD
          refine ⟨F, hF, eF.trans ?_⟩
          congr 1
          rw [Finset.union_comm (Brooqs.Side.hyb ℓ').taxa S₁.taxa, Finset.union_right_comm KH]
      | node ℓ' b' M S =>
        rw [baseTree_cycle_node, pairs_cycle_node]
        rcases hK with ⟨K₁, hK₁, K₂, hK₂, rfl⟩ | ⟨K₁, hK₁, K₂, hK₂, rfl⟩
        -- the hybrid component hangs from `S₁`: no added edge of the cycle
        · obtain ⟨Ga, hGa, eA⟩ := exists_kept_attach S₁ hS₁ hn₁ H.taxa K₁ hK₁
          obtain ⟨Gd, hGd, eD⟩ := exists_kept_detach _ hS₂ hn₂ rfl ∅ K₂ hK₂
          exact cycle_kept hS₁ hS₂ rfl hH hd₁ (Or.inl ⟨rfl, rfl⟩) hFH eH hGa eA hGd eD
        -- the hybrid component hangs from `S₂`: the added edge of the cycle is kept
        · obtain ⟨Ga, hGa, eA⟩ := exists_kept_attach S₁ hS₁ hn₁ ∅ K₁ hK₁
          obtain ⟨Gd, hGd, eD⟩ := exists_kept_detach _ hS₂ hn₂ rfl H.taxa K₂ hK₂
          exact cycle_kept hS₁ hS₂ rfl hH hd₁ (Or.inr ⟨rfl, rfl⟩) hFH eH hGa eA hGd eD

/-- The attach side: the clusters along a side with the taxa `T` below its hybrid edge, in the
tree of the side with a tree `X` attached, with the taxa `Y` removed from the strict ancestors of
`X`, when `X` without `Y` has the taxa `T`. -/
theorem exists_kept_attach : ∀ (S : Brooqs.Side L), S.IsMetric → S.leaves.Nodup →
    ∀ (T : Finset L), ∀ K ∈ S.displayed T, ∃ G ⊆ attachPairs S ∅,
      ∀ (X : PhyloTree) (FX : Finset Pair) (Y : Finset ℕ),
        Disjoint Y (S.taxa.map (Coalescent.label L)) → X.taxa \ Y = T.map (Coalescent.label L) →
        nodeClades (attachTree S X) (G ∪ liftHang S FX) (dropOn (hangAddr S) Y) =
          K.image (Finset.map (Coalescent.label L)) ∪ keptClades X FX
  | .hyb ℓ, _, _, T, K, hK => by
      simp only [Brooqs.Side.displayed, List.mem_singleton] at hK
      subst hK
      refine ⟨∅, Finset.empty_subset _, fun X FX Y _ _ => ?_⟩
      have hf : dropOn (hangAddr (.hyb ℓ : Brooqs.Side L)) Y = fun _ C => C := by
        funext y C
        simp [dropOn, hangAddr, Brooqs.Side.nodes]
      simp only [attachTree, liftHang, Finset.empty_union, hf, Finset.image_empty,
        keptClades_eq_nodeClades]
  | .node ℓ b M S, hS, hnd, T, K, hK => by
      obtain ⟨hnM, hnS⟩ := nodup_node hnd
      simp only [Brooqs.Side.displayed, List.mem_flatMap, List.mem_map] at hK
      obtain ⟨K', hK', KM, hKM, rfl⟩ := hK
      obtain ⟨FM, hFM, eM⟩ := exists_kept_net M ⟨hS.2.2.1, hnM⟩ KM hKM
      obtain ⟨G', hG', eS⟩ := exists_kept_attach S hS.2.2.2 hnS T K' hK'
      refine ⟨liftPairs false FM ∪ liftPairs true G', Finset.union_subset_union
        (Finset.image_subset_image hFM) (Finset.image_subset_image hG'), fun X FX Y hY hXY => ?_⟩
      have hYS : Disjoint Y (S.taxa.map (Coalescent.label L)) := hY.mono_right (by
        rw [Brooqs.Side.taxa_node, Finset.map_union]
        exact Finset.subset_union_right)
      have hYM : Disjoint Y (M.taxa.map (Coalescent.label L)) := hY.mono_right (by
        rw [Brooqs.Side.taxa_node, Finset.map_union]
        exact Finset.subset_union_left)
      have hF : liftPairs false FM ∪ liftPairs true G' ∪ liftHang (.node ℓ b M S) FX =
          liftPairs false FM ∪ liftPairs true (G' ∪ liftHang S FX) := by
        simp only [liftHang, liftPairs_union, Finset.union_assoc]
      rw [hF]
      change nodeClades (.fork (baseTree M) (attachTree S X)) _ (dropOn (hangAddr (.node ℓ b M S)) Y)
        = _
      rw [nodeClades_fork]
      have hl : (fun y => dropOn (hangAddr (.node ℓ b M S)) Y (false :: y)) =
          fun _ C => C := by
        funext y C
        simp [dropOn, hangAddr_node]
      have hr : (fun y => dropOn (hangAddr (.node ℓ b M S)) Y (true :: y)) =
          dropOn (hangAddr S) Y := by
        funext y C
        simp [dropOn, hangAddr_node]
      have h0 : dropOn (hangAddr (.node ℓ b M S)) Y []
          ((baseTree M).taxa ∪ (attachTree S X).taxa) =
          (T ∪ S.taxa ∪ M.taxa).map (Coalescent.label L) := by
        rw [dropOn, ite_eq_left ⟨List.nil_prefix, by rw [hangAddr_node]; simp⟩,
          taxa_baseTree hS.2.2.1, taxa_attachTree hS.2.2.2, Finset.union_sdiff_distrib,
          Finset.union_sdiff_distrib, Finset.sdiff_eq_self_of_disjoint hYM.symm,
          Finset.sdiff_eq_self_of_disjoint hYS.symm, hXY, Finset.map_union, Finset.map_union]
        ext a
        simp only [Finset.mem_union]
        tauto
      rw [hl, hr, h0, ← keptClades_eq_nodeClades, eM, eS X FX Y hYS hXY, Finset.image_insert,
        Finset.image_union]
      ext C
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto

/-- The detach side: the clusters along a side with a node and the taxa `T` below its hybrid edge,
in the tree of the side with its hybrid edge deleted, with the taxa `Y = T` added to the strict
ancestors of the last pendant network, and the cluster of the last node. -/
theorem exists_kept_detach : ∀ (S : Brooqs.Side L), S.IsMetric → S.leaves.Nodup → hasNode S →
    ∀ (T : Finset L), ∀ K ∈ S.displayed T, ∃ G ⊆ detachPairs S,
      ∀ (Y : Finset ℕ), Y = T.map (Coalescent.label L) →
        nodeClades (detachTree S) G (addOn (lastAddr S) Y) ∪
          {keptClade (detachTree S) G (lastAddr S) ∪ Y} =
            K.image (Finset.map (Coalescent.label L))
  | .hyb _, _, _, h, _, _, _ => by simp at h
  | .node ℓ b M (.hyb ℓ'), hS, hnd, _, T, K, hK => by
      obtain ⟨hnM, -⟩ := nodup_node hnd
      simp only [Brooqs.Side.displayed, List.mem_flatMap, List.mem_map, List.mem_singleton] at hK
      obtain ⟨K', rfl, KM, hKM, rfl⟩ := hK
      obtain ⟨FM, hFM, eM⟩ := exists_kept_net M ⟨hS.2.2.1, hnM⟩ KM hKM
      refine ⟨FM, by rw [detachPairs_single]; exact hFM, fun Y hY => ?_⟩
      rw [detachTree_single, lastAddr_single]
      have hf : addOn [] Y = fun _ C => C := by
        funext y C
        simp [addOn]
      rw [hf, ← keptClades_eq_nodeClades, eM,
        keptClade_nil _ fun e he => pairs_ne_nil (hFM he), taxa_baseTree hS.2.2.1, hY,
        Brooqs.Side.taxa_hyb, Finset.union_empty, Finset.empty_union, Finset.image_insert]
      ext C
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, Finset.map_union]
      rw [Finset.union_comm (M.taxa.map _)]
      tauto
  | .node ℓ b M (.node ℓ' b' M' S), hS, hnd, _, T, K, hK => by
      obtain ⟨hnM, hnS⟩ := nodup_node hnd
      rw [Brooqs.Side.displayed, List.mem_flatMap] at hK
      obtain ⟨K', hK', hK⟩ := hK
      rw [List.mem_map] at hK
      obtain ⟨KM, hKM, rfl⟩ := hK
      obtain ⟨FM, hFM, eM⟩ := exists_kept_net M ⟨hS.2.2.1, hnM⟩ KM hKM
      obtain ⟨G', hG', eS⟩ := exists_kept_detach (.node ℓ' b' M' S) hS.2.2.2 hnS rfl T K' hK'
      refine ⟨liftPairs false FM ∪ liftPairs true G', by
        rw [detachPairs_node]
        exact Finset.union_subset_union (Finset.image_subset_image hFM)
          (Finset.image_subset_image hG'), fun Y hY => ?_⟩
      have hr0 := nodeAt_fork_true (baseTree M) (detachTree (.node ℓ' b' M' S))
      have hlast : keptClade (.fork (baseTree M) (detachTree (.node ℓ' b' M' S)))
          (liftPairs false FM ∪ liftPairs true G') (true :: lastAddr (.node ℓ' b' M' S)) =
          keptClade (detachTree (.node ℓ' b' M' S)) G' (lastAddr (.node ℓ' b' M' S)) := by
        rw [Finset.union_comm]
        exact keptClade_cons (b := true) (c := false) (by decide) hr0 G' FM _
      rw [detachTree_node, lastAddr_node, nodeClades_fork, hlast]
      have hl : (fun y => addOn (true :: lastAddr (.node ℓ' b' M' S)) Y (false :: y)) =
          fun _ C => C := by
        funext y C
        simp [addOn]
      have hr : (fun y => addOn (true :: lastAddr (.node ℓ' b' M' S)) Y (true :: y)) =
          addOn (lastAddr (.node ℓ' b' M' S)) Y := by
        funext y C
        simp [addOn]
      have h0 : addOn (true :: lastAddr (.node ℓ' b' M' S)) Y []
          ((baseTree M).taxa ∪ (detachTree (.node ℓ' b' M' S)).taxa) =
          (T ∪ (Brooqs.Side.node ℓ' b' M' S).taxa ∪ M.taxa).map (Coalescent.label L) := by
        rw [addOn, ite_eq_left ⟨List.nil_prefix, by simp⟩, taxa_baseTree hS.2.2.1,
          taxa_detachTree hS.2.2.2 (by simp [Brooqs.Side.nodes]), hY, Finset.map_union,
          Finset.map_union]
        ext a
        simp only [Finset.mem_union]
        tauto
      rw [hl, hr, h0, ← keptClades_eq_nodeClades, eM, Finset.image_insert, Finset.image_union,
        ← eS Y hY]
      ext C
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto
end


/-! ### No ghost donor -/

theorem liftPairs_noGhost {b : Bool} {F : Finset Pair} (h : ∀ e ∈ F, ¬e.1 <+: e.2) :
    ∀ e ∈ liftPairs b F, ¬e.1 <+: e.2 := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := mem_liftPairs.1 he
  simpa using h f hf

mutual
/-- The pairs of `N` have no ghost donor: the donor end of each is not an ancestor of its recipient
end (the two ends lie on the two sides of the top node of a cycle). -/
theorem pairs_noGhost : ∀ (N : Brooqs.Net L), ∀ e ∈ pairs N, ¬e.1 <+: e.2
  | .leaf _, e, he => by simp [pairs] at he
  | .tree _ N₁ _ N₂, e, he => by
      rcases Finset.mem_union.1 he with he | he
      · exact liftPairs_noGhost (pairs_noGhost N₁) e he
      · exact liftPairs_noGhost (pairs_noGhost N₂) e he
  | .cycle _ S₁ S₂ _ H, e, he => by
      unfold pairs at he
      split_ifs at he
      all_goals
        rcases Finset.mem_insert.1 he with rfl | he
        · simp
        rcases Finset.mem_union.1 he with he | he
        · exact liftPairs_noGhost (attachPairs_noGhost _ _ (pairs_noGhost H)) e he
        · exact liftPairs_noGhost (detachPairs_noGhost _) e he

theorem attachPairs_noGhost : ∀ (S : Brooqs.Side L) (P : Finset Pair),
    (∀ e ∈ P, ¬e.1 <+: e.2) → ∀ e ∈ attachPairs S P, ¬e.1 <+: e.2
  | .hyb _, _, hP, e, he => hP e he
  | .node _ _ M S, P, hP, e, he => by
      rcases Finset.mem_union.1 he with he | he
      · exact liftPairs_noGhost (pairs_noGhost M) e he
      · exact liftPairs_noGhost (attachPairs_noGhost S P hP) e he

theorem detachPairs_noGhost : ∀ (S : Brooqs.Side L), ∀ e ∈ detachPairs S, ¬e.1 <+: e.2
  | .hyb _, e, he => by simp [detachPairs] at he
  | .node _ _ M S, e, he => by
      unfold detachPairs at he
      split_ifs at he
      · rcases Finset.mem_union.1 he with he | he
        · exact liftPairs_noGhost (pairs_noGhost M) e he
        · exact liftPairs_noGhost (detachPairs_noGhost S) e he
      · exact pairs_noGhost M e he
end

/-! ### Every displayed tree is a tree of the graph -/

/-- **Every displayed tree of `N` is the tree of a switching of its graph.** For a metric
level-1 network `N` with distinct leaf labels and a displayed tree `K` of `N` (CAMUS's
Definition 1 in the model, `Brooqs.Net.displayed`), some switching `S` of the graph
`Realization.graph (baseTree N) (pairs N)` of `N` has the clusters of `K` as the clades below its
vertices: it keeps, at each cycle whose displayed tree hangs the hybrid component from the side
whose hybrid edge the base tree deletes, the added edge of the cycle. -/
theorem exists_switching_of_mem_displayed {N : Brooqs.Net L} (hN : N.WellFormed)
    {K : Finset (Finset L)} (hK : K ∈ N.displayed) :
    ∃ S, (Realization.graph (baseTree N) (pairs N)).Switching S ∧
      (Realization.graph (baseTree N) (pairs N)).vertices.image
          ((Realization.graph (baseTree N) (pairs N)).cladeBelow S) =
        K.image (Finset.map (Coalescent.label L)) := by
  obtain ⟨F, hF, hFK⟩ := exists_kept_net N hN K hK
  refine ⟨keptSwitching (baseTree N) (pairs N) F,
    keptSwitching_switching (separated_pairs N).1 hF, ?_⟩
  rw [image_cladeBelow_keptSwitching (wellLabelled_baseTree hN) (separated_pairs N) hF
    (pairs_noGhost N), hFK]

/-- **Every displayed tree of `N` is a tree of its graph** (Definition 1). For a metric level-1
network `N` with distinct leaf labels and a displayed tree `K` of `N`, there is a tree `T` on which
the graph `Realization.graph (baseTree N) (pairs N)` of `N` is built, in the sense of
Definition 1, whose clades are the clusters of `K`. -/
theorem exists_builtOn_of_mem_displayed {N : Brooqs.Net L} (hN : N.WellFormed)
    {K : Finset (Finset L)} (hK : K ∈ N.displayed) :
    ∃ T : PhyloTree, (Realization.graph (baseTree N) (pairs N)).BuiltOn T ∧
      T.clades.toFinset = K.image (Finset.map (Coalescent.label L)) := by
  obtain ⟨S, hS, hSK⟩ := exists_switching_of_mem_displayed hN hK
  exact exists_builtOn_of_switching_clades hN hS hSK


/-! ### Recovery through every displayed tree -/

section Genes

open Filter Topology MeasureTheory ProbabilityTheory Coalescent Algorithm1

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]

open DynamicProgramming in
/-- **Sections 3.2 to 3.4 under the NMSC, through every displayed tree of `N`.** Let the gene trees
be independent, each with the law of the NMSC on a metric level-1 network `N` with distinct leaf
labels on the taxa `L`, without the anomalous configuration, and let `0 < t < t₀(N)`; let the root
of the graph `Nr = Realization.graph (baseTree N) (pairs N)` of `N` have an outgroup leaf `z` as a
child. For every displayed tree `K` of `N` ("T* is one of the underlying trees", Section 3.3),
there is a tree `T` of `Nr` (Definition 1) whose clades are the clusters of `K`, and if `Nr` is
identifiable under inclusion among the networks built on `T`, then almost surely, for all large
numbers `n` of genes, every network built on `T` that has the best score for the output `Q` of
Quartet Filtering on the quartet trees of the first `n` gene trees, with the fewest reticulations
among the networks with the best score, is isomorphic to `Nr`: "CAMUS will add the correct
reticulations and return N" (Section 3.2). -/
theorem nmsc_recovery_displayed {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) (hna : NoAnomaly N) (G : ℕ → Ω → Finset (Finset L))
    (hind : iIndepFun G P) (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) {t : ℝ} (ht : 0 < t)
    (ht₀ : t < threshold N) {z : ℕ} (hz : z ∈ (Realization.graph (baseTree N) (pairs N)).taxa)
    (hzr : ((Realization.graph (baseTree N) (pairs N)).root,
        (Realization.graph (baseTree N) (pairs N)).leaf z) ∈
      (Realization.graph (baseTree N) (pairs N)).edges)
    {K : Finset (Finset L)} (hK : K ∈ N.displayed) :
    ∃ T : PhyloTree, (Realization.graph (baseTree N) (pairs N)).BuiltOn T ∧
      T.clades.toFinset = K.image (Finset.map (Coalescent.label L)) ∧
      ((∀ R : RootedNetwork, R.AnchoredExtension T →
        (∀ q, (Realization.graph (baseTree N) (pairs N)).DisplaysQuartet q →
          R.DisplaysQuartet q) →
        R.reticulationCount ≤ (Realization.graph (baseTree N) (pairs N)).reticulationCount →
        Nonempty (R.Iso (Realization.graph (baseTree N) (pairs N)))) →
      ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ R : RootedNetwork, R.AnchoredExtension T →
        (∀ R' : RootedNetwork, R'.AnchoredExtension T →
          score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R') ≤
            score (filterQuartets t (geneQuartets (fun i => G i ω) n))
              (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R)) →
        (∀ R' : RootedNetwork, R'.AnchoredExtension T →
          (∀ R'' : RootedNetwork, R''.AnchoredExtension T →
            score (filterQuartets t (geneQuartets (fun i => G i ω) n))
                (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R'') ≤
              score (filterQuartets t (geneQuartets (fun i => G i ω) n))
                (repertoire (filterQuartets t (geneQuartets (fun i => G i ω) n)) R')) →
          R.reticulationCount ≤ R'.reticulationCount) →
        Nonempty (R.Iso (Realization.graph (baseTree N) (pairs N)))) := by
  -- the displayed tree is a tree of the graph (Definition 1)
  obtain ⟨T, hT, hc⟩ := exists_builtOn_of_mem_displayed hN hK
  -- and Section 3.2's argument applies through it
  exact ⟨T, hT, hc, fun identifiable => nmsc_recovery_builtOn hN htaxa hna G hind hid hlaw ht
    ht₀ hz hzr T hT identifiable⟩

end Genes

end NMSC

end Camus
