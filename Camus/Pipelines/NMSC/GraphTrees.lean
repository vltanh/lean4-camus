module

public import Camus.Pipelines.NMSC.Switchings

/-!
# The trees of the graph of a network by the edges kept into its reticulations

(module docstring to be written)
-/

@[expose] public section

namespace Camus

namespace RootedNetwork

variable {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- The clade below a vertex in `S` is its own taxon, if it is a leaf, and the clades below its
children in `S`. -/
theorem cladeBelow_eq_children (v : ℕ) :
    N.cladeBelow S v = N.taxa.filter (fun a => N.leaf a = v) ∪
      (S.filter (fun x => x.1 = v)).biUnion (fun x => N.cladeBelow S x.2) := by
  classical
  ext a
  simp only [mem_cladeBelow, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨ha, h⟩
    rcases h.cases_head with h | ⟨c, hvc, hc⟩
    · exact Or.inl ⟨ha, h.symm⟩
    · exact Or.inr ⟨(v, c), ⟨hvc, rfl⟩, ha, hc⟩
  · rintro (⟨ha, h⟩ | ⟨x, ⟨hx, rfl⟩, ha, hc⟩)
    · exact ⟨ha, h ▸ .refl⟩
    · exact ⟨ha, Relation.ReflTransGen.head hx hc⟩

open Classical in
/-- The number of vertices reached from `v` along `S`. -/
noncomputable def reachCount (N : RootedNetwork) (S : Finset (ℕ × ℕ)) (v : ℕ) : ℕ :=
  (N.vertices.filter fun x => Relation.ReflTransGen (fun u w => (u, w) ∈ S) v x).card

/-- Along an edge of `S ⊆ N.edges`, fewer vertices are reached: `N` has no directed cycle. -/
theorem reachCount_lt (hN : N.RootedBinaryLevelOne) (hSN : S ⊆ N.edges) {v c : ℕ}
    (hvc : (v, c) ∈ S) : N.reachCount S c < N.reachCount S v := by
  classical
  unfold reachCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨v, Finset.mem_filter.2 ⟨(hN.2.1 _ (hSN hvc)).1, .refl⟩, fun h => ?_⟩
    exact false_of_reach_of_edge hN hSN (Finset.mem_filter.1 h).2 (hSN hvc)
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, Relation.ReflTransGen.head hvc hx.2⟩

end RootedNetwork

namespace Realization

variable {t : PhyloTree} {E F : Finset Pair}

/-- The switching of `Realization.graph t E` that keeps the added edges of the pairs of `F ⊆ E`
and the support edges that do not enter their recipients. -/
noncomputable def keptSwitching (t : PhyloTree) (E F : Finset Pair) : Finset (ℕ × ℕ) :=
  (supportEdges t E).filter (fun x => ∀ e ∈ F, x.2 ≠ recipient t e) ∪
    F.image (fun e => (donor t e, recipient t e))

theorem keptSwitching_subset (hF : F ⊆ E) : keptSwitching t E F ⊆ (graph t E).edges := by
  intro x hx
  rcases Finset.mem_union.1 hx with hx | hx
  · exact Finset.mem_union_left _ (Finset.mem_filter.1 hx).1
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hF he))

/-- `Realization.keptSwitching t E F` is a switching of `Realization.graph t E`. -/
theorem keptSwitching_switching (hE : E ⊆ EdgeAbove.candidates t) (hF : F ⊆ E) :
    (graph t E).Switching (keptSwitching t E F) := by
  refine ⟨keptSwitching_subset hF, fun v hv hvr => ?_⟩
  have hS := (support_switching t E hE).2 v hv hvr
  have hdisj : Disjoint ((supportEdges t E).filter (fun x => ∀ e ∈ F, x.2 ≠ recipient t e))
      (F.image (fun e => (donor t e, recipient t e))) :=
    Finset.disjoint_left.2 fun x hx hx' => by
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx'
      exact (Finset.mem_filter.1 hx).2 e he rfl
  unfold keptSwitching
  rw [Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter hdisj)]
  by_cases hvF : ∃ e ∈ F, recipient t e = v
  · obtain ⟨e, he, rfl⟩ := hvF
    have h1 : ((supportEdges t E).filter (fun x => ∀ e ∈ F, x.2 ≠ recipient t e)).filter
        (fun x => x.2 = recipient t e) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨⟨_, h⟩, h'⟩
      exact h e he h'
    have h2 : (F.image (fun e => (donor t e, recipient t e))).filter
        (fun x => x.2 = recipient t e) = {(donor t e, recipient t e)} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨f, hf, rfl⟩, h⟩
        rw [recipient_injective t (hE (hF hf)) (hE (hF he)) h]
      · rintro rfl
        exact ⟨⟨e, he, rfl⟩, rfl⟩
    rw [h1, h2]
    rfl
  · simp only [not_exists, not_and] at hvF
    have h1 : ((supportEdges t E).filter (fun x => ∀ e ∈ F, x.2 ≠ recipient t e)).filter
        (fun x => x.2 = v) = (supportEdges t E).filter (fun x => x.2 = v) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · exact fun h => ⟨⟨h.1, fun e he h' => hvF e he (h'.symm.trans h.2)⟩, h.2⟩
    have h2 : (F.image (fun e => (donor t e, recipient t e))).filter
        (fun x => x.2 = v) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.notMem_empty, iff_false]
      rintro ⟨⟨f, hf, rfl⟩, h⟩
      exact hvF f hf h
    rw [h1, h2, Finset.card_empty, add_zero, hS]

end Realization


namespace Realization

/-! ### Prefixes -/

theorem sp_child (p : Address) (b : Bool) : p <+: p ++ [b] ∧ p ≠ p ++ [b] :=
  ⟨List.prefix_append p [b], fun h => by simpa using congrArg List.length h⟩

theorem sp_of_child_prefix {p q : Address} {b : Bool} (h : p ++ [b] <+: q) :
    p <+: q ∧ p ≠ q :=
  ⟨(List.prefix_append p [b]).trans h, fun h' => by
    subst h'
    have := h.length_le
    simp at this⟩

theorem exists_child_of_sp {p q : Address} (h : p <+: q) (hne : p ≠ q) :
    ∃ b, p ++ [b] <+: q := by
  obtain ⟨r, rfl⟩ := h
  cases r with
  | nil => simp at hne
  | cons b r => exact ⟨b, ⟨r, by simp⟩⟩

theorem child_eq_of_prefix {p q : Address} {b b' : Bool} (h : p ++ [b] <+: q)
    (h' : p ++ [b'] <+: q) : b = b' := by
  rcases List.prefix_or_prefix_of_prefix h h' with h'' | h''
  · simpa using (List.prefix_append_right_inj p).1 h''
  · exact ((by simpa using (List.prefix_append_right_inj p).1 h'') : b' = b).symm

theorem eq_child_of_between {p x : Address} {b : Bool} (hpx : p <+: x) (hne : p ≠ x)
    (hx : x <+: p ++ [b]) : x = p ++ [b] := by
  refine hx.eq_of_length (le_antisymm hx.length_le ?_)
  have h1 := hpx.length_le
  have h2 : p.length ≠ x.length := fun h => hne (hpx.eq_of_length h)
  simp only [List.length_append, List.length_singleton]
  omega

/-! ### Consequences of cycle separation -/

variable {t : PhyloTree} {E : Finset Pair}

theorem admissible_of_mem (hE : EdgeAbove.CycleSeparated t E) {e : Pair} (he : e ∈ E) :
    EdgeAbove.Admissible t e :=
  (Finset.mem_filter.mp (hE.1 he)).2

/-- Two pairs of a cycle-separated family with the same recipient end are equal. -/
theorem eq_of_recipient_eq (hE : EdgeAbove.CycleSeparated t E) {e f : Pair} (he : e ∈ E)
    (hf : f ∈ E) (h : e.2 = f.2) : e = f := by
  by_contra hne
  refine Finset.disjoint_left.mp (hE.2 he hf hne)
    (recipient_parent_mem_footprint (admissible_of_mem hE he)) ?_
  rw [h]
  exact recipient_parent_mem_footprint (admissible_of_mem hE hf)

/-- If the recipient end of `f` lies strictly below the recipient end `w` of `e`, so does its
donor end: otherwise `parent(w)` is on the cycles of both pairs. -/
theorem recipient_inside (hE : EdgeAbove.CycleSeparated t E) {e f : Pair} (he : e ∈ E)
    (hf : f ∈ E) (h : e.2 <+: f.2) (hne : e.2 ≠ f.2) : e.2 <+: f.1 := by
  have hae := admissible_of_mem hE he
  by_contra hout
  have ht : EdgeAbove.target f <+: e.2 := by
    rcases List.prefix_or_prefix_of_prefix (lca_prefix_right f.1 f.2) h with h' | h'
    · exact h'
    · exact absurd (h'.trans (lca_prefix_left f.1 f.2)) hout
  have htne : EdgeAbove.target f ≠ e.2 := fun h' => hout (h' ▸ lca_prefix_left f.1 f.2)
  have hpf : parent e.2 ∈ EdgeAbove.footprint t f := by
    refine Finset.mem_filter.mpr ⟨t.nodes_prefix_closed hae.2.1 (parent_prefix e.2),
      prefix_parent_of_ne ht htne, Or.inr ⟨(parent_prefix e.2).trans h, ?_⟩⟩
    intro h'
    have h1 := h.length_le
    rw [← h'] at h1
    have hpos := List.length_pos_iff.mpr hae.2.2.2.1
    simp only [parent, List.length_take] at h1
    omega
  by_cases hef : e = f
  · subst hef
    exact hne rfl
  · exact Finset.disjoint_left.mp (hE.2 he hf hef) (recipient_parent_mem_footprint hae) hpf

/-- If the donor end of `f` is the recipient end of `e`, the donor of `f` is a ghost donor: its
donor end is an ancestor of its recipient end. -/
theorem donor_eq_recipient_ghost (hE : EdgeAbove.CycleSeparated t E) {e f : Pair} (he : e ∈ E)
    (hf : f ∈ E) (h : f.1 = e.2) : f.1 <+: f.2 := by
  by_contra hng
  have hne : EdgeAbove.target f ≠ f.1 := fun h' => hng ((lca_eq_left_iff _ _).1 h')
  have h1 := donor_parent_mem_footprint (admissible_of_mem hE hf) hne
  rw [h] at h1
  by_cases hef : e = f
  · subst hef
    exact (admissible_of_mem hE he).2.2.2.2 (by rw [← h])
  · exact Finset.disjoint_left.mp (hE.2 he hf hef)
      (recipient_parent_mem_footprint (admissible_of_mem hE he)) h1

/-! ### The clades of the tree of a switching -/

/-- The pairs of `F` whose added edge moves the subtree of their recipient end out of the clade
of `p`: `p` is a strict ancestor of the recipient end and not of the donor end. -/
def movesOut (F : Finset Pair) (p : Address) : Finset Pair :=
  F.filter fun e => (p <+: e.2 ∧ p ≠ e.2) ∧ ¬(p <+: e.1 ∧ p ≠ e.1)

/-- The pairs of `F` whose added edge moves the subtree of their recipient end into the clade of
`p`: `p` is a strict ancestor of the donor end and not of the recipient end. -/
def movesIn (F : Finset Pair) (p : Address) : Finset Pair :=
  F.filter fun e => (p <+: e.1 ∧ p ≠ e.1) ∧ ¬(p <+: e.2 ∧ p ≠ e.2)

/-- The clade of the vertex `p` of `T` in the tree of the switching of `Realization.graph t E`
that keeps the added edges of the pairs of `F`: the clade of `p` in `T`, without the subtrees
moved out of it and with the subtrees moved into it. -/
def keptClade (t : PhyloTree) (F : Finset Pair) (p : Address) : Finset ℕ :=
  (t.taxaAt p \ (movesOut F p).biUnion fun e => t.taxaAt e.2) ∪
    (movesIn F p).biUnion fun e => t.taxaAt e.2

/-- The taxa that the kept added edges with donor end `c` bring to the wire above `c`. -/
def donorTaxa (t : PhyloTree) (F : Finset Pair) (c : Address) : Finset ℕ :=
  (F.filter fun e => e.1 = c).biUnion fun e => t.taxaAt e.2

open Classical in
/-- The taxa that the wire above `c` brings to its upper end: none if a kept added edge enters
it, and otherwise the clade of `c` with the subtrees brought by the kept added edges with donor
end `c`. -/
noncomputable def wireTaxa (t : PhyloTree) (F : Finset Pair) (c : Address) : Finset ℕ :=
  if ∃ e ∈ F, e.2 = c then ∅ else keptClade t F c ∪ donorTaxa t F c

variable {F : Finset Pair}

theorem mem_taxaAt_of_mem {ht : t.WellLabelled} {q : Address} (hq : q ∈ t.nodes) {a : ℕ}
    (ha : a ∈ t.taxa) : a ∈ t.taxaAt q ↔ q <+: leafAddress t a := by
  rw [PhyloTree.mem_taxaAt_iff ht hq]
  exact and_iff_right ha

theorem mem_keptClade (ht : t.WellLabelled) (hF : ∀ e ∈ F, e.2 ∈ t.nodes) {p : Address}
    (hp : p ∈ t.nodes) {a : ℕ} (ha : a ∈ t.taxa) :
    a ∈ keptClade t F p ↔
      (p <+: leafAddress t a ∧ ∀ e ∈ F, (p <+: e.2 ∧ p ≠ e.2) → ¬(p <+: e.1 ∧ p ≠ e.1) →
        ¬e.2 <+: leafAddress t a) ∨
      ∃ e ∈ F, (p <+: e.1 ∧ p ≠ e.1) ∧ ¬(p <+: e.2 ∧ p ≠ e.2) ∧ e.2 <+: leafAddress t a := by
  simp only [keptClade, movesOut, movesIn, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_biUnion, Finset.mem_filter, mem_taxaAt_of_mem (ht := ht) hp ha]
  constructor
  · rintro (⟨hpa, hno⟩ | ⟨e, ⟨he, h1, h2⟩, hae⟩)
    · refine Or.inl ⟨hpa, fun e he h1 h2 hea => hno ⟨e, ⟨he, h1, h2⟩, ?_⟩⟩
      exact (mem_taxaAt_of_mem (ht := ht) (hF e he) ha).2 hea
    · exact Or.inr ⟨e, he, h1, h2, (mem_taxaAt_of_mem (ht := ht) (hF e he) ha).1 hae⟩
  · rintro (⟨hpa, hno⟩ | ⟨e, he, h1, h2, hea⟩)
    · refine Or.inl ⟨hpa, ?_⟩
      rintro ⟨e, ⟨he, h1, h2⟩, hae⟩
      exact hno e he h1 h2 ((mem_taxaAt_of_mem (ht := ht) (hF e he) ha).1 hae)
    · exact Or.inr ⟨e, ⟨he, h1, h2⟩, (mem_taxaAt_of_mem (ht := ht) (hF e he) ha).2 hea⟩

theorem mem_donorTaxa (ht : t.WellLabelled) (hF : ∀ e ∈ F, e.2 ∈ t.nodes) {c : Address}
    {a : ℕ} (ha : a ∈ t.taxa) :
    a ∈ donorTaxa t F c ↔ ∃ e ∈ F, e.1 = c ∧ e.2 <+: leafAddress t a := by
  simp only [donorTaxa, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨e, ⟨he, h1⟩, hae⟩
    exact ⟨e, he, h1, (mem_taxaAt_of_mem (ht := ht) (hF e he) ha).1 hae⟩
  · rintro ⟨e, he, h1, hea⟩
    exact ⟨e, ⟨he, h1⟩, (mem_taxaAt_of_mem (ht := ht) (hF e he) ha).2 hea⟩

theorem keptClade_subset_taxa (p : Address) : keptClade t F p ⊆ t.taxa := by
  intro a ha
  simp only [keptClade, Finset.mem_union, Finset.mem_sdiff, Finset.mem_biUnion] at ha
  rcases ha with ⟨ha, -⟩ | ⟨e, -, ha⟩ <;> exact PhyloTree.taxaAt_subset t _ ha

theorem donorTaxa_subset_taxa (c : Address) : donorTaxa t F c ⊆ t.taxa := by
  intro a ha
  simp only [donorTaxa, Finset.mem_biUnion] at ha
  obtain ⟨e, -, ha⟩ := ha
  exact PhyloTree.taxaAt_subset t _ ha

theorem sp_of_sp_prefix {p x y : Address} (h : p <+: x ∧ p ≠ x) (hxy : x <+: y) :
    p <+: y ∧ p ≠ y :=
  ⟨h.1.trans hxy, fun h' => by
    subst h'
    exact h.2 (List.IsPrefix.eq_of_length h.1 (le_antisymm h.1.length_le hxy.length_le))⟩

/-- The prefix logic of the clade of an internal vertex `p`: a leaf `ℓ` is in the clade of `p` in
the tree of the switching iff it is brought by the wire above one of the two children of `p`. -/
theorem fork_logic {F : Finset Pair} {p ℓ : Address} (hpℓ : p ≠ ℓ)
    (hadm : ∀ e ∈ F, ¬e.2 <+: e.1)
    (hS1 : ∀ e ∈ F, ∀ f ∈ F, e.2 <+: f.1 → e.2 <+: f.2)
    (hS2 : ∀ e ∈ F, ∀ f ∈ F, e.2 <+: f.2 → e.2 ≠ f.2 → e.2 <+: f.1)
    (hS3 : ∀ e ∈ F, ∀ f ∈ F, e.2 = f.2 → e = f) :
    ((p <+: ℓ ∧ ∀ e ∈ F, (p <+: e.2 ∧ p ≠ e.2) → ¬(p <+: e.1 ∧ p ≠ e.1) → ¬e.2 <+: ℓ) ∨
      ∃ e ∈ F, (p <+: e.1 ∧ p ≠ e.1) ∧ ¬(p <+: e.2 ∧ p ≠ e.2) ∧ e.2 <+: ℓ) ↔
    ∃ b : Bool, (¬∃ e ∈ F, e.2 = p ++ [b]) ∧
      (((p ++ [b] <+: ℓ ∧ ∀ e ∈ F, (p ++ [b] <+: e.2 ∧ p ++ [b] ≠ e.2) →
          ¬(p ++ [b] <+: e.1 ∧ p ++ [b] ≠ e.1) → ¬e.2 <+: ℓ) ∨
        ∃ e ∈ F, (p ++ [b] <+: e.1 ∧ p ++ [b] ≠ e.1) ∧ ¬(p ++ [b] <+: e.2 ∧ p ++ [b] ≠ e.2) ∧
          e.2 <+: ℓ) ∨
       ∃ e ∈ F, e.1 = p ++ [b] ∧ e.2 <+: ℓ) := by
  constructor
  · rintro (⟨hpl, hX⟩ | ⟨e, he, hpe1, hpe2, hel⟩)
    · obtain ⟨b, hb⟩ := exists_child_of_sp hpl hpℓ
      by_cases hcut : ∃ e ∈ F, e.2 = p ++ [b]
      -- a kept added edge enters the wire above the child of `p` toward `ℓ`
      · obtain ⟨e, he, he2⟩ := hcut
        have hsp2 : p <+: e.2 ∧ p ≠ e.2 := he2 ▸ sp_child p b
        have hel : e.2 <+: ℓ := he2 ▸ hb
        have hsp1 : p <+: e.1 ∧ p ≠ e.1 := by
          by_contra h
          exact hX e he hsp2 h hel
        obtain ⟨b', hb'⟩ := exists_child_of_sp hsp1.1 hsp1.2
        have hbb' : b ≠ b' := by
          rintro rfl
          exact hadm e he (he2 ▸ hb')
        refine ⟨b', ?_, ?_⟩
        · rintro ⟨f, hf, hf2⟩
          have h := hS1 f hf e he (hf2 ▸ hb')
          rw [hf2, he2] at h
          exact hbb' (child_eq_of_prefix (List.prefix_refl _) h)
        · by_cases h1 : e.1 = p ++ [b']
          · exact Or.inr ⟨e, he, h1, hel⟩
          · refine Or.inl (Or.inr ⟨e, he, ⟨hb', fun h => h1 h.symm⟩, fun h => ?_, hel⟩)
            rw [he2] at h
            exact hbb' (child_eq_of_prefix (List.prefix_refl _) h.1)
      · by_cases hXb : ∃ e ∈ F, (p ++ [b] <+: e.2 ∧ p ++ [b] ≠ e.2) ∧
            ¬(p ++ [b] <+: e.1 ∧ p ++ [b] ≠ e.1) ∧ e.2 <+: ℓ
        -- a kept added edge moves `ℓ` out of the child of `p`
        · obtain ⟨e, he, h1, h2, hel⟩ := hXb
          have hsp2 : p <+: e.2 ∧ p ≠ e.2 := sp_of_child_prefix h1.1
          have hsp1 : p <+: e.1 ∧ p ≠ e.1 := by
            by_contra h
            exact hX e he hsp2 h hel
          by_cases h3 : e.1 = p ++ [b]
          · exact ⟨b, hcut, Or.inr ⟨e, he, h3, hel⟩⟩
          · obtain ⟨b', hb'⟩ := exists_child_of_sp hsp1.1 hsp1.2
            have hbb' : b' ≠ b := by
              rintro rfl
              exact h2 ⟨hb', fun h => h3 h.symm⟩
            refine ⟨b', ?_, ?_⟩
            · rintro ⟨f, hf, hf2⟩
              have h := hS1 f hf e he (hf2 ▸ hb')
              rw [hf2] at h
              exact hbb' (child_eq_of_prefix h h1.1)
            · by_cases h4 : e.1 = p ++ [b']
              · exact Or.inr ⟨e, he, h4, hel⟩
              · refine Or.inl (Or.inr ⟨e, he, ⟨hb', fun h => h4 h.symm⟩, fun h => ?_, hel⟩)
                exact hbb' (child_eq_of_prefix h.1 h1.1)
        · refine ⟨b, hcut, Or.inl (Or.inl ⟨hb, fun e he h1 h2 hel => hXb ⟨e, he, h1, h2, hel⟩⟩)⟩
    -- a kept added edge moves `ℓ` into the clade of `p`
    · obtain ⟨b, hb⟩ := exists_child_of_sp hpe1.1 hpe1.2
      refine ⟨b, ?_, ?_⟩
      · rintro ⟨f, hf, hf2⟩
        have h := hS1 f hf e he (hf2 ▸ hb)
        rw [hf2] at h
        exact hpe2 (sp_of_child_prefix h)
      · by_cases h1 : e.1 = p ++ [b]
        · exact Or.inr ⟨e, he, h1, hel⟩
        · exact Or.inl (Or.inr ⟨e, he, ⟨hb, fun h => h1 h.symm⟩,
            fun h => hpe2 (sp_of_child_prefix h.1), hel⟩)
  · rintro ⟨b, hcut, (⟨hbl, hXb⟩ | ⟨e, he, h1, h2, hel⟩) | ⟨e, he, h1, hel⟩⟩
    -- `ℓ` stays in the child of `p`
    · refine Or.inl ⟨(sp_of_child_prefix hbl).1, fun e' he' h1' h2' hel' => ?_⟩
      rcases List.prefix_or_prefix_of_prefix hel' hbl with h | h
      · exact hcut ⟨e', he', eq_child_of_between h1'.1 h1'.2 h⟩
      · by_cases heq : p ++ [b] = e'.2
        · exact hcut ⟨e', he', heq.symm⟩
        · exact hXb e' he' ⟨h, heq⟩ (fun h' => h2' (sp_of_child_prefix h'.1)) hel'
    -- `ℓ` is moved into the child of `p`
    · have hsp1 : p <+: e.1 ∧ p ≠ e.1 := sp_of_child_prefix h1.1
      by_cases hsp2 : p <+: e.2 ∧ p ≠ e.2
      · obtain ⟨b', hb'⟩ := exists_child_of_sp hsp2.1 hsp2.2
        have hbb' : b' ≠ b := by
          rintro rfl
          by_cases heq : p ++ [b'] = e.2
          · exact hadm e he (heq ▸ h1.1)
          · exact h2 ⟨hb', heq⟩
        refine Or.inl ⟨hsp2.1.trans hel, fun e' he' h1' h2' hel' => ?_⟩
        rcases List.prefix_or_prefix_of_prefix hel' hel with h | h
        · by_cases heq : e'.2 = e.2
          · obtain rfl := hS3 e' he' e he heq
            exact h2' hsp1
          · have h3 := hS2 e' he' e he h heq
            obtain ⟨b'', hb''⟩ := exists_child_of_sp h1'.1 h1'.2
            have hb2 := child_eq_of_prefix (hb''.trans h) hb'
            subst hb2
            exact hbb' (child_eq_of_prefix (hb''.trans h3) h1.1)
        · by_cases heq : e.2 = e'.2
          · obtain rfl := hS3 e he e' he' heq
            exact h2' hsp1
          · exact h2' (sp_of_sp_prefix hsp2 (hS2 e he e' he' h heq))
      · exact Or.inr ⟨e, he, hsp1, hsp2, hel⟩
    -- `ℓ` is brought by a kept added edge with donor end the child of `p`
    · have hsp1 : p <+: e.1 ∧ p ≠ e.1 := h1 ▸ sp_child p b
      by_cases hsp2 : p <+: e.2 ∧ p ≠ e.2
      · refine Or.inl ⟨hsp2.1.trans hel, fun e' he' h1' h2' hel' => ?_⟩
        rcases List.prefix_or_prefix_of_prefix hel' hel with h | h
        · by_cases heq : e'.2 = e.2
          · obtain rfl := hS3 e' he' e he heq
            exact h2' hsp1
          · have h3 := hS2 e' he' e he h heq
            rw [h1] at h3
            exact hcut ⟨e', he', eq_child_of_between h1'.1 h1'.2 h3⟩
        · by_cases heq : e.2 = e'.2
          · obtain rfl := hS3 e he e' he' heq
            exact h2' hsp1
          · exact h2' (sp_of_sp_prefix hsp2 (hS2 e he e' he' h heq))
      · exact Or.inr ⟨e, he, hsp1, hsp2, hel⟩

end Realization


namespace Realization

variable {t : PhyloTree} {E F : Finset Pair}

theorem separation_props (hE : EdgeAbove.CycleSeparated t E) (hF : F ⊆ E) :
    (∀ e ∈ F, ¬e.2 <+: e.1) ∧ (∀ e ∈ F, ∀ f ∈ F, e.2 <+: f.1 → e.2 <+: f.2) ∧
      (∀ e ∈ F, ∀ f ∈ F, e.2 <+: f.2 → e.2 ≠ f.2 → e.2 <+: f.1) ∧
      (∀ e ∈ F, ∀ f ∈ F, e.2 = f.2 → e = f) :=
  ⟨fun _ he => (admissible_of_mem hE (hF he)).2.2.2.2,
    fun _ he _ hf h => recipient_cone_closed_pairs hE (hF he) (hF hf) h,
    fun _ he _ hf h hne => recipient_inside hE (hF he) (hF hf) h hne,
    fun _ he _ hf h => eq_of_recipient_eq hE (hF he) (hF hf) h⟩

theorem mem_wireTaxa {c : Address} {a : ℕ} :
    a ∈ wireTaxa t F c ↔ (¬∃ e ∈ F, e.2 = c) ∧ (a ∈ keptClade t F c ∨ a ∈ donorTaxa t F c) := by
  classical
  unfold wireTaxa
  split_ifs with h
  · simp [h]
  · simp [h]

/-- **The clade of an internal vertex.** In the tree of the switching that keeps the added edges
of `F`, the clade of an internal vertex `p` of `T` is the union of the taxa brought by the wires
above its two children. -/
theorem keptClade_fork (ht : t.WellLabelled) (hE : EdgeAbove.CycleSeparated t E) (hF : F ⊆ E)
    {p : Address} {l r : PhyloTree} (hp : t.nodeAt p = some (.fork l r)) :
    keptClade t F p = wireTaxa t F (p ++ [false]) ∪ wireTaxa t F (p ++ [true]) := by
  have hpn : p ∈ t.nodes := (t.mem_nodes_iff p).2 ⟨_, hp⟩
  have hc : ∀ b : Bool, p ++ [b] ∈ t.nodes := fun b => (t.mem_nodes_iff _).2
    ⟨if b then r else l, by rw [PhyloTree.nodeAt_append, hp]; cases b <;> simp [PhyloTree.nodeAt]⟩
  have hF2 : ∀ e ∈ F, e.2 ∈ t.nodes := fun e he => (admissible_of_mem hE (hF he)).2.1
  obtain ⟨hadm, hS1, hS2, hS3⟩ := separation_props hE hF
  ext a
  by_cases ha : a ∈ t.taxa
  · have hℓ : p ≠ leafAddress t a := by
      intro h
      have h' := leafAddress_nodeAt ha
      rw [← h, hp] at h'
      cases h'
    rw [Finset.mem_union, mem_wireTaxa, mem_wireTaxa, mem_keptClade ht hF2 hpn ha,
      mem_keptClade ht hF2 (hc false) ha, mem_keptClade ht hF2 (hc true) ha,
      mem_donorTaxa ht hF2 ha, mem_donorTaxa ht hF2 ha]
    exact (fork_logic hℓ hadm hS1 hS2 hS3).trans Bool.exists_bool
  · have h1 : a ∉ keptClade t F p := fun h => ha (keptClade_subset_taxa p h)
    have h2 : ∀ b : Bool, a ∉ wireTaxa t F (p ++ [b]) := by
      intro b h
      rcases (mem_wireTaxa.1 h).2 with h | h
      · exact ha (keptClade_subset_taxa _ h)
      · exact ha (donorTaxa_subset_taxa _ h)
    simp only [Finset.mem_union, h1, h2 false, h2 true, or_self]

/-- **The clade of a leaf.** The clade of a leaf of `T` is its taxon: no added edge moves anything
into or out of it. -/
theorem keptClade_leaf (hE : EdgeAbove.CycleSeparated t E) (hF : F ⊆ E) {p : Address} {a : ℕ}
    (hp : t.nodeAt p = some (.leaf a)) : keptClade t F p = {a} := by
  have hno : ∀ q ∈ t.nodes, ¬(p <+: q ∧ p ≠ q) := by
    rintro q hq ⟨⟨r, rfl⟩, hne⟩
    cases r with
    | nil => simp at hne
    | cons b r =>
      obtain ⟨s, hs⟩ := (t.mem_nodes_iff _).1 hq
      rw [PhyloTree.nodeAt_append, hp] at hs
      simp [PhyloTree.nodeAt] at hs
  have h1 : movesOut F p = ∅ := Finset.filter_false_of_mem fun e he h =>
    hno e.2 (admissible_of_mem hE (hF he)).2.1 h.1
  have h2 : movesIn F p = ∅ := Finset.filter_false_of_mem fun e he h =>
    hno e.1 (admissible_of_mem hE (hF he)).1 h.1
  simp only [keptClade, h1, h2, Finset.biUnion_empty, Finset.sdiff_empty, Finset.union_empty,
    PhyloTree.taxaAt_eq hp]
  simp [PhyloTree.taxa, PhyloTree.labels]

/-- **The clade below a recipient.** For a pair `e₀ ∈ E`, the wire above its recipient end `w`
brings, below its recipient vertex, the clade of `w` in `T`: the kept added edges move subtrees
of `T_w` only inside `T_w`. -/
theorem recipient_clade (ht : t.WellLabelled) (hE : EdgeAbove.CycleSeparated t E) (hF : F ⊆ E)
    {e₀ : Pair} (he₀ : e₀ ∈ E) :
    keptClade t F e₀.2 ∪ donorTaxa t F e₀.2 = t.taxaAt e₀.2 := by
  have hn : e₀.2 ∈ t.nodes := (admissible_of_mem hE he₀).2.1
  have hF2 : ∀ e ∈ F, e.2 ∈ t.nodes := fun e he => (admissible_of_mem hE (hF he)).2.1
  ext a
  by_cases ha : a ∈ t.taxa
  · rw [Finset.mem_union, mem_keptClade ht hF2 hn ha, mem_donorTaxa ht hF2 ha,
      mem_taxaAt_of_mem (ht := ht) hn ha]
    constructor
    · rintro ((⟨h, -⟩ | ⟨e, he, h1, h2, hel⟩) | ⟨e, he, h1, hel⟩)
      · exact h
      · exfalso
        have h3 := recipient_cone_closed_pairs hE he₀ (hF he) h1.1
        have heq : e₀.2 = e.2 := by
          by_contra hne
          exact h2 ⟨h3, hne⟩
        obtain rfl := eq_of_recipient_eq hE he₀ (hF he) heq
        exact (admissible_of_mem hE he₀).2.2.2.2 h1.1
      · have hg := donor_eq_recipient_ghost hE he₀ (hF he) h1
        rw [h1] at hg
        exact hg.trans hel
    · intro h
      by_cases hX : ∃ e ∈ F, (e₀.2 <+: e.2 ∧ e₀.2 ≠ e.2) ∧ ¬(e₀.2 <+: e.1 ∧ e₀.2 ≠ e.1) ∧
          e.2 <+: leafAddress t a
      · obtain ⟨e, he, h1, h2, hel⟩ := hX
        have h3 := recipient_inside hE he₀ (hF he) h1.1 h1.2
        have h4 : e.1 = e₀.2 := by
          by_contra hne
          exact h2 ⟨h3, fun h' => hne h'.symm⟩
        exact Or.inr ⟨e, he, h4, hel⟩
      · exact Or.inl (Or.inl ⟨h, fun e he h1 h2 hel => hX ⟨e, he, h1, h2, hel⟩⟩)
  · have h1 : a ∉ keptClade t F e₀.2 := fun h => ha (keptClade_subset_taxa _ h)
    have h2 : a ∉ donorTaxa t F e₀.2 := fun h => ha (donorTaxa_subset_taxa _ h)
    have h3 : a ∉ t.taxaAt e₀.2 := fun h => ha (PhyloTree.taxaAt_subset t _ h)
    simp only [Finset.mem_union, h1, h2, h3, or_self]


/-! ### The wires of the canonical network -/

theorem wireEdges_cons_of_ne_nil (a : ℕ) {L : List ℕ} (hL : L ≠ []) :
    wireEdges (a :: L) = insert (a, L.headD 0) (wireEdges L) := by
  cases L with
  | nil => exact absurd rfl hL
  | cons b L => rw [wireEdges_cons_cons]; rfl

/-- On a path without repetition, the edge out of `v` goes to the vertex after `v`. -/
theorem mem_wireEdges_iff_of_nodup {A B : List ℕ} {v x : ℕ} (h : (A ++ v :: B).Nodup) :
    (v, x) ∈ wireEdges (A ++ v :: B) ↔ B ≠ [] ∧ x = B.headD 0 := by
  induction A with
  | nil =>
    cases B with
    | nil => simp [wireEdges]
    | cons b B =>
      simp only [List.nil_append] at h ⊢
      rw [wireEdges_cons_cons, Finset.mem_insert]
      constructor
      · rintro (h' | h')
        · simp only [Prod.mk.injEq] at h'
          exact ⟨List.cons_ne_nil _ _, h'.2⟩
        · exact absurd (edge_first_mem h') (List.nodup_cons.1 h).1
      · rintro ⟨-, rfl⟩
        exact Or.inl rfl
  | cons a A ih =>
    have hne : A ++ v :: B ≠ [] := by simp
    rw [List.cons_append, wireEdges_cons_of_ne_nil a hne, Finset.mem_insert]
    have hav : a ≠ v := fun hav => (List.nodup_cons.1 h).1 (by rw [hav]; simp)
    constructor
    · rintro (h' | h')
      · exact absurd (congrArg Prod.fst h').symm hav
      · exact (ih (List.nodup_cons.1 h).2).1 h'
    · intro h'
      exact Or.inr ((ih (List.nodup_cons.1 h).2).2 h')

/-- The first vertex below the upper end of the wire above `c`: its outer endpoint, or else its
ghost donor, or else `c` itself. -/
noncomputable def firstBelow (t : PhyloTree) (E : Finset Pair) (c : Address) : ℕ :=
  (outerEndpoints t E c ++ ghostEndpoints t E c ++ [Address.code c]).headD 0

/-- The vertex after the outer endpoint of the wire above `c`: its ghost donor, or else `c`. -/
noncomputable def afterOuter (t : PhyloTree) (E : Finset Pair) (c : Address) : ℕ :=
  (ghostEndpoints t E c ++ [Address.code c]).headD 0

theorem wire_eq (t : PhyloTree) (E : Finset Pair) (c : Address) :
    wire t E c = [] ++ Address.code (parent c) ::
      (outerEndpoints t E c ++ ghostEndpoints t E c ++ [Address.code c]) := by
  simp [wire, List.append_assoc]

/-- The support edges out of a vertex `p` of `T` go to the first vertices below the upper ends of
the wires above its children. -/
theorem mem_support_code {p : Address} (hE : E ⊆ EdgeAbove.candidates t) (hp : p ∈ t.nodes)
    {x : ℕ} : (Address.code p, x) ∈ supportEdges t E ↔
      ∃ c ∈ t.nodes, c ≠ [] ∧ parent c = p ∧ x = firstBelow t E c := by
  constructor
  · intro h
    obtain ⟨c, hc, hcx⟩ := Finset.mem_biUnion.mp h
    obtain ⟨hc0, hc⟩ := Finset.mem_erase.mp hc
    have hpc : p = parent c :=
      (mem_code_dropLast_iff hp).1 (edge_first_mem_dropLast hcx)
    refine ⟨c, hc, hc0, hpc.symm, ?_⟩
    have hnd := wire_nodup t E hE hc hc0
    rw [wire_eq, ← hpc] at hcx hnd
    exact ((mem_wireEdges_iff_of_nodup hnd).1 hcx).2
  · rintro ⟨c, hc, hc0, rfl, rfl⟩
    refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_erase.mpr ⟨hc0, hc⟩, ?_⟩
    have hnd := wire_nodup t E hE hc hc0
    rw [wire_eq] at hnd ⊢
    exact (mem_wireEdges_iff_of_nodup hnd).2 ⟨by simp, rfl⟩

/-- The support edge out of the outer endpoint of the wire above `c` goes to the vertex after it.
-/
theorem mem_support_outer (hE : EdgeAbove.CycleSeparated t E) {c : Address} (hc : c ∈ t.nodes)
    (hc0 : c ≠ []) {v : ℕ} (hv : v ∈ outerEndpoints t E c) {x : ℕ} :
    (v, x) ∈ supportEdges t E ↔ x = afterOuter t E c := by
  have hint : v ∈ wireInterior (wire t E c) := by
    rw [wireInterior_eq]
    exact List.mem_toFinset.2 (List.mem_append_left _ hv)
  have h := congrArg (fun S => (v, x) ∈ S) (support_outgoing_eq_wire t E hE.1 hc hc0 hint)
  simp only [Finset.mem_filter, and_true] at h
  rw [h]
  have hw : wire t E c = [Address.code (parent c)] ++ v ::
      (ghostEndpoints t E c ++ [Address.code c]) := by
    simp [wire, outerEndpoints_eq_singleton hE hv]
  have hnd := wire_nodup t E hE.1 hc hc0
  rw [hw] at hnd ⊢
  rw [mem_wireEdges_iff_of_nodup hnd]
  simp [afterOuter]

/-- The support edge out of the ghost donor of the wire above `c` goes to `c`. -/
theorem mem_support_ghost (hE : EdgeAbove.CycleSeparated t E) {c : Address} (hc : c ∈ t.nodes)
    (hc0 : c ≠ []) {v : ℕ} (hv : v ∈ ghostEndpoints t E c) {x : ℕ} :
    (v, x) ∈ supportEdges t E ↔ x = Address.code c := by
  have hint : v ∈ wireInterior (wire t E c) := by
    rw [wireInterior_eq]
    exact List.mem_toFinset.2 (List.mem_append_right _ hv)
  have h := congrArg (fun S => (v, x) ∈ S) (support_outgoing_eq_wire t E hE.1 hc hc0 hint)
  simp only [Finset.mem_filter, and_true] at h
  rw [h]
  have hw : wire t E c = ([Address.code (parent c)] ++ outerEndpoints t E c) ++ v ::
      [Address.code c] := by
    simp [wire, ghostEndpoints_eq_singleton hE hv]
  have hnd := wire_nodup t E hE.1 hc hc0
  rw [hw] at hnd ⊢
  rw [mem_wireEdges_iff_of_nodup hnd]
  simp

theorem mem_keptSwitching {v x : ℕ} :
    (v, x) ∈ keptSwitching t E F ↔
      ((v, x) ∈ supportEdges t E ∧ ∀ e ∈ F, x ≠ recipient t e) ∨
        ∃ e ∈ F, donor t e = v ∧ recipient t e = x := by
  simp only [keptSwitching, Finset.mem_union, Finset.mem_filter, Finset.mem_image,
    Prod.mk.injEq]


/-- The taxa that the kept added edges of the ghost donors at `c` bring. -/
def ghostTaxa (t : PhyloTree) (F : Finset Pair) (c : Address) : Finset ℕ :=
  (F.filter fun e => e.1 = c ∧ EdgeAbove.target e = c).biUnion fun e => t.taxaAt e.2

theorem headD_mem_append (L : List ℕ) (x d : ℕ) : (L ++ [x]).headD d ∈ L ++ [x] := by
  cases L <;> simp

/-- The first vertex below the upper end of the wire above `c` is a recipient of a kept added
edge iff a kept added edge enters this wire. -/
theorem firstBelow_recipient_iff (hE : EdgeAbove.CycleSeparated t E) (hF : F ⊆ E)
    {c : Address} (hc : c ∈ t.nodes) :
    (∃ e ∈ F, firstBelow t E c = recipient t e) ↔ ∃ e ∈ F, e.2 = c := by
  constructor
  · rintro ⟨e, he, h⟩
    have hmem : firstBelow t E c ∈ outerEndpoints t E c ++ ghostEndpoints t E c ++
        [Address.code c] := headD_mem_append _ _ _
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with (hmem | hmem) | hmem
    · obtain ⟨f, hf, ⟨-, -, hd⟩ | ⟨hf2, hr⟩⟩ := mem_outerEndpoints.mp hmem
      · exact absurd (hd.symm.trans h) (donor_ne_recipient t f e)
      · have := recipient_injective t (hE.1 hf) (hE.1 (hF he)) (hr.symm.trans h)
        subst this
        exact ⟨f, he, hf2⟩
    · obtain ⟨f, -, -, -, hd⟩ := mem_ghostEndpoints.mp hmem
      exact absurd (hd.symm.trans h) (donor_ne_recipient t f e)
    · exact absurd (hmem.symm.trans h).symm (recipient_ne_code e hc)
  · rintro ⟨e, he, rfl⟩
    have hmem : recipient t e ∈ outerEndpoints t E e.2 :=
      mem_outerEndpoints.mpr ⟨e, hF he, Or.inr ⟨rfl, rfl⟩⟩
    refine ⟨e, he, ?_⟩
    simp [firstBelow, outerEndpoints_eq_singleton hE hmem]

/-- The kept added edge out of the donor `v` of the wire above `c`: its pair has donor end `c`. -/
theorem donor_end_of_mem {c : Address} {e : Pair} (hE : EdgeAbove.CycleSeparated t E)
    (hF : F ⊆ E) (he : e ∈ F) {v : ℕ} (hv : v ∈ outerEndpoints t E c ++ ghostEndpoints t E c)
    (hd : donor t e = v) : e.1 = c := by
  rcases List.mem_append.1 hv with hv | hv
  · obtain ⟨f, hf, ⟨hf1, -, hd'⟩ | ⟨-, hr⟩⟩ := mem_outerEndpoints.mp hv
    · rw [donor_injective t (hE.1 (hF he)) (hE.1 hf) (hd.trans hd')]
      exact hf1
    · exact absurd (hd.trans hr) (donor_ne_recipient t e f)
  · obtain ⟨f, hf, hf1, -, hd'⟩ := mem_ghostEndpoints.mp hv
    rw [donor_injective t (hE.1 (hF he)) (hE.1 hf) (hd.trans hd')]
    exact hf1

/-- The taxa of the graph whose leaf is a fresh vertex: none. -/
theorem leaf_ne_fresh {c : Address} {v : ℕ}
    (hv : v ∈ outerEndpoints t E c ++ ghostEndpoints t E c) {a : ℕ} (ha : a ∈ t.taxa) :
    (graph t E).leaf a ≠ v := by
  intro h
  change Address.code (leafAddress t a) = v at h
  have hl := leafAddress_mem_nodes ha
  rcases List.mem_append.1 hv with hv | hv
  · obtain ⟨f, -, ⟨-, -, hd⟩ | ⟨-, hr⟩⟩ := mem_outerEndpoints.mp hv
    · exact donor_ne_code f hl (hd.symm.trans h.symm)
    · exact recipient_ne_code f hl (hr.symm.trans h.symm)
  · obtain ⟨f, -, -, -, hd⟩ := mem_ghostEndpoints.mp hv
    exact donor_ne_code f hl (hd.symm.trans h.symm)

/-- The claim of `Realization.cladeBelow_keptSwitching` at one vertex `v`. -/
def KeptCladeClaim (t : PhyloTree) (E F : Finset Pair) (v : ℕ) : Prop :=
  (∀ p ∈ t.nodes, Address.code p = v →
    (graph t E).cladeBelow (keptSwitching t E F) v = keptClade t F p) ∧
  (∀ c ∈ t.nodes, c ≠ [] → v ∈ outerEndpoints t E c →
    (graph t E).cladeBelow (keptSwitching t E F) v = keptClade t F c ∪ donorTaxa t F c) ∧
  (∀ c ∈ t.nodes, c ≠ [] → v ∈ ghostEndpoints t E c →
    (graph t E).cladeBelow (keptSwitching t E F) v = keptClade t F c ∪ ghostTaxa t F c)

/-- From the claims at the vertices below the upper end of the wire above `c`, the clade below the
first of them. -/
theorem cladeBelow_firstBelow (hF : F ⊆ E) {c : Address}
    (hc : c ∈ t.nodes) (hc0 : c ≠ []) (h : KeptCladeClaim t E F (firstBelow t E c)) :
    (graph t E).cladeBelow (keptSwitching t E F) (firstBelow t E c) =
      keptClade t F c ∪ donorTaxa t F c := by
  rcases ho : outerEndpoints t E c with _ | ⟨w, L⟩
  · rcases hg : ghostEndpoints t E c with _ | ⟨g, L'⟩
    · -- no fresh vertex: the first vertex is `c`, and no pair has donor end `c`
      have hfb : firstBelow t E c = Address.code c := by simp [firstBelow, ho, hg]
      rw [h.1 c hc hfb.symm]
      have hd : donorTaxa t F c = ∅ := by
        ext a
        simp only [donorTaxa, Finset.mem_biUnion, Finset.mem_filter, Finset.notMem_empty,
          iff_false]
        rintro ⟨e, ⟨he, he1⟩, -⟩
        by_cases hg' : EdgeAbove.target e = c
        · have := (mem_ghostEndpoints (t := t)).mpr ⟨e, hF he, he1, hg', rfl⟩
          rw [hg] at this
          simp at this
        · have := (mem_outerEndpoints (t := t)).mpr ⟨e, hF he, Or.inl ⟨he1, hg', rfl⟩⟩
          rw [ho] at this
          simp at this
      rw [hd, Finset.union_empty]
    · -- the first vertex is the ghost donor; no pair has a non-ghost donor at `c`
      have hgm : g ∈ ghostEndpoints t E c := by rw [hg]; simp
      have hfb : firstBelow t E c = g := by simp [firstBelow, ho, hg]
      rw [hfb] at h ⊢
      rw [h.2.2 c hc hc0 hgm]
      congr 1
      unfold ghostTaxa donorTaxa
      congr 1
      refine Finset.filter_congr fun e he => ⟨fun h1 => h1.1, fun h1 => ⟨h1, ?_⟩⟩
      by_contra hg'
      have := (mem_outerEndpoints (t := t)).mpr ⟨e, hF he, Or.inl ⟨h1, hg', rfl⟩⟩
      rw [ho] at this
      simp at this
  · have hwm : w ∈ outerEndpoints t E c := by rw [ho]; simp
    have hfb : firstBelow t E c = w := by simp [firstBelow, ho]
    rw [hfb] at h ⊢
    exact h.2.1 c hc hc0 hwm


/-- From the claims at the vertex after the outer endpoint of the wire above `c`, the clade below
it. -/
theorem cladeBelow_afterOuter (hF : F ⊆ E) {c : Address} (hc : c ∈ t.nodes) (hc0 : c ≠ [])
    (h : KeptCladeClaim t E F (afterOuter t E c)) :
    (graph t E).cladeBelow (keptSwitching t E F) (afterOuter t E c) =
      keptClade t F c ∪ ghostTaxa t F c := by
  rcases hg : ghostEndpoints t E c with _ | ⟨g, L'⟩
  · have hfb : afterOuter t E c = Address.code c := by simp [afterOuter, hg]
    rw [h.1 c hc hfb.symm]
    have hd : ghostTaxa t F c = ∅ := by
      ext a
      simp only [ghostTaxa, Finset.mem_biUnion, Finset.mem_filter, Finset.notMem_empty,
        iff_false]
      rintro ⟨e, ⟨he, he1, hg'⟩, -⟩
      have := (mem_ghostEndpoints (t := t)).mpr ⟨e, hF he, he1, hg', rfl⟩
      rw [hg] at this
      simp at this
    rw [hd, Finset.union_empty]
  · have hgm : g ∈ ghostEndpoints t E c := by rw [hg]; simp
    have hfb : afterOuter t E c = g := by simp [afterOuter, hg]
    rw [hfb] at h ⊢
    exact h.2.2 c hc hc0 hgm

/-- **The clades of the switching that keeps the added edges of `F`.** In
`Realization.graph t E`, with the switching `Realization.keptSwitching t E F`, the clade below
the vertex of `T` at `p` is `keptClade t F p`; below the outer endpoint of the wire above `c` it is
`keptClade t F c ∪ donorTaxa t F c`, and below its ghost donor `keptClade t F c ∪ ghostTaxa t F c`.
-/
theorem cladeBelow_keptSwitching (ht : t.WellLabelled) (hE : EdgeAbove.CycleSeparated t E)
    (hF : F ⊆ E) (v : ℕ) : KeptCladeClaim t E F v := by
  have hG := levelOne t ht E hE
  have hSG : keptSwitching t E F ⊆ (graph t E).edges := keptSwitching_subset hF
  induction h : (graph t E).reachCount (keptSwitching t E F) v using Nat.strong_induction_on
    generalizing v with
  | _ n ih =>
  -- the claims hold at the children of `v`
  have hch : ∀ y, (v, y) ∈ keptSwitching t E F → KeptCladeClaim t E F y := fun y hy =>
    ih _ (h ▸ RootedNetwork.reachCount_lt hG hSG hy) y rfl
  -- below the recipient of a kept added edge lies the clade of its recipient end
  have hrec : ∀ e ∈ F, (v, recipient t e) ∈ keptSwitching t E F →
      (graph t E).cladeBelow (keptSwitching t E F) (recipient t e) = t.taxaAt e.2 := by
    intro e he hy
    have hmem : recipient t e ∈ outerEndpoints t E e.2 :=
      mem_outerEndpoints.mpr ⟨e, hF he, Or.inr ⟨rfl, rfl⟩⟩
    have ha := admissible_of_mem hE (hF he)
    rw [(hch _ hy).2.1 e.2 ha.2.1 ha.2.2.2.1 hmem]
    exact recipient_clade ht hE hF (hF he)
  refine ⟨?_, ?_, ?_⟩
  -- a vertex `p` of `T`
  · rintro p hp rfl
    obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff p).1 hp
    rw [RootedNetwork.cladeBelow_eq_children]
    cases sub with
    | leaf a₀ =>
      -- a leaf: its taxon, and no child
      rw [keptClade_leaf hE hF hsub]
      have hnc : ∀ y, (Address.code p, y) ∉ keptSwitching t E F := by
        intro y hy
        rcases mem_keptSwitching.1 hy with ⟨hy, -⟩ | ⟨e, -, hd, -⟩
        · obtain ⟨c, hc, hc0, hcp, -⟩ := (mem_support_code hE.1 hp).1 hy
          obtain ⟨sc, hsc⟩ := (t.mem_nodes_iff c).1 hc
          rcases (parent_eq_iff hc0).1 hcp with rfl | rfl <;>
          · rw [PhyloTree.nodeAt_append, hsub] at hsc
            simp [PhyloTree.nodeAt] at hsc
        · exact donor_ne_code e hp hd
      ext a
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_singleton]
      constructor
      · rintro (⟨ha, hla⟩ | ⟨x, ⟨hx, hx1⟩, -⟩)
        · change Address.code (leafAddress t a) = Address.code p at hla
          have hl := Address.code_injective hla
          have h' := leafAddress_nodeAt ha
          rw [hl, hsub] at h'
          simpa using h'.symm
        · obtain ⟨x1, x2⟩ := x
          simp only at hx1
          subst hx1
          exact absurd hx (hnc x2)
      · intro haa
        subst haa
        refine Or.inl ⟨?_, ?_⟩
        · exact List.mem_toFinset.2 (PhyloTree.leaf_label_mem hsub)
        · change Address.code (leafAddress t a) = Address.code p
          rw [leafAddress_eq ht hsub]
    | fork l r =>
      -- an internal vertex: the wires above its two children
      rw [keptClade_fork ht hE hF hsub]
      ext a
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion]
      have hnl : ¬(a ∈ (graph t E).taxa ∧ (graph t E).leaf a = Address.code p) := by
        rintro ⟨ha, hla⟩
        change Address.code (leafAddress t a) = Address.code p at hla
        have h' := leafAddress_nodeAt ha
        rw [Address.code_injective hla, hsub] at h'
        cases h'
      simp only [hnl, false_or]
      constructor
      · rintro ⟨⟨x1, y⟩, ⟨hx, hx1⟩, hay⟩
        simp only at hx1 hay
        subst hx1
        rcases mem_keptSwitching.1 hx with ⟨hy, hnr⟩ | ⟨e, -, hd, -⟩
        · obtain ⟨c, hc, hc0, hcp, rfl⟩ := (mem_support_code hE.1 hp).1 hy
          have hcut : ¬∃ e ∈ F, e.2 = c := fun hc' => by
            obtain ⟨e, he, h'⟩ := (firstBelow_recipient_iff hE hF hc).2 hc'
            exact hnr e he h'
          rw [cladeBelow_firstBelow hF hc hc0 (hch _ hx)] at hay
          rcases (parent_eq_iff hc0).1 hcp with rfl | rfl
          · exact Or.inl (mem_wireTaxa.2 ⟨hcut, Finset.mem_union.1 hay⟩)
          · exact Or.inr (mem_wireTaxa.2 ⟨hcut, Finset.mem_union.1 hay⟩)
        · exact absurd hd (donor_ne_code e hp)
      · intro ha
        obtain ⟨b, hb⟩ : ∃ b : Bool, a ∈ wireTaxa t F (p ++ [b]) := by
          rcases ha with ha | ha
          · exact ⟨false, ha⟩
          · exact ⟨true, ha⟩
        obtain ⟨hcut, hab⟩ := mem_wireTaxa.1 hb
        have hc : p ++ [b] ∈ t.nodes := (t.mem_nodes_iff _).2
          ⟨if b then r else l, by rw [PhyloTree.nodeAt_append, hsub]; cases b <;>
            simp [PhyloTree.nodeAt]⟩
        have hc0 : p ++ [b] ≠ [] := by simp
        have hx : (Address.code p, firstBelow t E (p ++ [b])) ∈ keptSwitching t E F := by
          refine mem_keptSwitching.2 (Or.inl ⟨(mem_support_code hE.1 hp).2
            ⟨p ++ [b], hc, hc0, parent_append_singleton p b, rfl⟩, fun e he h' => ?_⟩)
          exact hcut ((firstBelow_recipient_iff hE hF hc).1 ⟨e, he, h'⟩)
        refine ⟨_, ⟨hx, rfl⟩, ?_⟩
        rw [cladeBelow_firstBelow hF hc hc0 (hch _ hx)]
        exact Finset.mem_union.2 hab
  -- the outer endpoint of the wire above `c`
  · intro c hc hc0 hv
    have hvm : v ∈ outerEndpoints t E c ++ ghostEndpoints t E c := List.mem_append_left _ hv
    rw [RootedNetwork.cladeBelow_eq_children]
    ext a
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion]
    have hnl : ¬(a ∈ (graph t E).taxa ∧ (graph t E).leaf a = v) :=
      fun h' => leaf_ne_fresh hvm h'.1 h'.2
    simp only [hnl, false_or]
    have hafter : (v, afterOuter t E c) ∈ keptSwitching t E F := by
      refine mem_keptSwitching.2 (Or.inl ⟨(mem_support_outer hE hc hc0 hv).2 rfl,
        fun e _ h' => ?_⟩)
      have hmem : afterOuter t E c ∈ ghostEndpoints t E c ++ [Address.code c] :=
        headD_mem_append _ _ _
      rcases List.mem_append.1 hmem with hmem | hmem
      · obtain ⟨f, -, -, -, hd⟩ := mem_ghostEndpoints.mp hmem
        exact donor_ne_recipient t f e (hd.symm.trans h')
      · exact recipient_ne_code e hc ((List.mem_singleton.1 hmem).symm.trans h').symm
    have hA := cladeBelow_afterOuter hF hc hc0 (hch _ hafter)
    constructor
    · rintro ⟨⟨x1, y⟩, ⟨hx, hx1⟩, hay⟩
      simp only at hx1 hay
      subst hx1
      rcases mem_keptSwitching.1 hx with ⟨hy, -⟩ | ⟨e, he, hd, rfl⟩
      · rw [(mem_support_outer hE hc hc0 hv).1 hy, hA] at hay
        rcases Finset.mem_union.1 hay with hay | hay
        · exact Or.inl hay
        · simp only [ghostTaxa, donorTaxa, Finset.mem_biUnion, Finset.mem_filter] at hay ⊢
          obtain ⟨e, ⟨he, he1, -⟩, hae⟩ := hay
          exact Or.inr ⟨e, ⟨he, he1⟩, hae⟩
      · rw [hrec e he hx] at hay
        simp only [donorTaxa, Finset.mem_biUnion, Finset.mem_filter]
        exact Or.inr ⟨e, ⟨he, donor_end_of_mem hE hF he hvm hd⟩, hay⟩
    · rintro (ha | ha)
      · exact ⟨_, ⟨hafter, rfl⟩, by rw [hA]; exact Finset.mem_union_left _ ha⟩
      · simp only [donorTaxa, Finset.mem_biUnion, Finset.mem_filter] at ha
        obtain ⟨e, ⟨he, he1⟩, hae⟩ := ha
        by_cases hg' : EdgeAbove.target e = c
        · refine ⟨_, ⟨hafter, rfl⟩, ?_⟩
          rw [hA]
          simp only [ghostTaxa, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
          exact Or.inr ⟨e, ⟨he, he1, hg'⟩, hae⟩
        · have hdm : donor t e ∈ outerEndpoints t E c :=
            mem_outerEndpoints.mpr ⟨e, hF he, Or.inl ⟨he1, hg', rfl⟩⟩
          have hdv : donor t e = v := by
            have := outerEndpoints_eq_singleton hE hv
            rw [this] at hdm
            exact List.mem_singleton.1 hdm
          have hx : (v, recipient t e) ∈ keptSwitching t E F :=
            mem_keptSwitching.2 (Or.inr ⟨e, he, hdv, rfl⟩)
          exact ⟨_, ⟨hx, rfl⟩, by rw [hrec e he hx]; exact hae⟩
  -- the ghost donor of the wire above `c`
  · intro c hc hc0 hv
    have hvm : v ∈ outerEndpoints t E c ++ ghostEndpoints t E c := List.mem_append_right _ hv
    obtain ⟨e₂, he₂, he₂1, he₂t, rfl⟩ := mem_ghostEndpoints.mp hv
    rw [RootedNetwork.cladeBelow_eq_children]
    ext a
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion]
    have hnl : ¬(a ∈ (graph t E).taxa ∧ (graph t E).leaf a = donor t e₂) :=
      fun h' => leaf_ne_fresh hvm h'.1 h'.2
    simp only [hnl, false_or]
    have hcode : (donor t e₂, Address.code c) ∈ keptSwitching t E F :=
      mem_keptSwitching.2 (Or.inl ⟨(mem_support_ghost hE hc hc0 hv).2 rfl,
        fun e _ h' => recipient_ne_code e hc h'.symm⟩)
    have hC := (hch _ hcode).1 c hc rfl
    constructor
    · rintro ⟨⟨x1, y⟩, ⟨hx, hx1⟩, hay⟩
      simp only at hx1 hay
      subst hx1
      rcases mem_keptSwitching.1 hx with ⟨hy, -⟩ | ⟨e, he, hd, rfl⟩
      · rw [(mem_support_ghost hE hc hc0 hv).1 hy, hC] at hay
        exact Or.inl hay
      · rw [hrec e he hx] at hay
        have hee : e = e₂ := donor_injective t (hE.1 (hF he)) (hE.1 he₂) hd
        subst hee
        simp only [ghostTaxa, Finset.mem_biUnion, Finset.mem_filter]
        exact Or.inr ⟨e, ⟨he, he₂1, he₂t⟩, hay⟩
    · rintro (ha | ha)
      · exact ⟨_, ⟨hcode, rfl⟩, by rw [hC]; exact ha⟩
      · simp only [ghostTaxa, Finset.mem_biUnion, Finset.mem_filter] at ha
        obtain ⟨e, ⟨he, he1, het⟩, hae⟩ := ha
        have hee : e = e₂ := by
          have hdm := (mem_ghostEndpoints (t := t)).mpr ⟨e, hF he, he1, het, rfl⟩
          rw [ghostEndpoints_eq_singleton hE hv] at hdm
          exact donor_injective t (hE.1 (hF he)) (hE.1 he₂) (List.mem_singleton.1 hdm)
        subst hee
        have hx : (donor t e, recipient t e) ∈ keptSwitching t E F :=
          mem_keptSwitching.2 (Or.inr ⟨e, he, rfl, rfl⟩)
        exact ⟨_, ⟨hx, rfl⟩, by rw [hrec e he hx]; exact hae⟩


/-! ### The family of the clades and the switchings of the canonical network -/

/-- The clades of the tree of the switching that keeps the added edges of `F`, when no pair has a
ghost donor: the clades of the vertices of `T`, and for each kept added edge the clade of its
donor vertex, the clade of its donor end together with the subtree moved below it. -/
def keptClades (t : PhyloTree) (F : Finset Pair) : Finset (Finset ℕ) :=
  t.nodes.image (keptClade t F) ∪ F.image fun e => keptClade t F e.1 ∪ t.taxaAt e.2

/-- With no ghost donor, the taxa brought to the wire above the donor end of a kept added edge
are the subtree of its recipient end. -/
theorem donorTaxa_of_mem (hE : EdgeAbove.CycleSeparated t E) (hF : F ⊆ E)
    (hng : ∀ e ∈ E, ¬e.1 <+: e.2) {e : Pair} (he : e ∈ F) :
    donorTaxa t F e.1 = t.taxaAt e.2 := by
  have hu : ∀ f ∈ F, f.1 = e.1 → f = e := by
    intro f hf hfe
    have hdf : donor t f ∈ outerEndpoints t E e.1 := mem_outerEndpoints.mpr
      ⟨f, hF hf, Or.inl ⟨hfe, fun h => hng f (hF hf) (hfe ▸ h ▸ lca_prefix_right f.1 f.2), rfl⟩⟩
    have hde : donor t e ∈ outerEndpoints t E e.1 := mem_outerEndpoints.mpr
      ⟨e, hF he, Or.inl ⟨rfl, fun h => hng e (hF he) (h ▸ lca_prefix_right e.1 e.2), rfl⟩⟩
    exact donor_injective t (hE.1 (hF hf)) (hE.1 (hF he)) (outerEndpoints_mem_unique hE hdf hde)
  ext a
  simp only [donorTaxa, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨f, ⟨hf, hfe⟩, ha⟩
    rw [← hu f hf hfe]
    exact ha
  · exact fun ha => ⟨e, ⟨he, rfl⟩, ha⟩

/-- **The clades of the tree of the switching that keeps the added edges of `F`.** For a
cycle-separated family `E` without ghost donors and `F ⊆ E`, the sets of taxa below the vertices
of `Realization.graph t E` in `Realization.keptSwitching t E F` are `Realization.keptClades t F`.
-/
theorem image_cladeBelow_keptSwitching (ht : t.WellLabelled) (hE : EdgeAbove.CycleSeparated t E)
    (hF : F ⊆ E) (hng : ∀ e ∈ E, ¬e.1 <+: e.2) :
    (graph t E).vertices.image ((graph t E).cladeBelow (keptSwitching t E F)) =
      keptClades t F := by
  have hnog : ∀ c, ghostEndpoints t E c = [] := by
    intro c
    apply List.eq_nil_iff_forall_not_mem.2
    intro v hv
    obtain ⟨e, he, he1, het, -⟩ := mem_ghostEndpoints.mp hv
    exact hng e he (he1 ▸ het ▸ lca_prefix_right e.1 e.2)
  have hcl := cladeBelow_keptSwitching (F := F) ht hE hF
  ext C
  simp only [Finset.mem_image, keptClades, Finset.mem_union]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [vertices_covered t E hE.1] at hv
    rcases Finset.mem_union.1 hv with hv | hv
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv
      exact Or.inl ⟨p, hp, ((hcl _).1 p hp rfl).symm⟩
    · obtain ⟨c, hc, hv⟩ := Finset.mem_biUnion.1 hv
      obtain ⟨hc0, hc⟩ := Finset.mem_erase.1 hc
      rw [wireInterior_eq, hnog, List.append_nil, List.mem_toFinset] at hv
      rw [(hcl v).2.1 c hc hc0 hv]
      by_cases hd : ∃ e ∈ F, e.1 = c
      · obtain ⟨e, he, rfl⟩ := hd
        exact Or.inr ⟨e, he, by rw [donorTaxa_of_mem hE hF hng he]⟩
      · have hd' : donorTaxa t F c = ∅ := by
          ext a
          simp only [donorTaxa, Finset.mem_biUnion, Finset.mem_filter, Finset.notMem_empty,
            iff_false]
          rintro ⟨e, ⟨he, he1⟩, -⟩
          exact hd ⟨e, he, he1⟩
        exact Or.inl ⟨c, hc, by rw [hd', Finset.union_empty]⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨e, he, rfl⟩)
    · refine ⟨Address.code p, ?_, (hcl _).1 p hp rfl⟩
      rw [vertices_covered t E hE.1]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)
    · have ha := admissible_of_mem hE (hF he)
      have hdm : donor t e ∈ outerEndpoints t E e.1 := mem_outerEndpoints.mpr
        ⟨e, hF he, Or.inl ⟨rfl, fun h => hng e (hF he) (h ▸ lca_prefix_right e.1 e.2), rfl⟩⟩
      refine ⟨donor t e, ?_, ?_⟩
      · rw [vertices_covered t E hE.1]
        refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨e.1,
          Finset.mem_erase.2 ⟨ha.2.2.1, ha.1⟩, ?_⟩)
        rw [wireInterior_eq]
        exact List.mem_toFinset.2 (List.mem_append_left _ hdm)
      · rw [(hcl _).2.1 e.1 ha.1 ha.2.2.1 hdm, donorTaxa_of_mem hE hF hng he]

/-- **Every switching keeps a set of added edges.** A switching `S` of `Realization.graph t E` is
`Realization.keptSwitching t E F` for the set `F` of the pairs whose added edge is in `S`. -/
theorem switching_eq_keptSwitching (ht : t.WellLabelled) (hE : EdgeAbove.CycleSeparated t E)
    {S : Finset (ℕ × ℕ)} (hS : (graph t E).Switching S) :
    S = keptSwitching t E (E.filter fun e => (donor t e, recipient t e) ∈ S) := by
  have hG := levelOne t ht E hE
  have hSu := support_switching t E hE.1
  ext ⟨x, y⟩
  rw [mem_keptSwitching]
  simp only [Finset.mem_filter]
  constructor
  · intro hxy
    rcases Finset.mem_union.1 (hS.1 hxy) with hsup | hadd
    · refine Or.inl ⟨hsup, fun e ⟨he, heS⟩ hye => ?_⟩
      subst hye
      have hxe := hS.eq_of_edge hG hxy heS
      subst hxe
      exact added_edge_not_support hE.1 he hsup
    · obtain ⟨e, he, hxe⟩ := Finset.mem_image.1 hadd
      simp only [Prod.mk.injEq] at hxe
      obtain ⟨rfl, rfl⟩ := hxe
      exact Or.inr ⟨e, ⟨he, hxy⟩, rfl, rfl⟩
  · rintro (⟨hsup, hnr⟩ | ⟨e, ⟨-, heS⟩, rfl, rfl⟩)
    · have hyV : y ∈ (graph t E).vertices := (hG.2.1 _ (Finset.mem_union_left _ hsup)).2
      have hyr : y ≠ (graph t E).root := by
        intro h
        have h0 := support_root_incoming_empty t E
        have hmem : (x, y) ∈ (supportEdges t E).filter (fun e => e.2 = Address.code []) :=
          Finset.mem_filter.2 ⟨hsup, h⟩
        rw [h0] at hmem
        simp at hmem
      obtain ⟨z, hz⟩ := Finset.card_eq_one.1 (hS.2 y hyV hyr)
      have hzF : z ∈ S.filter (fun e => e.2 = y) := by rw [hz]; exact Finset.mem_singleton_self z
      obtain ⟨hzS, hz2⟩ := Finset.mem_filter.1 hzF
      clear hzF hz
      obtain ⟨z1, z2⟩ := z
      simp only at hz2
      subst hz2
      rcases Finset.mem_union.1 (hS.1 hzS) with hzs | hza
      · have hzx := hSu.eq_of_edge hG hzs hsup
        subst hzx
        exact hzS
      · obtain ⟨e, he, hze⟩ := Finset.mem_image.1 hza
        simp only [Prod.mk.injEq] at hze
        obtain ⟨rfl, rfl⟩ := hze
        exact absurd rfl (hnr e ⟨he, hzS⟩)
    · exact heS

end Realization

end Camus
