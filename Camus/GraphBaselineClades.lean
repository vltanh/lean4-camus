module

public import Camus.GraphBaselineCuts
public import Camus.GraphInvarianceRename

@[expose] public section

namespace Camus.PhyloTree

theorem subtree_taxa_subset {t sub : PhyloTree} {p : Address}
    (hp : t.nodeAt p = some sub) : sub.taxa ⊆ t.taxa := by
  induction t generalizing p with
  | leaf a =>
    cases p with
    | nil => simp only [nodeAt, Option.some.injEq] at hp; subst sub; exact Finset.Subset.refl _
    | cons b p => simp [nodeAt] at hp
  | fork l r ihl ihr =>
    cases p with
    | nil => simp only [nodeAt, Option.some.injEq] at hp; subst sub; exact Finset.Subset.refl _
    | cons b p =>
      cases b
      · intro a ha
        have hl := ihl hp ha
        simp only [taxa, labels, List.toFinset_append]
        exact Finset.mem_union_left _ hl
      · intro a ha
        have hr := ihr hp ha
        simp only [taxa, labels, List.toFinset_append]
        exact Finset.mem_union_right _ hr

theorem clades_mem_iff (t : PhyloTree) (S : Finset ℕ) :
    S ∈ t.clades ↔ ∃ p sub, t.nodeAt p = some sub ∧ sub.taxa = S := by
  induction t with
  | leaf a =>
    constructor
    · intro h
      simp only [clades, List.mem_singleton] at h
      exact ⟨[], .leaf a, rfl, by simp [taxa, labels, h]⟩
    · rintro ⟨p, sub, hp, rfl⟩
      cases p with
      | nil => simp only [nodeAt, Option.some.injEq] at hp; subst sub; simp [taxa, labels, clades]
      | cons b p => simp [nodeAt] at hp
  | fork l r ihl ihr =>
    constructor
    · intro h
      simp only [clades, List.mem_cons, List.mem_append] at h
      rcases h with h | h | h
      · exact ⟨[], .fork l r, rfl, by simp [taxa, labels, h]⟩
      · obtain ⟨p, sub, hp, hs⟩ := ihl.mp h
        exact ⟨false :: p, sub, hp, hs⟩
      · obtain ⟨p, sub, hp, hs⟩ := ihr.mp h
        exact ⟨true :: p, sub, hp, hs⟩
    · rintro ⟨p, sub, hp, rfl⟩
      cases p with
      | nil =>
        simp only [nodeAt, Option.some.injEq] at hp
        subst sub
        simp [taxa, labels, clades]
      | cons b p =>
        cases b
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihl.mpr ⟨p, sub, hp, rfl⟩))
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihr.mpr ⟨p, sub, hp, rfl⟩))

theorem subtree_taxa_iff_prefix {t sub : PhyloTree} (ht : t.WellLabelled)
    {p : Address} (hp : t.nodeAt p = some sub) {a : ℕ} (ha : a ∈ t.taxa) :
    a ∈ sub.taxa ↔ p <+: Realization.leafAddress t a := by
  constructor
  · intro hasub
    obtain ⟨q, hq⟩ := exists_leaf_address (List.mem_toFinset.mp hasub)
    have hwhole : t.nodeAt (p ++ q) = some (.leaf a) := by rw [nodeAt_append, hp]; exact hq
    rw [Realization.leafAddress_eq ht hwhole]
    exact List.prefix_append _ _
  · rintro ⟨q, heq⟩
    have hleaf := Realization.leafAddress_nodeAt ha
    rw [← heq, nodeAt_append, hp] at hleaf
    exact List.mem_toFinset.mpr (leaf_label_mem hleaf)

end Camus.PhyloTree

namespace Camus.Quartet

theorem sides_nonempty (q : Quartet) : q.sides.1.Nonempty ∧ q.sides.2.Nonempty := by
  unfold sides
  split_ifs <;> simp

theorem cutBy_not_whole (q : Quartet) (S : Finset ℕ) (hq : q.taxa ⊆ S) : q.cutBy S ≠ true := by
  intro h
  have hp : q.sides.1 ⊆ S ∧ Disjoint q.sides.2 S ∨
      q.sides.2 ⊆ S ∧ Disjoint q.sides.1 S := of_decide_eq_true h
  rcases hp with h | h
  · obtain ⟨a, ha⟩ := q.sides_nonempty.2
    exact Finset.disjoint_left.mp h.2 ha (hq (q.sides_subset_taxa.2 ha))
  · obtain ⟨a, ha⟩ := q.sides_nonempty.1
    exact Finset.disjoint_left.mp h.2 ha (hq (q.sides_subset_taxa.1 ha))

end Camus.Quartet

namespace Camus.Realization

theorem side_partition_iff {A B : Finset ℕ} (hA : A.Nonempty) (hB : B.Nonempty)
    (P : ℕ → Prop) :
    ((∀ a ∈ A, ∀ b ∈ A, P a ↔ P b) ∧
      (∀ a ∈ B, ∀ b ∈ B, P a ↔ P b) ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬(P a ↔ P b))) ↔
    ((∀ a ∈ A, P a) ∧ (∀ b ∈ B, ¬P b) ∨
      (∀ a ∈ A, ¬P a) ∧ (∀ b ∈ B, P b)) := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  constructor
  · rintro ⟨hAA, hBB, hAB⟩
    by_cases hPa : P a
    · have hPb : ¬P b := fun hPb => hAB a ha b hb ⟨fun _ => hPb, fun _ => hPa⟩
      exact Or.inl ⟨fun x hx => (hAA a ha x hx).mp hPa,
        fun x hx hPx => hPb ((hBB x hx b hb).mp hPx)⟩
    · have hPb : P b := by
        by_contra h
        exact hAB a ha b hb ⟨fun h => (hPa h).elim, fun h' => (h h').elim⟩
      exact Or.inr ⟨fun x hx hPx => hPa ((hAA x hx a ha).mp hPx),
        fun x hx => (hBB b hb x hx).mp hPb⟩
  · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩)
    · exact ⟨fun a ha b hb => ⟨fun _ => hA b hb, fun _ => hA a ha⟩,
        fun a ha b hb => ⟨fun h => (hB a ha h).elim, fun h => (hB b hb h).elim⟩,
        fun a ha b hb h => hB b hb (h.mp (hA a ha))⟩
    · exact ⟨fun a ha b hb => ⟨fun h => (hA a ha h).elim, fun h => (hA b hb h).elim⟩,
        fun a ha b hb => ⟨fun _ => hB b hb, fun _ => hB a ha⟩,
        fun a ha b hb h => hA a ha (h.mpr (hB b hb))⟩

theorem baselineCut_separates_iff {t sub : PhyloTree} (ht : t.WellLabelled)
    {p : Address} (hp : t.nodeAt p = some sub) (q : Quartet)
    (hq : q.taxa ⊆ t.taxa) :
    (graph t ∅).Separates (baselineCutGraph t p) q ↔ q.cutBy sub.taxa = true := by
  have reach (a b : ℕ) (ha : a ∈ t.taxa) (hb : b ∈ t.taxa) :
      (baselineCutGraph t p).Reachable ((graph t ∅).leaf a) ((graph t ∅).leaf b) ↔
        (a ∈ sub.taxa ↔ b ∈ sub.taxa) := by
    change (baselineCutGraph t p).Reachable (Address.code (leafAddress t a))
      (Address.code (leafAddress t b)) ↔ _
    rw [baselineCut_reachable_iff (leafAddress_mem_nodes ha) (leafAddress_mem_nodes hb),
      ← PhyloTree.subtree_taxa_iff_prefix ht hp ha, ← PhyloTree.subtree_taxa_iff_prefix ht hp hb]
  have hfirst (a : ℕ) (ha : a ∈ q.sides.1) : a ∈ t.taxa := hq (q.sides_subset_taxa.1 ha)
  have hsecond (a : ℕ) (ha : a ∈ q.sides.2) : a ∈ t.taxa := hq (q.sides_subset_taxa.2 ha)
  have hbool : q.cutBy sub.taxa = true ↔
      ((∀ a ∈ q.sides.1, a ∈ sub.taxa) ∧ (∀ b ∈ q.sides.2, b ∉ sub.taxa) ∨
        (∀ a ∈ q.sides.1, a ∉ sub.taxa) ∧ (∀ b ∈ q.sides.2, b ∈ sub.taxa)) := by
    simp only [Quartet.cutBy, decide_eq_true_eq, Finset.subset_iff, Finset.disjoint_left]
    tauto
  rw [hbool, ← side_partition_iff q.sides_nonempty.1 q.sides_nonempty.2 (· ∈ sub.taxa)]
  constructor
  · rintro ⟨hAA, hBB, hAB⟩
    exact ⟨fun a ha b hb => (reach a b (hfirst a ha) (hfirst b hb)).mp (hAA a ha b hb),
      fun a ha b hb => (reach a b (hsecond a ha) (hsecond b hb)).mp (hBB a ha b hb),
      fun a ha b hb h => hAB a ha b hb ((reach a b (hfirst a ha) (hsecond b hb)).mpr h)⟩
  · rintro ⟨hAA, hBB, hAB⟩
    exact ⟨fun a ha b hb => (reach a b (hfirst a ha) (hfirst b hb)).mpr (hAA a ha b hb),
      fun a ha b hb => (reach a b (hsecond a ha) (hsecond b hb)).mpr (hBB a ha b hb),
      fun a ha b hb h => hAB a ha b hb ((reach a b (hfirst a ha) (hsecond b hb)).mp h)⟩

theorem baseline_switching_unique (t : PhyloTree) (ht : t.WellLabelled)
    {S : Finset (ℕ × ℕ)} (hS : (graph t ∅).Switching S) : S = (graph t ∅).edges := by
  classical
  have hempty : EdgeAbove.CycleSeparated t ∅ := by simp [EdgeAbove.CycleSeparated, Set.Pairwise]
  have htotal : (graph t ∅).Switching (graph t ∅).edges := by
    simpa only [graph, Finset.image_empty, Finset.union_empty] using (support t ht ∅ hempty).switching
  apply Finset.Subset.antisymm hS.1
  intro e he
  have he' := he
  rw [baseline_edges] at he'
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp he'
  have hp' := Finset.mem_erase.mp hp
  have hev : e.2 ∈ (graph t ∅).vertices := by
    rw [← heq]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp'.2, rfl⟩)
  have henil : e.2 ≠ (graph t ∅).root := by
    rw [← heq]
    exact fun h => hp'.1 (Address.code_injective h)
  have hcard := hS.2 e.2 hev henil
  have hpos : (S.filter (fun f => f.2 = e.2)).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨f, hf⟩ := hpos
  have hfN : f ∈ (graph t ∅).edges.filter (fun f => f.2 = e.2) :=
    Finset.mem_filter.mpr ⟨hS.1 (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2⟩
  have heN : e ∈ (graph t ∅).edges.filter (fun f => f.2 = e.2) := Finset.mem_filter.mpr ⟨he, rfl⟩
  have hfe := Finset.card_le_one.mp (htotal.2 e.2 hev henil).le f hfN e heN
  exact hfe ▸ (Finset.mem_filter.mp hf).1

theorem baseline_edgeSet (t : PhyloTree) (edge : Sym2 ℕ) :
    edge ∈ (graph t ∅).underlying.edgeSet ↔
      ∃ p ∈ t.nodes, p ≠ [] ∧ baselineCut p = edge := by
  induction edge using Sym2.inductionOn with
  | _ u v =>
    change (graph t ∅).underlying.Adj u v ↔ _
    constructor
    · rintro ⟨hne, he | he⟩
      · rw [baseline_edges] at he
        obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp he
        obtain ⟨hu, hv⟩ := Prod.mk.inj heq
        exact ⟨p, (Finset.mem_erase.mp hp).2, (Finset.mem_erase.mp hp).1, by rw [baselineCut, hu, hv]⟩
      · rw [baseline_edges] at he
        obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp he
        obtain ⟨hv, hu⟩ := Prod.mk.inj heq
        exact ⟨p, (Finset.mem_erase.mp hp).2, (Finset.mem_erase.mp hp).1,
          by rw [baselineCut, hv, hu, Sym2.eq_swap]⟩
    · rintro ⟨p, hp, hn, heq⟩
      have he : (Address.code (parent p), Address.code p) ∈ (graph t ∅).edges := by
        rw [baseline_edges]
        exact Finset.mem_image.mpr ⟨p, Finset.mem_erase.mpr ⟨hn, hp⟩, rfl⟩
      have hne : Address.code (parent p) ≠ Address.code p := by
        intro h
        exact EdgeAbove.parent_ne_self hn (Address.code_injective h)
      have hmem : baselineCut p ∈ (graph t ∅).underlying.edgeSet := ⟨hne, Or.inl he⟩
      change s(u,v) ∈ (graph t ∅).underlying.edgeSet
      exact heq ▸ hmem

end Camus.Realization
