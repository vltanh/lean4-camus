module

public import Camus.Pipelines.NMSC.Quartets
public import Camus.DP.Packing

/-!
# A level-1 network of the NMSC as a tree with added edges

Section 3.2 takes the true network `N` to be a rooted binary level-1 network built on the
constraint tree `T`: `N` is `T` with an edge added above a pair `(u, w)` of vertices of `T` for each
of its cycles (Definition 3, `Realization.graph`). This file gives this description for the
networks `Brooqs.Net` of the network multispecies coalescent. The tree `NMSC.baseTree N` is a
displayed tree of `N` with the root of `N`: at each cycle, the hybrid edge of one side is deleted
(of the side `S₂` if it has a node, and of `S₁` otherwise, so that the top node of the cycle keeps
two children), and the vertices left with one child are suppressed. Adding back the deleted hybrid
edges gives the pairs `NMSC.pairs N`: for each cycle, the donor `u` is the root of the network
hanging from the last node of the side whose hybrid edge was deleted, and the recipient `w` is the
root of the hybrid component. The family is cycle-separated (`NMSC.separated_pairs`), so that
`Realization.graph (baseTree N) (pairs N)` is a rooted binary level-1 network built on
`baseTree N`.

## Main results

* `NMSC.baseTree`, `NMSC.pairs`: the base tree and the pairs of the added edges.
* `NMSC.wellLabelled_baseTree`, `NMSC.taxa_baseTree`: the base tree is a phylogenetic tree on the
  taxa of `N`.
* `NMSC.separated_pairs`: the family of pairs is cycle-separated.
-/

@[expose] public section

namespace Camus

namespace NMSC

open Finset

variable {L : Finset ℕ}

/-! ### The base tree and the pairs -/

/-- The pairs `E` of a subtree, moved into the child `b` of a root: both addresses get the step
`b` in front. -/
def liftPairs (b : Bool) (E : Finset (Address × Address)) : Finset (Address × Address) :=
  E.image fun e => (b :: e.1, b :: e.2)

/-- The side has a node: it is not a single hybrid edge. -/
def hasNode : Brooqs.Side L → Bool
  | .hyb _ => false
  | .node .. => true

@[simp] theorem hasNode_hyb (ℓ : ℝ) : hasNode (.hyb ℓ : Brooqs.Side L) = false := rfl

@[simp] theorem hasNode_node (ℓ b : ℝ) (M : Brooqs.Net L) (S : Brooqs.Side L) :
    hasNode (.node ℓ b M S) = true := rfl

/-- The address of the root of the hybrid component in the tree of a side with the hybrid
component attached (`NMSC.attachTree`): one step right for each node of the side. -/
def hangAddr (S : Brooqs.Side L) : Address := List.replicate S.nodes.length true

/-- The address of the root of the network hanging from the last node of a side in the tree of the
side with its hybrid edge deleted (`NMSC.detachTree`). -/
def lastAddr (S : Brooqs.Side L) : Address := List.replicate (S.nodes.length - 1) true

mutual
/-- The base tree of `N`: the displayed tree of `N` that, at each cycle, deletes the hybrid edge
of the side `S₂` if `S₂` has a node, and the hybrid edge of `S₁` otherwise; the vertices left with
one child are suppressed. Its root is the root of `N`, and its leaves are labelled by the taxa of
`N`, as natural numbers. -/
def baseTree : Brooqs.Net L → PhyloTree
  | .leaf x => .leaf x.1
  | .tree _ N₁ _ N₂ => .fork (baseTree N₁) (baseTree N₂)
  | .cycle _ S₁ S₂ _ H =>
      if hasNode S₂ then .fork (attachTree S₁ (baseTree H)) (detachTree S₂)
      else .fork (attachTree S₂ (baseTree H)) (detachTree S₁)

/-- The tree of a side with the tree `X` hanging from its hybrid edge: a caterpillar with the
base trees of the networks hanging from the nodes of the side, from the top, and `X` at the
bottom. -/
def attachTree : Brooqs.Side L → PhyloTree → PhyloTree
  | .hyb _, X => X
  | .node _ _ M S, X => .fork (baseTree M) (attachTree S X)

/-- The tree of a side whose hybrid edge is deleted: a caterpillar with the base trees of the
networks hanging from the nodes of the side, from the top; the last node, left with one child, is
suppressed. A side without a node gives no tree (the value is then a single leaf). -/
def detachTree : Brooqs.Side L → PhyloTree
  | .hyb _ => .leaf 0
  | .node _ _ M S => if hasNode S then .fork (baseTree M) (detachTree S) else baseTree M
end

mutual
/-- The pairs `(u, w)` of the edges added to `baseTree N` to obtain `N`, one for each cycle: the
donor `u` is the root of the network hanging from the last node of the side whose hybrid edge is
deleted in the base tree, and the recipient `w` is the root of the hybrid component. -/
def pairs : Brooqs.Net L → Finset (Address × Address)
  | .leaf _ => ∅
  | .tree _ N₁ _ N₂ => liftPairs false (pairs N₁) ∪ liftPairs true (pairs N₂)
  | .cycle _ S₁ S₂ _ H =>
      if hasNode S₂ then
        insert (true :: lastAddr S₂, false :: hangAddr S₁)
          (liftPairs false (attachPairs S₁ (pairs H)) ∪ liftPairs true (detachPairs S₂))
      else
        insert (true :: lastAddr S₁, false :: hangAddr S₂)
          (liftPairs false (attachPairs S₂ (pairs H)) ∪ liftPairs true (detachPairs S₁))

/-- The pairs of the cycles below a side, in `NMSC.attachTree`, given the pairs `P` of the tree
hanging from its hybrid edge. -/
def attachPairs : Brooqs.Side L → Finset (Address × Address) → Finset (Address × Address)
  | .hyb _, P => P
  | .node _ _ M S, P => liftPairs false (pairs M) ∪ liftPairs true (attachPairs S P)

/-- The pairs of the cycles below a side, in `NMSC.detachTree`. -/
def detachPairs : Brooqs.Side L → Finset (Address × Address)
  | .hyb _ => ∅
  | .node _ _ M S =>
      if hasNode S then liftPairs false (pairs M) ∪ liftPairs true (detachPairs S) else pairs M
end

theorem baseTree_cycle_hyb (γ : ℝ) (S₁ : Brooqs.Side L) (ℓ' ℓ : ℝ) (H : Brooqs.Net L) :
    baseTree (.cycle γ S₁ (.hyb ℓ') ℓ H) =
      .fork (attachTree (.hyb ℓ' : Brooqs.Side L) (baseTree H)) (detachTree S₁) := rfl

theorem baseTree_cycle_node (γ : ℝ) (S₁ : Brooqs.Side L) (ℓ' b : ℝ) (M : Brooqs.Net L)
    (S : Brooqs.Side L) (ℓ : ℝ) (H : Brooqs.Net L) :
    baseTree (.cycle γ S₁ (.node ℓ' b M S) ℓ H) =
      .fork (attachTree S₁ (baseTree H)) (detachTree (.node ℓ' b M S)) := rfl

theorem detachTree_single (ℓ b ℓ' : ℝ) (M : Brooqs.Net L) :
    detachTree (.node ℓ b M (.hyb ℓ')) = baseTree M := rfl

theorem detachTree_node (ℓ b ℓ' b' : ℝ) (M M' : Brooqs.Net L) (S : Brooqs.Side L) :
    detachTree (.node ℓ b M (.node ℓ' b' M' S)) =
      .fork (baseTree M) (detachTree (.node ℓ' b' M' S)) := rfl

theorem pairs_cycle_hyb (γ : ℝ) (S₁ : Brooqs.Side L) (ℓ' ℓ : ℝ) (H : Brooqs.Net L) :
    pairs (.cycle γ S₁ (.hyb ℓ') ℓ H) =
      insert (true :: lastAddr S₁, false :: hangAddr (.hyb ℓ' : Brooqs.Side L))
        (liftPairs false (attachPairs (.hyb ℓ' : Brooqs.Side L) (pairs H)) ∪
          liftPairs true (detachPairs S₁)) := rfl

theorem pairs_cycle_node (γ : ℝ) (S₁ : Brooqs.Side L) (ℓ' b : ℝ) (M : Brooqs.Net L)
    (S : Brooqs.Side L) (ℓ : ℝ) (H : Brooqs.Net L) :
    pairs (.cycle γ S₁ (.node ℓ' b M S) ℓ H) =
      insert (true :: lastAddr (.node ℓ' b M S), false :: hangAddr S₁)
        (liftPairs false (attachPairs S₁ (pairs H)) ∪
          liftPairs true (detachPairs (.node ℓ' b M S))) := rfl

theorem detachPairs_single (ℓ b ℓ' : ℝ) (M : Brooqs.Net L) :
    detachPairs (.node ℓ b M (.hyb ℓ')) = pairs M := rfl

theorem detachPairs_node (ℓ b ℓ' b' : ℝ) (M M' : Brooqs.Net L) (S : Brooqs.Side L) :
    detachPairs (.node ℓ b M (.node ℓ' b' M' S)) =
      liftPairs false (pairs M) ∪ liftPairs true (detachPairs (.node ℓ' b' M' S)) := rfl

/-! ### Labels and taxa -/

mutual
/-- The leaf labels of the base tree are the taxa of `N`, as natural numbers, up to order. -/
theorem labels_baseTree :
    ∀ N : Brooqs.Net L, N.IsMetric → (baseTree N).labels.Perm (N.leaves.map Subtype.val)
  | .leaf x, _ => by simp [baseTree, PhyloTree.labels, Brooqs.Net.leaves]
  | .tree _ N₁ _ N₂, h => by
      simp only [baseTree, PhyloTree.labels, Brooqs.Net.leaves, List.map_append]
      exact (labels_baseTree N₁ h.2.2.1).append (labels_baseTree N₂ h.2.2.2)
  | .cycle _ S₁ (.hyb _) _ H, h => by
      have h1 : S₁.nodes ≠ [] := h.2.2.2.2.2.2.resolve_right (by simp [Brooqs.Side.nodes])
      rw [baseTree_cycle_hyb]
      simp only [attachTree, PhyloTree.labels, Brooqs.Net.leaves, Brooqs.Side.leaves,
        List.append_nil, List.map_append]
      exact ((labels_baseTree H h.2.2.2.2.2.1).append (labels_detachTree S₁ h.2.2.2.1 h1)).trans
        List.perm_append_comm
  | .cycle _ S₁ (.node ℓ b M S₂) _ H, h => by
      have h2 : (Brooqs.Side.node ℓ b M S₂).nodes ≠ [] := by simp [Brooqs.Side.nodes]
      simp only [baseTree, Brooqs.Net.leaves, List.map_append]
      refine ((labels_attachTree S₁ (baseTree H) h.2.2.2.1).append
        (labels_detachTree _ h.2.2.2.2.1 h2)).trans ?_
      refine (((List.Perm.refl _).append (labels_baseTree H h.2.2.2.2.2.1)).append
        (List.Perm.refl _)).trans ?_
      rw [List.append_assoc, List.append_assoc]
      exact (List.Perm.refl _).append List.perm_append_comm

/-- The leaf labels of the tree of a side with `X` attached: the taxa below the side and the
labels of `X`. -/
theorem labels_attachTree : ∀ (S : Brooqs.Side L) (X : PhyloTree), S.IsMetric →
    (attachTree S X).labels.Perm (S.leaves.map Subtype.val ++ X.labels)
  | .hyb _, X, _ => by simp [attachTree, Brooqs.Side.leaves]
  | .node _ _ M S, X, h => by
      simp only [attachTree, PhyloTree.labels, Brooqs.Side.leaves, List.map_append,
        List.append_assoc]
      exact (labels_baseTree M h.2.2.1).append (labels_attachTree S X h.2.2.2)

/-- The leaf labels of the tree of a side with a node whose hybrid edge is deleted: the taxa below
the side. -/
theorem labels_detachTree : ∀ (S : Brooqs.Side L), S.IsMetric → S.nodes ≠ [] →
    (detachTree S).labels.Perm (S.leaves.map Subtype.val)
  | .hyb _, _, h => absurd rfl h
  | .node _ _ M (.hyb _), h, _ => by
      simpa [detachTree, Brooqs.Side.leaves] using labels_baseTree M h.2.2.1
  | .node _ _ M (.node ℓ b M' S), h, _ => by
      have hS : (Brooqs.Side.node ℓ b M' S).nodes ≠ [] := by simp [Brooqs.Side.nodes]
      have h' := (labels_baseTree M h.2.2.1).append (labels_detachTree _ h.2.2.2 hS)
      simp only [detachTree, Brooqs.Side.leaves, List.map_append] at h' ⊢
      exact h'
end

/-- The base tree of a metric level-1 network with distinct leaf labels is a phylogenetic tree:
its leaves have distinct labels. -/
theorem wellLabelled_baseTree {N : Brooqs.Net L} (hN : N.WellFormed) :
    (baseTree N).WellLabelled :=
  (labels_baseTree N hN.1).nodup_iff.2 (hN.2.map Subtype.val_injective)

/-- The taxa of the base tree are the taxa of `N`, as natural numbers. -/
theorem taxa_baseTree {N : Brooqs.Net L} (hN : N.IsMetric) :
    (baseTree N).taxa = N.taxa.map (Coalescent.label L) := by
  ext a
  simp only [PhyloTree.taxa, List.mem_toFinset, (labels_baseTree N hN).mem_iff, List.mem_map,
    Brooqs.Net.taxa, Finset.mem_map, Coalescent.label, Function.Embedding.subtype_apply]

/-- The taxa of the tree of a side with `X` attached. -/
theorem taxa_attachTree {S : Brooqs.Side L} (hS : S.IsMetric) (X : PhyloTree) :
    (attachTree S X).taxa = S.taxa.map (Coalescent.label L) ∪ X.taxa := by
  ext a
  simp only [PhyloTree.taxa, List.mem_toFinset, (labels_attachTree S X hS).mem_iff,
    List.mem_append, List.mem_map, Brooqs.Side.taxa, Finset.mem_union, Finset.mem_map,
    Coalescent.label, Function.Embedding.subtype_apply]

/-- The taxa of the tree of a side with a node whose hybrid edge is deleted. -/
theorem taxa_detachTree {S : Brooqs.Side L} (hS : S.IsMetric) (hne : S.nodes ≠ []) :
    (detachTree S).taxa = S.taxa.map (Coalescent.label L) := by
  ext a
  simp only [PhyloTree.taxa, List.mem_toFinset, (labels_detachTree S hS hne).mem_iff,
    List.mem_map, Brooqs.Side.taxa, Finset.mem_map, Coalescent.label,
    Function.Embedding.subtype_apply]

/-! ### Addresses along a side -/

theorem hangAddr_node (ℓ b : ℝ) (M : Brooqs.Net L) (S : Brooqs.Side L) :
    hangAddr (.node ℓ b M S) = true :: hangAddr S := by
  simp [hangAddr, Brooqs.Side.nodes, List.replicate_succ]

theorem lastAddr_single (ℓ b ℓ' : ℝ) (M : Brooqs.Net L) :
    lastAddr (.node ℓ b M (.hyb ℓ') : Brooqs.Side L) = [] := by
  simp [lastAddr, Brooqs.Side.nodes]

theorem lastAddr_node (ℓ b ℓ' b' : ℝ) (M M' : Brooqs.Net L) (S : Brooqs.Side L) :
    lastAddr (.node ℓ b M (.node ℓ' b' M' S)) = true :: lastAddr (.node ℓ' b' M' S) := by
  simp [lastAddr, Brooqs.Side.nodes, List.replicate_succ]

/-- The tree `X` hangs at the address `hangAddr S` of the tree of the side `S` with `X`
attached. -/
theorem nodeAt_hangAddr : ∀ (S : Brooqs.Side L) (X : PhyloTree),
    (attachTree S X).nodeAt (hangAddr S) = some X
  | .hyb _, X => by simp [attachTree, hangAddr, Brooqs.Side.nodes, PhyloTree.nodeAt]
  | .node _ _ M S, X => by
      rw [hangAddr_node]
      simpa [attachTree, PhyloTree.nodeAt] using nodeAt_hangAddr S X

/-- The address `lastAddr S` is a vertex of the tree of the side `S` with its hybrid edge
deleted. -/
theorem lastAddr_mem_nodes : ∀ S : Brooqs.Side L, lastAddr S ∈ (detachTree S).nodes
  | .hyb _ => by simp [lastAddr, detachTree, PhyloTree.nodes, Brooqs.Side.nodes]
  | .node _ _ M (.hyb _) => by
      rw [lastAddr_single]
      exact PhyloTree.root_mem_nodes _
  | .node _ _ M (.node ℓ b M' S) => by
      rw [lastAddr_node, detachTree_node]
      simp only [PhyloTree.nodes]
      exact mem_insert_of_mem (mem_union_right _ (mem_image_of_mem _ (lastAddr_mem_nodes _)))

/-! ### The family of pairs is cycle-separated -/

theorem mem_liftPairs {b : Bool} {E : Finset (Address × Address)} {e : Address × Address} :
    e ∈ liftPairs b E ↔ ∃ f ∈ E, e = (b :: f.1, b :: f.2) := by
  simp only [liftPairs, mem_image]
  exact exists_congr fun f => and_congr_right fun _ => eq_comm

theorem target_cons (b : Bool) (u w : Address) :
    EdgeAbove.target (b :: u, b :: w) = b :: EdgeAbove.target (u, w) := by
  simp [EdgeAbove.target, lca]

theorem mem_candidates {t : PhyloTree} {e : Address × Address} :
    e ∈ EdgeAbove.candidates t ↔ EdgeAbove.Admissible t e := by
  simp only [EdgeAbove.candidates, mem_filter, mem_product]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1, h.2.1⟩, h⟩⟩

theorem mem_nodes_cons {t s : PhyloTree} {b : Bool} (h : t.nodeAt [b] = some s) (y : Address) :
    b :: y ∈ t.nodes ↔ y ∈ s.nodes := by
  rw [PhyloTree.mem_nodes_iff, PhyloTree.mem_nodes_iff, show b :: y = [b] ++ y from rfl,
    PhyloTree.nodeAt_append, h]
  rfl

/-- A pair admissible in the child `b` of the root is admissible once moved into that child. -/
theorem admissible_cons {t s : PhyloTree} {b : Bool} (h : t.nodeAt [b] = some s)
    {e : Address × Address} (he : EdgeAbove.Admissible s e) :
    EdgeAbove.Admissible t (b :: e.1, b :: e.2) :=
  ⟨(mem_nodes_cons h _).2 he.1, (mem_nodes_cons h _).2 he.2.1, List.cons_ne_nil _ _,
    List.cons_ne_nil _ _, fun h' => he.2.2.2.2 (List.cons_prefix_cons.1 h').2⟩

/-- The cycle of a pair moved into the child `b` of the root: its vertices are those of the cycle
in the child, moved into it. -/
theorem mem_footprint_cons {t s : PhyloTree} {b : Bool} (h : t.nodeAt [b] = some s)
    (e : Address × Address) (x : Address) :
    x ∈ EdgeAbove.footprint t (b :: e.1, b :: e.2) ↔
      ∃ y ∈ EdgeAbove.footprint s e, x = b :: y := by
  simp only [EdgeAbove.footprint, mem_filter, target_cons]
  cases x with
  | nil => simp
  | cons c y =>
    constructor
    · rintro ⟨hx, ht, hu⟩
      obtain ⟨rfl, ht'⟩ := List.cons_prefix_cons.1 ht
      refine ⟨y, ⟨(mem_nodes_cons h y).1 hx, ht', ?_⟩, rfl⟩
      simpa using hu
    · rintro ⟨y', ⟨hy, ht, hu⟩, hxy⟩
      obtain ⟨rfl, rfl⟩ := List.cons.inj hxy
      refine ⟨(mem_nodes_cons h _).2 hy, List.cons_prefix_cons.2 ⟨rfl, ht⟩, ?_⟩
      simpa using hu

/-- Two cycle-separated families, of the two children of the root, give a cycle-separated
family. -/
theorem separated_fork {l r : PhyloTree} {E F : Finset (Address × Address)}
    (hE : EdgeAbove.CycleSeparated l E) (hF : EdgeAbove.CycleSeparated r F) :
    EdgeAbove.CycleSeparated (.fork l r) (liftPairs false E ∪ liftPairs true F) := by
  have hl : (PhyloTree.fork l r).nodeAt [false] = some l := by simp [PhyloTree.nodeAt]
  have hr : (PhyloTree.fork l r).nodeAt [true] = some r := by simp [PhyloTree.nodeAt]
  refine ⟨fun e he => ?_, ?_⟩
  · rcases mem_union.1 he with he | he
    · obtain ⟨f, hf, rfl⟩ := mem_liftPairs.1 he
      exact mem_candidates.2 (admissible_cons hl (mem_candidates.1 (hE.1 hf)))
    · obtain ⟨f, hf, rfl⟩ := mem_liftPairs.1 he
      exact mem_candidates.2 (admissible_cons hr (mem_candidates.1 (hF.1 hf)))
  · intro e he e' he' hne
    simp only [coe_union, Set.mem_union, mem_coe] at he he'
    refine disjoint_left.2 fun x hx hx' => ?_
    rcases he with he | he <;> rcases he' with he' | he' <;>
      obtain ⟨f, hf, rfl⟩ := mem_liftPairs.1 he <;> obtain ⟨f', hf', rfl⟩ := mem_liftPairs.1 he'
    · obtain ⟨y, hy, rfl⟩ := (mem_footprint_cons hl f x).1 hx
      obtain ⟨y', hy', hyy⟩ := (mem_footprint_cons hl f' _).1 hx'
      cases hyy
      have hff : f ≠ f' := fun h => hne (by rw [h])
      exact disjoint_left.1 (hE.2 hf hf' hff) hy hy'
    · obtain ⟨y, hy, rfl⟩ := (mem_footprint_cons hl f x).1 hx
      obtain ⟨y', hy', hyy⟩ := (mem_footprint_cons hr f' _).1 hx'
      simp at hyy
    · obtain ⟨y, hy, rfl⟩ := (mem_footprint_cons hr f x).1 hx
      obtain ⟨y', hy', hyy⟩ := (mem_footprint_cons hl f' _).1 hx'
      simp at hyy
    · obtain ⟨y, hy, rfl⟩ := (mem_footprint_cons hr f x).1 hx
      obtain ⟨y', hy', hyy⟩ := (mem_footprint_cons hr f' _).1 hx'
      cases hyy
      have hff : f ≠ f' := fun h => hne (by rw [h])
      exact disjoint_left.1 (hF.2 hf hf' hff) hy hy'

/-- Adding an admissible pair whose cycle avoids the cycles of a cycle-separated family gives a
cycle-separated family. -/
theorem separated_insert {t : PhyloTree} {E : Finset (Address × Address)} {e : Address × Address}
    (hE : EdgeAbove.CycleSeparated t E) (he : EdgeAbove.Admissible t e)
    (hdisj : ∀ f ∈ E, Disjoint (EdgeAbove.footprint t e) (EdgeAbove.footprint t f)) :
    EdgeAbove.CycleSeparated t (insert e E) := by
  refine ⟨fun f hf => ?_, ?_⟩
  · rcases mem_insert.1 hf with rfl | hf
    · exact mem_candidates.2 he
    · exact hE.1 hf
  · rw [coe_insert]
    exact hE.2.insert fun f hf _ => ⟨hdisj f hf, (hdisj f hf).symm⟩

/-- The cycles of the pairs below a side, in the tree of the side with a tree attached, avoid the
path from the top of the side to the attached tree: a vertex below the target of such a pair and
above the attached tree is its root. -/
theorem attachPairs_off_path : ∀ (S : Brooqs.Side L) (P : Finset (Address × Address)),
    ∀ e ∈ attachPairs S P, ∀ x, EdgeAbove.target e <+: x → x <+: hangAddr S → x = hangAddr S
  | .hyb _, P, e, he, x, _, h2 => by simpa [hangAddr, Brooqs.Side.nodes] using h2
  | .node _ _ M S, P, e, he, x, h1, h2 => by
      rw [hangAddr_node] at h2 ⊢
      simp only [attachPairs, mem_union] at he
      rcases he with he | he
      · obtain ⟨f, -, rfl⟩ := mem_liftPairs.1 he
        obtain ⟨y, rfl⟩ := h1
        simp [target_cons] at h2
      · obtain ⟨f, hf, rfl⟩ := mem_liftPairs.1 he
        obtain ⟨y, rfl⟩ := h1
        simp only [target_cons, List.cons_append, List.cons_prefix_cons, true_and,
          List.cons.injEq] at h2 ⊢
        exact attachPairs_off_path S P f hf _ (List.prefix_append _ _) h2

/-- The cycles of the pairs below a side, in the tree of the side with its hybrid edge deleted,
avoid the path from the top of the side to its last pendant network. -/
theorem detachPairs_off_path : ∀ (S : Brooqs.Side L),
    ∀ e ∈ detachPairs S, ∀ x, EdgeAbove.target e <+: x → x <+: lastAddr S → x = lastAddr S
  | .hyb _, e, he, _, _, _ => by simp [detachPairs] at he
  | .node _ _ M (.hyb _), e, he, x, _, h2 => by
      rw [lastAddr_single] at h2 ⊢
      exact List.prefix_nil.1 h2
  | .node _ _ M (.node ℓ b M' S), e, he, x, h1, h2 => by
      rw [lastAddr_node] at h2 ⊢
      rw [detachPairs_node, mem_union] at he
      rcases he with he | he
      · obtain ⟨f, -, rfl⟩ := mem_liftPairs.1 he
        obtain ⟨y, rfl⟩ := h1
        simp [target_cons] at h2
      · obtain ⟨f, hf, rfl⟩ := mem_liftPairs.1 he
        obtain ⟨y, rfl⟩ := h1
        simp only [target_cons, List.cons_append, List.cons_prefix_cons, true_and,
          List.cons.injEq] at h2 ⊢
        exact detachPairs_off_path _ f hf _ (List.prefix_append _ _) h2

theorem footprint_cases {t : PhyloTree} {e : Address × Address} {x : Address}
    (hx : x ∈ EdgeAbove.footprint t e) : (x <+: e.1 ∧ x ≠ e.1) ∨ (x <+: e.2 ∧ x ≠ e.2) :=
  (mem_filter.1 hx).2.2

/-- The pairs of a cycle and of the cycles below it form a cycle-separated family of the tree
of the cycle: the side `Sa` with the tree `X` of the hybrid component attached, and the side `Sd`
with its hybrid edge deleted. -/
theorem separated_cycle {Sa Sd : Brooqs.Side L} {X : PhyloTree} {P : Finset (Address × Address)}
    (hA : EdgeAbove.CycleSeparated (attachTree Sa X) (attachPairs Sa P))
    (hD : EdgeAbove.CycleSeparated (detachTree Sd) (detachPairs Sd)) :
    EdgeAbove.CycleSeparated (.fork (attachTree Sa X) (detachTree Sd))
      (insert (true :: lastAddr Sd, false :: hangAddr Sa)
        (liftPairs false (attachPairs Sa P) ∪ liftPairs true (detachPairs Sd))) := by
  have hl : (PhyloTree.fork (attachTree Sa X) (detachTree Sd)).nodeAt [false] =
      some (attachTree Sa X) := by simp [PhyloTree.nodeAt]
  have hr : (PhyloTree.fork (attachTree Sa X) (detachTree Sd)).nodeAt [true] =
      some (detachTree Sd) := by simp [PhyloTree.nodeAt]
  refine separated_insert (separated_fork hA hD)
    ⟨(mem_nodes_cons hr _).2 (lastAddr_mem_nodes _),
      (mem_nodes_cons hl _).2 ((PhyloTree.mem_nodes_iff _ _).2 ⟨_, nodeAt_hangAddr _ _⟩),
      List.cons_ne_nil _ _, List.cons_ne_nil _ _, by simp⟩
    fun f hf => disjoint_left.2 fun x hx hx' => ?_
  have hx'' := EdgeAbove.footprint_below hx'
  rcases footprint_cases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases mem_union.1 hf with hf | hf <;>
    obtain ⟨g, hg, rfl⟩ := mem_liftPairs.1 hf <;> rw [target_cons] at hx'' <;>
    obtain ⟨y, rfl⟩ := hx''
  · simp at h1
  · simp only [List.cons_append, List.cons_prefix_cons, true_and, ne_eq,
      List.cons.injEq] at h1 h2
    exact h2 (detachPairs_off_path _ g hg _ (List.prefix_append _ _) h1)
  · simp only [List.cons_append, List.cons_prefix_cons, true_and, ne_eq,
      List.cons.injEq] at h1 h2
    exact h2 (attachPairs_off_path Sa P g hg _ (List.prefix_append _ _) h1)
  · simp at h1

mutual
/-- **Section 3.2**: the pairs of the added edges of a level-1 network `N` form a cycle-separated
family of the base tree, so that adding an edge above each of them gives a rooted binary level-1
network built on the base tree (`Realization.levelOne`). -/
theorem separated_pairs : ∀ N : Brooqs.Net L, EdgeAbove.CycleSeparated (baseTree N) (pairs N)
  | .leaf _ => by simp [EdgeAbove.CycleSeparated, pairs]
  | .tree _ N₁ _ N₂ => separated_fork (separated_pairs N₁) (separated_pairs N₂)
  | .cycle _ S₁ (.hyb _) _ H =>
      separated_cycle (separated_attach _ (separated_pairs H)) (separated_detach S₁)
  | .cycle _ S₁ (.node ..) _ H =>
      separated_cycle (separated_attach S₁ (separated_pairs H)) (separated_detach _)

/-- The pairs below a side, with a tree and a cycle-separated family of it attached, form a
cycle-separated family. -/
theorem separated_attach : ∀ (S : Brooqs.Side L) {X : PhyloTree} {P : Finset (Address × Address)},
    EdgeAbove.CycleSeparated X P → EdgeAbove.CycleSeparated (attachTree S X) (attachPairs S P)
  | .hyb _, _, _, h => h
  | .node _ _ M S, _, _, h => separated_fork (separated_pairs M) (separated_attach S h)

/-- The pairs below a side, with its hybrid edge deleted, form a cycle-separated family. -/
theorem separated_detach :
    ∀ S : Brooqs.Side L, EdgeAbove.CycleSeparated (detachTree S) (detachPairs S)
  | .hyb _ => by simp [EdgeAbove.CycleSeparated, detachPairs]
  | .node _ _ M (.hyb _) => separated_pairs M
  | .node _ _ M (.node ..) => separated_fork (separated_pairs M) (separated_detach _)
end

end NMSC

end Camus
