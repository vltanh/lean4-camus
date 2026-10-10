module

public import Camus.Complexity.Timed
public import Camus.Complexity.Operations

/-!
# Section 2.3: the preprocessing tables

Section 2.3 of the paper first performs a preprocessing "in order to enable constant time LCA
queries of all pairs of vertices, the leafsets for all vertices, and the depth of every node in the
tree", and states that it "can be computed in O(n²) time". This file writes this preprocessing as a
program in the cost monad of `Camus/Complexity/Timed.lean` and proves both claims. One traversal of
`T` lists its vertices in preorder, each with its parent, its depth and its kind (a leaf with its
label, or an internal vertex with its two children); the tables of parents, depths and kinds, and
the table of the leaf of each taxon, are filled from this list. The table of lowest common
ancestors is then filled pair by pair, each entry in `O(1)` from entries computed before it, by the
recurrence `lca(p, q) = p` if `p = q`, `lca(parent p, q)` if `|p| ≥ |q|`, and `lca(p, parent q)`
otherwise (`Complexity.lca_recurrence`): looping over `p` and then over `q` in preorder, the entries
`(parent p, q)` and `(p, parent q)` come first, since a vertex comes after its ancestors in
preorder. The leaf sets are not tabulated: a taxon `a` is in the clade of `p` exactly when `p` is
an ancestor of the leaf of `a`, and the ancestor test `p <+: x` is `lca(p, x) = p`, one read of the
table (`Complexity.prefix_iff_lca`).

## Main results

* `PhyloTree.preorder`: the vertices of `T` in preorder; `PhyloTree.preorder_ancestor_before`: a
  vertex comes after its proper ancestors.
* `Complexity.lca_recurrence`: the recurrence of the table of lowest common ancestors.
* `Complexity.preprocess`: the preprocessing, as a program.
* `Complexity.preprocess_correct`: the tables agree with `parent`, `List.length`, the kinds of the
  vertices, the leaves of the taxa and `Camus.lca` on the vertices of `T`
  (`Complexity.Tables.Correct`, `Complexity.Tables.Correct.leafOf_eq`).
* `Complexity.preprocess_time`: the preprocessing takes at most `20 |V(T)|²` operations.
-/

@[expose] public section

namespace Camus

namespace PhyloTree

/-- The vertices of `t` in preorder: the root, then the vertices of the left subtree, then those of
the right subtree. -/
def preorder : PhyloTree → List Address
  | .leaf _ => [[]]
  | .fork l r => [] :: ((preorder l).map (false :: ·) ++ (preorder r).map (true :: ·))

/-- The vertices listed by `preorder` are the vertices of `t`. -/
theorem mem_preorder (t : PhyloTree) (p : Address) : p ∈ t.preorder ↔ p ∈ t.nodes := by
  induction t generalizing p with
  | leaf a => simp [preorder, nodes]
  | fork l r ihl ihr =>
    cases p with
    | nil => simp [preorder, nodes]
    | cons b p =>
      cases b <;> simp [preorder, nodes, ihl, ihr]

/-- `preorder` lists each vertex once. -/
theorem preorder_nodup (t : PhyloTree) : t.preorder.Nodup := by
  induction t with
  | leaf a => simp [preorder]
  | fork l r ihl ihr =>
    simp only [preorder, List.nodup_cons, List.mem_append, List.mem_map, not_or]
    refine ⟨⟨fun ⟨_, _, h⟩ => List.cons_ne_nil _ _ h, fun ⟨_, _, h⟩ => List.cons_ne_nil _ _ h⟩, ?_⟩
    rw [List.nodup_append]
    refine ⟨ihl.map (fun _ _ h => (List.cons.inj h).2), ihr.map (fun _ _ h => (List.cons.inj h).2),
      ?_⟩
    intro x hx y hy hxy
    obtain ⟨x', _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨y', _, rfl⟩ := List.mem_map.mp hy
    exact Bool.false_ne_true (List.cons.inj hxy).1

theorem preorder_toFinset (t : PhyloTree) : t.preorder.toFinset = t.nodes := by
  ext p
  simp [mem_preorder]

theorem preorder_length (t : PhyloTree) : t.preorder.length = t.nodes.card := by
  rw [← preorder_toFinset, List.toFinset_card_of_nodup (preorder_nodup t)]

/-- In preorder, no vertex comes after one of its proper descendants. -/
theorem preorder_pairwise (t : PhyloTree) :
    t.preorder.Pairwise (fun p x => ¬(x <+: p ∧ x ≠ p)) := by
  induction t with
  | leaf a => simp [preorder]
  | fork l r ihl ihr =>
    simp only [preorder, List.pairwise_cons, List.pairwise_append, List.pairwise_map,
      List.mem_append, List.mem_map]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro x - ⟨hx, hne⟩
      exact hne (List.prefix_nil.mp hx)
    · exact ihl.imp fun h ⟨hx, hne⟩ =>
        h ⟨(List.cons_prefix_cons.mp hx).2, fun he => hne (by rw [he])⟩
    · exact ihr.imp fun h ⟨hx, hne⟩ =>
        h ⟨(List.cons_prefix_cons.mp hx).2, fun he => hne (by rw [he])⟩
    · rintro a ⟨a', -, rfl⟩ b ⟨b', -, rfl⟩ ⟨hx, -⟩
      exact Bool.false_ne_true (List.cons_prefix_cons.mp hx).1.symm

/-- A vertex comes after its proper ancestors in preorder: if `preorder t = A ++ x :: B` and `p`
is a proper ancestor of `x`, then `p` is in `A`. -/
theorem preorder_ancestor_before {t : PhyloTree} {A B : List Address} {x p : Address}
    (h : t.preorder = A ++ x :: B) (hpx : p <+: x) (hne : p ≠ x) : p ∈ A := by
  have hx : x ∈ t.nodes := (mem_preorder t x).mp (by simp [h])
  have hp : p ∈ t.preorder := (mem_preorder t p).mpr (t.nodes_prefix_closed hx hpx)
  have hpw := preorder_pairwise t
  rw [h] at hp hpw
  rcases List.mem_append.mp hp with hA | hxB
  · exact hA
  · rcases List.mem_cons.mp hxB with rfl | hB
    · exact (hne rfl).elim
    · have := List.pairwise_append.mp hpw
      exact ((List.pairwise_cons.mp this.2.1).1 p hB ⟨hpx, hne⟩).elim

/-- A vertex comes after its proper descendants in reversed preorder. -/
theorem reverse_preorder_descendant_before {t : PhyloTree} {A B : List Address}
    {v y : Address} (h : t.preorder.reverse = A ++ v :: B) (hy : y ∈ t.nodes)
    (hvy : v <+: y) (hne : v ≠ y) : y ∈ A := by
  have h' : t.preorder = B.reverse ++ v :: A.reverse := by
    rw [← List.reverse_reverse t.preorder, h]
    simp
  have hyp : y ∈ t.preorder := (mem_preorder t y).mpr hy
  rw [h'] at hyp
  rcases List.mem_append.mp hyp with hB | hyA
  · -- `y` before `v` in preorder, yet `v` is a proper ancestor of `y`
    obtain ⟨C, D, hCD⟩ := List.append_of_mem hB
    have h'' : t.preorder = C ++ y :: (D ++ v :: A.reverse) := by
      rw [h', hCD]
      simp
    have hvC := preorder_ancestor_before h'' hvy hne
    have hnd := preorder_nodup t
    rw [h''] at hnd
    have hv : v ∈ D ++ v :: A.reverse := by simp
    exact (List.disjoint_of_nodup_append hnd hvC (List.mem_cons_of_mem _ hv)).elim
  · rcases List.mem_cons.mp hyA with rfl | hA
    · exact (hne rfl).elim
    · exact List.mem_reverse.mp hA

end PhyloTree

namespace Complexity

/-- `lca p p = p`. -/
theorem lca_self (p : Address) : lca p p = p := (lca_eq_left_iff p p).mpr (List.prefix_refl p)

/-- Two prefixes of each other are equal. -/
theorem prefix_antisymm {p q : Address} (hpq : p <+: q) (hqp : q <+: p) : p = q :=
  hpq.eq_of_length_le hqp.length_le

/-- If `p ≠ q` and `|q| ≤ |p|`, then `lca(p, q) = lca(parent p, q)`. -/
theorem lca_parent_left {p q : Address} (hne : p ≠ q) (hle : q.length ≤ p.length) :
    lca p q = lca (parent p) q := by
  have hz : lca p q ≠ p := by
    intro h
    exact hne (((lca_eq_left_iff p q).mp h).eq_of_length_le hle)
  apply prefix_antisymm
  · exact prefix_lca (prefix_parent_of_ne (lca_prefix_left p q) hz) (lca_prefix_right p q)
  · exact prefix_lca ((lca_prefix_left _ _).trans (parent_prefix p)) (lca_prefix_right _ _)

/-- If `|p| < |q|`, then `lca(p, q) = lca(p, parent q)`. -/
theorem lca_parent_right {p q : Address} (hlt : p.length < q.length) :
    lca p q = lca p (parent q) := by
  have hne : q ≠ p := by
    intro h
    rw [h] at hlt
    exact lt_irrefl _ hlt
  rw [lca_comm p q, lca_parent_left hne hlt.le, lca_comm]

/-- Section 2.3: the recurrence of the table of lowest common ancestors. `lca(p, q)` is `p` if
`p = q`, `lca(parent p, q)` if `|q| ≤ |p|`, and `lca(p, parent q)` otherwise. -/
theorem lca_recurrence (p q : Address) :
    lca p q = if p = q then p else if q.length ≤ p.length then lca (parent p) q
      else lca p (parent q) := by
  split_ifs with h hle
  · rw [h, lca_self]
  · exact lca_parent_left h hle
  · exact lca_parent_right (by omega)

/-- The ancestor test from the table of lowest common ancestors: `p <+: x` iff
`lca(p, x) = p`. -/
theorem prefix_iff_lca (p x : Address) : p <+: x ↔ lca p x = p := (lca_eq_left_iff p x).symm

open Timed

/-- What the tables record about a vertex: a leaf with its label, or an internal vertex with the
names of its left and right children. -/
inductive Kind where
  | leaf (a : ℕ)
  | fork (l r : Address)
  deriving DecidableEq, Inhabited

/-- The kind of the vertex `p` of `t` (a leaf labelled `0` if `p` is not a vertex). -/
def kindAt (t : PhyloTree) (p : Address) : Kind :=
  match t.nodeAt p with
  | some (.leaf a) => .leaf a
  | some (.fork _ _) => .fork (p ++ [false]) (p ++ [true])
  | none => .leaf 0

/-- One vertex, as listed by the traversal: its name, its parent, its depth and its kind. -/
structure Entry where
  addr : Address
  parent : Address
  depth : ℕ
  kind : Kind

/-- The entry of the vertex `p` of `t`. -/
def entryAt (t : PhyloTree) (p : Address) : Entry := ⟨p, parent p, p.length, kindAt t p⟩

/-- The traversal of `T`, from the subtree `sub` at the vertex `p` with parent `par` and depth `d`:
it lists the entries of the vertices of `sub` in preorder in front of `acc`, creating the names of
the two children of each internal vertex. One operation per leaf, four per internal vertex. -/
def visit : PhyloTree → Address → Address → ℕ → List Entry → Timed (List Entry)
  | .leaf a, p, par, d, acc => step (⟨p, par, d, .leaf a⟩ :: acc)
  | .fork l r, p, par, d, acc => do
      let pl ← step (p ++ [false])
      let pr ← step (p ++ [true])
      let d' ← step (d + 1)
      let acc ← visit r pr p d' acc
      let acc ← visit l pl p d' acc
      step (⟨p, par, d, .fork pl pr⟩ :: acc)

/-- The traversal lists the entries of the vertices in preorder. -/
theorem val_visit {t sub : PhyloTree} {p : Address} (h : t.nodeAt p = some sub)
    (acc : List Entry) :
    (visit sub p (parent p) p.length acc).val =
      sub.preorder.map (fun x => entryAt t (p ++ x)) ++ acc := by
  induction sub generalizing p acc with
  | leaf a =>
    simp [visit, PhyloTree.preorder, entryAt, kindAt, h]
  | fork l r ihl ihr =>
    have hl : t.nodeAt (p ++ [false]) = some l := by
      rw [PhyloTree.nodeAt_append, h]; simp [PhyloTree.nodeAt]
    have hr : t.nodeAt (p ++ [true]) = some r := by
      rw [PhyloTree.nodeAt_append, h]; simp [PhyloTree.nodeAt]
    have el := ihl hl
    have er := ihr hr
    simp only [parent_child, List.length_append, List.length_singleton] at el er
    simp only [visit, val_bind, val_step, er, el, PhyloTree.preorder, List.map_cons,
      List.map_append, List.map_map, List.cons_append, List.append_assoc, List.append_nil]
    congr 1
    simp [entryAt, kindAt, h]

/-- The traversal performs at most four operations per vertex. -/
theorem time_visit (sub : PhyloTree) (p par : Address) (d : ℕ) (acc : List Entry) :
    (visit sub p par d acc).time ≤ 4 * sub.nodes.card := by
  induction sub generalizing p par d acc with
  | leaf a => simp [visit, PhyloTree.nodes]
  | fork l r ihl ihr =>
    simp only [visit, time_bind, time_step, val_step]
    rw [PhyloTree.nodes_card_fork]
    have h1 := ihl (p ++ [false]) p (d + 1) (visit r (p ++ [true]) p (d + 1) acc).val
    have h2 := ihr (p ++ [true]) p (d + 1) acc
    omega

/-- The preprocessing tables: the parent, the depth and the kind of each vertex, the leaf of each
taxon, and the lowest common ancestor of each pair of vertices. Each is a function, updated and
read one entry at a time. -/
structure Tables where
  parent : Address → Address
  depth : Address → ℕ
  kind : Address → Kind
  leafOf : ℕ → Option Address
  lca : Address × Address → Address

/-- The tables before the preprocessing. -/
def Tables.empty : Tables :=
  ⟨fun _ => [], fun _ => 0, fun _ => default, fun _ => none, fun _ => []⟩

/-- The table of leaves after recording the vertex `p` of kind `k`: if `p` is a leaf labelled `a`,
its entry for `a` becomes `p`. -/
def setLeaf (f : ℕ → Option Address) (k : Kind) (p : Address) : ℕ → Option Address :=
  match k with
  | .leaf a => Function.update f a (some p)
  | .fork _ _ => f

/-- Record one entry in the tables: four writes and one test of the kind. -/
def record (T : Tables) (x : Entry) : Timed Tables := do
  let T ← step { T with parent := Function.update T.parent x.addr x.parent }
  let T ← step { T with depth := Function.update T.depth x.addr x.depth }
  let T ← step { T with kind := Function.update T.kind x.addr x.kind }
  steps 2 { T with leafOf := setLeaf T.leafOf x.kind x.addr }

/-- One entry of the table of lowest common ancestors, from earlier entries: `lca(p, q)` by
`lca_recurrence`, at most six operations. -/
def lcaEntry (T : Tables) (p q : Address) : Timed Address := do
  let same ← step (decide (p = q))
  if same then pure p
  else do
    let dp ← step (T.depth p)
    let dq ← step (T.depth q)
    let up ← step (decide (dq ≤ dp))
    if up then do
      let pp ← step (T.parent p)
      step (T.lca (pp, q))
    else do
      let pq ← step (T.parent q)
      step (T.lca (p, pq))

/-- The row of `p` in the table of lowest common ancestors: the entries `(p, q)` for the vertices
`q` of `pre`, in order. -/
def lcaRow (pre : List Address) (T : Tables) (p : Address) : Timed Tables :=
  forList (fun T q => do
    let x ← lcaEntry T p q
    step { T with lca := Function.update T.lca (p, q) x }) pre T

/-- The table of lowest common ancestors, row by row in the order of `pre`. -/
def lcaTable (pre : List Address) (T : Tables) : Timed Tables :=
  forList (lcaRow pre) pre T

/-- Section 2.3: the preprocessing. A traversal lists the vertices of `T` in preorder; the tables
of parents, depths, kinds and leaves are filled from the list; then the table of lowest common
ancestors. Returns the tables and the vertices of `T` in preorder.

Departure from the paper: the leaf sets of the vertices are not tabulated. The leaf of each taxon
and the ancestor test (`Complexity.prefix_iff_lca`) answer the same membership queries in constant
time: a taxon is in the clade of `p` iff `p` is an ancestor of its leaf. -/
def preprocess (t : PhyloTree) : Timed (Tables × List Address) := do
  let es ← visit t [] [] 0 []
  let T ← forList record es Tables.empty
  let pre ← mapList (fun x => pure x.addr) es
  let T ← lcaTable pre T
  pure (T, pre)

/-- The tables `T` agree with the tree `t` on its vertices: parents, depths, kinds, lowest common
ancestors; the table of leaves gives a leaf labelled `a` for every taxon `a`, and only such
leaves. -/
structure Tables.Correct (t : PhyloTree) (T : Tables) : Prop where
  parent : ∀ p ∈ t.nodes, T.parent p = Camus.parent p
  depth : ∀ p ∈ t.nodes, T.depth p = p.length
  kind : ∀ p ∈ t.nodes, T.kind p = kindAt t p
  leafOf_sound : ∀ a p, T.leafOf a = some p → t.nodeAt p = some (.leaf a)
  leafOf_complete : ∀ a ∈ t.taxa, ∃ p, T.leafOf a = some p
  lca : ∀ p ∈ t.nodes, ∀ q ∈ t.nodes, T.lca (p, q) = Camus.lca p q

/-- With correct tables of a well-labelled tree, the table of leaves gives the leaf address of
each taxon (`Realization.leafAddress`), and nothing for the other labels. -/
theorem Tables.Correct.leafOf_eq {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    (ht : t.WellLabelled) (a : ℕ) :
    T.leafOf a = if a ∈ t.taxa then some (Realization.leafAddress t a) else none := by
  split_ifs with ha
  · obtain ⟨p, hp⟩ := hT.leafOf_complete a ha
    rw [hp, Realization.leafAddress_eq ht (hT.leafOf_sound a p hp)]
  · cases h : T.leafOf a with
    | none => rfl
    | some p =>
      exact (ha (List.mem_toFinset.mpr (PhyloTree.leaf_label_mem (hT.leafOf_sound a p h)))).elim

section Lemmas

variable {α κ β : Type} [DecidableEq κ]

/-- After a loop of updates, a key that no element updates keeps its value. -/
theorem foldl_update_of_not_mem (key : α → κ) (v : α → β) (l : List α) (f : κ → β) {k : κ}
    (hk : ∀ a ∈ l, key a ≠ k) :
    (l.foldl (fun f a => Function.update f (key a) (v a)) f) k = f k := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun b hb => hk b (by simp [hb]))]
    exact Function.update_of_ne (hk a (by simp)).symm _ _

/-- After a loop of updates with distinct keys, the key of `x` holds the value of `x`. -/
theorem foldl_update_of_mem (key : α → κ) (v : α → β) (l : List α) (f : κ → β)
    (hl : (l.map key).Nodup) {x : α} (hx : x ∈ l) :
    (l.foldl (fun f a => Function.update f (key a) (v a)) f) (key x) = v x := by
  induction l generalizing f with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hl
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [foldl_update_of_not_mem key v l _ (fun b hb h => hl.1 ⟨b, hb, h⟩)]
      simp
    · exact ih _ hl.2 hx

end Lemmas

/-- The table of parents after recording a list of entries. -/
theorem foldl_record_parent (es : List Entry) (T : Tables) :
    (es.foldl (fun T x => (record T x).val) T).parent =
      es.foldl (fun f x => Function.update f x.addr x.parent) T.parent := by
  induction es generalizing T with
  | nil => rfl
  | cons x es ih => simp only [List.foldl_cons, ih]; rfl

theorem foldl_record_depth (es : List Entry) (T : Tables) :
    (es.foldl (fun T x => (record T x).val) T).depth =
      es.foldl (fun f x => Function.update f x.addr x.depth) T.depth := by
  induction es generalizing T with
  | nil => rfl
  | cons x es ih => simp only [List.foldl_cons, ih]; rfl

theorem foldl_record_kind (es : List Entry) (T : Tables) :
    (es.foldl (fun T x => (record T x).val) T).kind =
      es.foldl (fun f x => Function.update f x.addr x.kind) T.kind := by
  induction es generalizing T with
  | nil => rfl
  | cons x es ih => simp only [List.foldl_cons, ih]; rfl

theorem foldl_record_leafOf (es : List Entry) (T : Tables) :
    (es.foldl (fun T x => (record T x).val) T).leafOf =
      es.foldl (fun f x => setLeaf f x.kind x.addr) T.leafOf := by
  induction es generalizing T with
  | nil => rfl
  | cons x es ih => simp only [List.foldl_cons, ih]; rfl

theorem foldl_record_lca (es : List Entry) (T : Tables) :
    (es.foldl (fun T x => (record T x).val) T).lca = T.lca := by
  induction es generalizing T with
  | nil => rfl
  | cons x es ih => simp only [List.foldl_cons, ih]; rfl

/-- The table of leaves only records leaves of the listed entries. -/
theorem setLeaf_sound (es : List Entry) (f : ℕ → Option Address) (a : ℕ) (p : Address)
    (h : (es.foldl (fun f x => setLeaf f x.kind x.addr) f) a = some p) :
    f a = some p ∨ ∃ x ∈ es, x.kind = .leaf a ∧ x.addr = p := by
  induction es generalizing f with
  | nil => exact Or.inl h
  | cons x es ih =>
    rcases ih _ h with h' | ⟨y, hy, hk, ha⟩
    · change setLeaf f x.kind x.addr a = some p at h'
      cases hx : x.kind with
      | leaf b =>
        rw [hx] at h'
        by_cases hab : a = b
        · subst hab
          simp only [setLeaf, Function.update_self, Option.some.injEq] at h'
          exact Or.inr ⟨x, by simp, hx, h'⟩
        · simp only [setLeaf, ne_eq, hab, not_false_eq_true, Function.update_of_ne] at h'
          exact Or.inl h'
      | fork l r =>
        rw [hx] at h'
        exact Or.inl h'
    · exact Or.inr ⟨y, by simp [hy], hk, ha⟩

/-- The table of leaves has an entry for the label of every listed leaf. -/
theorem setLeaf_complete (es : List Entry) (f : ℕ → Option Address) (a : ℕ)
    (h : (∃ p, f a = some p) ∨ ∃ x ∈ es, x.kind = .leaf a) :
    ∃ p, (es.foldl (fun f x => setLeaf f x.kind x.addr) f) a = some p := by
  induction es generalizing f with
  | nil =>
    rcases h with h | ⟨x, hx, _⟩
    · exact h
    · simp at hx
  | cons x es ih =>
    apply ih
    rcases h with ⟨p, hp⟩ | ⟨y, hy, hk⟩
    · left
      cases hx : x.kind with
      | leaf b =>
        by_cases hab : a = b
        · subst hab; exact ⟨x.addr, by simp [setLeaf, hx]⟩
        · exact ⟨p, by simp [setLeaf, hx, hab, hp]⟩
      | fork l r => exact ⟨p, by simp [setLeaf, hx, hp]⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · left
        exact ⟨y.addr, by simp [setLeaf, hk]⟩
      · exact Or.inr ⟨y, hy, hk⟩

/-- The traversal of `t` from its root lists the entries of its vertices in preorder. -/
theorem val_visit_root (t : PhyloTree) :
    (visit t [] [] 0 []).val = t.preorder.map (entryAt t) := by
  have h := val_visit (t := t) (sub := t) (p := []) (by cases t <;> rfl) []
  simpa [parent] using h

/-- The tables of parents, depths, kinds and leaves after recording the entries of the vertices of
`t`. -/
theorem record_correct (t : PhyloTree) :
    let T := (t.preorder.map (entryAt t)).foldl (fun T x => (record T x).val) Tables.empty
    (∀ p ∈ t.nodes, T.parent p = parent p) ∧ (∀ p ∈ t.nodes, T.depth p = p.length) ∧
      (∀ p ∈ t.nodes, T.kind p = kindAt t p) ∧
      (∀ a p, T.leafOf a = some p → t.nodeAt p = some (.leaf a)) ∧
      (∀ a ∈ t.taxa, ∃ p, T.leafOf a = some p) ∧ T.lca = Tables.empty.lca := by
  intro T
  have hkeys : ((t.preorder.map (entryAt t)).map Entry.addr).Nodup := by
    simpa [List.map_map, Function.comp_def, entryAt] using PhyloTree.preorder_nodup t
  have hmem : ∀ p ∈ t.nodes, entryAt t p ∈ t.preorder.map (entryAt t) := fun p hp =>
    List.mem_map.mpr ⟨p, (PhyloTree.mem_preorder t p).mpr hp, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [T, foldl_record_parent]
    exact foldl_update_of_mem Entry.addr Entry.parent _ _ hkeys (hmem p hp)
  · intro p hp
    simp only [T, foldl_record_depth]
    exact foldl_update_of_mem Entry.addr Entry.depth _ _ hkeys (hmem p hp)
  · intro p hp
    simp only [T, foldl_record_kind]
    exact foldl_update_of_mem Entry.addr Entry.kind _ _ hkeys (hmem p hp)
  · intro a p h
    simp only [T, foldl_record_leafOf] at h
    rcases setLeaf_sound _ _ a p h with h0 | ⟨x, hx, hk, ha⟩
    · simp [Tables.empty] at h0
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      simp only [entryAt] at hk ha
      subst ha
      obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff q).mp ((PhyloTree.mem_preorder t q).mp hq)
      unfold kindAt at hk
      rw [hsub] at hk ⊢
      cases sub with
      | leaf b => cases hk; rfl
      | fork l r => cases hk
  · intro a ha
    simp only [T, foldl_record_leafOf]
    apply setLeaf_complete
    right
    obtain ⟨p, hp⟩ := PhyloTree.exists_leaf_address (List.mem_toFinset.mp ha)
    have hpn : p ∈ t.nodes := (t.mem_nodes_iff p).mpr ⟨_, hp⟩
    exact ⟨entryAt t p, hmem p hpn, by simp [entryAt, kindAt, hp]⟩
  · simp only [T, foldl_record_lca]

/-- The entry computed by `lcaEntry` is `lca p q`, if the tables of depths and parents are correct
and the earlier entries `(parent p, q)` (when `p ≠ q` and `|q| ≤ |p|`) and `(p, parent q)` (when
`|p| < |q|`) are. -/
theorem val_lcaEntry {t : PhyloTree} {T : Tables} {p q : Address}
    (hp : p ∈ t.nodes) (hq : q ∈ t.nodes)
    (hdepth : ∀ x ∈ t.nodes, T.depth x = x.length)
    (hparent : ∀ x ∈ t.nodes, T.parent x = parent x)
    (hleft : p ≠ q → q.length ≤ p.length → T.lca (parent p, q) = lca (parent p) q)
    (hright : p.length < q.length → T.lca (p, parent q) = lca p (parent q)) :
    (lcaEntry T p q).val = lca p q := by
  rw [lca_recurrence]
  by_cases hpq : p = q
  · simp [lcaEntry, hpq]
  · by_cases hle : q.length ≤ p.length
    · simp [lcaEntry, hpq, hle, hdepth p hp, hdepth q hq, hparent p hp, hleft hpq hle]
    · simp [lcaEntry, hpq, hle, hdepth p hp, hdepth q hq, hparent q hq, hright (by omega)]

theorem time_lcaEntry (T : Tables) (p q : Address) : (lcaEntry T p q).time ≤ 6 := by
  unfold lcaEntry
  by_cases hpq : p = q
  · simp [hpq]
  · by_cases hle : T.depth q ≤ T.depth p <;> simp [hpq, hle]

/-- The table of lowest common ancestors filled by `lcaTable` over the preorder of `t` is correct,
and the other tables are not changed. -/
theorem lcaTable_correct (t : PhyloTree) (T : Tables)
    (hdepth : ∀ x ∈ t.nodes, T.depth x = x.length)
    (hparent : ∀ x ∈ t.nodes, T.parent x = parent x) :
    let T' := (lcaTable t.preorder T).val
    T'.parent = T.parent ∧ T'.depth = T.depth ∧ T'.kind = T.kind ∧ T'.leafOf = T.leafOf ∧
      ∀ p ∈ t.nodes, ∀ q ∈ t.nodes, T'.lca (p, q) = lca p q := by
  intro T'
  -- The invariant of the outer loop: the rows of the processed vertices are correct.
  let Out : List Address → Tables → Prop := fun A U =>
    U.parent = T.parent ∧ U.depth = T.depth ∧ U.kind = T.kind ∧ U.leafOf = T.leafOf ∧
      ∀ p ∈ A, ∀ q ∈ t.preorder, U.lca (p, q) = lca p q
  have hout : Out t.preorder T' := by
    simp only [T', lcaTable, val_forList]
    apply foldl_invariant t.preorder _ Out
    · exact ⟨rfl, rfl, rfl, rfl, by simp⟩
    · intro A p B U hsplit hU
      obtain ⟨hpar, hdep, hkind, hleaf, hrows⟩ := hU
      have hpn : p ∈ t.nodes := (PhyloTree.mem_preorder t p).mp (by simp [hsplit])
      have hpA : p ∉ A := by
        have hnd := PhyloTree.preorder_nodup t
        rw [hsplit] at hnd
        exact fun h => List.disjoint_of_nodup_append hnd h (by simp)
      -- The invariant of the inner loop: in addition, the processed entries of row `p`.
      let In : List Address → Tables → Prop := fun A' V =>
        V.parent = T.parent ∧ V.depth = T.depth ∧ V.kind = T.kind ∧ V.leafOf = T.leafOf ∧
          (∀ p' ∈ A, ∀ q ∈ t.preorder, V.lca (p', q) = lca p' q) ∧
          ∀ q ∈ A', V.lca (p, q) = lca p q
      have hin : In t.preorder ((lcaRow t.preorder U p).val) := by
        simp only [lcaRow, val_forList]
        apply foldl_invariant t.preorder _ In
        · exact ⟨hpar, hdep, hkind, hleaf, hrows, by simp⟩
        · intro A' q B' V hsplit' hV
          obtain ⟨vpar, vdep, vkind, vleaf, vrows, vrow⟩ := hV
          have hqn : q ∈ t.nodes := (PhyloTree.mem_preorder t q).mp (by simp [hsplit'])
          have hqA : q ∉ A' := by
            have hnd := PhyloTree.preorder_nodup t
            rw [hsplit'] at hnd
            exact fun h => List.disjoint_of_nodup_append hnd h (by simp)
          have hentry : (lcaEntry V p q).val = lca p q := by
            apply val_lcaEntry hpn hqn
            · intro x hx; rw [vdep]; exact hdepth x hx
            · intro x hx; rw [vpar]; exact hparent x hx
            · intro hne hle
              have hp0 : p ≠ [] := by
                intro h0
                rw [h0] at hle
                exact hne (h0.trans (List.eq_nil_of_length_eq_zero (by simpa using hle)).symm)
              exact vrows _ (PhyloTree.preorder_ancestor_before hsplit (parent_prefix p)
                (EdgeAbove.parent_ne_self hp0)) q (by simp [hsplit'])
            · intro hlt
              have hq0 : q ≠ [] := by
                intro h0; rw [h0] at hlt; simp at hlt
              exact vrow _ (PhyloTree.preorder_ancestor_before hsplit' (parent_prefix q)
                (EdgeAbove.parent_ne_self hq0))
          simp only [val_bind, val_step, hentry]
          refine ⟨vpar, vdep, vkind, vleaf, ?_, ?_⟩
          · intro p' hp' q' hq'
            have hne : (p', q') ≠ (p, q) := fun h => hpA (by rw [← (Prod.mk.inj h).1]; exact hp')
            dsimp only
            rw [Function.update_of_ne hne]
            exact vrows p' hp' q' hq'
          · intro q' hq'
            rcases List.mem_append.mp hq' with hq' | hq'
            · have hne : (p, q') ≠ (p, q) :=
                fun h => hqA (by rw [← (Prod.mk.inj h).2]; exact hq')
              dsimp only
              rw [Function.update_of_ne hne]
              exact vrow q' hq'
            · rw [List.mem_singleton.mp hq']
              simp
      obtain ⟨ipar, idep, ikind, ileaf, irows, irow⟩ := hin
      refine ⟨ipar, idep, ikind, ileaf, ?_⟩
      intro p' hp' q hq
      rcases List.mem_append.mp hp' with hp' | hp'
      · exact irows p' hp' q hq
      · rw [List.mem_singleton.mp hp']
        exact irow q hq
  obtain ⟨hpar, hdep, hkind, hleaf, hrows⟩ := hout
  exact ⟨hpar, hdep, hkind, hleaf, fun p hp q hq =>
    hrows p ((PhyloTree.mem_preorder t p).mpr hp) q ((PhyloTree.mem_preorder t q).mpr hq)⟩

/-- The table of lowest common ancestors over a list of `N` vertices takes at most `N (8N + 1)`
operations. -/
theorem time_lcaTable (pre : List Address) (T : Tables) :
    (lcaTable pre T).time ≤ pre.length * (8 * pre.length + 1) := by
  unfold lcaTable
  have hrow : ∀ (U : Tables), ∀ p ∈ pre, (lcaRow pre U p).time ≤ 8 * pre.length := by
    intro U p _
    unfold lcaRow
    calc
      _ ≤ (pre.map fun _ => 7 + 1).sum := by
        apply time_forList_le
        intro V q _
        simp only [time_bind, time_step]
        have := time_lcaEntry V p q
        omega
      _ = _ := by simp; ring
  calc
    _ ≤ (pre.map fun _ => 8 * pre.length + 1).sum := time_forList_le _ pre T _ hrow
    _ = _ := by simp

/-- The preprocessing returns the vertices of `t` in preorder. -/
theorem preprocess_order (t : PhyloTree) : (preprocess t).val.2 = t.preorder := by
  simp [preprocess, val_visit_root, List.map_map, Function.comp_def, entryAt]

/-- Section 2.3: the preprocessing is correct. Its tables give the parent, the depth, the kind and
the lowest common ancestors of the vertices of `t`, and a leaf for each taxon. -/
theorem preprocess_correct (t : PhyloTree) : (preprocess t).val.1.Correct t := by
  obtain ⟨hpar, hdep, hkind, hsound, hcomplete, -⟩ := record_correct t
  have hl := lcaTable_correct t
    ((t.preorder.map (entryAt t)).foldl (fun T x => (record T x).val) Tables.empty) hdep hpar
  have hpre : (mapList (fun x => (pure x.addr : Timed Address)) (t.preorder.map (entryAt t))).val =
      t.preorder := by
    simp [List.map_map, Function.comp_def, entryAt]
  simp only [preprocess, val_bind, val_forList, val_visit_root, val_pure, hpre]
  obtain ⟨lpar, ldep, lkind, lleaf, llca⟩ := hl
  exact ⟨fun p hp => by rw [lpar]; exact hpar p hp, fun p hp => by rw [ldep]; exact hdep p hp,
    fun p hp => by rw [lkind]; exact hkind p hp,
    fun a p h => by rw [lleaf] at h; exact hsound a p h,
    fun a ha => by rw [lleaf]; exact hcomplete a ha, llca⟩

/-- Section 2.3: "The preprocessing can be computed in O(n²) time": at most `20 |V(T)|²`
operations, where `|V(T)| = 2n − 1` (`PhyloTree.nodes_count`). -/
theorem preprocess_time (t : PhyloTree) : (preprocess t).time ≤ 20 * t.nodes.card ^ 2 := by
  have hN : 1 ≤ t.nodes.card := Finset.card_pos.mpr ⟨[], PhyloTree.root_mem_nodes t⟩
  have hlen := PhyloTree.preorder_length t
  have hvisit := time_visit t [] [] 0 []
  have hrecord : (forList record (t.preorder.map (entryAt t)) Tables.empty).time ≤
      6 * t.nodes.card := by
    calc
      _ ≤ ((t.preorder.map (entryAt t)).map fun _ => 5 + 1).sum :=
        time_forList_le _ _ _ (fun _ => 5) (fun T x _ => by simp [record])
      _ = _ := by rw [sum_map_const_nat]; simp [hlen]; ring
  have hmap : (mapList (fun x => (pure x.addr : Timed Address))
      (t.preorder.map (entryAt t))).time = t.nodes.card := by
    simp [Function.comp_def, hlen]
  have hpre : (mapList (fun x => (pure x.addr : Timed Address)) (t.preorder.map (entryAt t))).val =
      t.preorder := by
    simp [List.map_map, Function.comp_def, entryAt]
  have hlca := time_lcaTable t.preorder
    ((forList record (t.preorder.map (entryAt t)) Tables.empty).val)
  rw [hlen] at hlca
  simp only [preprocess, time_bind, val_visit_root, time_pure, hpre]
  nlinarith

end Complexity
end Camus
