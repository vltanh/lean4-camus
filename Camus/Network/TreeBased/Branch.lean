module

public import Camus.Network.RootAbove.RootWire
public import Camus.Network.Clades

/-!
# The parts of a switching below its vertices

Section 2.1 obtains the trees of a rooted binary level-1 network `N` from its switchings: keep one
incoming edge at every vertex other than the root (`RootedNetwork.Switching`), then clean up. To
build the tree of a switching `S` vertex by vertex, this file cuts `S` at each vertex `v`: the
part of `N` below `v` in `S` (`RootedNetwork.branch`) has the vertices reached from `v` along
edges of `S` (`RootedNetwork.below`), the edges of `S` out of them, the root `v` and the taxa whose
leaves lie below `v` (`RootedNetwork.cladeBelow`). It proves the facts on these parts that the
construction of `Camus/Network/TreeBased/Main.lean` uses: a vertex has zero, one or two children in
`S`, the part below it is made of the vertex and the parts below its children, the parts below two
children are disjoint, a vertex is not below its children, and the edges of `S` below `v` form a
switching of the part below `v`.

## Main results

* `RootedNetwork.below`, `RootedNetwork.belowEdges`, `RootedNetwork.branch`: the part of `N`
  below a vertex of `S`.
* `RootedNetwork.children_cases`: a vertex has no child, one child or two children in `S`.
* `RootedNetwork.below_eq_of_children`, `RootedNetwork.belowEdges_eq_of_children`,
  `RootedNetwork.cladeBelow_eq_of_children`: the part below a vertex with children.
* `RootedNetwork.below_disjoint`: the parts below two children of a vertex are disjoint.
* `RootedNetwork.not_mem_below_of_edge`: a vertex is not below its children.
* `RootedNetwork.branch_switching`: the edges of `S` below `v` form a switching of the part
  below `v`.
* `RootedNetwork.below_root`, `RootedNetwork.belowEdges_root`, `RootedNetwork.cladeBelow_root`:
  below the root of `N` lies all of `N`.
-/

@[expose] public section

namespace Camus

namespace RootedNetwork

/-- The vertices of `N` below `v` in `S`: the vertices of `N` reached from `v` by a directed path
of edges of `S`, `v` included when it is a vertex of `N`. -/
noncomputable def below (N : RootedNetwork) (S : Finset (ℕ × ℕ)) (v : ℕ) : Finset ℕ := by
  classical
  exact N.vertices.filter fun x => Relation.ReflTransGen (fun a b => (a, b) ∈ S) v x

/-- The edges of `S` out of the vertices below `v` in `S`. -/
noncomputable def belowEdges (N : RootedNetwork) (S : Finset (ℕ × ℕ)) (v : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact S.filter fun e => e.1 ∈ N.below S v

/-- The part of `N` below the vertex `v` in the switching `S`: the vertices below `v`, the edges
of `S` out of them, the root `v`, and the taxa whose leaves lie below `v`. For the root of `N`, it
has the vertices, the root and the taxa of `N`, and the edges of `S` (`RootedNetwork.below_root`,
`RootedNetwork.belowEdges_root`, `RootedNetwork.cladeBelow_root`). -/
noncomputable def branch (N : RootedNetwork) (S : Finset (ℕ × ℕ)) (v : ℕ) : RootedNetwork where
  vertices := N.below S v
  edges := N.belowEdges S v
  root := v
  taxa := N.cladeBelow S v
  leaf := N.leaf

variable {N : RootedNetwork} {S : Finset (ℕ × ℕ)}

/-- A vertex is below `v` iff it is a vertex of `N` reached from `v` along edges of `S`. -/
theorem mem_below {v x : ℕ} :
    x ∈ N.below S v ↔ x ∈ N.vertices ∧ Relation.ReflTransGen (fun a b => (a, b) ∈ S) v x := by
  classical
  unfold below
  exact Finset.mem_filter

/-- An edge lies below `v` iff it is an edge of `S` whose tail is below `v`. -/
theorem mem_belowEdges {v : ℕ} {e : ℕ × ℕ} :
    e ∈ N.belowEdges S v ↔ e ∈ S ∧ e.1 ∈ N.below S v := by
  classical
  unfold belowEdges
  exact Finset.mem_filter

/-- A vertex of `N` is below itself. -/
theorem self_mem_below {v : ℕ} (hv : v ∈ N.vertices) : v ∈ N.below S v :=
  mem_below.mpr ⟨hv, .refl⟩

/-- The vertices below a child `c` of `v` in `S` are below `v`. -/
theorem below_subset_of_edge {v c : ℕ} (hvc : (v, c) ∈ S) : N.below S c ⊆ N.below S v := by
  intro x hx
  obtain ⟨hxN, hcx⟩ := mem_below.mp hx
  exact mem_below.mpr ⟨hxN, Relation.ReflTransGen.head hvc hcx⟩

/-- The vertices below `v` are `v` and the vertices below the children of `v` in `S`. -/
theorem mem_below_iff_children {v x : ℕ} (hv : v ∈ N.vertices) :
    x ∈ N.below S v ↔ x = v ∨ ∃ c, (v, c) ∈ S ∧ x ∈ N.below S c := by
  constructor
  · intro hx
    rcases (mem_below.mp hx).2.cases_head with h | ⟨c, hvc, hcx⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨c, hvc, mem_below.mpr ⟨(mem_below.mp hx).1, hcx⟩⟩
  · rintro (rfl | ⟨c, hvc, hx⟩)
    · exact self_mem_below hv
    · exact below_subset_of_edge hvc hx

/-- The vertices below a vertex `v` of `N` with children `c₁` and `c₂` in `S` (equal when `v` has
one child) are `v` and the vertices below `c₁` and `c₂`. -/
theorem below_eq_of_children {v c₁ c₂ : ℕ} (hv : v ∈ N.vertices) (h₁ : (v, c₁) ∈ S)
    (h₂ : (v, c₂) ∈ S) (hout : ∀ w, (v, w) ∈ S → w = c₁ ∨ w = c₂) :
    N.below S v = insert v (N.below S c₁ ∪ N.below S c₂) := by
  ext x
  rw [mem_below_iff_children hv, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro (h | ⟨c, hvc, hx⟩)
    · exact Or.inl h
    · rcases hout c hvc with rfl | rfl
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr ⟨c₁, h₁, h⟩
    · exact Or.inr ⟨c₂, h₂, h⟩

/-- The edges of `S` below a vertex `v` of `N` with children `c₁` and `c₂` in `S` are the edges
from `v` to `c₁` and `c₂` and the edges of `S` below `c₁` and `c₂`. -/
theorem belowEdges_eq_of_children {v c₁ c₂ : ℕ} (hv : v ∈ N.vertices) (h₁ : (v, c₁) ∈ S)
    (h₂ : (v, c₂) ∈ S) (hout : ∀ w, (v, w) ∈ S → w = c₁ ∨ w = c₂) :
    N.belowEdges S v =
      insert (v, c₁) (insert (v, c₂) (N.belowEdges S c₁ ∪ N.belowEdges S c₂)) := by
  ext e
  rw [mem_belowEdges, below_eq_of_children hv h₁ h₂ hout]
  simp only [Finset.mem_insert, Finset.mem_union, mem_belowEdges]
  constructor
  · rintro ⟨he, h | h | h⟩
    · have he' : (v, e.2) = e := Prod.ext h.symm rfl
      rcases hout e.2 (he' ▸ he) with h' | h'
      · exact Or.inl (Prod.ext h h')
      · exact Or.inr (Or.inl (Prod.ext h h'))
    · exact Or.inr (Or.inr (Or.inl ⟨he, h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨he, h⟩))
  · rintro (rfl | rfl | ⟨he, h⟩ | ⟨he, h⟩)
    · exact ⟨h₁, Or.inl rfl⟩
    · exact ⟨h₂, Or.inl rfl⟩
    · exact ⟨he, Or.inr (Or.inl h)⟩
    · exact ⟨he, Or.inr (Or.inr h)⟩

/-- Below a vertex `v` of `N` without children in `S` lies `v` alone. -/
theorem below_eq_singleton_of_childless {v : ℕ} (hv : v ∈ N.vertices)
    (hchild : ∀ w, (v, w) ∉ S) : N.below S v = {v} := by
  ext x
  rw [mem_below_iff_children hv, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨c, hvc, _⟩)
    · exact h
    · exact absurd hvc (hchild c)
  · exact Or.inl

/-- Below a vertex `v` of `N` without children in `S` lies no edge of `S`. -/
theorem belowEdges_eq_empty_of_childless {v : ℕ} (hv : v ∈ N.vertices)
    (hchild : ∀ w, (v, w) ∉ S) : N.belowEdges S v = ∅ := by
  ext e
  rw [mem_belowEdges, below_eq_singleton_of_childless hv hchild, Finset.mem_singleton]
  simp only [Finset.notMem_empty, iff_false, not_and]
  intro he h
  exact hchild e.2 (by rw [← h]; exact he)

/-- The part below a child `c` of `v` that does not contain `v` has fewer vertices than the part
below `v`. -/
theorem below_card_lt {v c : ℕ} (hv : v ∈ N.vertices) (hvc : (v, c) ∈ S)
    (hc : v ∉ N.below S c) : (N.below S c).card < (N.below S v).card :=
  Finset.card_lt_card ((Finset.ssubset_iff_of_subset (below_subset_of_edge hvc)).mpr
    ⟨v, self_mem_below hv, hc⟩)

section Switching

variable (hN : N.RootedBinaryLevelOne) (hS : N.Switching S)
include hN hS

/-- A vertex is not below its children in `S`: `N` has no directed cycle. -/
theorem not_mem_below_of_edge {v c : ℕ} (hvc : (v, c) ∈ S) : v ∉ N.below S c := by
  intro hv
  have hcv := Relation.ReflTransGen.mono (fun a b hab => hS.1 hab) _ _ (mem_below.mp hv).2
  exact hN.2.2.1 v (Relation.TransGen.head' (hS.1 hvc) hcv)

/-- Two vertices from which a vertex `x` is reached along `S` are comparable: one is reached from
the other. The edge of `S` into a vertex is unique, so the two paths to `x` agree from the point
where the shorter one starts. -/
theorem reach_comparable {c₁ c₂ x : ℕ}
    (h₁ : Relation.ReflTransGen (fun a b => (a, b) ∈ S) c₁ x)
    (h₂ : Relation.ReflTransGen (fun a b => (a, b) ∈ S) c₂ x) :
    Relation.ReflTransGen (fun a b => (a, b) ∈ S) c₁ c₂ ∨
      Relation.ReflTransGen (fun a b => (a, b) ∈ S) c₂ c₁ := by
  revert h₂
  induction h₁ with
  | refl => exact fun h₂ => Or.inr h₂
  | @tail y x h₁ hyx ih =>
    intro h₂
    rcases h₂.cases_tail with rfl | ⟨y', h₂, hy'x⟩
    · exact Or.inl (h₁.tail hyx)
    · rw [switching_incoming_unique hN hS hy'x hyx] at h₂
      exact ih h₂

/-- The vertices below two distinct children of a vertex `v` in `S` are disjoint. -/
theorem below_disjoint {v c₁ c₂ : ℕ} (h₁ : (v, c₁) ∈ S) (h₂ : (v, c₂) ∈ S) (hne : c₁ ≠ c₂) :
    Disjoint (N.below S c₁) (N.below S c₂) := by
  -- if `c₂` is reached from `c₁`, the edge of `S` into `c₂` is `(v, c₂)`, so `v` is below `c₁`
  have key : ∀ {d₁ d₂ : ℕ}, (v, d₁) ∈ S → (v, d₂) ∈ S → d₁ ≠ d₂ →
      ¬Relation.ReflTransGen (fun a b => (a, b) ∈ S) d₁ d₂ := by
    intro d₁ d₂ hd₁ hd₂ hd h
    rcases h.cases_tail with h | ⟨y, hy, hyd⟩
    · exact hd h.symm
    · rw [switching_incoming_unique hN hS hyd hd₂] at hy
      exact not_mem_below_of_edge hN hS hd₁ (mem_below.mpr ⟨(hN.2.1 _ (hS.1 hd₁)).1, hy⟩)
  refine Finset.disjoint_left.mpr fun x hx₁ hx₂ => ?_
  rcases reach_comparable hN hS (mem_below.mp hx₁).2 (mem_below.mp hx₂).2 with h | h
  · exact key h₁ h₂ hne h
  · exact key h₂ h₁ hne.symm h

/-- A vertex with a child in `S` is not the leaf of a taxon: leaves have no child in `N`. -/
theorem leaf_ne_of_edge {v c : ℕ} (hvc : (v, c) ∈ S) {a : ℕ} (ha : a ∈ N.taxa) :
    N.leaf a ≠ v := by
  intro h
  have hzero := (hN.2.2.2.2.2.2.2.1 a ha).2.2
  have hpos : 0 < N.outdegree (N.leaf a) :=
    Finset.card_pos.mpr ⟨(v, c), Finset.mem_filter.mpr ⟨hS.1 hvc, h.symm⟩⟩
  omega

/-- The edges of `S` below `v` form a switching of the part of `N` below `v`: a vertex below `v`
other than `v` has one edge of `S` into it, and its tail is below `v`. -/
theorem branch_switching (v : ℕ) : (N.branch S v).Switching (N.belowEdges S v) := by
  classical
  refine ⟨subset_rfl, fun x hx hxv => ?_⟩
  change x ∈ N.below S v at hx
  change x ≠ v at hxv
  obtain ⟨hxN, hvx⟩ := mem_below.mp hx
  rcases hvx.cases_tail with h | ⟨y, hvy, hyx⟩
  · exact absurd h hxv
  have hy : y ∈ N.below S v := mem_below.mpr ⟨(hN.2.1 _ (hS.1 hyx)).1, hvy⟩
  rw [Finset.card_eq_one]
  refine ⟨(y, x), Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨mem_belowEdges.mpr ⟨hyx, hy⟩, rfl⟩
  · intro e he
    obtain ⟨he, hex⟩ := Finset.mem_filter.mp he
    have heS := (mem_belowEdges.mp he).1
    have hey : e.1 = y := switching_incoming_unique hN hS (by rw [← hex]; exact heS) hyx
    exact Prod.ext hey hex

/-- Below the root of `N` lie all the vertices of `N` (`RootedNetwork.switching_reachable`). -/
theorem below_root : N.below S N.root = N.vertices := by
  ext x
  rw [mem_below]
  exact ⟨fun h => h.1, fun hx => ⟨hx, switching_reachable hN hS hx⟩⟩

/-- The edges of `S` below the root of `N` are all the edges of `S`. -/
theorem belowEdges_root : N.belowEdges S N.root = S := by
  ext e
  rw [mem_belowEdges, below_root hN hS]
  exact ⟨fun h => h.1, fun he => ⟨he, (hN.2.1 e (hS.1 he)).1⟩⟩

/-- The taxa below the root of `N` are all the taxa of `N`. -/
theorem cladeBelow_root : N.cladeBelow S N.root = N.taxa := by
  ext a
  rw [mem_cladeBelow]
  exact ⟨fun h => h.1,
    fun ha => ⟨ha, switching_reachable hN hS (hN.2.2.2.2.2.2.2.1 a ha).1⟩⟩

/-- The taxa below a vertex `v` with children `c₁` and `c₂` in `S` (equal when `v` has one child)
are the taxa below `c₁` and `c₂`: `v` is not a leaf. -/
theorem cladeBelow_eq_of_children {v c₁ c₂ : ℕ} (h₁ : (v, c₁) ∈ S) (h₂ : (v, c₂) ∈ S)
    (hout : ∀ w, (v, w) ∈ S → w = c₁ ∨ w = c₂) :
    N.cladeBelow S v = N.cladeBelow S c₁ ∪ N.cladeBelow S c₂ := by
  ext a
  rw [Finset.mem_union, mem_cladeBelow, mem_cladeBelow, mem_cladeBelow]
  constructor
  · rintro ⟨ha, hr⟩
    rcases hr.cases_head with h | ⟨c, hvc, hc⟩
    · exact absurd h.symm (leaf_ne_of_edge hN hS h₁ ha)
    · rcases hout c hvc with rfl | rfl
      · exact Or.inl ⟨ha, hc⟩
      · exact Or.inr ⟨ha, hc⟩
  · rintro (⟨ha, hc⟩ | ⟨ha, hc⟩)
    · exact ⟨ha, Relation.ReflTransGen.head h₁ hc⟩
    · exact ⟨ha, Relation.ReflTransGen.head h₂ hc⟩

omit hS in
/-- The taxa below a vertex `v` without children in `S` are the taxon `a` whose leaf is `v`. -/
theorem cladeBelow_eq_singleton_of_childless {v : ℕ} (hchild : ∀ w, (v, w) ∉ S) {a : ℕ}
    (ha : a ∈ N.taxa) (hleaf : N.leaf a = v) : N.cladeBelow S v = {a} := by
  ext b
  rw [mem_cladeBelow, Finset.mem_singleton]
  constructor
  · rintro ⟨hb, hr⟩
    rcases hr.cases_head with h | ⟨c, hvc, _⟩
    · exact hN.2.2.2.2.2.2.1 hb ha (h.symm.trans hleaf.symm)
    · exact absurd hvc (hchild c)
  · rintro rfl
    exact ⟨ha, hleaf ▸ .refl⟩

omit hS in
/-- The leaf of a taxon below `c` is a vertex below `c`. -/
theorem leaf_mem_below {c a : ℕ} (ha : a ∈ N.cladeBelow S c) : N.leaf a ∈ N.below S c :=
  mem_below.mpr ⟨(hN.2.2.2.2.2.2.2.1 a (mem_cladeBelow.mp ha).1).1, (mem_cladeBelow.mp ha).2⟩

/-- A vertex `v` of `N` has no child in `S`, one child, or two distinct children. -/
theorem children_cases {v : ℕ} (hv : v ∈ N.vertices) :
    (∀ w, (v, w) ∉ S) ∨ (∃ c, (v, c) ∈ S ∧ ∀ w, (v, w) ∈ S → w = c) ∨
      ∃ c₁ c₂, c₁ ≠ c₂ ∧ (v, c₁) ∈ S ∧ (v, c₂) ∈ S ∧ ∀ w, (v, w) ∈ S → w = c₁ ∨ w = c₂ := by
  classical
  set C := S.filter (fun e => e.1 = v) with hC
  have hle : C.card ≤ 2 :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hS.1)).trans (outdegree_le_two hN hv)
  have hmem : ∀ w, (v, w) ∈ S ↔ (v, w) ∈ C :=
    fun w => ⟨fun h => Finset.mem_filter.mpr ⟨h, rfl⟩, fun h => (Finset.mem_filter.mp h).1⟩
  have hedge : ∀ e ∈ C, (v, e.2) ∈ S := by
    intro e he
    obtain ⟨heS, he1⟩ := Finset.mem_filter.mp he
    have he' : (v, e.2) = e := Prod.ext he1.symm rfl
    rw [he']
    exact heS
  rcases (by omega : C.card = 0 ∨ C.card = 1 ∨ C.card = 2) with h | h | h
  · left
    intro w hw
    rw [Finset.card_eq_zero.mp h] at hmem
    exact Finset.notMem_empty _ ((hmem w).mp hw)
  · right; left
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp h
    refine ⟨e.2, hedge e (he ▸ Finset.mem_singleton_self e), fun w hw => ?_⟩
    have hw' := (hmem w).mp hw
    rw [he, Finset.mem_singleton] at hw'
    rw [← hw']
  · right; right
    obtain ⟨e₁, e₂, hne, he⟩ := Finset.card_eq_two.mp h
    have he₁ : e₁ ∈ C := he ▸ Finset.mem_insert_self _ _
    have he₂ : e₂ ∈ C := he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    refine ⟨e₁.2, e₂.2, fun h12 => hne ?_, hedge e₁ he₁, hedge e₂ he₂, fun w hw => ?_⟩
    · exact Prod.ext ((Finset.mem_filter.mp he₁).2.trans (Finset.mem_filter.mp he₂).2.symm) h12
    · have hw' := (hmem w).mp hw
      rw [he, Finset.mem_insert, Finset.mem_singleton] at hw'
      rcases hw' with h' | h'
      · exact Or.inl (by rw [← h'])
      · exact Or.inr (by rw [← h'])

end Switching

end RootedNetwork

end Camus
