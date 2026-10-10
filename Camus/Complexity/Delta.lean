module

public import Camus.Complexity.Tables
public import Camus.Network.SingleEdge
public import Camus.Network.Baseline.Clades

/-!
# Section 2.3: δ_T in constant time

Section 2.3 of the paper states that after the preprocessing, δ_T(q, (u, w)) "for a single triplet
q, u, w" takes `O(1)` time, "since determining which quartets are induced can be determined by the
nodes they attach to in the cycle". This file proves the remark and writes the test as a program
with a constant number of table reads and comparisons (`Complexity.delta`), which returns
`EdgeAbove.satisfies t e q` (δ_T of Definition 4) in at most `130` operations.

`EdgeAbove.satisfies t e q` asks that the taxa of `q` be taxa of `T`, that `T` not induce `q`,
and that some clade of the tree `T'` displayed by `T + e` through the added edge
(`EdgeAbove.switchedClades`) cut `q`, that is, contain one side of `q` and avoid the other. Both
tests reduce to ancestor tests between the leaves of `q`, the donor `u` and the recipient `w`:

* `T` induces `ab|cd` iff the clade of `lca(a, b)` contains neither `c` nor `d`, or the clade of
  `lca(c, d)` contains neither `a` nor `b` (`exists_clade_iff`): the clades containing `a` and `b`
  are those of the ancestors of `lca(a, b)`, and the smallest is that of `lca(a, b)`.
* The same holds in `T'` with its own lowest common ancestors (`exists_switchedClade_iff`). The
  lowest vertex of `T'` above two leaves `x`, `y` of `T` (`Complexity.lowest`) is `lca(x, y)` if
  both or neither lie below `w`; if only `x` does, it is the new vertex u' above `u` when `y` lies
  below `u`, and `lca(u, y)` otherwise (`below_lowest_left`, `below_of_below_lowest`).
* A leaf `x` lies below a vertex `p` of `T` in `T'` iff `p` is an ancestor of `x` in `T`, except
  that the leaves below `w` leave the strict ancestors of `w` and join the strict ancestors of `u`
  (`mem_switchedClade_iff`): a Boolean combination of ancestor tests among `p`, `u`, `w` and `x`.

Each ancestor test `p <+: x` is one read of the table of lowest common ancestors and one comparison
(`prefix_iff_lca`).

## Main results

* `Complexity.exists_clade_iff`, `Complexity.exists_switchedClade_iff`: the remark, for `T` and
  for `T'`.
* `Complexity.delta`: the test, as a program.
* `Complexity.val_delta`: it computes `EdgeAbove.satisfies t e q`.
* `Complexity.time_delta`: it takes at most `130` operations.
-/

@[expose] public section

namespace Camus

namespace Complexity

open Timed

section Clades

variable {t : PhyloTree}

/-- In a well-labelled tree, the taxon `α` with leaf `x` is in the clade of `p` iff `p` is an
ancestor of `x` (or `x` itself). -/
theorem mem_taxaAt_iff (ht : t.WellLabelled) {x : Address} {α : ℕ}
    (hx : t.nodeAt x = some (.leaf α)) (p : Address) : α ∈ t.taxaAt p ↔ p <+: x := by
  have hxn : x ∈ t.nodes := (t.mem_nodes_iff x).mpr ⟨_, hx⟩
  have hα : α ∈ t.taxa := List.mem_toFinset.mpr (PhyloTree.leaf_label_mem hx)
  cases hp : t.nodeAt p with
  | none =>
    simp only [PhyloTree.taxaAt, hp, Finset.notMem_empty, false_iff]
    intro hpx
    obtain ⟨s, hs⟩ := (t.mem_nodes_iff p).mp (t.nodes_prefix_closed hxn hpx)
    rw [hp] at hs
    cases hs
  | some sub =>
    simp only [PhyloTree.taxaAt, hp]
    rw [PhyloTree.subtree_taxa_iff_prefix ht hp hα, Realization.leafAddress_eq ht hx]

/-- The clades of `T` are the clades of its vertices. -/
theorem mem_clades_iff (t : PhyloTree) (C : Finset ℕ) :
    C ∈ t.clades ↔ ∃ p ∈ t.nodes, C = t.taxaAt p := by
  rw [PhyloTree.clades_mem_iff]
  constructor
  · rintro ⟨p, sub, hp, rfl⟩
    exact ⟨p, (t.mem_nodes_iff p).mpr ⟨sub, hp⟩, by simp [PhyloTree.taxaAt, hp]⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨sub, hs⟩ := (t.mem_nodes_iff p).mp hp
    exact ⟨p, sub, hs, by simp [PhyloTree.taxaAt, hs]⟩

/-- Section 2.3, for `T`: for taxa `τ₁, …, τ₄` with leaves `x₁, …, x₄`, some clade of `T` contains
`τ₁` and `τ₂` and avoids `τ₃` and `τ₄` iff `lca(x₁, x₂)` is an ancestor of neither `x₃` nor
`x₄`. -/
theorem exists_clade_iff (ht : t.WellLabelled) {x₁ x₂ x₃ x₄ : Address} {τ₁ τ₂ τ₃ τ₄ : ℕ}
    (h₁ : t.nodeAt x₁ = some (.leaf τ₁)) (h₂ : t.nodeAt x₂ = some (.leaf τ₂))
    (h₃ : t.nodeAt x₃ = some (.leaf τ₃)) (h₄ : t.nodeAt x₄ = some (.leaf τ₄)) :
    (∃ C ∈ t.clades, τ₁ ∈ C ∧ τ₂ ∈ C ∧ τ₃ ∉ C ∧ τ₄ ∉ C) ↔
      ¬lca x₁ x₂ <+: x₃ ∧ ¬lca x₁ x₂ <+: x₄ := by
  constructor
  · rintro ⟨C, hC, i₁, i₂, i₃, i₄⟩
    obtain ⟨p, -, rfl⟩ := (mem_clades_iff t C).mp hC
    rw [mem_taxaAt_iff ht h₁] at i₁
    rw [mem_taxaAt_iff ht h₂] at i₂
    rw [mem_taxaAt_iff ht h₃] at i₃
    rw [mem_taxaAt_iff ht h₄] at i₄
    have hp := prefix_lca i₁ i₂
    exact ⟨fun h => i₃ (hp.trans h), fun h => i₄ (hp.trans h)⟩
  · rintro ⟨n₃, n₄⟩
    have hx₁ : x₁ ∈ t.nodes := (t.mem_nodes_iff x₁).mpr ⟨_, h₁⟩
    refine ⟨t.taxaAt (lca x₁ x₂), (mem_clades_iff t _).mpr
      ⟨_, t.nodes_prefix_closed hx₁ (lca_prefix_left _ _), rfl⟩, ?_⟩
    rw [mem_taxaAt_iff ht h₁, mem_taxaAt_iff ht h₂, mem_taxaAt_iff ht h₃, mem_taxaAt_iff ht h₄]
    exact ⟨lca_prefix_left _ _, lca_prefix_right _ _, n₃, n₄⟩

end Clades

section Switched

/-- In the tree `T'` displayed by `T + e` through the added edge `e = (u, w)`, the leaf `x` of `T`
lies below the vertex `p` of `T` (`EdgeAbove.switchedClade`): `p` is a strict ancestor of `w`, an
ancestor of `x`, and `x` is not below `w`; or `p` is not a strict ancestor of `w` and is an
ancestor of `x`; or `p` is a strict ancestor of `u` and `x` is below `w`. -/
def belowOld (e : Address × Address) (p x : Address) : Prop :=
  (p <+: e.2 ∧ p ≠ e.2 ∧ p <+: x ∧ ¬e.2 <+: x) ∨ (¬(p <+: e.2 ∧ p ≠ e.2) ∧ p <+: x) ∨
    (p <+: e.1 ∧ p ≠ e.1 ∧ e.2 <+: x)

instance (e : Address × Address) (p x : Address) : Decidable (belowOld e p x) := by
  unfold belowOld; infer_instance

/-- `belowOld`, by whether `x` lies below `w`: if it does, `x` is below `p` in `T'` iff `p` lies
between `w` and `x`, or `p` is a strict ancestor of `u`; if not, iff `p` is an ancestor of `x`. -/
theorem belowOld_iff (e : Address × Address) (p x : Address) :
    belowOld e p x ↔ if e.2 <+: x then (e.2 <+: p ∧ p <+: x) ∨ (p <+: e.1 ∧ p ≠ e.1)
      else p <+: x := by
  unfold belowOld
  by_cases hw : e.2 <+: x
  · simp only [hw, not_true_eq_false, and_false, false_or, and_true, ↓reduceIte]
    constructor
    · rintro (⟨hstrict, hpx⟩ | hu)
      · left
        refine ⟨?_, hpx⟩
        rcases List.prefix_or_prefix_of_prefix hpx hw with h | h
        · by_cases hpw : p = e.2
          · rw [hpw]
          · exact (hstrict ⟨h, hpw⟩).elim
        · exact h
      · exact Or.inr hu
    · rintro (⟨hwp, hpx⟩ | hu)
      · left
        refine ⟨fun ⟨hpw, hne⟩ => hne (prefix_antisymm hpw hwp), hpx⟩
      · exact Or.inr hu
  · simp only [hw, not_false_eq_true, and_true, and_false, or_false, ↓reduceIte]
    tauto

/-- A vertex of the tree `T'` displayed by `T + e` through the added edge `e = (u, w)`: a vertex
`p` of `T`, the new vertex u' above the donor, or the new vertex w' above the recipient. -/
inductive SwitchedVertex where
  | old (p : Address)
  | donor
  | recipient
  deriving DecidableEq

namespace SwitchedVertex

/-- The clade of a vertex of `T'`: `EdgeAbove.switchedClade t e p` for a vertex `p` of `T`, the
clade of `u` in `T'` together with `T_w` for u', and `T_w` for w'. These are the members of
`EdgeAbove.switchedClades t e`. -/
def clade (t : PhyloTree) (e : Address × Address) : SwitchedVertex → Finset ℕ
  | old p => EdgeAbove.switchedClade t e p
  | donor => EdgeAbove.switchedClade t e e.1 ∪ t.taxaAt e.2
  | recipient => t.taxaAt e.2

/-- The leaf `x` of `T` lies below the vertex `s` of `T'`, by ancestor tests in `T`. -/
def below (e : Address × Address) : SwitchedVertex → Address → Prop
  | old p, x => belowOld e p x
  | donor, x => belowOld e e.1 x ∨ e.2 <+: x
  | recipient, x => e.2 <+: x

instance (e : Address × Address) (s : SwitchedVertex) (x : Address) : Decidable (below e s x) := by
  cases s <;> unfold below <;> infer_instance

end SwitchedVertex

open SwitchedVertex

variable {t : PhyloTree}

/-- Section 2.3: membership of a taxon in a clade of `T'` is a Boolean combination of ancestor
tests in `T` among `p`, `u`, `w` and the leaf of the taxon. -/
theorem mem_switchedClade_iff (ht : t.WellLabelled) {x : Address} {α : ℕ}
    (hx : t.nodeAt x = some (.leaf α)) (e : Address × Address) (p : Address) :
    α ∈ EdgeAbove.switchedClade t e p ↔ belowOld e p x := by
  unfold EdgeAbove.switchedClade belowOld
  rw [Finset.mem_union]
  split_ifs with h₁ h₂ h₂
  · simp only [Finset.mem_sdiff, mem_taxaAt_iff ht hx]
    tauto
  · simp only [Finset.mem_sdiff, mem_taxaAt_iff ht hx, Finset.notMem_empty, or_false]
    tauto
  · simp only [mem_taxaAt_iff ht hx]
    tauto
  · simp only [mem_taxaAt_iff ht hx, Finset.notMem_empty, or_false]
    tauto

/-- The taxon with leaf `x` is in the clade of the vertex `s` of `T'` iff `x` lies below `s`. -/
theorem mem_clade_iff (ht : t.WellLabelled) {x : Address} {α : ℕ}
    (hx : t.nodeAt x = some (.leaf α)) (e : Address × Address) (s : SwitchedVertex) :
    α ∈ s.clade t e ↔ below e s x := by
  cases s with
  | old p => exact mem_switchedClade_iff ht hx e p
  | donor =>
    simp only [clade, below, Finset.mem_union, mem_switchedClade_iff ht hx, mem_taxaAt_iff ht hx]
  | recipient => exact mem_taxaAt_iff ht hx _

/-- The clades of `T'` are the clades of its vertices: of the vertices of `T`, of u' and of w'. -/
theorem mem_switchedClades_iff (e : Address × Address) (C : Finset ℕ) :
    C ∈ EdgeAbove.switchedClades t e ↔
      C = donor.clade t e ∨ C = recipient.clade t e ∨ ∃ p ∈ t.nodes, C = (old p).clade t e := by
  simp only [EdgeAbove.switchedClades, Finset.mem_insert, Finset.mem_image, clade]
  constructor
  · rintro (h | h | ⟨p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨p, hp, rfl⟩)
  · rintro (h | h | ⟨p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨p, hp, rfl⟩)

/-- The lowest vertex of `T'` above the leaves `x` and `y` of `T`, for `e = (u, w)`: `lca(x, y)`
if both or neither of `x`, `y` lie below `w`; otherwise, with `z` the one not below `w`, the new
vertex u' if `z` lies below `u`, and `lca(u, z)` if not. -/
def lowest (e : Address × Address) (x y : Address) : SwitchedVertex :=
  if decide (e.2 <+: x) = decide (e.2 <+: y) then .old (lca x y)
  else
    let z := if e.2 <+: x then y else x
    if e.1 <+: z then .donor else .old (lca e.1 z)

theorem lowest_comm (e : Address × Address) (x y : Address) : lowest e x y = lowest e y x := by
  unfold lowest
  by_cases hx : e.2 <+: x <;> by_cases hy : e.2 <+: y <;> simp [hx, hy, lca_comm]

/-- If `w` is not an ancestor of `u`, then a vertex between `w` and `x` is not an ancestor of
`u`. -/
theorem not_prefix_donor {e : Address × Address} (he : ¬e.2 <+: e.1) {p : Address}
    (hwp : e.2 <+: p) : ¬p <+: e.1 := fun h => he (hwp.trans h)

/-- A vertex below `lca(u, z)`... the strict ancestors of `u` below `p`: if `p <+: m` and `m` is a
strict ancestor of `u`, so is `p`. -/
theorem strict_of_prefix {p m u : Address} (hpm : p <+: m) (hmu : m <+: u) (hne : m ≠ u) :
    p <+: u ∧ p ≠ u := by
  refine ⟨hpm.trans hmu, fun h => hne ?_⟩
  rw [h] at hpm
  exact prefix_antisymm hmu hpm

/-- The lowest vertex of `T'` above `x` and `y` when both or neither lie below `w`. -/
theorem lowest_same {e : Address × Address} {x y : Address} (h : e.2 <+: x ↔ e.2 <+: y) :
    lowest e x y = .old (lca x y) := by
  unfold lowest
  rw [ite_eq_left (decide_eq_decide.mpr h)]

/-- The lowest vertex of `T'` above `x` and `y` when `x` lies below `w` and `y` does not. -/
theorem lowest_split {e : Address × Address} {x y : Address} (hx : e.2 <+: x) (hy : ¬e.2 <+: y) :
    lowest e x y = if e.1 <+: y then .donor else .old (lca e.1 y) := by
  unfold lowest
  rw [ite_eq_right (by simp [hx, hy])]
  simp only [hx, ↓reduceIte]

/-- Both leaves lie below their lowest vertex in `T'`, in the case where `x` lies below `w` and `y`
does not. -/
theorem below_lowest_split {e : Address × Address} {x y : Address} (hx : e.2 <+: x)
    (hy : ¬e.2 <+: y) : below e (lowest e x y) x ∧ below e (lowest e x y) y := by
  rw [lowest_split hx hy]
  by_cases huy : e.1 <+: y
  · rw [ite_eq_left huy]
    simp only [below, belowOld_iff, hy, ↓reduceIte]
    exact ⟨Or.inr hx, Or.inl huy⟩
  · rw [ite_eq_right huy]
    simp only [below, belowOld_iff, hx, hy, ↓reduceIte]
    refine ⟨Or.inr ⟨lca_prefix_left _ _, fun h => huy ?_⟩, lca_prefix_right _ _⟩
    rw [← h]
    exact lca_prefix_right _ _

/-- Section 2.3: the leaf `x` lies below the lowest vertex of `T'` above `x` and `y`. -/
theorem below_lowest_left (e : Address × Address) (x y : Address) :
    below e (lowest e x y) x := by
  by_cases hx : e.2 <+: x <;> by_cases hy : e.2 <+: y
  · rw [lowest_same (by simp [hx, hy])]
    simp only [below, belowOld_iff, hx, ↓reduceIte]
    exact Or.inl ⟨prefix_lca hx hy, lca_prefix_left _ _⟩
  · exact (below_lowest_split hx hy).1
  · rw [lowest_comm]
    exact (below_lowest_split hy hx).2
  · rw [lowest_same (by simp [hx, hy])]
    simp only [below, belowOld_iff, hx, ↓reduceIte]
    exact lca_prefix_left _ _

/-- The leaf `y` lies below the lowest vertex of `T'` above `x` and `y`. -/
theorem below_lowest_right (e : Address × Address) (x y : Address) :
    below e (lowest e x y) y := by
  rw [lowest_comm]
  exact below_lowest_left e y x

/-- The minimality of `lowest` in the case where `x` lies below `w` and `y` does not. -/
theorem below_of_below_lowest_split {e : Address × Address} {x y z : Address}
    (hwx : e.2 <+: x) (hwy : ¬e.2 <+: y) (s : SwitchedVertex)
    (hx : below e s x) (hy : below e s y) (hz : below e (lowest e x y) z) : below e s z := by
  rw [lowest_split hwx hwy] at hz
  cases s with
  | recipient => exact (hwy hy).elim
  | donor =>
    by_cases huy : e.1 <+: y
    · rw [ite_eq_left huy] at hz
      exact hz
    · -- the donor is not above `y`
      simp only [below, belowOld_iff, hwy, ↓reduceIte, or_false] at hy
      exact (huy hy).elim
  | old p =>
    simp only [below, belowOld_iff, hwx, hwy, ↓reduceIte] at hx hy
    -- `p` is a strict ancestor of `u` and an ancestor of `y`
    have hpu : p <+: e.1 ∧ p ≠ e.1 := by
      rcases hx with ⟨hwp, -⟩ | hpu
      · exact (hwy (hwp.trans hy)).elim
      · exact hpu
    simp only [below, belowOld_iff]
    by_cases hwz : e.2 <+: z
    · simp only [hwz, ↓reduceIte]
      exact Or.inr hpu
    · simp only [hwz, ↓reduceIte]
      by_cases huy : e.1 <+: y
      · rw [ite_eq_left huy] at hz
        simp only [below, belowOld_iff, hwz, ↓reduceIte, or_false] at hz
        exact hpu.1.trans hz
      · rw [ite_eq_right huy] at hz
        simp only [below, belowOld_iff, hwz, ↓reduceIte] at hz
        exact (prefix_lca hpu.1 hy).trans hz

/-- Section 2.3: the lowest vertex of `T'` above `x` and `y` is below every vertex of `T'` above
both: every leaf below it lies below such a vertex. -/
theorem below_of_below_lowest {e : Address × Address} (he : ¬e.2 <+: e.1) {x y z : Address}
    (s : SwitchedVertex) (hx : below e s x) (hy : below e s y)
    (hz : below e (lowest e x y) z) : below e s z := by
  by_cases hwx : e.2 <+: x <;> by_cases hwy : e.2 <+: y
  · -- both below `w`: the lowest vertex is `m = lca(x, y)`, between `w` and `z`
    rw [lowest_same (by simp [hwx, hwy])] at hz
    have hwm : e.2 <+: lca x y := prefix_lca hwx hwy
    have hmz : e.2 <+: z ∧ lca x y <+: z := by
      simp only [below, belowOld_iff] at hz
      by_cases hwz : e.2 <+: z
      · simp only [hwz, ↓reduceIte] at hz
        rcases hz with ⟨-, hmz⟩ | ⟨hmu, -⟩
        · exact ⟨hwz, hmz⟩
        · exact (not_prefix_donor he hwm hmu).elim
      · simp only [hwz, ↓reduceIte] at hz
        exact (hwz (hwm.trans hz)).elim
    cases s with
    | recipient => exact hmz.1
    | donor => exact Or.inr hmz.1
    | old p =>
      simp only [below, belowOld_iff, hwx, hwy, hmz.1, ↓reduceIte] at hx hy ⊢
      rcases hx with ⟨hwp, hpx⟩ | hpu
      · rcases hy with ⟨-, hpy⟩ | hpu
        · exact Or.inl ⟨hwp, (prefix_lca hpx hpy).trans hmz.2⟩
        · exact Or.inr hpu
      · exact Or.inr hpu
  · exact below_of_below_lowest_split hwx hwy s hx hy hz
  · rw [lowest_comm] at hz
    exact below_of_below_lowest_split hwy hwx s hy hx hz
  · -- neither below `w`: the lowest vertex is `m = lca(x, y)`
    rw [lowest_same (by simp [hwx, hwy])] at hz
    simp only [below, belowOld_iff] at hz
    cases s with
    | recipient => exact (hwx hx).elim
    | donor =>
      simp only [below, belowOld_iff, hwx, hwy, ↓reduceIte, or_false] at hx hy
      by_cases hwz : e.2 <+: z
      · exact Or.inr hwz
      · simp only [hwz, ↓reduceIte] at hz
        left
        simp only [belowOld_iff, hwz, ↓reduceIte]
        exact (prefix_lca hx hy).trans hz
    | old p =>
      simp only [below, belowOld_iff, hwx, hwy, ↓reduceIte] at hx hy ⊢
      have hpm := prefix_lca hx hy
      by_cases hwz : e.2 <+: z
      · simp only [hwz, ↓reduceIte] at hz ⊢
        rcases hz with ⟨hwm, -⟩ | ⟨hmu, hmne⟩
        · exact (hwx (hwm.trans (lca_prefix_left _ _))).elim
        · exact Or.inr (strict_of_prefix hpm hmu hmne)
      · simp only [hwz, ↓reduceIte] at hz ⊢
        exact hpm.trans hz

/-- The lowest vertex of `T'` above `x` and `y` is `lca(x, y)`, the new vertex u', or `lca(u, z)`
for some `z`. -/
theorem lowest_cases (e : Address × Address) (x y : Address) :
    lowest e x y = .old (lca x y) ∨ lowest e x y = .donor ∨
      ∃ z, lowest e x y = .old (lca e.1 z) := by
  by_cases hx : e.2 <+: x <;> by_cases hy : e.2 <+: y
  · exact Or.inl (lowest_same (by simp [hx, hy]))
  · rw [lowest_split hx hy]
    split_ifs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨y, rfl⟩)
  · rw [lowest_comm, lowest_split hy hx]
    split_ifs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨x, rfl⟩)
  · exact Or.inl (lowest_same (by simp [hx, hy]))

/-- The lowest vertex of `T'` above two vertices of `T` has its clade among the clades of `T'`. -/
theorem lowest_mem {e : Address × Address} (he : EdgeAbove.Admissible t e) {x y : Address}
    (hx : x ∈ t.nodes) : (lowest e x y).clade t e ∈ EdgeAbove.switchedClades t e := by
  rw [mem_switchedClades_iff]
  rcases lowest_cases e x y with h | h | ⟨z, h⟩ <;> rw [h]
  · exact Or.inr (Or.inr ⟨_, t.nodes_prefix_closed hx (lca_prefix_left _ _), rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨_, t.nodes_prefix_closed he.1 (lca_prefix_left _ _), rfl⟩)

/-- Section 2.3, for `T'`: for taxa `τ₁, …, τ₄` of `T` with leaves `x₁, …, x₄`, some clade of
`T'` contains `τ₁` and `τ₂` and avoids `τ₃` and `τ₄` iff neither `x₃` nor `x₄` lies below the
lowest vertex of `T'` above `x₁` and `x₂`. -/
theorem exists_switchedClade_iff (ht : t.WellLabelled) {e : Address × Address}
    (he : EdgeAbove.Admissible t e) {x₁ x₂ x₃ x₄ : Address} {τ₁ τ₂ τ₃ τ₄ : ℕ}
    (h₁ : t.nodeAt x₁ = some (.leaf τ₁)) (h₂ : t.nodeAt x₂ = some (.leaf τ₂))
    (h₃ : t.nodeAt x₃ = some (.leaf τ₃)) (h₄ : t.nodeAt x₄ = some (.leaf τ₄)) :
    (∃ C ∈ EdgeAbove.switchedClades t e, τ₁ ∈ C ∧ τ₂ ∈ C ∧ τ₃ ∉ C ∧ τ₄ ∉ C) ↔
      ¬below e (lowest e x₁ x₂) x₃ ∧ ¬below e (lowest e x₁ x₂) x₄ := by
  have hwu : ¬e.2 <+: e.1 := he.2.2.2.2
  constructor
  · rintro ⟨C, hC, i₁, i₂, i₃, i₄⟩
    have hs : ∃ s : SwitchedVertex, C = s.clade t e := by
      rcases (mem_switchedClades_iff e C).mp hC with h | h | ⟨p, -, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    obtain ⟨s, rfl⟩ := hs
    rw [mem_clade_iff ht h₁] at i₁
    rw [mem_clade_iff ht h₂] at i₂
    rw [mem_clade_iff ht h₃] at i₃
    rw [mem_clade_iff ht h₄] at i₄
    exact ⟨fun h => i₃ (below_of_below_lowest hwu s i₁ i₂ h),
      fun h => i₄ (below_of_below_lowest hwu s i₁ i₂ h)⟩
  · rintro ⟨n₃, n₄⟩
    have hx₁ : x₁ ∈ t.nodes := (t.mem_nodes_iff x₁).mpr ⟨_, h₁⟩
    refine ⟨_, lowest_mem (y := x₂) he hx₁, ?_⟩
    rw [mem_clade_iff ht h₁, mem_clade_iff ht h₂, mem_clade_iff ht h₃, mem_clade_iff ht h₄]
    exact ⟨below_lowest_left e _ _, below_lowest_right e _ _, n₃, n₄⟩

end Switched

section Quartets

open SwitchedVertex

/-- The four taxa (or leaves) `a, b, c, d` of a quartet, listed as its two sides for the split
`s`: `(a, b, c, d)` for ab|cd, `(a, c, b, d)` for ac|bd, `(a, d, b, c)` for ad|bc. -/
def bySplit {β : Type} (s : Fin 3) (a b c d : β) : β × β × β × β :=
  if s = 0 then (a, b, c, d) else if s = 1 then (a, c, b, d) else (a, d, b, c)

/-- A relation that holds between the four pairs `(a, a')`, …, `(d, d')` holds between the
corresponding components of `bySplit`. -/
theorem bySplit_rel {β γ : Type} (R : β → γ → Prop) (s : Fin 3) {a b c d : β} {a' b' c' d' : γ}
    (ha : R a a') (hb : R b b') (hc : R c c') (hd : R d d') :
    R (bySplit s a b c d).1 (bySplit s a' b' c' d').1 ∧
      R (bySplit s a b c d).2.1 (bySplit s a' b' c' d').2.1 ∧
      R (bySplit s a b c d).2.2.1 (bySplit s a' b' c' d').2.2.1 ∧
      R (bySplit s a b c d).2.2.2 (bySplit s a' b' c' d').2.2.2 := by
  unfold bySplit
  split_ifs <;> exact ⟨‹_›, ‹_›, ‹_›, ‹_›⟩

/-- The sides of `q`, by `bySplit`. -/
theorem sides_eq_bySplit (q : Quartet) :
    q.sides = ({(bySplit q.split q.a q.b q.c q.d).1, (bySplit q.split q.a q.b q.c q.d).2.1},
      {(bySplit q.split q.a q.b q.c q.d).2.2.1, (bySplit q.split q.a q.b q.c q.d).2.2.2}) := by
  unfold Quartet.sides bySplit
  split_ifs <;> rfl

/-- `q.cutBy C`: `C` contains the two taxa of one side of `q` and neither taxon of the other. -/
theorem cutBy_iff (q : Quartet) (C : Finset ℕ) :
    q.cutBy C = true ↔
      let s := bySplit q.split q.a q.b q.c q.d
      (s.1 ∈ C ∧ s.2.1 ∈ C ∧ s.2.2.1 ∉ C ∧ s.2.2.2 ∉ C) ∨
        (s.2.2.1 ∈ C ∧ s.2.2.2 ∈ C ∧ s.1 ∉ C ∧ s.2.1 ∉ C) := by
  unfold Quartet.cutBy
  rw [sides_eq_bySplit]
  simp only [decide_eq_true_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff,
    Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
  tauto

variable {t : PhyloTree}

/-- Section 2.3: whether `T` induces `q`, by ancestor tests among its leaves. With `x₁, y₁` the
leaves of one side of `q` and `x₂, y₂` those of the other, `T` induces `q` iff `lca(x₁, y₁)` is an
ancestor of neither `x₂` nor `y₂`, or `lca(x₂, y₂)` of neither `x₁` nor `y₁`. -/
theorem induced_iff (ht : t.WellLabelled) {q : Quartet} {la lb lc ld : Address}
    (ha : t.nodeAt la = some (.leaf q.a)) (hb : t.nodeAt lb = some (.leaf q.b))
    (hc : t.nodeAt lc = some (.leaf q.c)) (hd : t.nodeAt ld = some (.leaf q.d)) :
    let x := bySplit q.split la lb lc ld
    q.induced t = true ↔
      (¬lca x.1 x.2.1 <+: x.2.2.1 ∧ ¬lca x.1 x.2.1 <+: x.2.2.2) ∨
        (¬lca x.2.2.1 x.2.2.2 <+: x.1 ∧ ¬lca x.2.2.1 x.2.2.2 <+: x.2.1) := by
  intro x
  have hq : q.taxa ⊆ t.taxa := by
    intro τ hτ
    simp only [Quartet.taxa, Finset.mem_insert, Finset.mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl
    · exact List.mem_toFinset.mpr (PhyloTree.leaf_label_mem ha)
    · exact List.mem_toFinset.mpr (PhyloTree.leaf_label_mem hb)
    · exact List.mem_toFinset.mpr (PhyloTree.leaf_label_mem hc)
    · exact List.mem_toFinset.mpr (PhyloTree.leaf_label_mem hd)
  obtain ⟨h₁, h₂, h₃, h₄⟩ := bySplit_rel (fun (y : Address) (τ : ℕ) =>
    t.nodeAt y = some (.leaf τ)) q.split ha hb hc hd
  simp only [Quartet.induced, hq, decide_true, Bool.true_and, List.any_eq_true, cutBy_iff]
  rw [← exists_clade_iff ht h₁ h₂ h₃ h₄, ← exists_clade_iff ht h₃ h₄ h₁ h₂]
  constructor
  · rintro ⟨C, hC, h | h⟩
    · exact Or.inl ⟨C, hC, h⟩
    · exact Or.inr ⟨C, hC, h⟩
  · rintro (⟨C, hC, h⟩ | ⟨C, hC, h⟩)
    · exact ⟨C, hC, Or.inl h⟩
    · exact ⟨C, hC, Or.inr h⟩

/-- Section 2.3: whether some clade of `T'` cuts `q`, by ancestor tests. With `x₁, y₁` the leaves
of one side of `q` and `x₂, y₂` those of the other, some clade of `T'` cuts `q` iff neither `x₂`
nor `y₂` lies below the lowest vertex of `T'` above `x₁` and `y₁`, or neither `x₁` nor `y₁` below
the lowest vertex of `T'` above `x₂` and `y₂`. -/
theorem switched_cut_iff (ht : t.WellLabelled) {e : Address × Address}
    (he : EdgeAbove.Admissible t e) {q : Quartet} {la lb lc ld : Address}
    (ha : t.nodeAt la = some (.leaf q.a)) (hb : t.nodeAt lb = some (.leaf q.b))
    (hc : t.nodeAt lc = some (.leaf q.c)) (hd : t.nodeAt ld = some (.leaf q.d)) :
    let x := bySplit q.split la lb lc ld
    (∃ C ∈ EdgeAbove.switchedClades t e, q.cutBy C = true) ↔
      (¬below e (lowest e x.1 x.2.1) x.2.2.1 ∧ ¬below e (lowest e x.1 x.2.1) x.2.2.2) ∨
        (¬below e (lowest e x.2.2.1 x.2.2.2) x.1 ∧ ¬below e (lowest e x.2.2.1 x.2.2.2) x.2.1) := by
  intro x
  obtain ⟨h₁, h₂, h₃, h₄⟩ := bySplit_rel (fun (y : Address) (τ : ℕ) =>
    t.nodeAt y = some (.leaf τ)) q.split ha hb hc hd
  simp only [cutBy_iff]
  rw [← exists_switchedClade_iff ht he h₁ h₂ h₃ h₄, ← exists_switchedClade_iff ht he h₃ h₄ h₁ h₂]
  constructor
  · rintro ⟨C, hC, h | h⟩
    · exact Or.inl ⟨C, hC, h⟩
    · exact Or.inr ⟨C, hC, h⟩
  · rintro (⟨C, hC, h⟩ | ⟨C, hC, h⟩)
    · exact ⟨C, hC, Or.inl h⟩
    · exact ⟨C, hC, Or.inr h⟩

end Quartets


section Program

open SwitchedVertex

variable {t : PhyloTree} {T : Tables}

/-- The ancestor test `p <+: x` (`prefix_iff_lca`): one read of the table of lowest common
ancestors and one comparison. -/
def ancestor (T : Tables) (p x : Address) : Timed Bool := do
  let m ← step (T.lca (p, x))
  step (decide (m = p))

@[simp] theorem time_ancestor (T : Tables) (p x : Address) : (ancestor T p x).time = 2 := rfl

theorem val_ancestor (hT : T.Correct t) {p x : Address} (hp : p ∈ t.nodes) (hx : x ∈ t.nodes) :
    (ancestor T p x).val = decide (p <+: x) := by
  simp only [ancestor, val_bind, val_step, hT.lca p hp x hx]
  exact decide_eq_decide.mpr (prefix_iff_lca p x).symm

/-- Whether the leaf `x` lies below the vertex `p` of `T` in `T'` (`belowOld`): four ancestor tests,
two comparisons and eight Boolean operations. -/
def belowOldTest (T : Tables) (e : Address × Address) (p x : Address) : Timed Bool := do
  let pw ← ancestor T p e.2
  let pnw ← step (!decide (p = e.2))
  let px ← ancestor T p x
  let wx ← ancestor T e.2 x
  let pu ← ancestor T p e.1
  let pnu ← step (!decide (p = e.1))
  steps 8 ((pw && pnw && px && !wx) || (!(pw && pnw) && px) || (pu && pnu && wx))

@[simp] theorem time_belowOldTest (T : Tables) (e : Address × Address) (p x : Address) :
    (belowOldTest T e p x).time = 18 := rfl

theorem val_belowOldTest (hT : T.Correct t) {e : Address × Address}
    (he : EdgeAbove.Admissible t e) {p x : Address} (hp : p ∈ t.nodes) (hx : x ∈ t.nodes) :
    (belowOldTest T e p x).val = decide (belowOld e p x) := by
  simp only [belowOldTest, val_bind, val_step, val_steps, val_ancestor hT hp he.2.1,
    val_ancestor hT hp hx, val_ancestor hT he.2.1 hx, val_ancestor hT hp he.1]
  rw [Bool.eq_iff_iff]
  simp only [belowOld, decide_eq_true_eq]
  simp
  tauto

/-- The vertex of `T` named by a vertex of `T'`, if any, is a vertex of `T`. -/
def InTree (t : PhyloTree) : SwitchedVertex → Prop
  | old p => p ∈ t.nodes
  | donor => True
  | recipient => True

/-- Whether the leaf `x` lies below the vertex `s` of `T'` (`SwitchedVertex.below`). -/
def belowTest (T : Tables) (e : Address × Address) (s : SwitchedVertex) (x : Address) :
    Timed Bool :=
  match s with
  | old p => belowOldTest T e p x
  | donor => do
      let a ← belowOldTest T e e.1 x
      let b ← ancestor T e.2 x
      step (a || b)
  | recipient => ancestor T e.2 x

theorem time_belowTest (T : Tables) (e : Address × Address) (s : SwitchedVertex) (x : Address) :
    (belowTest T e s x).time ≤ 21 := by
  cases s <;> simp [belowTest]

theorem val_belowTest (hT : T.Correct t) {e : Address × Address} (he : EdgeAbove.Admissible t e)
    {s : SwitchedVertex} (hs : InTree t s) {x : Address} (hx : x ∈ t.nodes) :
    (belowTest T e s x).val = decide (below e s x) := by
  cases s with
  | old p => exact val_belowOldTest hT he hs hx
  | donor =>
    simp [belowTest, below, val_belowOldTest hT he he.1 hx, val_ancestor hT he.2.1 hx]
  | recipient => exact val_ancestor hT he.2.1 hx

/-- The lowest vertex of `T'` above the leaves `x` and `y` (`lowest`): at most three ancestor
tests, two comparisons and two reads. -/
def lowestTest (T : Tables) (e : Address × Address) (x y : Address) : Timed SwitchedVertex := do
  let wx ← ancestor T e.2 x
  let wy ← ancestor T e.2 y
  let same ← step (decide (wx = wy))
  if same then do
    let m ← step (T.lca (x, y))
    pure (old m)
  else do
    let z ← step (if wx then y else x)
    let uz ← ancestor T e.1 z
    if uz then pure donor
    else do
      let m ← step (T.lca (e.1, z))
      pure (old m)

theorem time_lowestTest (T : Tables) (e : Address × Address) (x y : Address) :
    (lowestTest T e x y).time ≤ 9 := by
  unfold lowestTest
  simp only [time_bind, time_ancestor, time_step, val_step]
  split_ifs <;> simp <;> split_ifs <;> omega

theorem val_lowestTest (hT : T.Correct t) {e : Address × Address}
    (he : EdgeAbove.Admissible t e) {x y : Address} (hx : x ∈ t.nodes) (hy : y ∈ t.nodes) :
    (lowestTest T e x y).val = lowest e x y ∧ InTree t (lowest e x y) := by
  have hu := he.1
  have hw := he.2.1
  refine ⟨?_, ?_⟩
  · by_cases hwx : e.2 <+: x <;> by_cases hwy : e.2 <+: y
    · rw [lowest_same (by simp [hwx, hwy])]
      simp [lowestTest, val_ancestor hT hw hx, val_ancestor hT hw hy, hwx, hwy,
        hT.lca x hx y hy]
    · rw [lowest_split hwx hwy]
      by_cases huy : e.1 <+: y <;>
        simp [lowestTest, val_ancestor hT hw hx, val_ancestor hT hw hy, hwx, hwy,
          val_ancestor hT hu hy, huy, hT.lca _ hu y hy]
    · rw [lowest_comm, lowest_split hwy hwx]
      by_cases hux : e.1 <+: x <;>
        simp [lowestTest, val_ancestor hT hw hx, val_ancestor hT hw hy, hwx, hwy,
          val_ancestor hT hu hx, hux, hT.lca _ hu x hx]
    · rw [lowest_same (by simp [hwx, hwy])]
      simp [lowestTest, val_ancestor hT hw hx, val_ancestor hT hw hy, hwx, hwy,
        hT.lca x hx y hy]
  · rcases lowest_cases e x y with h | h | ⟨z, h⟩ <;> rw [h]
    · exact t.nodes_prefix_closed hx (lca_prefix_left _ _)
    · trivial
    · exact t.nodes_prefix_closed hu (lca_prefix_left _ _)

/-- Whether some clade of `T` cuts the quartet with sides `{x₁, y₁}` and `{x₂, y₂}`
(`induced_iff`): two reads, four ancestor tests and five Boolean operations. -/
def cutsTreeTest (T : Tables) (x₁ y₁ x₂ y₂ : Address) : Timed Bool := do
  let m ← step (T.lca (x₁, y₁))
  let a ← ancestor T m x₂
  let b ← ancestor T m y₂
  let m' ← step (T.lca (x₂, y₂))
  let c ← ancestor T m' x₁
  let d ← ancestor T m' y₁
  steps 5 ((!a && !b) || (!c && !d))

@[simp] theorem time_cutsTreeTest (T : Tables) (x₁ y₁ x₂ y₂ : Address) :
    (cutsTreeTest T x₁ y₁ x₂ y₂).time = 15 := rfl

theorem val_cutsTreeTest (hT : T.Correct t) {x₁ y₁ x₂ y₂ : Address} (h₁ : x₁ ∈ t.nodes)
    (h₂ : y₁ ∈ t.nodes) (h₃ : x₂ ∈ t.nodes) (h₄ : y₂ ∈ t.nodes) :
    (cutsTreeTest T x₁ y₁ x₂ y₂).val =
      decide ((¬lca x₁ y₁ <+: x₂ ∧ ¬lca x₁ y₁ <+: y₂) ∨
        (¬lca x₂ y₂ <+: x₁ ∧ ¬lca x₂ y₂ <+: y₁)) := by
  have m₁ := t.nodes_prefix_closed h₁ (lca_prefix_left x₁ y₁)
  have m₂ := t.nodes_prefix_closed h₃ (lca_prefix_left x₂ y₂)
  simp [cutsTreeTest, hT.lca x₁ h₁ y₁ h₂, hT.lca x₂ h₃ y₂ h₄, val_ancestor hT m₁ h₃,
    val_ancestor hT m₁ h₄, val_ancestor hT m₂ h₁, val_ancestor hT m₂ h₂]

/-- Whether some clade of `T'` cuts the quartet with sides `{x₁, y₁}` and `{x₂, y₂}`
(`switched_cut_iff`): two lowest vertices of `T'` and four tests of `below`. -/
def cutsSwitchedTest (T : Tables) (e : Address × Address) (x₁ y₁ x₂ y₂ : Address) :
    Timed Bool := do
  let s ← lowestTest T e x₁ y₁
  let a ← belowTest T e s x₂
  let b ← belowTest T e s y₂
  let s' ← lowestTest T e x₂ y₂
  let c ← belowTest T e s' x₁
  let d ← belowTest T e s' y₁
  steps 5 ((!a && !b) || (!c && !d))

theorem time_cutsSwitchedTest (T : Tables) (e : Address × Address) (x₁ y₁ x₂ y₂ : Address) :
    (cutsSwitchedTest T e x₁ y₁ x₂ y₂).time ≤ 107 := by
  simp only [cutsSwitchedTest, time_bind, time_steps]
  have := time_lowestTest T e x₁ y₁
  have := time_lowestTest T e x₂ y₂
  have := time_belowTest T e (lowestTest T e x₁ y₁).val x₂
  have := time_belowTest T e (lowestTest T e x₁ y₁).val y₂
  have := time_belowTest T e (lowestTest T e x₂ y₂).val x₁
  have := time_belowTest T e (lowestTest T e x₂ y₂).val y₁
  omega

theorem val_cutsSwitchedTest (hT : T.Correct t) {e : Address × Address}
    (he : EdgeAbove.Admissible t e) {x₁ y₁ x₂ y₂ : Address} (h₁ : x₁ ∈ t.nodes)
    (h₂ : y₁ ∈ t.nodes) (h₃ : x₂ ∈ t.nodes) (h₄ : y₂ ∈ t.nodes) :
    (cutsSwitchedTest T e x₁ y₁ x₂ y₂).val =
      decide ((¬below e (lowest e x₁ y₁) x₂ ∧ ¬below e (lowest e x₁ y₁) y₂) ∨
        (¬below e (lowest e x₂ y₂) x₁ ∧ ¬below e (lowest e x₂ y₂) y₁)) := by
  obtain ⟨l₁, i₁⟩ := val_lowestTest hT he h₁ h₂
  obtain ⟨l₂, i₂⟩ := val_lowestTest hT he h₃ h₄
  simp [cutsSwitchedTest, l₁, l₂, val_belowTest hT he i₁ h₃, val_belowTest hT he i₁ h₄,
    val_belowTest hT he i₂ h₁, val_belowTest hT he i₂ h₂]

/-- Section 2.3: δ_T(q, (u, w)) in `O(1)` time after the preprocessing. Four reads give the leaves
of the taxa of `q` (if one is missing, `q` is not satisfied); `T` must not induce `q`
(`cutsTreeTest`), and some clade of `T'` must cut it (`cutsSwitchedTest`). -/
def delta (T : Tables) (e : Address × Address) (q : Quartet) : Timed Bool := do
  let la ← step (T.leafOf q.a)
  let lb ← step (T.leafOf q.b)
  let lc ← step (T.leafOf q.c)
  let ld ← step (T.leafOf q.d)
  match la, lb, lc, ld with
  | some a, some b, some c, some d => do
      let x ← steps 3 (bySplit q.split a b c d)
      let ind ← cutsTreeTest T x.1 x.2.1 x.2.2.1 x.2.2.2
      let cut ← cutsSwitchedTest T e x.1 x.2.1 x.2.2.1 x.2.2.2
      step (!ind && cut)
  | _, _, _, _ => pure false

/-- Section 2.3: the test takes at most `130` operations, whatever its arguments. -/
theorem time_delta (T : Tables) (e : Address × Address) (q : Quartet) :
    (delta T e q).time ≤ 130 := by
  unfold delta
  rcases T.leafOf q.a with _ | la <;> rcases T.leafOf q.b with _ | lb <;>
    rcases T.leafOf q.c with _ | lc <;> rcases T.leafOf q.d with _ | ld <;>
    simp only [time_bind, time_step, val_step, time_pure] <;> try omega
  simp only [time_steps, val_steps, time_cutsTreeTest]
  have := time_cutsSwitchedTest T e (bySplit q.split la lb lc ld).1
    (bySplit q.split la lb lc ld).2.1 (bySplit q.split la lb lc ld).2.2.1
    (bySplit q.split la lb lc ld).2.2.2
  omega

/-- Section 2.3: after a correct preprocessing of a well-labelled tree `T`, the test computes
δ_T of Definition 4: `delta T e q` returns `EdgeAbove.satisfies t e q` for every admissible pair
`e` and every quartet `q`. -/
theorem val_delta (ht : t.WellLabelled) (hT : T.Correct t) {e : Address × Address}
    (he : e ∈ EdgeAbove.candidates t) (q : Quartet) :
    (delta T e q).val = EdgeAbove.satisfies t e q := by
  have hae := (Finset.mem_filter.mp he).2
  by_cases hq : q.taxa ⊆ t.taxa
  · obtain ⟨la, hla⟩ := hT.leafOf_complete q.a (hq (by simp [Quartet.taxa]))
    obtain ⟨lb, hlb⟩ := hT.leafOf_complete q.b (hq (by simp [Quartet.taxa]))
    obtain ⟨lc, hlc⟩ := hT.leafOf_complete q.c (hq (by simp [Quartet.taxa]))
    obtain ⟨ld, hld⟩ := hT.leafOf_complete q.d (hq (by simp [Quartet.taxa]))
    have ha := hT.leafOf_sound _ _ hla
    have hb := hT.leafOf_sound _ _ hlb
    have hc := hT.leafOf_sound _ _ hlc
    have hd := hT.leafOf_sound _ _ hld
    obtain ⟨n₁, n₂, n₃, n₄⟩ := bySplit_rel (fun (y : Address) (_ : ℕ) => y ∈ t.nodes) q.split
      (b := lb) (c := lc) (d := ld) (a' := q.a) (b' := q.b) (c' := q.c) (d' := q.d)
      ((t.mem_nodes_iff la).mpr ⟨_, ha⟩) ((t.mem_nodes_iff lb).mpr ⟨_, hb⟩)
      ((t.mem_nodes_iff lc).mpr ⟨_, hc⟩) ((t.mem_nodes_iff ld).mpr ⟨_, hd⟩)
    have hind := induced_iff ht ha hb hc hd
    have hsw := switched_cut_iff ht hae ha hb hc hd
    simp only at hind hsw
    simp only [delta, val_bind, val_step, hla, hlb, hlc, hld, val_steps,
      val_cutsTreeTest hT n₁ n₂ n₃ n₄, val_cutsSwitchedTest hT hae n₁ n₂ n₃ n₄,
      EdgeAbove.satisfies, hq, decide_true, Bool.true_and]
    congr 1
    · congr 1
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact hind.symm
    · exact decide_eq_decide.mpr hsw.symm
  · have hnone : ¬∃ a b c d, T.leafOf q.a = some a ∧ T.leafOf q.b = some b ∧
        T.leafOf q.c = some c ∧ T.leafOf q.d = some d := by
      rintro ⟨a, b, c, d, ha, hb, hc, hd⟩
      apply hq
      intro τ hτ
      simp only [Quartet.taxa, Finset.mem_insert, Finset.mem_singleton] at hτ
      rcases hτ with rfl | rfl | rfl | rfl
      · exact List.mem_toFinset.mpr (PhyloTree.leaf_label_mem (hT.leafOf_sound _ _ ha))
      · exact List.mem_toFinset.mpr (PhyloTree.leaf_label_mem (hT.leafOf_sound _ _ hb))
      · exact List.mem_toFinset.mpr (PhyloTree.leaf_label_mem (hT.leafOf_sound _ _ hc))
      · exact List.mem_toFinset.mpr (PhyloTree.leaf_label_mem (hT.leafOf_sound _ _ hd))
    have hsat : EdgeAbove.satisfies t e q = false := by
      simp [EdgeAbove.satisfies, hq]
    rw [hsat]
    unfold delta
    cases ha : T.leafOf q.a <;> cases hb : T.leafOf q.b <;> cases hc : T.leafOf q.c <;>
      cases hd : T.leafOf q.d <;> simp only [val_bind, val_step, val_pure]
    exact (hnone ⟨_, _, _, _, ha, hb, hc, hd⟩).elim

end Program

end Complexity

end Camus
