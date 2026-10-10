module

public import Camus.Complexity.Delta
public import Camus.DP.Theorem1

/-!
# Section 2.3: CAMUS as a program, and its running time

This file writes the dynamic program of Section 2.2 as a program in the cost monad of
`Camus/Complexity/Timed.lean` and proves the two claims of Section 2.3 about it: it computes the DP
array, and it runs in time `O(n²(|Q| + n))`, where `n` is the number of leaves of `T` and `|Q|` the
number of distinct quartets of `Q`.

The program (`Complexity.camus`) follows the paper.

1. The preprocessing of `Camus/Complexity/Tables.lean`: the tables of parents, depths, kinds,
   leaves and lowest common ancestors, in `O(n²)` time (`Complexity.preprocess_time`).
2. The candidate pairs are enumerated once (`Complexity.enumerate`): each pair `(u, w)` of vertices
   is tested for admissibility, and an admissible pair is put in the bucket of its target
   `lca(u, w)`, its weight `s_e(u, w)` of Equation (1) being computed in this preprocessing step
   by one scan of the distinct quartets of `Q` with their multiplicities, each tested in `O(1)` by
   `Complexity.delta` (`Complexity.weightScan`).
3. `M` is filled bottom-up (`Complexity.fill`), in the reverse of the preorder, a postorder in
   which every vertex comes after its descendants: `M[v] = 0` at a leaf, and otherwise
   `M[v] = max(M[l(v)] + M[r(v)], s(v))` (Equation (2)), where `s(v)` is the maximum over the
   bucket of `v` of `s_e + s_dp` (Equation (3)), and `s_dp` is the sum of `M` over the roots of
   the subtrees hanging off the cycle (Equations (4) and (5)), listed by walking from `u` and from
   `w` up to the target (`Complexity.hangingList`).

## Main results

* `Complexity.camus`: the program.
* `Complexity.camus_array`: for a well-labelled `T`, the computed `M` satisfies the recurrence
  (`DynamicProgramming.Array`) for the weights `s_e` of Equation (1).
* `Complexity.camus_optimal`: so, by Theorem 1, `M[root]` is the largest number of quartets of `Q`
  satisfied by a network built on `T`, attained by a network obtained by backtracking.
* `Complexity.camus_time`: Section 2.3's running time, at most `600 n² (|Q| + n)` operations.
* `Complexity.mem_hanging_cross`, `Complexity.mem_hanging_ghost`: the roots of the subtrees hanging
  off a cycle are `u`, `w` and the siblings of the vertices on the paths from the target to `u` and
  to `w` (the terms of Equations (4) and (5)).
* `Complexity.hangingList_spec`, `Complexity.enumerate_buckets`: the walks list these roots, and
  the buckets are the sets Pairs(v).

Backtracking, within the same bound, is in `Camus/Complexity/Backtracking.lean`, and the memory in
`Camus/Complexity/Memory.lean` (the final tables) and `Camus/Complexity/PeakMemory.lean` (the peak).

The weights are computed with the test of `Camus/Complexity/Delta.lean`, which returns
`EdgeAbove.satisfies`; that its sum is Equation (1) is
`DynamicProgramming.edgeWeight_eq_satisfies` (`Camus/Network/SingleEdge.lean`).

## Proof (the paper's)

The running time follows the four steps of the paper's analysis.

(i) The preprocessing takes `O(n²)` time (`Complexity.preprocess_time`).
(ii) After it, δ_T(q, (u, w)) takes `O(1)` time (`Complexity.time_delta`), so the weight of a pair
  takes `O(|Q|)` time (`Complexity.time_weightScan`).
(iii) Solving `s(v)` takes `O(|Pairs(v)| · n)` time, besides the weights: for each pair of the
  bucket of `v`, the walks list at most `|V(T)|` hanging subtrees
  (`Complexity.time_hangingList`, `Complexity.length_hangingList`, `Complexity.hanging_bound`),
  and `s_dp` is their sum (`Complexity.time_pairValue`, `Complexity.time_solveVertex`).
(iv) "No edge is ever considered in the s(·) function more than once over all subproblems": the
  buckets partition the candidate pairs (`Complexity.enumerate_buckets`,
  `Complexity.candidate_visits`, `Complexity.time_fill`), so the total is
  `O(|candidates| (|Q| + n)) = O(n²(|Q| + n))` (`Complexity.candidates_bound`,
  `PhyloTree.nodes_count`, `Complexity.camus_time`).
-/

@[expose] public section

namespace Camus

namespace Complexity

/-- The sibling of a vertex: the other child of its parent. -/
def sibling (c : Address) : Address := parent c ++ [!(c.getLast?.getD false)]

/-- A non-root vertex is its parent followed by its last step. -/
theorem parent_append_getLast (c : Address) (h : c ≠ []) : parent c ++ [c.getLast h] = c :=
  List.take_append_getLast c h

theorem sibling_append (p : Address) (b : Bool) : sibling (p ++ [b]) = p ++ [!b] := by
  simp [sibling, parent_child]

theorem parent_sibling (c : Address) : parent (sibling c) = parent c := by
  simp [sibling, parent_child]

theorem length_parent {c : Address} (h : c ≠ []) : (parent c).length + 1 = c.length := by
  have := congrArg List.length (parent_append_getLast c h)
  simpa using this

theorem length_sibling {c : Address} (h : c ≠ []) : (sibling c).length = c.length := by
  simp only [sibling, List.length_append, List.length_singleton]
  exact length_parent h

theorem sibling_ne_self {c : Address} (h : c ≠ []) : sibling c ≠ c := by
  intro hs
  have h1 := parent_append_getLast c h
  rw [← h1, sibling_append] at hs
  simp at hs

/-- Two non-root vertices with the same parent are equal or siblings. -/
theorem eq_or_eq_sibling {r y : Address} (hr : r ≠ []) (hy : y ≠ []) (h : parent r = parent y) :
    r = y ∨ r = sibling y := by
  rw [← parent_append_getLast r hr, ← parent_append_getLast y hy, h, sibling_append]
  cases r.getLast hr <;> cases y.getLast hy <;> simp

/-- The sibling of an ancestor `y` of `x` (or of `x` itself) is not an ancestor of `x`. -/
theorem sibling_not_prefix {y x : Address} (hy : y ≠ []) (hyx : y <+: x) :
    ¬sibling y <+: x := by
  intro hs
  have heq : sibling y = y :=
    (List.prefix_of_prefix_length_le hs hyx (length_sibling hy).le).eq_of_length
      (length_sibling hy)
  exact sibling_ne_self hy heq

/-- The sibling of a non-root vertex of `T` is a vertex of `T`. -/
theorem sibling_mem_nodes {t : PhyloTree} {y : Address} (hy : y ∈ t.nodes) (hy0 : y ≠ []) :
    sibling y ∈ t.nodes := by
  have hsplit := parent_append_getLast y hy0
  obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff (parent y)).mp
    (t.nodes_prefix_closed hy (parent_prefix y))
  cases sub with
  | leaf a =>
    exfalso
    obtain ⟨s, hs⟩ := (t.mem_nodes_iff y).mp hy
    rw [← hsplit, PhyloTree.nodeAt_append, hsub] at hs
    simp [PhyloTree.nodeAt] at hs
  | fork l r =>
    rw [← hsplit, sibling_append]
    exact PhyloTree.child_mem_nodes hsub _

/-- The child of `P` on the path to `u`, for a strict ancestor `P` of `u`. -/
theorem child_toward {P u : Address} (hP : P <+: u) (hne : P ≠ u) :
    u.take (P.length + 1) <+: u ∧ (u.take (P.length + 1)).length = P.length + 1 ∧
      parent (u.take (P.length + 1)) = P ∧ u.take (P.length + 1) ≠ [] := by
  have hlt : P.length < u.length := by
    have := hP.length_le
    by_contra h
    exact hne (hP.eq_of_length (by omega))
  have hlen : (u.take (P.length + 1)).length = P.length + 1 := by
    simp only [List.length_take]; omega
  refine ⟨List.take_prefix _ _, hlen, ?_, ?_⟩
  · simp only [parent, hlen, Nat.add_sub_cancel, List.take_take]
    rw [Nat.min_eq_left (by omega)]
    exact (List.prefix_iff_eq_take.mp hP).symm
  · intro h
    rw [h] at hlen
    simp at hlen

/-- A strict ancestor is shorter. -/
theorem length_lt_of_strict {p x : Address} (h : p <+: x) (hne : p ≠ x) : p.length < x.length := by
  have := h.length_le
  by_contra hn
  exact hne (h.eq_of_length (by omega))

/-- Two ancestors of `x` are comparable, by length. -/
theorem prefix_of_le {a b x : Address} (ha : a <+: x) (hb : b <+: x) (hl : a.length ≤ b.length) :
    a <+: b := List.prefix_of_prefix_length_le ha hb hl

section Hanging

open EdgeAbove

/-- A vertex of `T` hangs off the cycle `γ(e)` if it is not on the cycle and its parent is. -/
theorem mem_hanging_of {t : PhyloTree} {e : Address × Address} {r : Address}
    (hrn : r ∈ t.nodes) (hr0 : r ≠ []) (hP : parent r ∈ footprint t e)
    (hr : ¬(target e <+: r ∧ ((r <+: e.1 ∧ r ≠ e.1) ∨ (r <+: e.2 ∧ r ≠ e.2)))) :
    r ∈ DynamicProgramming.hanging t e :=
  Finset.mem_filter.mpr ⟨hrn, hr0, hP, fun h => hr (Finset.mem_filter.mp h).2⟩

/-- The sibling of a vertex `y` on the path from the target `v` to `x ∈ {u, w}`, at least one level
below `v`, has its parent on the cycle. -/
theorem parent_sibling_mem_footprint {t : PhyloTree} {e : Address × Address} {x y : Address}
    (hx : x ∈ t.nodes) (hvx : target e <+: x) (hxe : x = e.1 ∨ x = e.2) (hyx : y <+: x)
    (hy : (target e).length + 1 ≤ y.length) : parent (sibling y) ∈ footprint t e := by
  have hy0 : y ≠ [] := by intro h; rw [h] at hy; simp at hy
  have hlen := length_parent hy0
  have hPx : parent y <+: x := (parent_prefix y).trans hyx
  rw [parent_sibling]
  refine Finset.mem_filter.mpr ⟨t.nodes_prefix_closed hx hPx, prefix_of_le hvx hPx (by omega), ?_⟩
  have hne : parent y ≠ x := by
    intro h
    have := hyx.length_le
    rw [← h] at this
    omega
  rcases hxe with rfl | rfl
  · exact Or.inl ⟨hPx, hne⟩
  · exact Or.inr ⟨hPx, hne⟩

/-- The roots of the subtrees hanging off `γ(u, w)` for a pair with `u ≠ v`, where `v = lca(u, w)`
(the terms of Equation (4)): `u`, `w`, and the siblings of the vertices `y` on the paths from `v` to
`u` and to `w` that lie at least two levels below `v`. -/
theorem mem_hanging_cross {t : PhyloTree} {e : Address × Address} (he : Admissible t e)
    (hc : target e ≠ e.1) (r : Address) :
    r ∈ DynamicProgramming.hanging t e ↔ r = e.1 ∨ r = e.2 ∨
      (∃ y, y <+: e.1 ∧ (target e).length + 2 ≤ y.length ∧ r = sibling y) ∨
      (∃ y, y <+: e.2 ∧ (target e).length + 2 ≤ y.length ∧ r = sibling y) := by
  have hvu : target e <+: e.1 := lca_prefix_left _ _
  have hvw : target e <+: e.2 := lca_prefix_right _ _
  have hvw' : target e ≠ e.2 := by
    intro h
    exact he.2.2.2.2 ((lca_eq_right_iff _ _).mp h)
  -- a common ancestor of `u` and `w` is an ancestor of `v`
  have below_v : ∀ P, P <+: e.1 → P <+: e.2 → P.length ≤ (target e).length := fun P h1 h2 =>
    (prefix_lca h1 h2).length_le
  -- the two children of `v` towards `u` and `w` are siblings
  have hchildren : e.1.take ((target e).length + 1) ≠ e.2.take ((target e).length + 1) := by
    intro h
    have h1 := (child_toward hvu hc).1
    have h2 := (child_toward hvw hvw').1
    have hl := (child_toward hvu hc).2.1
    have := below_v _ h1 (h ▸ h2)
    omega
  constructor
  · intro hr
    obtain ⟨hrn, hr0, hpf, hrf⟩ := Finset.mem_filter.mp hr
    obtain ⟨-, hvP, hP⟩ := Finset.mem_filter.mp hpf
    have hvr : target e <+: r := hvP.trans (parent_prefix r)
    have hnot : ¬((r <+: e.1 ∧ r ≠ e.1) ∨ (r <+: e.2 ∧ r ≠ e.2)) := fun h =>
      hrf (Finset.mem_filter.mpr ⟨hrn, hvr, h⟩)
    rcases hP with ⟨hPu, hPne⟩ | ⟨hPw, hPne⟩
    · obtain ⟨hyu, hylen, hypar, hy0⟩ := child_toward hPu hPne
      rcases eq_or_eq_sibling hr0 hy0 hypar.symm with hry | hry
      · left
        by_contra hne
        exact hnot (Or.inl ⟨hry ▸ hyu, hne⟩)
      · by_cases hPv : parent r = target e
        · -- `r` is the child of `v` towards `w`
          obtain ⟨hzw, -, hzpar, hz0⟩ := child_toward hvw hvw'
          have hyv : e.1.take ((parent r).length + 1) = e.1.take ((target e).length + 1) := by
            rw [hPv]
          rcases eq_or_eq_sibling hz0 hy0 (hzpar.trans (hypar.trans hPv).symm) with h | h
          · exact (hchildren (hyv.symm.trans h.symm)).elim
          · right; left
            have hrz : r = e.2.take ((target e).length + 1) := hry.trans h.symm
            by_contra hne
            exact hnot (Or.inr ⟨hrz ▸ hzw, hne⟩)
        · right; right; left
          refine ⟨_, hyu, ?_, hry⟩
          have := length_lt_of_strict hvP (Ne.symm hPv)
          omega
    · obtain ⟨hyw, hylen, hypar, hy0⟩ := child_toward hPw hPne
      rcases eq_or_eq_sibling hr0 hy0 hypar.symm with hry | hry
      · right; left
        by_contra hne
        exact hnot (Or.inr ⟨hry ▸ hyw, hne⟩)
      · by_cases hPv : parent r = target e
        · -- `r` is the child of `v` towards `u`
          obtain ⟨hzu, -, hzpar, hz0⟩ := child_toward hvu hc
          have hyv : e.2.take ((parent r).length + 1) = e.2.take ((target e).length + 1) := by
            rw [hPv]
          rcases eq_or_eq_sibling hz0 hy0 (hzpar.trans (hypar.trans hPv).symm) with h | h
          · exact (hchildren (h.trans hyv)).elim
          · left
            have hrz : r = e.1.take ((target e).length + 1) := hry.trans h.symm
            by_contra hne
            exact hnot (Or.inl ⟨hrz ▸ hzu, hne⟩)
        · right; right; right
          refine ⟨_, hyw, ?_, hry⟩
          have := length_lt_of_strict hvP (Ne.symm hPv)
          omega
  · rintro (rfl | rfl | ⟨y, hyu, hy, rfl⟩ | ⟨y, hyw, hy, rfl⟩)
    · exact donor_mem_frontier he hc
    · exact recipient_mem_frontier he
    · have hy0 : y ≠ [] := by intro h; rw [h] at hy; simp at hy
      have hlen := length_parent hy0
      refine mem_hanging_of (sibling_mem_nodes (t.nodes_prefix_closed he.1 hyu) hy0)
        (by intro h; have := length_sibling hy0; rw [h] at this; simp at this; omega)
        (parent_sibling_mem_footprint he.1 hvu (Or.inl rfl) hyu (by omega)) ?_
      rintro ⟨-, h | h⟩
      · exact sibling_not_prefix hy0 hyu h.1
      · have hP : parent y <+: e.2 := by
          rw [← parent_sibling]; exact (parent_prefix _).trans h.1
        have := below_v _ ((parent_prefix y).trans hyu) hP
        omega
    · have hy0 : y ≠ [] := by intro h; rw [h] at hy; simp at hy
      have hlen := length_parent hy0
      refine mem_hanging_of (sibling_mem_nodes (t.nodes_prefix_closed he.2.1 hyw) hy0)
        (by intro h; have := length_sibling hy0; rw [h] at this; simp at this; omega)
        (parent_sibling_mem_footprint he.2.1 hvw (Or.inr rfl) hyw (by omega)) ?_
      rintro ⟨-, h | h⟩
      · have hP : parent y <+: e.1 := by
          rw [← parent_sibling]; exact (parent_prefix _).trans h.1
        have := below_v _ hP ((parent_prefix y).trans hyw)
        omega
      · exact sibling_not_prefix hy0 hyw h.1

/-- The roots of the subtrees hanging off `γ(u, w)` for a ghost pair, `u = v = lca(u, w)` (the
terms of Equation (5)): `w`, and the siblings of the vertices `y` on the path from `v` to `w` that
lie below `v`. -/
theorem mem_hanging_ghost {t : PhyloTree} {e : Address × Address} (he : Admissible t e)
    (hg : target e = e.1) (r : Address) :
    r ∈ DynamicProgramming.hanging t e ↔ r = e.2 ∨
      ∃ y, y <+: e.2 ∧ (target e).length + 1 ≤ y.length ∧ r = sibling y := by
  have hvw : target e <+: e.2 := lca_prefix_right _ _
  constructor
  · intro hr
    obtain ⟨hrn, hr0, hpf, hrf⟩ := Finset.mem_filter.mp hr
    obtain ⟨-, hvP, hP⟩ := Finset.mem_filter.mp hpf
    have hvr : target e <+: r := hvP.trans (parent_prefix r)
    have hnot : ¬((r <+: e.1 ∧ r ≠ e.1) ∨ (r <+: e.2 ∧ r ≠ e.2)) := fun h =>
      hrf (Finset.mem_filter.mpr ⟨hrn, hvr, h⟩)
    rcases hP with ⟨hPu, hPne⟩ | ⟨hPw, hPne⟩
    · exact (hPne (prefix_antisymm hPu (hg ▸ hvP))).elim
    · obtain ⟨hyw, hylen, hypar, hy0⟩ := child_toward hPw hPne
      rcases eq_or_eq_sibling hr0 hy0 hypar.symm with hry | hry
      · left
        by_contra hne
        exact hnot (Or.inr ⟨hry ▸ hyw, hne⟩)
      · right
        refine ⟨_, hyw, ?_, hry⟩
        have := hvP.length_le
        omega
  · rintro (rfl | ⟨y, hyw, hy, rfl⟩)
    · exact recipient_mem_frontier he
    · have hy0 : y ≠ [] := by intro h; rw [h] at hy; simp at hy
      have hlen := length_parent hy0
      refine mem_hanging_of (sibling_mem_nodes (t.nodes_prefix_closed he.2.1 hyw) hy0)
        (by intro h; have := length_sibling hy0; rw [h] at this; simp at this; omega)
        (parent_sibling_mem_footprint he.2.1 hvw (Or.inr rfl) hyw hy) ?_
      rintro ⟨-, h | h⟩
      · have := h.1.length_le
        rw [length_sibling hy0, ← hg] at this
        omega
      · exact sibling_not_prefix hy0 hyw h.1

end Hanging

open Timed DynamicProgramming

/-! ### The subtrees hanging off a cycle, by walking up to the target -/

/-- The siblings met when walking up from `c` towards its ancestor `v`, with fuel `n`:
`sibling c`, `sibling (parent c)`, …, up to the vertex whose parent is `v`, excluded. -/
def sibsUp (v : Address) : ℕ → Address → List Address
  | 0, _ => []
  | n + 1, c => if parent c = v then [] else sibling c :: sibsUp v n (parent c)

/-- The walk from `c` up to `v` lists the siblings of the vertices `y` on the path from `v` to `c`
at least two levels below `v`, if the fuel is at least the length of the path. -/
theorem mem_sibsUp {v : Address} {n : ℕ} : ∀ {c : Address}, v <+: c → v ≠ c →
    c.length ≤ n + v.length → ∀ z, z ∈ sibsUp v n c ↔
      ∃ y, y <+: c ∧ v.length + 2 ≤ y.length ∧ z = sibling y := by
  induction n with
  | zero =>
    intro c hvc hne hn
    have := length_lt_of_strict hvc hne
    omega
  | succ n ih =>
    intro c hvc hne hn z
    have hc0 : c ≠ [] := by intro h; rw [h] at hvc; exact hne (List.prefix_nil.mp hvc ▸ h.symm)
    have hlen := length_parent hc0
    have hvp : v <+: parent c := prefix_parent_of_ne hvc hne
    simp only [sibsUp]
    by_cases hp : parent c = v
    · simp only [hp, ↓reduceIte, List.not_mem_nil, false_iff, not_exists, not_and]
      intro y hyc hy
      have := hyc.length_le
      rw [hp] at hlen
      omega
    · simp only [hp, ↓reduceIte, List.mem_cons]
      rw [ih hvp (Ne.symm hp) (by omega)]
      have hvlt := length_lt_of_strict hvp (Ne.symm hp)
      constructor
      · rintro (rfl | ⟨y, hyp, hy, rfl⟩)
        · exact ⟨c, List.prefix_refl c, by omega, rfl⟩
        · exact ⟨y, hyp.trans (parent_prefix c), hy, rfl⟩
      · rintro ⟨y, hyc, hy, rfl⟩
        by_cases hyc' : y = c
        · exact Or.inl (by rw [hyc'])
        · exact Or.inr ⟨y, prefix_parent_of_ne hyc hyc', hy, rfl⟩

/-- The walk lists no sibling twice. -/
theorem sibsUp_nodup {v : Address} {n : ℕ} : ∀ {c : Address}, v <+: c → v ≠ c →
    (sibsUp v n c).Nodup := by
  induction n with
  | zero => intro c _ _; simp [sibsUp]
  | succ n ih =>
    intro c hvc hne
    have hc0 : c ≠ [] := by intro h; rw [h] at hvc; exact hne (List.prefix_nil.mp hvc ▸ h.symm)
    have hvp : v <+: parent c := prefix_parent_of_ne hvc hne
    simp only [sibsUp]
    by_cases hp : parent c = v
    · simp [hp]
    · simp only [hp, ↓reduceIte, List.nodup_cons]
      refine ⟨?_, ih hvp (Ne.symm hp)⟩
      -- the siblings further up are shorter than `sibling c`
      have hlen : ∀ m (d : Address), v <+: d → v ≠ d → ∀ z ∈ sibsUp v m d,
          z.length ≤ d.length := by
        intro m
        induction m with
        | zero => intro d _ _ z hz; simp [sibsUp] at hz
        | succ m ihm =>
          intro d hvd hnd z hz
          have hd0 : d ≠ [] := by
            intro h; rw [h] at hvd; exact hnd (List.prefix_nil.mp hvd ▸ h.symm)
          simp only [sibsUp] at hz
          split_ifs at hz with hpd
          · simp at hz
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact (length_sibling hd0).le
            · have := ihm (parent d) (prefix_parent_of_ne hvd hnd) (Ne.symm hpd) z hz
              have := length_parent hd0
              omega
      intro hmem
      have h1 := hlen n (parent c) hvp (Ne.symm hp) _ hmem
      rw [length_sibling hc0] at h1
      have := length_parent hc0
      omega

/-- The sibling of the non-root vertex `c`, read from the tables: the parent of `c` and its two
children. Four operations. -/
def siblingTest (T : Tables) (c : Address) : Timed Address := do
  let p ← step (T.parent c)
  let k ← step (T.kind p)
  match k with
  | .fork l r => steps 2 (if l = c then r else l)
  | .leaf _ => steps 2 c

@[simp] theorem time_siblingTest (T : Tables) (c : Address) : (siblingTest T c).time = 4 := by
  unfold siblingTest
  cases h : T.kind (T.parent c) <;> simp [h]

theorem val_siblingTest {t : PhyloTree} {T : Tables} (hT : T.Correct t) {c : Address}
    (hc : c ∈ t.nodes) (hc0 : c ≠ []) : (siblingTest T c).val = sibling c := by
  have hsplit := parent_append_getLast c hc0
  have hpn := t.nodes_prefix_closed hc (parent_prefix c)
  obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff (parent c)).mp hpn
  cases sub with
  | leaf a =>
    exfalso
    obtain ⟨s, hs⟩ := (t.mem_nodes_iff c).mp hc
    rw [← hsplit, PhyloTree.nodeAt_append, hsub] at hs
    simp [PhyloTree.nodeAt] at hs
  | fork l r =>
    have hk : T.kind (parent c) = .fork (parent c ++ [false]) (parent c ++ [true]) := by
      rw [hT.kind _ hpn]; simp [kindAt, hsub]
    simp only [siblingTest, val_bind, val_step, hT.parent c hc, hk, val_steps]
    rw [sibling, List.getLast?_eq_some_getLast hc0]
    cases hb : c.getLast hc0
    · have hc' : parent c ++ [false] = c := by rw [← hb]; exact hsplit
      simp [hc']
    · have hc' : parent c ++ [true] = c := by rw [← hb]; exact hsplit
      have hne : parent c ++ [false] ≠ c := by rw [← hc']; simp
      simp [hne]

/-- Walk up from `c` towards its ancestor `v` (Section 2.3): read the parent of `c`; stop if it is
`v`; otherwise put the sibling of `c` in front of the list and continue from the parent. The fuel
`n` bounds the number of steps. -/
def climb (T : Tables) (v : Address) : ℕ → Address → List Address → Timed (List Address)
  | 0, _, acc => pure acc
  | n + 1, c, acc => do
      let p ← step (T.parent c)
      let stop ← step (decide (p = v))
      if stop then pure acc
      else do
        let s ← siblingTest T c
        climb T v n p (s :: acc)

/-- The walk costs two operations at the end and six per sibling it lists. -/
theorem time_climb (T : Tables) (v : Address) (n : ℕ) :
    ∀ (c : Address) (acc : List Address),
      (climb T v n c acc).time + 6 * acc.length ≤ 2 + 6 * (climb T v n c acc).val.length := by
  induction n with
  | zero => intro c acc; simp [climb]
  | succ n ih =>
    intro c acc
    by_cases hp : T.parent c = v
    · simp [climb, hp]
    · have h := ih (T.parent c) (sibling c :: acc)
      simp only [climb, time_bind, val_bind, time_step, val_step, hp, decide_false,
        Bool.false_eq_true, ↓reduceIte, time_siblingTest] at h ⊢
      have h' := ih (T.parent c) ((siblingTest T c).val :: acc)
      simp only [List.length_cons] at h'
      omega

/-- With correct tables, the walk from `c` up to its strict ancestor `v` lists `sibsUp`. -/
theorem val_climb {t : PhyloTree} {T : Tables} (hT : T.Correct t) {v : Address} {n : ℕ} :
    ∀ {c : Address} (acc : List Address), c ∈ t.nodes → v <+: c → v ≠ c →
      c.length ≤ n + v.length → (climb T v n c acc).val = (sibsUp v n c).reverse ++ acc := by
  induction n with
  | zero =>
    intro c acc _ hvc hne hn
    have := length_lt_of_strict hvc hne
    omega
  | succ n ih =>
    intro c acc hc hvc hne hn
    have hc0 : c ≠ [] := by intro h; rw [h] at hvc; exact hne (List.prefix_nil.mp hvc ▸ h.symm)
    have hlen := length_parent hc0
    by_cases hp : parent c = v
    · simp [climb, hT.parent c hc, hp, sibsUp]
    · have hvp : v <+: parent c := prefix_parent_of_ne hvc hne
      have hpn := t.nodes_prefix_closed hc (parent_prefix c)
      have h := ih (sibling c :: acc) hpn hvp (Ne.symm hp) (by omega)
      simp only [climb, val_bind, val_step, hT.parent c hc, hp, decide_false,
        Bool.false_eq_true, ↓reduceIte, val_siblingTest hT hc hc0, h, sibsUp,
        List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Section 2.3: the roots of the subtrees hanging off the cycle `γ(u, w)`, listed by walking from
`u` and from `w` up to the target `v = lca(u, w)` (Equations (4) and (5)). For a ghost pair
(`u = v`) the walk from `w` goes up to `v` itself, listing the off-cycle child of `v` too. -/
def hangingList (T : Tables) (e : Address × Address) : Timed (List Address) := do
  let v ← step (T.lca e)
  let ghost ← step (decide (v = e.1))
  let dw ← step (T.depth e.2)
  if ghost then do
    let pv ← step (T.parent v)
    climb T pv dw e.2 [e.2]
  else do
    let du ← step (T.depth e.1)
    let L ← climb T v du e.1 [e.1]
    climb T v dw e.2 (e.2 :: L)

/-- The walks cost at most `8 + 6 L` operations, where `L` is the number of hanging subtrees
they list. -/
theorem time_hangingList (T : Tables) (e : Address × Address) :
    (hangingList T e).time ≤ 8 + 6 * (hangingList T e).val.length := by
  by_cases hg : T.lca e = e.1
  · have h := time_climb T (T.parent (T.lca e)) (T.depth e.2) e.2 [e.2]
    simp only [hangingList, time_bind, val_bind, time_step, val_step, hg, decide_true,
      ↓reduceIte] at h ⊢
    simp only [List.length_cons, List.length_nil] at h
    omega
  · have h1 := time_climb T (T.lca e) (T.depth e.1) e.1 [e.1]
    have h2 := time_climb T (T.lca e) (T.depth e.2) e.2
      (e.2 :: (climb T (T.lca e) (T.depth e.1) e.1 [e.1]).val)
    simp only [hangingList, time_bind, val_bind, time_step, val_step, hg, decide_false,
      Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
    simp only [List.length_cons, List.length_nil] at h1 h2
    omega

/-- Section 2.3: with correct tables, the walks list the roots of the subtrees hanging off the
cycle of an admissible pair, each once (`DynamicProgramming.hanging`). -/
theorem hangingList_spec {t : PhyloTree} {T : Tables} (hT : T.Correct t) {e : Address × Address}
    (he : EdgeAbove.Admissible t e) :
    (hangingList T e).val.Nodup ∧ ∀ r, r ∈ (hangingList T e).val ↔ r ∈ hanging t e := by
  have hu := he.1
  have hw := he.2.1
  have hlca : T.lca e = EdgeAbove.target e := hT.lca e.1 hu e.2 hw
  have hvu : EdgeAbove.target e <+: e.1 := lca_prefix_left _ _
  have hvw : EdgeAbove.target e <+: e.2 := lca_prefix_right _ _
  have hvw' : EdgeAbove.target e ≠ e.2 := by
    intro h
    exact he.2.2.2.2 ((lca_eq_right_iff _ _).mp h)
  have hvn : EdgeAbove.target e ∈ t.nodes := t.nodes_prefix_closed hu hvu
  have below_v : ∀ P, P <+: e.1 → P <+: e.2 → P.length ≤ (EdgeAbove.target e).length :=
    fun P h1 h2 => (prefix_lca h1 h2).length_le
  by_cases hg : EdgeAbove.target e = e.1
  · -- Equation (5): the walk from `w` up to `v = u`, included
    have hv0 : EdgeAbove.target e ≠ [] := hg ▸ he.2.2.1
    have hlen := length_parent hv0
    have hpw : parent (EdgeAbove.target e) <+: e.2 := (parent_prefix _).trans hvw
    have hpw' : parent (EdgeAbove.target e) ≠ e.2 := by
      intro h
      have := hvw.length_le
      rw [← h] at this
      omega
    have hval : (hangingList T e).val =
        (sibsUp (parent (EdgeAbove.target e)) e.2.length e.2).reverse ++ [e.2] := by
      simp only [hangingList, val_bind, val_step, hlca, hg, decide_true, ↓reduceIte,
        hT.parent _ (hg ▸ hvn), hT.depth e.2 hw]
      rw [← hg, val_climb hT [e.2] hw hpw hpw' (by omega)]
    have hmem := mem_sibsUp hpw hpw' (n := e.2.length) (by omega)
    rw [hval]
    refine ⟨?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨List.nodup_reverse.mpr (sibsUp_nodup hpw hpw'), List.nodup_singleton _, ?_⟩
      intro z hz z' hz' hzz
      rw [List.mem_singleton] at hz'
      rw [hz'] at hzz
      obtain ⟨y, hyw, hy, hzy⟩ := (hmem z).mp (List.mem_reverse.mp hz)
      have hy0 : y ≠ [] := by intro h; rw [h] at hy; simp at hy
      apply sibling_not_prefix hy0 hyw
      rw [← hzy, hzz]
    · intro r
      rw [mem_hanging_ghost he hg, List.mem_append, List.mem_reverse, hmem,
        List.mem_singleton]
      constructor
      · rintro (⟨y, hyw, hy, rfl⟩ | rfl)
        · exact Or.inr ⟨y, hyw, by omega, rfl⟩
        · exact Or.inl rfl
      · rintro (rfl | ⟨y, hyw, hy, rfl⟩)
        · exact Or.inr rfl
        · exact Or.inl ⟨y, hyw, by omega, rfl⟩
  · -- Equation (4): the walks from `u` and from `w` up to `v`, excluded
    have hval : (hangingList T e).val =
        (sibsUp (EdgeAbove.target e) e.2.length e.2).reverse ++
          (e.2 :: ((sibsUp (EdgeAbove.target e) e.1.length e.1).reverse ++ [e.1])) := by
      simp only [hangingList, val_bind, val_step, hlca, hg, decide_false, Bool.false_eq_true,
        ↓reduceIte, hT.depth e.2 hw, hT.depth e.1 hu]
      rw [val_climb hT [e.1] hu hvu (Ne.symm (Ne.symm hg)) (by omega),
        val_climb hT _ hw hvw hvw' (by omega)]
    have memU := mem_sibsUp hvu hg (n := e.1.length) (by omega)
    have memW := mem_sibsUp hvw hvw' (n := e.2.length) (by omega)
    -- a sibling met on one walk is not met on the other, and is neither `u` nor `w`
    have off : ∀ x x' y, y <+: x → (EdgeAbove.target e).length + 2 ≤ y.length →
        parent y <+: x' → (x = e.1 ∧ x' = e.2 ∨ x = e.2 ∧ x' = e.1) → False := by
      intro x x' y hyx hy hPx' hxx
      have hy0 : y ≠ [] := by intro h; rw [h] at hy; simp at hy
      have hlen := length_parent hy0
      have hPx := (parent_prefix y).trans hyx
      rcases hxx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have := below_v _ hPx hPx'; omega
      · have := below_v _ hPx' hPx; omega
    have not_end : ∀ x y, y <+: x → (EdgeAbove.target e).length + 2 ≤ y.length →
        (x = e.1 ∨ x = e.2) → sibling y ≠ e.1 ∧ sibling y ≠ e.2 := by
      intro x y hyx hy hx
      have hy0 : y ≠ [] := by intro h; rw [h] at hy; simp at hy
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases hx with rfl | rfl
        · exact sibling_not_prefix hy0 hyx (h ▸ List.prefix_refl _)
        · exact off _ e.1 y hyx hy (by rw [← parent_sibling, h]; exact parent_prefix _)
            (Or.inr ⟨rfl, rfl⟩)
      · rcases hx with rfl | rfl
        · exact off _ e.2 y hyx hy (by rw [← parent_sibling, h]; exact parent_prefix _)
            (Or.inl ⟨rfl, rfl⟩)
        · exact sibling_not_prefix hy0 hyx (h ▸ List.prefix_refl _)
    rw [hval]
    refine ⟨?_, ?_⟩
    · rw [List.nodup_append, List.nodup_cons, List.nodup_append]
      refine ⟨List.nodup_reverse.mpr (sibsUp_nodup hvw hvw'), ⟨?_,
        List.nodup_reverse.mpr (sibsUp_nodup hvu hg), List.nodup_singleton _, ?_⟩, ?_⟩
      · rw [List.mem_append, List.mem_reverse, List.mem_singleton, memU]
        rintro (⟨y, hyu, hy, hzy⟩ | h)
        · exact (not_end _ y hyu hy (Or.inl rfl)).2 hzy.symm
        · exact EdgeAbove.endpoints_distinct he h
      · intro z hz z' hz' hzz
        rw [List.mem_singleton] at hz'
        rw [hz'] at hzz
        obtain ⟨y, hyu, hy, hzy⟩ := (memU z).mp (List.mem_reverse.mp hz)
        exact (not_end _ y hyu hy (Or.inl rfl)).1 (hzy.symm.trans hzz)
      · intro z hz z' hz' hzz
        rw [← hzz] at hz'
        obtain ⟨y, hyw, hy, hzy⟩ := (memW z).mp (List.mem_reverse.mp hz)
        rw [List.mem_cons, List.mem_append, List.mem_reverse, List.mem_singleton, memU] at hz'
        rcases hz' with h | ⟨y', hyu, hy', hzy'⟩ | h
        · exact (not_end _ y hyw hy (Or.inr rfl)).2 (hzy.symm.trans h)
        · have hy0 : y ≠ [] := by intro h; rw [h] at hy; simp at hy
          have hy0' : y' ≠ [] := by intro h; rw [h] at hy'; simp at hy'
          have hpar : parent y = parent y' := by
            rw [← parent_sibling y, ← parent_sibling y', ← hzy, ← hzy']
          exact off _ e.1 y hyw hy (hpar ▸ (parent_prefix y').trans hyu) (Or.inr ⟨rfl, rfl⟩)
        · exact (not_end _ y hyw hy (Or.inr rfl)).1 (hzy.symm.trans h)
    · intro r
      rw [mem_hanging_cross he hg, List.mem_append, List.mem_reverse, memW,
        List.mem_cons, List.mem_append, List.mem_reverse, memU, List.mem_singleton]
      constructor
      · rintro (h | h | h | h)
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inl h
      · rintro (h | h | h | h)
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inl h

/-! ### The candidate pairs, their weights and their buckets -/

/-- The admissibility test of the pair `e = (u, w)` (`EdgeAbove.Admissible`): neither `u` nor `w` is
the root, and `w` is not an ancestor of `u`. Seven operations. -/
def admissibleTest (T : Tables) (e : Address × Address) : Timed Bool := do
  let a ← step (decide (e.1 ≠ []))
  let b ← step (decide (e.2 ≠ []))
  let c ← ancestor T e.2 e.1
  steps 3 (a && b && !c)

@[simp] theorem time_admissibleTest (T : Tables) (e : Address × Address) :
    (admissibleTest T e).time = 7 := rfl

theorem val_admissibleTest {t : PhyloTree} {T : Tables} (hT : T.Correct t) {e : Address × Address}
    (hu : e.1 ∈ t.nodes) (hw : e.2 ∈ t.nodes) :
    (admissibleTest T e).val = decide (EdgeAbove.Admissible t e) := by
  simp only [admissibleTest, val_bind, val_step, val_steps, val_ancestor hT hw hu]
  rw [Bool.eq_iff_iff]
  simp [EdgeAbove.Admissible, hu, hw, and_assoc]

/-- Equation (1) by one scan of the distinct quartets of `Q`, read as a weighted set
(Section 2.3): `s_e(u, w)` is the sum of the multiplicities of the quartets accepted by the test
`delta`. The multiplicity of a quartet is stored with it, so reading it is one operation. -/
def weightScan (T : Tables) (Q : Multiset Quartet) (e : Address × Address) : Timed ℕ :=
  sumOver Q.toFinset fun q => do
    let d ← delta T e q
    step (if d then Q.count q else 0)

/-- The scan computes `s_e(u, w)` of Equation (1), for a well-labelled `T` and an admissible pair
(through `DynamicProgramming.edgeWeight_eq_satisfies`). -/
theorem val_weightScan {t : PhyloTree} (ht : t.WellLabelled) {T : Tables} (hT : T.Correct t)
    (Q : Multiset Quartet) {e : Address × Address} (he : e ∈ EdgeAbove.candidates t) :
    (weightScan T Q e).val = edgeWeight t Q e := by
  rw [edgeWeight_eq_satisfies ht he Q]
  simp [weightScan, val_delta ht hT he]

/-- Section 2.3: the weight of one pair takes `O(|Q|)` time, at most `133 |Q|` operations, where
`|Q|` is the number of distinct quartets of `Q`. -/
theorem time_weightScan (T : Tables) (Q : Multiset Quartet) (e : Address × Address) :
    (weightScan T Q e).time ≤ 133 * Q.toFinset.card := by
  unfold weightScan
  calc
    _ ≤ Q.toFinset.card * (131 + 2) := time_sumOver_le _ _ 131 (fun q _ => by
        simp only [time_bind, time_step]
        have := time_delta T e q
        omega)
    _ = _ := by ring

/-- The state of the enumeration: the bucket of each target, the pairs found so far with that
target, and the table of the weights `s_e`. -/
abbrev Buckets := (Address → List (Address × Address)) × (Address × Address → ℕ)

/-- Process the pair `e`: if it is admissible, compute its weight `s_e` (Equation (1)), write it in
the table, and put `e` in the bucket of its target `lca(u, w)`. -/
def visitPair (T : Tables) (Q : Multiset Quartet) (S : Buckets) (e : Address × Address) :
    Timed Buckets := do
  let ok ← admissibleTest T e
  if ok then do
    let s ← weightScan T Q e
    let v ← step (T.lca e)
    let b ← step (S.1 v)
    let B ← step (Function.update S.1 v (e :: b))
    let W ← step (Function.update S.2 e s)
    pure (B, W)
  else pure S

theorem val_visitPair (T : Tables) (Q : Multiset Quartet) (S : Buckets) (e : Address × Address) :
    (visitPair T Q S e).val = if (admissibleTest T e).val then
      (Function.update S.1 (T.lca e) (e :: S.1 (T.lca e)),
        Function.update S.2 e (weightScan T Q e).val) else S := by
  unfold visitPair
  cases h : (admissibleTest T e).val <;> simp [h]

theorem time_visitPair (T : Tables) (Q : Multiset Quartet) (S : Buckets)
    (e : Address × Address) :
    (visitPair T Q S e).time =
      7 + if (admissibleTest T e).val then (weightScan T Q e).time + 4 else 0 := by
  unfold visitPair
  cases h : (admissibleTest T e).val <;> simp [h]

/-- All pairs of elements of a list. -/
def pairList (l : List Address) : List (Address × Address) :=
  l.flatMap fun u => l.map fun w => (u, w)

theorem mem_pairList (l : List Address) (e : Address × Address) :
    e ∈ pairList l ↔ e.1 ∈ l ∧ e.2 ∈ l := by
  simp only [pairList, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    exact ⟨hu, hw⟩
  · intro h
    exact ⟨e.1, h.1, e.2, h.2, rfl⟩

theorem pairList_nodup {l : List Address} (hl : l.Nodup) : (pairList l).Nodup := by
  unfold pairList
  rw [List.nodup_flatMap]
  refine ⟨fun u _ => hl.map (fun a b h => (Prod.mk.inj h).2), ?_⟩
  refine hl.imp ?_
  intro u u' hne
  rw [Function.onFun, List.disjoint_left]
  intro e he he'
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp he
  obtain ⟨w', -, h⟩ := List.mem_map.mp he'
  exact hne (Prod.mk.inj h).1.symm

/-- Section 2.3: enumerate the candidate pairs once, putting each admissible pair in the bucket of
its target, and computing the weights `s_e` "in a preprocessing step" (Section 2.2). -/
def enumerate (T : Tables) (Q : Multiset Quartet) (pre : List Address) : Timed Buckets :=
  forList (visitPair T Q) (pairList pre) (fun _ => [], fun _ => 0)

/-- With correct tables, the enumeration over the vertices of `T` puts in the bucket of `v`
exactly the pairs of Pairs(v) (`DynamicProgramming.pairsAt`), each once, and writes the weight of
every candidate pair. -/
theorem enumerate_buckets {t : PhyloTree} {T : Tables} (hT : T.Correct t) (Q : Multiset Quartet) :
    let S := (enumerate T Q t.preorder).val
    (∀ v, (S.1 v).Nodup ∧ ∀ e, e ∈ S.1 v ↔ e ∈ pairsAt t v) ∧
      ∀ e ∈ EdgeAbove.candidates t, S.2 e = (weightScan T Q e).val := by
  intro S
  let Inv : List (Address × Address) → Buckets → Prop := fun A S =>
    (∀ v, (S.1 v).Nodup) ∧
      (∀ v e, e ∈ S.1 v ↔ e ∈ A ∧ EdgeAbove.Admissible t e ∧ EdgeAbove.target e = v) ∧
      ∀ e ∈ A, EdgeAbove.Admissible t e → S.2 e = (weightScan T Q e).val
  have hinv : Inv (pairList t.preorder) S := by
    simp only [S, enumerate, val_forList]
    apply foldl_invariant (pairList t.preorder) _ Inv
    · refine ⟨fun v => List.nodup_nil, fun v e => ?_, fun e he => by simp at he⟩
      simp
    · intro A e B U hsplit hU
      obtain ⟨hnd, hmem, hw⟩ := hU
      have heA : e ∉ A := by
        have h := pairList_nodup (PhyloTree.preorder_nodup t)
        rw [hsplit] at h
        exact fun h' => List.disjoint_of_nodup_append h h' (by simp)
      have he : e ∈ pairList t.preorder := by rw [hsplit]; simp
      obtain ⟨hu, hw'⟩ := (mem_pairList _ e).mp he
      rw [PhyloTree.mem_preorder] at hu hw'
      rw [val_visitPair, val_admissibleTest hT hu hw', hT.lca e.1 hu e.2 hw']
      by_cases hadm : EdgeAbove.Admissible t e
      · simp only [hadm, decide_true, ↓reduceIte]
        set v := lca e.1 e.2 with hv
        refine ⟨?_, ?_, ?_⟩
        · intro v'
          by_cases hvv : v' = v
          · subst hvv
            simp only [Function.update_self, List.nodup_cons]
            exact ⟨fun h => heA ((hmem _ e).mp h).1, hnd _⟩
          · simp only [ne_eq, hvv, not_false_eq_true, Function.update_of_ne]
            exact hnd v'
        · intro v' e'
          by_cases hvv : v' = v
          · subst hvv
            simp only [Function.update_self, List.mem_cons, hmem, List.mem_append,
              List.not_mem_nil, or_false]
            constructor
            · rintro (rfl | ⟨h1, h2, h3⟩)
              · exact ⟨Or.inr rfl, hadm, rfl⟩
              · exact ⟨Or.inl h1, h2, h3⟩
            · rintro ⟨h1 | rfl, h2, h3⟩
              · exact Or.inr ⟨h1, h2, h3⟩
              · exact Or.inl rfl
          · simp only [ne_eq, hvv, not_false_eq_true, Function.update_of_ne, hmem,
              List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro ⟨h1, h2, h3⟩
              exact ⟨Or.inl h1, h2, h3⟩
            · rintro ⟨h1 | rfl, h2, h3⟩
              · exact ⟨h1, h2, h3⟩
              · exact (hvv h3.symm).elim
        · intro e' he' hadm'
          rcases List.mem_append.mp he' with he' | he'
          · have hne : e' ≠ e := fun h => heA (h ▸ he')
            simp only [ne_eq, hne, not_false_eq_true, Function.update_of_ne]
            exact hw e' he' hadm'
          · rw [List.mem_singleton.mp he']
            simp
      · simp only [hadm, decide_false, Bool.false_eq_true, ↓reduceIte]
        refine ⟨hnd, fun v e' => ?_, fun e' he' hadm' => ?_⟩
        · rw [hmem, List.mem_append, List.mem_singleton]
          constructor
          · rintro ⟨h1, h2, h3⟩
            exact ⟨Or.inl h1, h2, h3⟩
          · rintro ⟨h1 | rfl, h2, h3⟩
            · exact ⟨h1, h2, h3⟩
            · exact (hadm h2).elim
        · rcases List.mem_append.mp he' with he' | he'
          · exact hw e' he' hadm'
          · rw [List.mem_singleton.mp he'] at hadm'
            exact (hadm hadm').elim
  obtain ⟨hnd, hmem, hw⟩ := hinv
  refine ⟨fun v => ⟨hnd v, fun e => ?_⟩, fun e he => ?_⟩
  · rw [hmem, mem_pairList, PhyloTree.mem_preorder, PhyloTree.mem_preorder]
    simp only [pairsAt, EdgeAbove.candidates, Finset.mem_filter, Finset.mem_product]
    tauto
  · obtain ⟨hn, hadm⟩ := Finset.mem_filter.mp he
    obtain ⟨hu, hw'⟩ := Finset.mem_product.mp hn
    exact hw e ((mem_pairList _ e).mpr ⟨(PhyloTree.mem_preorder t _).mpr hu,
      (PhyloTree.mem_preorder t _).mpr hw'⟩) hadm

/-- Section 2.3: the enumeration takes at most `8 |V(T)|² + |candidates| (133 |Q| + 4)`
operations: a constant number per pair of vertices, and the scan of `Q` per candidate pair. -/
theorem time_enumerate {t : PhyloTree} {T : Tables} (hT : T.Correct t) (Q : Multiset Quartet) :
    (enumerate T Q t.preorder).time ≤
      8 * t.nodes.card ^ 2 + (EdgeAbove.candidates t).card * (133 * Q.toFinset.card + 4) := by
  unfold enumerate
  rw [time_forList_eq _ _ _ (fun e => 7 + if (admissibleTest T e).val then
    (weightScan T Q e).time + 4 else 0) (fun S e _ => time_visitPair T Q S e)]
  have hnd := pairList_nodup (PhyloTree.preorder_nodup t)
  have hfin : (pairList t.preorder).toFinset = t.nodes ×ˢ t.nodes := by
    ext e
    simp [mem_pairList, PhyloTree.mem_preorder]
  rw [← List.sum_toFinset _ hnd, hfin]
  have hterm : ∀ e ∈ t.nodes ×ˢ t.nodes, (7 + (if (admissibleTest T e).val then
      (weightScan T Q e).time + 4 else 0)) + 1 ≤
      8 + if EdgeAbove.Admissible t e then 133 * Q.toFinset.card + 4 else 0 := by
    intro e he
    obtain ⟨hu, hw⟩ := Finset.mem_product.mp he
    rw [val_admissibleTest hT hu hw]
    by_cases hadm : EdgeAbove.Admissible t e
    · simp only [hadm, decide_true, ↓reduceIte]
      have := time_weightScan T Q e
      omega
    · simp [hadm]
  calc
    _ ≤ ∑ e ∈ t.nodes ×ˢ t.nodes,
        (8 + if EdgeAbove.Admissible t e then 133 * Q.toFinset.card + 4 else 0) :=
      Finset.sum_le_sum hterm
    _ = 8 * t.nodes.card ^ 2 + (EdgeAbove.candidates t).card * (133 * Q.toFinset.card + 4) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp only [Finset.sum_const, Finset.card_product, smul_eq_mul, EdgeAbove.candidates]
      ring

/-! ### Filling the array bottom-up -/

/-- `s_e + s_dp(v, u, w)` for the pair `e = (u, w)` with target `v` (Equation (3)): the weight of
`e`, read from the table `W`, plus the sum of `M` over the roots of the subtrees hanging off the
cycle `γ(u, w)` (Equations (4) and (5), `DynamicProgramming.hanging_score`), listed by
`hangingList`. -/
def pairValue (T : Tables) (W : Address × Address → ℕ) (M : Address → ℕ)
    (e : Address × Address) : Timed ℕ := do
  let s ← step (W e)
  let L ← hangingList T e
  let d ← sumList (fun r => step (M r)) L
  step (s + d)

/-- `s(v)` (Equation (3)): the maximum of `pairValue` over the bucket of `v` (`0` if it is
empty). -/
def sValue (T : Tables) (B : Address → List (Address × Address)) (W : Address × Address → ℕ)
    (M : Address → ℕ) (v : Address) : Timed ℕ := do
  let b ← step (B v)
  maxList (pairValue T W M) b

/-- Equation (2) at the vertex `v`: `M[v] = 0` at a leaf, and `M[v] = max(M[l(v)] + M[r(v)], s(v))`
otherwise. -/
def solveVertex (T : Tables) (B : Address → List (Address × Address))
    (W : Address × Address → ℕ) (M : Address → ℕ) (v : Address) : Timed (Address → ℕ) := do
  let k ← step (T.kind v)
  match k with
  | .leaf _ => step (Function.update M v 0)
  | .fork l r => do
      let a ← step (M l)
      let b ← step (M r)
      let sv ← sValue T B W M v
      let x ← steps 2 (max (a + b) sv)
      step (Function.update M v x)

/-- Fill the array `M` vertex by vertex in the order `order`, starting from `0`. -/
def fill (T : Tables) (B : Address → List (Address × Address)) (W : Address × Address → ℕ)
    (order : List Address) : Timed (Address → ℕ) :=
  forList (solveVertex T B W) order (fun _ => 0)

/-- The reverse of a list, one operation per element. -/
def reverseList (l : List Address) : Timed (List Address) :=
  forList (fun acc p => step (p :: acc)) l []

theorem val_reverseList (l : List Address) : (reverseList l).val = l.reverse := by
  have h : ∀ (acc : List Address), l.foldl (fun acc p => p :: acc) acc = l.reverse ++ acc := by
    induction l with
    | nil => simp
    | cons a l ih => intro acc; simp [ih]
  simp [reverseList, h]

theorem time_reverseList (l : List Address) : (reverseList l).time = 2 * l.length := by
  unfold reverseList
  rw [time_forList_eq _ _ _ (fun _ => 1) (fun _ _ _ => rfl)]
  simp
  ring

/-- **CAMUS** (Section 2.2), written as a program (Section 2.3): the preprocessing, the enumeration
of the candidate pairs with their weights, and the bottom-up fill of `M` in the reverse of the
preorder, which lists every vertex after its descendants. -/
def camus (t : PhyloTree) (Q : Multiset Quartet) : Timed (Address → ℕ) := do
  let P ← preprocess t
  let S ← enumerate P.1 Q P.2
  let order ← reverseList P.2
  fill P.1 S.1 S.2 order

/-! ### Correctness -/

/-- `DynamicProgramming.Array` depends only on the values of `M` at the vertices of `T`. -/
theorem array_congr {t : PhyloTree} {w : Pair → ℕ} {M M' : Address → ℕ} (hM : Array t w M)
    (h : ∀ p ∈ t.nodes, M p = M' p) : Array t w M' := by
  intro v hv
  have hrec := hM v hv
  obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff v).mp hv
  rw [hsub] at hrec ⊢
  cases sub with
  | leaf a =>
    change M v = 0 at hrec
    change M' v = 0
    rw [← h v hv]
    exact hrec
  | fork l r =>
    change M v = max (M (v ++ [false]) + M (v ++ [true])) (s t w M v) at hrec
    change M' v = max (M' (v ++ [false]) + M' (v ++ [true])) (s t w M' v)
    have hs : s t w M v = s t w M' v := by
      unfold s
      apply Finset.sup_congr rfl
      intro e he
      have hae := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
      rw [hanging_score t M e hae, hanging_score t M' e hae]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      exact h r (Finset.mem_filter.mp hr).1
    rw [← h v hv, ← h _ (PhyloTree.child_mem_nodes hsub false),
      ← h _ (PhyloTree.child_mem_nodes hsub true), ← hs]
    exact hrec

theorem val_pairValue {t : PhyloTree} {T : Tables} (hT : T.Correct t) {e : Address × Address}
    (he : EdgeAbove.Admissible t e) (W : Address × Address → ℕ) (M : Address → ℕ) :
    (pairValue T W M e).val = W e + ∑ r ∈ hanging t e, M r := by
  obtain ⟨hnd, hmem⟩ := hangingList_spec hT he
  simp only [pairValue, val_bind, val_step, val_sumList]
  congr 1
  rw [← List.sum_toFinset _ hnd]
  congr 1
  ext r
  simp [hmem]

theorem val_sValue {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} {v : Address}
    (hB : ∀ e, e ∈ B v ↔ e ∈ pairsAt t v) (W : Address × Address → ℕ) (M : Address → ℕ) :
    (sValue T B W M v).val = (pairsAt t v).sup fun e => W e + ∑ r ∈ hanging t e, M r := by
  simp only [sValue, val_bind, val_step, val_maxList]
  have hfin : (B v).toFinset = pairsAt t v := by
    ext e
    simp [hB]
  rw [hfin]
  apply Finset.sup_congr rfl
  intro e he
  exact val_pairValue hT (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2 W M

/-- One step of the fill: if `M` agrees with a solution `Mref` of the recurrence on the proper
descendants of `v`, `solveVertex` writes `Mref v` at `v`. -/
theorem val_solveVertex {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    (Q : Multiset Quartet) {B : Address → List (Address × Address)}
    (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v) {W : Address × Address → ℕ}
    (hW : ∀ e ∈ EdgeAbove.candidates t, W e = edgeWeight t Q e) {Mref : Address → ℕ}
    (hMref : Array t (edgeWeight t Q) Mref) {M : Address → ℕ} {v : Address} (hv : v ∈ t.nodes)
    (hdesc : ∀ y ∈ t.nodes, v <+: y → v ≠ y → M y = Mref y) :
    (solveVertex T B W M v).val = Function.update M v (Mref v) := by
  have hrec := hMref v hv
  obtain ⟨sub, hsub⟩ := (t.mem_nodes_iff v).mp hv
  have hk := hT.kind v hv
  rw [hsub] at hrec
  cases sub with
  | leaf a =>
    change Mref v = 0 at hrec
    have hk' : T.kind v = .leaf a := by rw [hk]; simp [kindAt, hsub]
    simp [solveVertex, hk', hrec]
  | fork l r =>
    change Mref v = max (Mref (v ++ [false]) + Mref (v ++ [true]))
      (s t (edgeWeight t Q) Mref v) at hrec
    have hk' : T.kind v = .fork (v ++ [false]) (v ++ [true]) := by rw [hk]; simp [kindAt, hsub]
    have hchild (b : Bool) : M (v ++ [b]) = Mref (v ++ [b]) :=
      hdesc _ (PhyloTree.child_mem_nodes hsub b) (List.prefix_append _ _) (by simp)
    have hs : ((pairsAt t v).sup fun e => W e + ∑ r ∈ hanging t e, M r) =
        s t (edgeWeight t Q) Mref v := by
      unfold s
      apply Finset.sup_congr rfl
      intro e he
      obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp he
      have hae := (Finset.mem_filter.mp hc).2
      rw [hW e hc, hanging_score t Mref e hae]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      have hgeo := frontier_below (EdgeAbove.footprint_region t e hae) hr
      exact hdesc r (Finset.mem_filter.mp hr).1 (htarget ▸ hgeo.1) (htarget ▸ hgeo.2)
    simp only [solveVertex, val_bind, val_step, hk', val_steps, val_sValue hT (hB v) W M,
      hchild, hs]
    rw [← hrec]

/-- Section 2.2: filled in the reverse of the preorder, which lists every vertex after its
descendants, `M` satisfies the recurrence (Equation (2)) for the weights of Equation (1). -/
theorem fill_array {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    (Q : Multiset Quartet) {B : Address → List (Address × Address)}
    (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v) {W : Address × Address → ℕ}
    (hW : ∀ e ∈ EdgeAbove.candidates t, W e = edgeWeight t Q e) :
    Array t (edgeWeight t Q) (fill T B W t.preorder.reverse).val := by
  -- the reference solution of the recurrence (`DynamicProgramming.bottomUp_array`)
  let Mref := DynamicProgramming.bottomUp t (edgeWeight t Q) (t.nodes.sup List.length + 1)
  have hMref : Array t (edgeWeight t Q) Mref := bottomUp_array t (edgeWeight t Q)
  have hinv : ∀ x ∈ t.preorder.reverse, (fill T B W t.preorder.reverse).val x = Mref x := by
    simp only [fill, val_forList]
    refine foldl_invariant t.preorder.reverse (fun M v => (solveVertex T B W M v).val)
      (fun (A : List Address) (M : Address → ℕ) => ∀ x ∈ A, M x = Mref x) (by simp) ?_
    · intro A v B' M hsplit hM
      have hv : v ∈ t.nodes := by
        rw [← PhyloTree.mem_preorder, ← List.mem_reverse, hsplit]; simp
      have hvA : v ∉ A := by
        have hnd := List.nodup_reverse.mpr (PhyloTree.preorder_nodup t)
        rw [hsplit] at hnd
        exact fun h => List.disjoint_of_nodup_append hnd h (by simp)
      rw [val_solveVertex hT Q hB hW hMref hv (fun y hy hvy hne =>
        hM y (PhyloTree.reverse_preorder_descendant_before hsplit hy hvy hne))]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · have hne : x ≠ v := fun h => hvA (h ▸ hx)
        rw [Function.update_of_ne hne]
        exact hM x hx
      · rw [List.mem_singleton.mp hx]
        simp
  exact array_congr hMref fun p hp =>
    (hinv p (List.mem_reverse.mpr ((PhyloTree.mem_preorder t p).mpr hp))).symm

/-- **Section 2.2, computed.** For a well-labelled tree `T` and a multiset `Q` of quartets, the
array `M` computed by `camus` satisfies the recurrence of Section 2.2 (Equations (2)–(5)) for the
weights `s_e` of Equation (1): `DynamicProgramming.Array t (edgeWeight t Q) M`. So Theorem 1
applies to it (`Camus.theorem1`, `Complexity.camus_optimal`). -/
theorem camus_array {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet) :
    Array t (edgeWeight t Q) (camus t Q).val := by
  have hT := preprocess_correct t
  have hpre := preprocess_order t
  obtain ⟨hB, hW⟩ := enumerate_buckets hT Q
  simp only [camus, val_bind, val_reverseList, hpre]
  exact fill_array hT Q (fun v e => (hB v).2 e)
    (fun e he => (hW e he).trans (val_weightScan ht hT Q he))

/-- Theorem 1 for the computed array. For a well-labelled tree `T`, backtracking through the array
computed by `camus` gives a family `E` of pairs whose network `Realization.graph t E` is built on
`T` and satisfies `M[root]` quartets of `Q`, and no network built on `T` satisfies more. -/
theorem camus_optimal {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet) :
    ∃ E, (Realization.graph t E).AnchoredExtension t ∧
      score Q (novel t Q (Realization.graph t E)) = (camus t Q).val [] ∧
      ∀ N : RootedNetwork, N.AnchoredExtension t →
        score Q (novel t Q N) ≤ (camus t Q).val [] := by
  obtain ⟨E, hE⟩ := exists_trace t (edgeWeight t Q) _ (camus_array ht Q)
    (PhyloTree.root_mem_nodes t)
  obtain ⟨h1, h2, h3, -⟩ := theorem1 t ht Q _ (camus_array ht Q) E hE
  exact ⟨E, h1, h2, fun N hN => h2 ▸ h3 N hN⟩

/-! ### Running time -/

/-- With correct tables, the walks of an admissible pair list `|hanging t e| ≤ |V(T)|` vertices. -/
theorem length_hangingList {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {e : Address × Address} (he : EdgeAbove.Admissible t e) :
    (hangingList T e).val.length ≤ t.nodes.card := by
  obtain ⟨hnd, hmem⟩ := hangingList_spec hT he
  have hfin : (hangingList T e).val.toFinset = hanging t e := by
    ext r
    simp [hmem]
  rw [← List.toFinset_card_of_nodup hnd, hfin]
  exact hanging_bound t e

/-- Section 2.3, step (iii): `s_e + s_dp` for one pair takes `O(n)` time: at most
`10 + 9 |V(T)|` operations. -/
theorem time_pairValue {t : PhyloTree} {T : Tables} (hT : T.Correct t) {e : Address × Address}
    (he : EdgeAbove.Admissible t e) (W : Address × Address → ℕ) (M : Address → ℕ) :
    (pairValue T W M e).time ≤ 10 + 9 * t.nodes.card := by
  have h1 := time_hangingList T e
  have h2 := length_hangingList hT he
  simp only [pairValue, time_bind, time_step, val_step, time_sumList, sum_map_const_nat]
  omega

/-- Section 2.3, step (iii): solving the subproblem at `v` takes `O(|Pairs(v)| · n)` time, besides
the weights: at most `7 + |Pairs(v)| (12 + 9 |V(T)|)` operations. -/
theorem time_solveVertex {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} {v : Address}
    (hB : ∀ e, e ∈ B v ↔ e ∈ pairsAt t v) (W : Address × Address → ℕ) (M : Address → ℕ) :
    (solveVertex T B W M v).time ≤ 7 + (B v).length * (12 + 9 * t.nodes.card) := by
  have hs : (sValue T B W M v).time ≤ 1 + (B v).length * (12 + 9 * t.nodes.card) := by
    simp only [sValue, time_bind, time_step, val_step, time_maxList]
    have : ((B v).map fun e => (pairValue T W M e).time + 2).sum ≤
        ((B v).map fun _ => 12 + 9 * t.nodes.card).sum := by
      apply List.sum_le_sum
      intro e he
      have hae := (Finset.mem_filter.mp (Finset.mem_filter.mp ((hB e).mp he)).1).2
      have := time_pairValue hT hae W M
      omega
    rw [sum_map_const_nat] at this
    omega
  unfold solveVertex
  cases hk : T.kind v with
  | leaf a =>
    simp only [time_bind, time_step, val_step]
    omega
  | fork l r =>
    simp only [time_bind, time_step, val_step, time_steps]
    omega

/-- Section 2.3, step (iv): filling `M` takes `O(|V(T)| + |candidates| · n)` time. Each candidate
pair is in exactly one bucket (`candidate_visits`): "no edge is ever considered in the s(·)
function more than once over all subproblems". -/
theorem time_fill {t : PhyloTree} {T : Tables} (hT : T.Correct t)
    {B : Address → List (Address × Address)} (hB : ∀ v e, e ∈ B v ↔ e ∈ pairsAt t v)
    (hnd : ∀ v, (B v).Nodup) (W : Address × Address → ℕ) :
    (fill T B W t.preorder.reverse).time ≤
      8 * t.nodes.card + (EdgeAbove.candidates t).card * (12 + 9 * t.nodes.card) := by
  have hlen : ∀ v, (B v).length = (pairsAt t v).card := by
    intro v
    rw [← List.toFinset_card_of_nodup (hnd v)]
    congr 1
    ext e
    simp [hB]
  unfold fill
  calc
    _ ≤ (t.preorder.reverse.map fun v => 7 + (B v).length * (12 + 9 * t.nodes.card) + 1).sum :=
      time_forList_le _ _ _ _ (fun M v _ => time_solveVertex hT (hB v) W M)
    _ = ∑ v ∈ t.nodes, (8 + (pairsAt t v).card * (12 + 9 * t.nodes.card)) := by
      rw [← List.sum_toFinset _ (List.nodup_reverse.mpr (PhyloTree.preorder_nodup t)),
        List.toFinset_reverse, PhyloTree.preorder_toFinset]
      apply Finset.sum_congr rfl
      intro v _
      rw [hlen]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, candidate_visits]
      simp [mul_comm]

/-- **Section 2.3: the running time `O(n²(|Q| + n))`.** For a well-labelled tree `T` with `n`
leaves and a multiset `Q` with `|Q|` distinct quartets, `camus t Q` performs at most
`600 n² (|Q| + n)` operations. -/
theorem camus_time {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet) :
    (camus t Q).time ≤ 600 * t.taxa.card ^ 2 * (Q.toFinset.card + t.taxa.card) := by
  have hT := preprocess_correct t
  have hpre := preprocess_order t
  obtain ⟨hB, -⟩ := enumerate_buckets hT Q
  -- (i) the preprocessing
  have t1 := preprocess_time t
  -- (ii) the enumeration, with one scan of `Q` per candidate pair
  have t2 := time_enumerate hT Q
  have t3 := time_reverseList t.preorder
  -- (iii) and (iv): the fill
  have t4 := time_fill hT (fun v e => (hB v).2 e) (fun v => (hB v).1)
    (enumerate (preprocess t).val.1 Q t.preorder).val.2
  simp only [camus, time_bind, val_reverseList]
  rw [hpre]
  rw [PhyloTree.preorder_length] at t3
  -- the sizes: `|V(T)| = 2n − 1` and at most `|V(T)|²` candidate pairs
  have hnodes := t.nodes_count
  have htaxa : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  have hn := t.labels_nonempty
  have hc := candidates_bound t
  rw [htaxa]
  set N := t.nodes.card
  set n := t.labels.length
  set C := (EdgeAbove.candidates t).card
  set q := Q.toFinset.card
  have hN : N ≤ 2 * n := by omega
  have hC : C ≤ 4 * n ^ 2 := by nlinarith
  have hCN : C * N ≤ 8 * n ^ 3 := by nlinarith [Nat.mul_le_mul hC hN]
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hn3 : n ^ 2 ≤ n ^ 3 := by nlinarith
  have hCq : C * q ≤ 4 * n ^ 2 * q := Nat.mul_le_mul_right q hC
  nlinarith

end Complexity

end Camus
