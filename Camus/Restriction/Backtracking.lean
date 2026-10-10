module

public import Camus.Restriction.Main

/-!
# Section 2.4: backtracking through the budget array

Section 2.4 of the paper modifies the dynamic program so that it "returns m networks
N_1, N_2, …, N_m", and Section 2.2 obtains networks from the array by backtracking ("backtracking
allow us to infer the optimal network"). This file defines the backtracking through the array
`M[v][k]` of Section 2.4 (`BudgetDP.Trace`) and proves that it returns the networks `N_k`. A trace
from `v` with budget `k` is a feasible family of exactly `k` added edges with targets in `T_v`,
whose value is the value kept in `M[v][k]`; a trace exists whenever that row is nonempty; and at the
root, with the weights `s_e` of Equation (1), the network of a trace is built on `T`, has exactly
`k` reticulations, and satisfies (and displays) at least as many quartets of `Q` as every network
built on `T` with exactly `k` reticulations. Choosing a trace for each budget gives the networks
`N_1, …, N_m` of Section 2.4.

The backtracking follows the recurrence (`BudgetDP.cases`). At a leaf, the budget is `0` and no
edge is added. At an internal vertex `v`, either the budget is split between the two children, and
their row values add up to the value kept in `M[v][k]`; or an edge `e ∈ Pairs(v)` is added, using
one unit of budget, and the remaining `k − 1` units are distributed over the subtrees hanging off
its cycle. The knapsack `BudgetDP.forest` keeps only the maximum after each convolution, so the
distribution is found by backtracking through the knapsack (`BudgetDP.Knapsack`): at each
convolution, the budgets chosen attain the value kept.

## Main results

* `BudgetDP.Knapsack`, `BudgetDP.Trace`: the backtracking through the knapsack and through the
  array.
* `BudgetDP.trace_sound`: a trace from `v` with budget `k` is a feasible family of exactly `k`
  edges with targets in `T_v`, whose value is in `M[v][k]`.
* `BudgetDP.exists_trace`: if `M[v][k]` is nonempty, there is a trace from `v` with budget `k`.
* `BudgetDP.trace_graph_optimal`: the network of a trace from the root is built on `T`, has exactly
  `k` reticulations, satisfies the value of `M[r][k]` quartets of `Q`, and is optimal among the
  networks built on `T` with exactly `k` reticulations.
* `BudgetDP.backtracking_networks`, `BudgetDP.exists_traces`: the networks `N_1, …, N_m` of
  Section 2.4, obtained by backtracking.

## Proof (the paper's)

The paper gives no argument for Section 2.4 beyond "a relatively simple modification of the dynamic
programming algorithm". The proofs follow the paper's proof of Theorem 1, for the budget array.

(a) The output is a level-1 network extending `T`: in a trace, the families of the two children lie
in disjoint subtrees (`DynamicProgramming.fork_feasible`), and the families below the subtrees
hanging off the cycle of an edge with target `v` avoid that cycle
(`DynamicProgramming.gall_feasible`). This is the feasibility part of `BudgetDP.trace_sound`, by
induction on the trace.

(b) The value of a trace is the value kept in the row: by induction on the trace, using that every
row holds at most one value (`BudgetDP.array_row_card`), and, for an edge with target `v`, that
the budgets and values chosen in the knapsack add up to the hanging budget and the knapsack value
(`BudgetDP.Knapsack.budget_eq`, `BudgetDP.Knapsack.value_eq`). The edge counts add up in the same
way (`BudgetDP.card_gall`).

(c) Optimality: every feasible family of `k` edges has value at most the value kept in the row
(`BudgetDP.exact_optimal`). At the root, Lemma 1 turns values into numbers of satisfied quartets,
as in `BudgetDP.exact_graph_optimal`.

A trace exists when the row is nonempty (`BudgetDP.exists_trace`), by strong induction over
subtrees as for `DynamicProgramming.exists_trace`: the value kept in `M[v][k]` comes from one of
the two cases of the recurrence, and in the second case backtracking through the knapsack gives
the budgets of the hanging subtrees (`BudgetDP.exists_knapsack`), whose rows are then nonempty.
-/

@[expose] public section

namespace Camus.BudgetDP

open DynamicProgramming

/-- Backtracking through the knapsack `forest M rs` (Section 2.4). `Knapsack M b s rs k z` says
that the budgets `b r` and the row values `s r ∈ M[r][b r]` of the subtrees `r ∈ rs` distribute the
budget `k` with total value `z`, and that the knapsack keeps each partial total: for
`rs = r :: rs'`, if the budgets of `rs'` add up to `k'` with total value `z'`, then `s r + z'` is
the value kept in row `b r + k'` of `forest M rs`. -/
inductive Knapsack (M : Address → ℕ → Finset ℕ) (b s : Address → ℕ) :
    List Address → ℕ → ℕ → Prop
  | nil : Knapsack M b s [] 0 0
  | cons (r : Address) (rs : List Address) (k z : ℕ)
      (row : s r ∈ M r (b r))
      (tail : Knapsack M b s rs k z)
      (chosen : s r + z ∈ forest M (r :: rs) (b r + k)) :
      Knapsack M b s (r :: rs) (b r + k) (s r + z)

/-- Section 2.4: the backtracking through the array `M` of the recurrence `BudgetDP.Array`, for
edge weights `w`. `Trace t w M v k E` says that the family `E` of pairs is a result of backtracking
from the vertex `v` with budget `k`.
* `leaf`: at a leaf, the budget is `0` and `E` is empty.
* `fork`: at an internal vertex, no added edge has target `v`. The budget is split as `i + j`
  between the two children, and `E` is the union of results there, whose row values `x` and `y`
  add up to the value kept in `M[v][i + j]`.
* `gall`: an edge `e ∈ Pairs(v)` is added, using one unit of budget. The remaining `k` units are
  distributed over the subtrees `r` hanging off the cycle of `e`, with budgets `b r` and values
  `s r` chosen by backtracking through the knapsack (`Knapsack`), and `E` consists of `e` and
  results at the hanging subtrees with these budgets; `w e` plus the knapsack value `z` is the value
  kept in `M[v][k + 1]`. -/
inductive Trace (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ) :
    Address → ℕ → Finset Pair → Prop
  | leaf (v : Address) (a : ℕ) (node : t.nodeAt v = some (.leaf a)) :
      Trace t w M v 0 ∅
  | fork (v : Address) (l r : PhyloTree) (i j x y : ℕ) (L R : Finset Pair)
      (node : t.nodeAt v = some (.fork l r))
      (left : Trace t w M (v ++ [false]) i L)
      (right : Trace t w M (v ++ [true]) j R)
      (leftRow : x ∈ M (v ++ [false]) i)
      (rightRow : y ∈ M (v ++ [true]) j)
      (chosen : x + y ∈ M v (i + j)) :
      Trace t w M v (i + j) (L ∪ R)
  | gall (v : Address) (e : Pair) (k z : ℕ) (b s : Address → ℕ) (F : Address → Finset Pair)
      (edge : e ∈ pairsAt t v)
      (knapsack : Knapsack M b s (hanging t e).toList k z)
      (branches : ∀ r ∈ hanging t e, Trace t w M r (b r) (F r))
      (chosen : w e + z ∈ M v (k + 1)) :
      Trace t w M v (k + 1) (insert e ((hanging t e).biUnion F))

namespace Knapsack

variable {M : Address → ℕ → Finset ℕ} {b s : Address → ℕ}

/-- The total value of a backtracking through the knapsack is the value kept in its row. -/
theorem mem_forest {rs : List Address} {k z : ℕ} (h : Knapsack M b s rs k z) :
    z ∈ forest M rs k := by
  cases h with
  | nil => simp [forest]
  | cons r rs k z row tail chosen => exact chosen

/-- The budget distributed by a backtracking through the knapsack is the sum of the budgets. -/
theorem budget_eq {rs : List Address} {k z : ℕ} (h : Knapsack M b s rs k z) :
    k = (rs.map b).sum := by
  induction h with
  | nil => rfl
  | cons r rs k z row tail chosen ih => simp [ih]

/-- The total value of a backtracking through the knapsack is the sum of the values. -/
theorem value_eq {rs : List Address} {k z : ℕ} (h : Knapsack M b s rs k z) :
    z = (rs.map s).sum := by
  induction h with
  | nil => rfl
  | cons r rs k z row tail chosen ih => simp [ih]

/-- Each value chosen by a backtracking through the knapsack is in the row of its budget. -/
theorem row_mem {rs : List Address} {k z : ℕ} (h : Knapsack M b s rs k z) :
    ∀ r ∈ rs, s r ∈ M r (b r) := by
  induction h with
  | nil => simp
  | cons r rs k z row tail chosen ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact row
    · exact ih x hx

/-- A backtracking through the knapsack depends only on the budgets and values of its subtrees. -/
theorem congr {b' s' : Address → ℕ} {rs : List Address} {k z : ℕ}
    (h : Knapsack M b s rs k z) (hb : ∀ r ∈ rs, b' r = b r) (hs : ∀ r ∈ rs, s' r = s r) :
    Knapsack M b' s' rs k z := by
  induction h with
  | nil => exact .nil
  | cons r rs k z row tail chosen ih =>
    have hbr := hb r (by simp)
    have hsr := hs r (by simp)
    have h := Knapsack.cons (b := b') (s := s') r rs k z (by rw [hbr, hsr]; exact row)
      (ih (fun x hx => hb x (by simp [hx])) (fun x hx => hs x (by simp [hx])))
      (by rw [hbr, hsr]; exact chosen)
    rwa [hbr, hsr] at h

end Knapsack

/-- Backtracking through the knapsack is always possible: every value kept in a row of
`forest M rs`, for a list `rs` without repetition, is the total value of a backtracking through
the knapsack. At each convolution, the value kept is the sum of a value of the row of the head
subtree and a value kept for the tail (`BudgetDP.mem_convolution`). -/
theorem exists_knapsack {M : Address → ℕ → Finset ℕ} {rs : List Address} (hrs : rs.Nodup)
    {k z : ℕ} (hz : z ∈ forest M rs k) : ∃ b s, Knapsack M b s rs k z := by
  induction rs generalizing k z with
  | nil =>
    simp only [forest] at hz
    split_ifs at hz with hk
    · rw [Finset.mem_singleton.mp hz, hk]
      exact ⟨fun _ => 0, fun _ => 0, .nil⟩
    · exact (Finset.notMem_empty _ hz).elim
  | cons r rs ih =>
    have hr : r ∉ rs := (List.nodup_cons.mp hrs).1
    -- the value kept is `x + y` with `x` in row `i` of `r` and `y` kept in row `j` of the tail
    obtain ⟨i, j, x, y, hij, hx, hy, hxy⟩ := mem_convolution.mp (mem_best.mp hz).1
    obtain ⟨b, s, h⟩ := ih (List.nodup_cons.mp hrs).2 hy
    let b' := Function.update b r i
    let s' := Function.update s r x
    have hb' : ∀ q ∈ rs, b' q = b q := fun q hq =>
      Function.update_of_ne (fun h : q = r => hr (h ▸ hq)) _ _
    have hs' : ∀ q ∈ rs, s' q = s q := fun q hq =>
      Function.update_of_ne (fun h : q = r => hr (h ▸ hq)) _ _
    have hbr : b' r = i := Function.update_self _ _ _
    have hsr : s' r = x := Function.update_self _ _ _
    have hcons := Knapsack.cons r rs j y (by rw [hbr, hsr]; exact hx) (h.congr hb' hs')
      (by rw [hbr, hsr, hxy, hij]; exact hz)
    rw [hbr, hsr, hxy, hij] at hcons
    exact ⟨b', s', hcons⟩

/-- Two values of the same row of an array satisfying the recurrence are equal. -/
theorem row_eq {t : PhyloTree} {w : Pair → ℕ} {M : Address → ℕ → Finset ℕ}
    (hM : Array t w M) {v : Address} (hv : v ∈ t.nodes) {k x y : ℕ}
    (hx : x ∈ M v k) (hy : y ∈ M v k) : x = y :=
  Finset.card_le_one.mp (array_row_card t w M hM hv k) x hx y hy

/-- If some feasible family of `k` edges below the root has value `z` and no such family has a
larger value, the root row `M[r][k]` is `{z}`. -/
theorem root_row_eq_singleton {t : PhyloTree} {w : Pair → ℕ} {M : Address → ℕ → Finset ℕ}
    (hM : Array t w M) {k z : ℕ} {E : Finset Pair} (hE : FeasibleBelow t [] E)
    (hEk : E.card = k) (hEz : value w E = z)
    (hbound : ∀ F, FeasibleBelow t [] F → F.card = k → value w F ≤ z) : M [] k = {z} := by
  obtain ⟨x, hx⟩ := (row_nonempty_iff t w M hM t.root_mem_nodes k).mpr ⟨E, hE, hEk⟩
  obtain ⟨E', hE', hE'k, hE'x, hmax⟩ := exact_optimal t w M hM t.root_mem_nodes hx
  have hxz : x = z := le_antisymm (hE'x ▸ hbound E' hE' hE'k) (hEz ▸ hmax E hE hEk)
  subst hxz
  exact Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hx, fun y hy => row_eq hM t.root_mem_nodes hy hx⟩

/-- Section 2.4, parts (a) and (b) of the proof of Theorem 1 for the budget array. If `M` satisfies
the recurrence (`BudgetDP.Array`) and `E` is a backtracking trace from `v` with budget `k`, then `E`
is feasible below `v` (its cycles are disjoint and its targets lie in `T_v`), has exactly `k` edges,
and its value is in `M[v][k]`. -/
theorem trace_sound (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (hM : Array t w M) {v : Address} {k : ℕ} {E : Finset Pair}
    (hv : v ∈ t.nodes) (trace : Trace t w M v k E) :
    FeasibleBelow t v E ∧ E.card = k ∧ value w E ∈ M v k := by
  -- Induction on the trace.
  induction trace with
  | leaf v a node =>
    -- A leaf: the empty family, and `M[v][0] = {0}`.
    refine ⟨feasible_empty t v, rfl, ?_⟩
    rw [hM v hv 0]
    apply mem_best.mpr
    simp [cases, node, value]
  | fork v l r i j x y L R node left right leftRow rightRow chosen ihl ihr =>
    -- No edge with target `v`: the families of the two children lie in disjoint subtrees, and
    -- their values are the values `x` and `y` kept in their rows.
    have hl := PhyloTree.child_mem_nodes node false
    have hr := PhyloTree.child_mem_nodes node true
    obtain ⟨hL, hLc, hLv⟩ := ihl hl
    obtain ⟨hR, hRc, hRv⟩ := ihr hr
    refine ⟨fork_feasible hL hR, ?_, ?_⟩
    · rw [Finset.card_union_of_disjoint (fork_disjoint hL hR), hLc, hRc]
    · rw [value, Finset.sum_union (fork_disjoint hL hR)]
      change value w L + value w R ∈ M v (i + j)
      rw [row_eq hM hl hLv leftRow, row_eq hM hr hRv rightRow]
      exact chosen
  | gall v e k z b s F edge knapsack branches chosen ih =>
    -- An edge `e` with target `v`: the families below the subtrees hanging off its cycle avoid
    -- the cycle and each other, and their budgets and values are those chosen in the knapsack.
    obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp edge
    have he := (Finset.mem_filter.mp hc).2
    have hsub : ∀ r ∈ hanging t e,
        FeasibleBelow t r (F r) ∧ (F r).card = b r ∧ value w (F r) ∈ M r (b r) :=
      fun r hr => ih r hr (Finset.mem_filter.mp hr).1
    have hF : ∀ r ∈ hanging t e, FeasibleBelow t r (F r) := fun r hr => (hsub r hr).1
    have hbudget : k = ∑ r ∈ hanging t e, b r := by
      rw [knapsack.budget_eq, Finset.sum_map_toList]
    have hvalue : z = ∑ r ∈ hanging t e, s r := by
      rw [knapsack.value_eq, Finset.sum_map_toList]
    refine ⟨htarget ▸ gall_feasible he F hF, ?_, ?_⟩
    · -- `1 + Σ_r |F r| = 1 + Σ_r b r = k + 1` edges
      have hcard : ∑ r ∈ hanging t e, (F r).card = ∑ r ∈ hanging t e, b r :=
        Finset.sum_congr rfl (fun r hr => (hsub r hr).2.1)
      rw [card_gall he F hF, hcard, ← hbudget]
      omega
    · -- value `w e + Σ_r value (F r) = w e + Σ_r s r = w e + z`
      rw [value_gall he w F hF]
      have hs : ∀ r ∈ hanging t e, value w (F r) = s r := fun r hr =>
        row_eq hM (Finset.mem_filter.mp hr).1 (hsub r hr).2.2
          (knapsack.row_mem r (Finset.mem_toList.mpr hr))
      rw [Finset.sum_congr rfl hs, ← hvalue]
      exact chosen

/-- Section 2.4, backtracking: if `M` satisfies the recurrence and the row `M[v][k]` is nonempty,
there is a backtracking trace from `v` with budget `k`. The value kept in the row comes from one of
the two cases of the recurrence (`BudgetDP.cases`); follow it, and in the second case backtrack
through the knapsack (`BudgetDP.exists_knapsack`). -/
theorem exists_trace (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (hM : Array t w M) {v : Address} (hv : v ∈ t.nodes) {k : ℕ} (hk : (M v k).Nonempty) :
    ∃ E, Trace t w M v k E := by
  classical
  -- Strong induction on `remainingDepth t v`, which decreases from `v` to its proper descendants.
  generalize hn : remainingDepth t v = n
  induction n using Nat.strong_induction_on generalizing v k with
  | h n ih =>
    obtain ⟨z, hz⟩ := hk
    have hzc := (mem_best.mp ((hM v hv k) ▸ hz)).1
    obtain ⟨sub, hnode⟩ := (PhyloTree.mem_nodes_iff _ _).mp hv
    cases sub with
    | leaf a =>
      -- A leaf: only the budget `0` has a value.
      simp only [cases, hnode] at hzc
      split_ifs at hzc with hk0
      · subst hk0
        exact ⟨∅, Trace.leaf v a hnode⟩
      · exact (Finset.notMem_empty _ hzc).elim
    | fork l r =>
      have hsub (q : Address) (hq : q ∈ t.nodes) (hvq : v <+: q) (hne : v ≠ q) {i : ℕ}
          (hi : (M q i).Nonempty) : ∃ F, Trace t w M q i F :=
        ih (remainingDepth t q) (hn ▸ remainingDepth_lt hq hvq hne) hq hi rfl
      have hchild (c : Bool) {i : ℕ} (hi : (M (v ++ [c]) i).Nonempty) :
          ∃ F, Trace t w M (v ++ [c]) i F :=
        hsub _ (PhyloTree.child_mem_nodes hnode c) (List.prefix_append _ _) (by simp) hi
      simp only [cases, hnode] at hzc
      rcases Finset.mem_union.mp hzc with hfork | hgall
      · -- The budget is split between the two children.
        obtain ⟨i, j, x, y, hij, hx, hy, hxy⟩ := mem_convolution.mp hfork
        obtain ⟨L, hL⟩ := hchild false ⟨x, hx⟩
        obtain ⟨R, hR⟩ := hchild true ⟨y, hy⟩
        subst hij
        exact ⟨L ∪ R, Trace.fork v l r i j x y L R hnode hL hR hx hy (hxy ▸ hz)⟩
      · -- An edge `e ∈ Pairs(v)` is added; backtrack through the knapsack of its hanging
        -- subtrees.
        split_ifs at hgall with hk0
        · exact (Finset.notMem_empty _ hgall).elim
        · obtain ⟨e, he, hz'⟩ := Finset.mem_biUnion.mp hgall
          obtain ⟨c, hc, hcz⟩ := Finset.mem_image.mp hz'
          obtain ⟨hec, het⟩ := Finset.mem_filter.mp he
          have hae := (Finset.mem_filter.mp hec).2
          obtain ⟨b, s, hks⟩ := exists_knapsack (Finset.nodup_toList _) hc
          have hbranches : ∀ q ∈ hanging t e, ∃ F, Trace t w M q (b q) F := by
            intro q hq
            have hgeo := frontier_below (EdgeAbove.footprint_region t e hae) hq
            exact hsub q (Finset.mem_filter.mp hq).1 (het ▸ hgeo.1) (het ▸ hgeo.2)
              ⟨s q, hks.row_mem q (Finset.mem_toList.mpr hq)⟩
          let F := fun q => if h : q ∈ hanging t e then Classical.choose (hbranches q h) else ∅
          have hF : ∀ q ∈ hanging t e, Trace t w M q (b q) (F q) := by
            intro q hq
            simpa only [F, dite_eq_left hq] using Classical.choose_spec (hbranches q hq)
          have hk1 : k - 1 + 1 = k := by omega
          have htrace := Trace.gall v e (k - 1) c b s F he hks hF (by rw [hk1, hcz]; exact hz)
          rw [hk1] at htrace
          exact ⟨_, htrace⟩

/-- Section 2.4, the network of a trace. Let `M` satisfy the recurrence with the weights `s_e` of
Equation (1), and let `E` be a backtracking trace of `M` from the root with budget `k`. Then the
network `Realization.graph t E`:
* is built on `T`, with the root of `T` at its root;
* has exactly `k` reticulations;
* satisfies the value of `M[r][k]` quartets of `Q`, counted with multiplicity;
* satisfies at least as many quartets of `Q` as every network built on `T` with exactly `k`
  reticulations;
* displays at least as many quartets of `Q` as every network built on `T` with exactly `k`
  reticulations. -/
theorem trace_graph_optimal (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (M : Address → ℕ → Finset ℕ) (hM : Array t (edgeWeight t Q) M)
    {k : ℕ} {E : Finset Pair} (trace : Trace t (edgeWeight t Q) M [] k E) :
    (Realization.graph t E).AnchoredExtension t ∧
      (Realization.graph t E).reticulationCount = k ∧
      score Q (novel t Q (Realization.graph t E)) ∈ M [] k ∧
      (∀ N : RootedNetwork, N.AnchoredExtension t → N.reticulationCount = k →
        score Q (novel t Q N) ≤ score Q (novel t Q (Realization.graph t E))) ∧
      (∀ N : RootedNetwork, N.AnchoredExtension t → N.reticulationCount = k →
        score Q (repertoire Q N) ≤ score Q (repertoire Q (Realization.graph t E))) := by
  classical
  -- (a), (b): the trace is a feasible family of `k` edges whose value is kept in `M[r][k]`
  obtain ⟨hE, hEk, hEv⟩ := trace_sound t (edgeWeight t Q) M hM t.root_mem_nodes trace
  -- by Lemma 1, its network satisfies as many quartets as its value
  have hscore := novel_score_value t ht Q E hE.1
  -- (c): no network built on `T` with exactly `k` reticulations satisfies more
  obtain ⟨_, _, _, _, hupper, _⟩ := exact_graph_optimal t ht Q M hM hEv
  have hnovel : ∀ N : RootedNetwork, N.AnchoredExtension t → N.reticulationCount = k →
      score Q (novel t Q N) ≤ score Q (novel t Q (Realization.graph t E)) :=
    fun N hN hNk => (hupper N hN hNk).trans_eq hscore.symm
  refine ⟨⟨Realization.levelOne t ht E hE.1,
      ⟨Realization.supportEdges t E, ⟨Realization.support t ht E hE.1⟩⟩⟩,
    (Realization.reticulationCount_eq_card t E hE.1).trans hEk, by rw [hscore]; exact hEv,
    hnovel, ?_⟩
  -- the quartets displayed are those of `T` and those satisfied, and every network built on `T`
  -- displays the quartets of `T`
  intro N hN hNk
  obtain ⟨S, ⟨H⟩⟩ := hN.2
  have hF := H.extracted_separated hN.1
  have hNF := Realization.levelOne t ht H.extracted hF
  obtain ⟨i⟩ := H.canonical_iso hN.1
  have hbaseN : repertoire Q (Realization.graph t ∅) ⊆ repertoire Q N := by
    rw [repertoire_iso Q hN.1 hNF i]
    exact baseline_subset t ht Q H.extracted hF
  rw [score_offset Q _ _ hbaseN, score_offset Q _ _ (baseline_subset t ht Q E hE.1)]
  exact Nat.add_le_add_left (hnovel N hN hNk) _

/-- The non-tree edges of the network obtained from `T` by adding an edge above each pair of a
family `E` of admissible pairs, that is, its edges outside the subdivided tree `T`, are the added
edges: there are `|E|` of them. -/
theorem graph_nonTree_card (t : PhyloTree) {E : Finset Pair}
    (hE : E ⊆ EdgeAbove.candidates t) :
    ((Realization.graph t E).edges \ Realization.supportEdges t E).card = E.card := by
  rw [Realization.nonSupportEdges t E hE]
  apply Finset.card_image_of_injOn
  intro e he f hf h
  exact Realization.donor_injective t (hE he) (hE hf) (Prod.mk.inj h).1

/-- The pair `(x ++ [false], x ++ [true])` of the two children of an internal vertex `x`: the edge
added above it forms a triangle, whose only vertex of `T` is `x`. -/
def triangle (x : Address) : Pair := (x ++ [false], x ++ [true])

/-- For an internal vertex `x` of `T`, the pair of its two children is admissible, and its cycle
meets `T` only in `x`. -/
theorem triangle_admissible_footprint {t : PhyloTree} {x : Address}
    (hx : x ∈ t.internalNodes) :
    EdgeAbove.Admissible t (triangle x) ∧ EdgeAbove.footprint t (triangle x) = {x} := by
  obtain ⟨l, r, hnode⟩ := (t.mem_internalNodes_iff x).mp hx
  have htarget : EdgeAbove.target (triangle x) = x := by
    simpa [triangle, EdgeAbove.target, lca] using lca_append x [false] [true]
  refine ⟨⟨PhyloTree.child_mem_nodes hnode false, PhyloTree.child_mem_nodes hnode true,
    by simp [triangle], by simp [triangle], ?_⟩, ?_⟩
  · intro h
    have := h.eq_of_length_le (by simp [triangle])
    simp [triangle] at this
  · ext y
    simp only [EdgeAbove.footprint, htarget, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hxy, hy⟩
      obtain ⟨c, rfl⟩ := hxy
      have hc : ∀ b : Bool, x ++ c <+: x ++ [b] → x ++ c ≠ x ++ [b] → c = [] := by
        intro b h hne
        have h' := (List.prefix_append_right_inj x).mp h
        rcases c with _ | ⟨d, c⟩
        · rfl
        · obtain ⟨rfl, hc⟩ := List.cons_prefix_cons.mp h'
          rw [List.prefix_nil.mp hc] at hne
          exact (hne rfl).elim
      rcases hy with ⟨h, hne⟩ | ⟨h, hne⟩
      · simp [hc false h hne]
      · simp [hc true h hne]
    · rintro rfl
      refine ⟨t.nodes_prefix_closed (PhyloTree.child_mem_nodes hnode false)
        (List.prefix_append _ _), List.prefix_refl _,
        Or.inl ⟨List.prefix_append _ _, by simp [triangle]⟩⟩

/-- Section 2.4: "a level-1 phylogenetic network on n leaves will not have more than n−1
reticulations", and every number up to `n − 1` is possible. If `M` satisfies the recurrence, the
row `M[r][k]` at the root is nonempty iff `k ≤ n − 1`: for `k ≤ n − 1`, add a triangle at `k`
distinct internal vertices of `T`. -/
theorem root_row_nonempty_iff_le (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (hM : Array t w M) (k : ℕ) : (M [] k).Nonempty ↔ k ≤ t.labels.length - 1 := by
  classical
  constructor
  · intro h
    by_contra hk
    rw [high_budget_empty t w M hM t.root_mem_nodes (by omega)] at h
    exact Finset.not_nonempty_empty h
  · intro hk
    rw [row_nonempty_iff t w M hM t.root_mem_nodes k]
    -- choose `k` internal vertices and add a triangle at each
    have hcount := PhyloTree.internalNodes_count t
    obtain ⟨X, hX, hXk⟩ := Finset.exists_subset_card_eq (s := t.internalNodes) (n := k)
      (by omega)
    have htri x (hx : x ∈ X) := triangle_admissible_footprint (hX hx)
    have hinj : Set.InjOn triangle X := by
      intro x _ y _ h
      simpa [triangle] using congrArg Prod.fst h
    refine ⟨X.image triangle, ⟨⟨?_, ?_⟩, fun _ _ => List.nil_prefix⟩, ?_⟩
    · intro e he
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨(htri x hx).1.1, (htri x hx).1.2.1⟩, (htri x hx).1⟩
    · intro e he f hf hne
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hf
      rw [(htri x hx).2, (htri y hy).2, Finset.disjoint_singleton]
      intro hxy
      exact hne (congrArg triangle hxy)
    · rw [Finset.card_image_of_injOn hinj, hXk]

/-- Backtracking chooses a trace for every nonempty row at the root: there is a family `E k` for
each budget `k` such that `E k` is a backtracking trace from the root with budget `k` whenever
`M[r][k]` is nonempty. -/
theorem exists_traces (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (hM : Array t w M) :
    ∃ E : ℕ → Finset Pair, ∀ k, (M [] k).Nonempty → Trace t w M [] k (E k) := by
  classical
  have h k (hk : (M [] k).Nonempty) := exists_trace t w M hM t.root_mem_nodes hk
  refine ⟨fun k => if hk : (M [] k).Nonempty then Classical.choose (h k hk) else ∅, ?_⟩
  intro k hk
  simpa only [dite_eq_left hk] using Classical.choose_spec (h k hk)

/-- Section 2.4: the networks `N_1, …, N_m` returned by the modified dynamic program. Let `M`
satisfy the recurrence with the weights `s_e` of Equation (1), let `m` be a number of
reticulations, and let `E k` be a backtracking trace from the root with budget `k`, for each
`k ≤ m` whose root row is nonempty (`BudgetDP.exists_traces`; the rows of `k ≤ n − 1` are all
nonempty, `BudgetDP.root_row_nonempty_iff_le`). Then for every such `k`, the network
`N_k = Realization.graph t (E k)`:
* is level-1;
* contains the constraint tree `T`: it is built on `T`, with the root of `T` at its root;
* contains exactly `k` non-tree edges (edges outside the subdivided tree `T`), and has exactly `k`
  reticulations;
* maximizes the number of quartets of `Q` it contains (displays, counted with multiplicity) subject
  to these constraints: no network built on `T` with exactly `k` reticulations displays more.
The paper lists `N_1, …, N_m`; the statement also covers `k = 0`, where `N_0` is `T`. -/
theorem backtracking_networks (t : PhyloTree) (ht : t.WellLabelled) (Q : Multiset Quartet)
    (M : Address → ℕ → Finset ℕ) (hM : Array t (edgeWeight t Q) M) (m : ℕ)
    (E : ℕ → Finset Pair)
    (traces : ∀ k ≤ m, (M [] k).Nonempty → Trace t (edgeWeight t Q) M [] k (E k))
    {k : ℕ} (hk : k ≤ m) (hrow : (M [] k).Nonempty) :
    (Realization.graph t (E k)).RootedBinaryLevelOne ∧
      (Realization.graph t (E k)).AnchoredExtension t ∧
      ((Realization.graph t (E k)).edges \ Realization.supportEdges t (E k)).card = k ∧
      (Realization.graph t (E k)).reticulationCount = k ∧
      ∀ N : RootedNetwork, N.AnchoredExtension t → N.reticulationCount = k →
        score Q (repertoire Q N) ≤ score Q (repertoire Q (Realization.graph t (E k))) := by
  have trace := traces k hk hrow
  obtain ⟨hE, hEk, _⟩ := trace_sound t (edgeWeight t Q) M hM t.root_mem_nodes trace
  obtain ⟨hN, hret, _, _, hopt⟩ := trace_graph_optimal t ht Q M hM trace
  exact ⟨hN.1, hN, (graph_nonTree_card t hE.1.1).trans hEk, hret, hopt⟩

end Camus.BudgetDP
