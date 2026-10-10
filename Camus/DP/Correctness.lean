module

public import Camus.DP.Frontier
public import Camus.Network.Realization.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Equations (4)–(5) and the correctness of the recurrence

This file proves Theorem 1 for arbitrary nonnegative edge weights. Let `M` satisfy the recurrence
of Section 2.2 (`DynamicProgramming.Array`: Equation (2) with the base case `M[v] = 0` at a leaf,
`s(v)` given by Equation (3), and `s_dp` by Equations (4)–(5)). A backtracking trace from a vertex
`v` (`DynamicProgramming.Trace`) is then a family of pairs feasible below `v` whose total weight is
`M[v]`, and no family feasible below `v` has larger total weight. `theorem1`
(`Camus/DP/Theorem1.lean`) applies this to the weights `s_e` of Equation (1) and turns total weight
into the number of satisfied quartets by Lemma 1.

## Main results

* `DynamicProgramming.equation4`, `DynamicProgramming.equation5`: Equations (4) and (5), the two
  cases of `DynamicProgramming.sdp`.
* `DynamicProgramming.hanging_score`: both equations sum `M` over the roots of the subtrees hanging
  off `γ(u, w)`.
* `DynamicProgramming.trace_correct`: a trace from `v` is feasible below `v` and has total weight
  `M[v]`.
* `DynamicProgramming.array_upper`: every family feasible below `v` has total weight at most `M[v]`.
* `DynamicProgramming.trace_optimal`: the two together.
* `DynamicProgramming.exists_array_trace`: the recurrence has a solution, with a trace from the
  root.

## Proof (the paper's)

The paper's proof of Theorem 1 has three steps. Here they are carried out for edge weights; the
value of a family is the sum of its weights (`DynamicProgramming.value`).

(a) The output is a level-1 network extending `T`: targets not in relation give vertex-disjoint
cycles, and when one target is above another, Equations (4)–(5) keep the cycles disjoint. This is
the feasibility part of `DynamicProgramming.trace_correct`, by induction on the trace. When `M[v]`
is `M[l(v)] + M[r(v)]`, the two families lie below the two children of `v`
(`DynamicProgramming.fork_feasible`). When it is `s_e + s_dp(v, u, w)` for an edge `e` with target
`v`, the other edges lie below the roots of the subtrees hanging off `γ(e)`, and their cycles avoid
`γ(e)` (`DynamicProgramming.gall_feasible`).

(b) `M[root]` counts the quartets satisfied by the output. Here the total weight of a trace from `v`
is `M[v]` (`DynamicProgramming.trace_correct`, by `DynamicProgramming.value_gall` and
`DynamicProgramming.hanging_score`).

(c) Optimality: `DynamicProgramming.array_upper`, by strong induction over subtrees. The formal
induction is on `DynamicProgramming.remainingDepth t v`, the height of `T` minus the depth of `v`,
which decreases from `v` to each proper descendant; the paper inducts on the number of leaves below
`v`. Let `F` be feasible below `v`.
* If `v` is a leaf, `F` is empty (`DynamicProgramming.feasible_leaf_empty`) and `M[v] = 0`.
* If no edge of `F` has target `v`, then `F` splits into the families below the two children of `v`
  (`DynamicProgramming.fork_partition`, `DynamicProgramming.restrict_feasible`); by induction its
  value is at most `M[l(v)] + M[r(v)]`.
* If an edge `e = (u, w)` of `F` has target `v`, it is the only one, by Lemma 2, and the other edges
  have targets in the subtrees hanging off `γ(e)` (`DynamicProgramming.gall_partition`,
  `DynamicProgramming.competitor_in_hanging`). By induction on each hanging subtree, the value of
  `F` is at most `s_e + Σ_r M[r]` over the hanging roots `r`, which is `s_e + s_dp(v, u, w)`
  (`DynamicProgramming.hanging_score`), at most `s(v)` (Equation (3)).

In each case the bound is at most `M[v]` (Equation (2)). The paper also invokes Lemma 1 here, so
that no quartet is counted twice. For weights, the value is additive by definition; Lemma 1 enters
in `theorem1`, which identifies the number of quartets satisfied by a network with the value of its
family (`DynamicProgramming.novel_score_value`).
-/

@[expose] public section

namespace Camus.DynamicProgramming

/-- **Equation (4)** (`E4`). For a pair `e = (u, w)` with target `v = lca(u, w)` and `u ≠ v`:
`s_dp(v, u, w) = M[w] + M[u] + Σ_x M[c(x)]`, the sum over the vertices `x ≠ v` of `T` on the cycle
`γ(u, w)` (`EdgeAbove.footprint t e` minus the target). Here `c(x) = Realization.offChild t e x` is
`l(x)` if `l(x) ∉ γ(u, w)` and `r(x)` otherwise, with the children of `x` taken in `T + e`
(Definition 5). -/
theorem equation4 (t : PhyloTree) (M : Address → ℕ) (e : Pair)
    (hcross : EdgeAbove.target e ≠ e.1) :
    sdp t M e = M e.2 + M e.1 +
      ∑ x ∈ (EdgeAbove.footprint t e).erase (EdgeAbove.target e),
        M (Realization.offChild t e x) := by
  simp only [sdp, hcross, ↓reduceIte, sdpCross]

/-- **Equation (5)** (`E5`). For a pair `e = (u, w)` whose donor is its target, `u = v = lca(u, w)`
(a ghost lineage): `s_dp(v, u, w) = M[w] + Σ_x M[c(x)]`, the sum over all vertices `x` of `T` on
`γ(u, w)`, `v` included, with `c(x)` the child of `x` off the cycle as in Equation (4). -/
theorem equation5 (t : PhyloTree) (M : Address → ℕ) (e : Pair)
    (hghost : EdgeAbove.target e = e.1) :
    sdp t M e = M e.2 + ∑ x ∈ EdgeAbove.footprint t e,
      M (Realization.offChild t e x) := by
  simp only [sdp, hghost, ↓reduceIte, sdpGhost]



/-- For an admissible pair `e = (u, w)`, Equations (4) and (5) both give
`s_dp(v, u, w) = Σ_r M[r]`, the sum over the roots `r` of the subtrees of `T` hanging off `γ(u, w)`
(`hanging t e`): "Equations 4 and 5 sum the subproblem scores for all the subnetworks hanging off of
γ(u,w)" (Section 2.2, after Equation (5)). The hanging roots are listed by
`EdgeAbove.frontier_cross` (Equation (4)) and `EdgeAbove.frontier_ghost` (Equation (5)). -/
theorem hanging_score (t : PhyloTree) (M : Address → ℕ) (e : Pair)
    (he : EdgeAbove.Admissible t e) :
    sdp t M e = ∑ r ∈ hanging t e, M r := by
  classical
  have hends := EdgeAbove.endpoint_not_off_image he
  have hsum : (∑ r ∈ (EdgeAbove.branchVertices t e).image (Realization.offChild t e), M r) =
      ∑ p ∈ EdgeAbove.branchVertices t e, M (Realization.offChild t e p) := by
    exact Finset.sum_image (EdgeAbove.offChild_injective he)
  by_cases hghost : EdgeAbove.target e = e.1
  · rw [equation5 t M e hghost, EdgeAbove.frontier_ghost he hghost,
      Finset.sum_insert hends.2, hsum]
    simp [EdgeAbove.branchVertices, hghost]
  · have hw : e.2 ∉ insert e.1
        ((EdgeAbove.branchVertices t e).image (Realization.offChild t e)) := by
      simpa only [Finset.mem_insert, not_or] using ⟨EdgeAbove.endpoints_distinct he, hends.2⟩
    rw [equation4 t M e hghost, EdgeAbove.frontier_cross he hghost,
      Finset.sum_insert hw, Finset.sum_insert hends.1, hsum]
    simp only [EdgeAbove.branchVertices, hghost, ↓reduceIte]
    omega

/-- Parts (a) and (b) of the proof of Theorem 1, for edge weights. If `M` satisfies the recurrence
(`Array`) and `E` is a backtracking trace from `v` (`Trace`), then `E` is feasible below `v` (its
cycles are disjoint and its targets lie in `T_v`) and its total weight is `M[v]`. -/
theorem trace_correct (t : PhyloTree) (weight : Pair → ℕ) (M : Address → ℕ)
    (hM : Array t weight M) {v : Address} {E : Finset Pair}
    (hv : v ∈ t.nodes) (trace : Trace t weight M v E) :
    FeasibleBelow t v E ∧ value weight E = M v := by
  -- Induction on the trace.
  induction trace with
  | leaf v a node =>
    -- A leaf: the empty family, and `M[v] = 0`.
    refine ⟨feasible_empty _ _, ?_⟩
    have hzero := hM v hv
    rw [node] at hzero
    simpa [value] using hzero.symm
  | fork v l r L R node left right chosen ihl ihr =>
    -- `M[v] = M[l(v)] + M[r(v)]`: the targets of the two families are not in relation, so their
    -- cycles are disjoint, and the values add up.
    have hL := ihl (PhyloTree.child_mem_nodes node false)
    have hR := ihr (PhyloTree.child_mem_nodes node true)
    refine ⟨fork_feasible hL.1 hR.1, ?_⟩
    rw [value, Finset.sum_union (fork_disjoint hL.1 hR.1)]
    exact (congrArg₂ (· + ·) hL.2 hR.2).trans chosen
  | gall v e F edge branches chosen ih =>
    -- `M[v] = s_e + s_dp(v, u, w)` for an edge `e` with target `v`, and traces below the roots of
    -- the subtrees hanging off `γ(e)`: their cycles avoid `γ(e)` (Equations (4)–(5)).
    obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp edge
    have he := (Finset.mem_filter.mp hc).2
    have hF : ∀ r ∈ hanging t e, FeasibleBelow t r (F r) := by
      intro r hr
      exact (ih r hr (Finset.mem_filter.mp hr).1).1
    refine ⟨htarget ▸ gall_feasible he F hF, ?_⟩
    -- The value is `s_e + Σ_r M[r] = s_e + s_dp(v, u, w) = M[v]`.
    rw [value_gall he weight F hF]
    have heq : (∑ r ∈ hanging t e, value weight (F r)) = ∑ r ∈ hanging t e, M r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (ih r hr (Finset.mem_filter.mp hr).1).2
    rw [heq, ← hanging_score t M e he]
    exact chosen

/-- Part (c) of the proof of Theorem 1, for edge weights. If `M` satisfies the recurrence
(`Array`), every family `F` feasible below `v` (cycles disjoint, targets in `T_v`) has total weight
at most `M[v]`. The proof is the paper's strong induction over subtrees. -/
theorem array_upper (t : PhyloTree) (weight : Pair → ℕ) (M : Address → ℕ)
    (hM : Array t weight M) {v : Address} (hv : v ∈ t.nodes)
    (F : Finset Pair) (hF : FeasibleBelow t v F) : value weight F ≤ M v := by
  -- Strong induction on `remainingDepth t v`, which decreases from `v` to its proper descendants.
  generalize hn : remainingDepth t v = n
  induction n using Nat.strong_induction_on generalizing v F with
  | h n ih =>
    obtain ⟨subtree, hnode⟩ := (PhyloTree.mem_nodes_iff _ _).mp hv
    have hrec := hM v hv
    rw [hnode] at hrec
    cases subtree with
    | leaf a =>
      -- Base case: below a leaf the only feasible family is empty.
      rw [feasible_leaf_empty hnode hF, value]
      simp
    | fork l r =>
      change M v = max (M (v ++ [false]) + M (v ++ [true])) (s t weight M v) at hrec
      by_cases hroot : ∃ e ∈ F, EdgeAbove.target e = v
      -- Case 2: an edge `e = (u, w)` of `F` has target `v`.
      · obtain ⟨e, he, htarget⟩ := hroot
        have hae := (Finset.mem_filter.mp (hF.1.1 he)).2
        -- The other edges, restricted below each root `r` of a subtree hanging off `γ(e)`.
        let branches := fun r => restrictBelow r (F.erase e)
        have hbranch : ∀ r ∈ hanging t e, FeasibleBelow t r (branches r) := by
          intro r hr
          exact restrict_feasible (feasible_subset hF (Finset.erase_subset _ _))
        -- Induction hypothesis on each hanging subtree, a proper subtree of `T_v`.
        have hupper : ∀ r ∈ hanging t e, value weight (branches r) ≤ M r := by
          intro r hr
          have hgeo := frontier_below (EdgeAbove.footprint_region t e hae) hr
          have hrv := htarget ▸ hgeo
          have hrnode := (Finset.mem_filter.mp hr).1
          apply ih (remainingDepth t r)
            (hn ▸ remainingDepth_lt hrnode hrv.1 hrv.2) hrnode (branches r)
            (hbranch r hr) rfl
        -- By Lemma 2, `e` is the only edge with target `v`, and every other edge has its target
        -- in a subtree hanging off `γ(e)`.
        have hpart := gall_partition hF he htarget
        -- So the value of `F` is at most `s_e + Σ_r M[r] = s_e + s_dp(v, u, w)`
        -- (Equations (4)–(5)).
        have hval : value weight F ≤ weight e + sdp t M e := by
          rw [hpart, value_gall hae weight branches hbranch, hanging_score t M e hae]
          exact Nat.add_le_add_left (Finset.sum_le_sum hupper) _
        -- `e ∈ Pairs(v)`, so this is at most `s(v)` (Equation (3)), hence at most `M[v]`.
        have hpair : e ∈ pairsAt t v := Finset.mem_filter.mpr ⟨hF.1.1 he, htarget⟩
        have hsup : weight e + sdp t M e ≤ s t weight M v := by
          unfold s
          exact Finset.le_sup (f := fun f : Pair => weight f + sdp t M f) hpair
        rw [hrec]
        exact hval.trans (hsup.trans (le_max_right _ _))
      -- Case 1: no edge of `F` has target `v`.
      · have hnoroot : ∀ e ∈ F, EdgeAbove.target e ≠ v := by
          intro e he heq
          exact hroot ⟨e, he, heq⟩
        have hL := restrict_feasible (r := v ++ [false]) hF
        have hR := restrict_feasible (r := v ++ [true]) hF
        -- Induction hypothesis on the two children.
        have upperChild (b : Bool) :
            value weight (restrictBelow (v ++ [b]) F) ≤ M (v ++ [b]) := by
          have hchild := PhyloTree.child_mem_nodes hnode b
          have hlt := remainingDepth_lt hchild (List.prefix_append _ _) (by simp)
          apply ih (remainingDepth t (v ++ [b])) (hn ▸ hlt) hchild
            (restrictBelow (v ++ [b]) F) (restrict_feasible hF) rfl
        -- `F` splits into the families below the two children, so its value is at most
        -- `M[l(v)] + M[r(v)] ≤ M[v]` (Equation (2)).
        have hpart := fork_partition hF hnoroot
        have hval : value weight F ≤ M (v ++ [false]) + M (v ++ [true]) := by
          conv_lhs => rw [hpart]
          rw [value, Finset.sum_union (fork_disjoint hL hR)]
          exact Nat.add_le_add (upperChild false) (upperChild true)
        rw [hrec]
        exact hval.trans (le_max_left _ _)


/-- Theorem 1 for edge weights. If `M` satisfies the recurrence (`Array`), a backtracking trace `E`
from `v` is feasible below `v` and has total weight `M[v]`, and every family feasible below `v` has
total weight at most `M[v]`. -/
theorem trace_optimal (t : PhyloTree) (weight : Pair → ℕ) (M : Address → ℕ)
    (hM : Array t weight M) {v : Address} {E : Finset Pair}
    (hv : v ∈ t.nodes) (trace : Trace t weight M v E) :
    FeasibleBelow t v E ∧ value weight E = M v ∧
      ∀ F, FeasibleBelow t v F → value weight F ≤ M v := by
  exact ⟨(trace_correct t weight M hM hv trace).1,
    (trace_correct t weight M hM hv trace).2, fun F hF => array_upper t weight M hM hv F hF⟩

/-- The recurrence applied in rounds, starting from the zero array: `bottomUp t weight (n + 1) v`
is `0` at a leaf and `max (M[l(v)] + M[r(v)]) s(v)` at an internal vertex, computed from
`M = bottomUp t weight n`, with `s_dp` in the form of `hanging_score`. -/
noncomputable def bottomUp (t : PhyloTree) (weight : Pair → ℕ) : ℕ → Address → ℕ
  | 0, _ => 0
  | n + 1, v =>
    match t.nodeAt v with
    | some (.fork _ _) => max (bottomUp t weight n (v ++ [false]) +
        bottomUp t weight n (v ++ [true]))
        ((pairsAt t v).sup (fun e => weight e + ∑ r ∈ hanging t e, bottomUp t weight n r))
    | _ => 0

/-- The value of `bottomUp` at `v` is the same after any two numbers of rounds larger than
`remainingDepth t v`. -/
theorem bottomUp_stable (t : PhyloTree) (weight : Pair → ℕ) {v : Address}
    (hv : v ∈ t.nodes) {a b : ℕ} (ha : remainingDepth t v < a)
    (hb : remainingDepth t v < b) : bottomUp t weight a v = bottomUp t weight b v := by
  generalize hn : remainingDepth t v = n at ha hb
  induction n using Nat.strong_induction_on generalizing v a b with
  | h n ih =>
    cases a with
    | zero => omega
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        obtain ⟨sub, hnode⟩ := (PhyloTree.mem_nodes_iff _ _).mp hv
        cases sub with
        | leaf x => simp [bottomUp, hnode]
        | fork l r =>
          simp only [bottomUp, hnode]
          have hchild (c : Bool) :
              bottomUp t weight a (v ++ [c]) = bottomUp t weight b (v ++ [c]) := by
            have hmem := PhyloTree.child_mem_nodes hnode c
            have hlt := remainingDepth_lt hmem (List.prefix_append _ _) (by simp)
            apply ih (remainingDepth t (v ++ [c])) (hn ▸ hlt) hmem rfl
              (by omega) (by omega)
          rw [hchild false, hchild true]
          congr 1
          apply Finset.sup_congr rfl
          intro e he
          congr 1
          apply Finset.sum_congr rfl
          intro r hr
          obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp he
          have hae := (Finset.mem_filter.mp hc).2
          have hgeo := frontier_below (EdgeAbove.footprint_region t e hae) hr
          have hrv := htarget ▸ hgeo
          have hrnode := (Finset.mem_filter.mp hr).1
          have hlt := remainingDepth_lt hrnode hrv.1 hrv.2
          apply ih (remainingDepth t r) (hn ▸ hlt) hrnode rfl (by omega) (by omega)

/-- After `h + 1` rounds, where `h` is the height of `T`, `bottomUp` satisfies the recurrence
(`Array`). -/
theorem bottomUp_array (t : PhyloTree) (weight : Pair → ℕ) :
    Array t weight (bottomUp t weight (t.nodes.sup List.length + 1)) := by
  let d := t.nodes.sup List.length
  intro v hv
  obtain ⟨sub, hnode⟩ := (PhyloTree.mem_nodes_iff _ _).mp hv
  rw [hnode]
  cases sub with
  | leaf a => simp [bottomUp, hnode]
  | fork l r =>
    change bottomUp t weight (d + 1) v =
      max (bottomUp t weight (d + 1) (v ++ [false]) + bottomUp t weight (d + 1) (v ++ [true]))
        (s t weight (bottomUp t weight (d + 1)) v)
    simp only [bottomUp, hnode]
    have hchild (c : Bool) :
        bottomUp t weight d (v ++ [c]) = bottomUp t weight (d + 1) (v ++ [c]) := by
      have hmem := PhyloTree.child_mem_nodes hnode c
      apply bottomUp_stable t weight hmem
      · unfold remainingDepth
        have hle : (v ++ [c]).length ≤ d := Finset.le_sup hmem
        simp only [List.length_append, List.length_singleton] at hle ⊢
        omega
      · unfold remainingDepth
        omega
    rw [hchild false, hchild true]
    congr 1
    unfold s
    apply Finset.sup_congr rfl
    intro e he
    obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp he
    have hae := (Finset.mem_filter.mp hc).2
    change weight e + (∑ r ∈ hanging t e, bottomUp t weight d r) =
      weight e + sdp t (bottomUp t weight (d + 1)) e
    rw [hanging_score t (bottomUp t weight (d + 1)) e hae]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    have hgeo := frontier_below (EdgeAbove.footprint_region t e hae) hr
    have hrv := htarget ▸ hgeo
    have hrnode := (Finset.mem_filter.mp hr).1
    apply bottomUp_stable t weight hrnode
    · have hlt := remainingDepth_lt hrnode hrv.1 hrv.2
      have hle : remainingDepth t v ≤ d := Nat.sub_le _ _
      omega
    · unfold remainingDepth
      omega

/-- Backtracking: if `M` satisfies the recurrence, there is a trace from every vertex `v`. At an
internal vertex, follow a term attaining the maximum in Equation (2), and in the second case a pair
attaining the maximum in Equation (3). -/
theorem exists_trace (t : PhyloTree) (weight : Pair → ℕ) (M : Address → ℕ)
    (hM : Array t weight M) {v : Address} (hv : v ∈ t.nodes) :
    ∃ E, Trace t weight M v E := by
  classical
  generalize hn : remainingDepth t v = n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    obtain ⟨sub, hnode⟩ := (PhyloTree.mem_nodes_iff _ _).mp hv
    cases sub with
    | leaf a => exact ⟨∅, Trace.leaf v a hnode⟩
    | fork l r =>
      have hrec := hM v hv
      rw [hnode] at hrec
      change M v = max (M (v ++ [false]) + M (v ++ [true])) (s t weight M v) at hrec
      by_cases hchoice : s t weight M v ≤ M (v ++ [false]) + M (v ++ [true])
      · have child_trace (b : Bool) : ∃ F, Trace t weight M (v ++ [b]) F := by
          have hmem := PhyloTree.child_mem_nodes hnode b
          have hlt := remainingDepth_lt hmem (List.prefix_append _ _) (by simp)
          exact ih (remainingDepth t (v ++ [b])) (hn ▸ hlt) hmem rfl
        obtain ⟨L, hL⟩ := child_trace false
        obtain ⟨R, hR⟩ := child_trace true
        exact ⟨L ∪ R, Trace.fork v l r L R hnode hL hR
          (by rw [hrec, max_eq_left hchoice])⟩
      · have hnonempty : (pairsAt t v).Nonempty := by
          by_contra h
          have hempty := Finset.not_nonempty_iff_eq_empty.mp h
          have hz : s t weight M v = 0 := by simp [s, hempty]
          exact hchoice (by omega)
        obtain ⟨e, he, hsup⟩ := Finset.exists_mem_eq_sup (pairsAt t v) hnonempty
          (fun e => weight e + sdp t M e)
        obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp he
        have hae := (Finset.mem_filter.mp hc).2
        have hbranches : ∀ r ∈ hanging t e, ∃ F, Trace t weight M r F := by
          intro r hr
          have hgeo := frontier_below (EdgeAbove.footprint_region t e hae) hr
          have hrv := htarget ▸ hgeo
          have hmem := (Finset.mem_filter.mp hr).1
          exact ih (remainingDepth t r) (hn ▸ remainingDepth_lt hmem hrv.1 hrv.2) hmem rfl
        let F := fun r => if h : r ∈ hanging t e then Classical.choose (hbranches r h) else ∅
        have hF : ∀ r ∈ hanging t e, Trace t weight M r (F r) := by
          intro r hr
          simpa only [F, dite_eq_left hr] using Classical.choose_spec (hbranches r hr)
        have hchosen : weight e + sdp t M e = M v := by
          rw [hrec, max_eq_right (by omega)]
          exact hsup.symm
        exact ⟨insert e ((hanging t e).biUnion F), Trace.gall v e F he hF hchosen⟩

/-- For every weight function, the recurrence has a solution `M` with a backtracking trace from the
root, so the hypotheses of `theorem1` can be met. -/
theorem exists_array_trace (t : PhyloTree) (weight : Pair → ℕ) :
    ∃ M, Array t weight M ∧ ∃ E, Trace t weight M [] E := by
  exact ⟨_, bottomUp_array t weight,
    exists_trace t weight _ (bottomUp_array t weight) (PhyloTree.root_mem_nodes t)⟩


end Camus.DynamicProgramming
