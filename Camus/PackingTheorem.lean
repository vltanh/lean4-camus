module

public import Camus.CycleFrontier
public import Camus.GraphRealizationBasics
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace Camus.DynamicProgramming

/-- Equation (4): cross-branch cycle, with children interpreted in the actual
subdivided single-edge graph. The selected off-cycle child is an original node. -/
theorem equation4 (t : PhyloTree) (M : Address → ℕ) (e : Pair)
    (hcross : EdgeAbove.target e ≠ e.1) :
    sdp t M e = M e.2 + M e.1 +
      ∑ x ∈ (EdgeAbove.footprint t e).erase (EdgeAbove.target e),
        M (Realization.offChild t e x) := by
  simp only [sdp, hcross, ↓reduceIte, sdpCross]

/-- Equation (5): a ghost donor includes the target's off-cycle child in the
sum and omits the donor subtree, which contains the whole cycle. -/
theorem equation5 (t : PhyloTree) (M : Address → ℕ) (e : Pair)
    (hghost : EdgeAbove.target e = e.1) :
    sdp t M e = M e.2 + ∑ x ∈ EdgeAbove.footprint t e,
      M (Realization.offChild t e x) := by
  simp only [sdp, hghost, ↓reduceIte, sdpGhost]



/-- The forest partition converts the literal Equations 4–5 to the independent
hanging subproblems used in the induction. Both case formulas are used. -/
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

theorem trace_correct (t : PhyloTree) (weight : Pair → ℕ) (M : Address → ℕ)
    (hM : Array t weight M) {v : Address} {E : Finset Pair}
    (hv : v ∈ t.nodes) (trace : Trace t weight M v E) :
    FeasibleBelow t v E ∧ value weight E = M v := by
  induction trace with
  | leaf v a node =>
    refine ⟨feasible_empty _ _, ?_⟩
    have hzero := hM v hv
    rw [node] at hzero
    simpa [value] using hzero.symm
  | fork v l r L R node left right chosen ihl ihr =>
    have hL := ihl (PhyloTree.child_mem_nodes node false)
    have hR := ihr (PhyloTree.child_mem_nodes node true)
    refine ⟨fork_feasible hL.1 hR.1, ?_⟩
    rw [value, Finset.sum_union (fork_disjoint hL.1 hR.1)]
    exact (congrArg₂ (· + ·) hL.2 hR.2).trans chosen
  | gall v e F edge branches chosen ih =>
    obtain ⟨hc, htarget⟩ := Finset.mem_filter.mp edge
    have he := (Finset.mem_filter.mp hc).2
    have hF : ∀ r ∈ hanging t e, FeasibleBelow t r (F r) := by
      intro r hr
      exact (ih r hr (Finset.mem_filter.mp hr).1).1
    refine ⟨htarget ▸ gall_feasible he F hF, ?_⟩
    rw [value_gall he weight F hF]
    have heq : (∑ r ∈ hanging t e, value weight (F r)) = ∑ r ∈ hanging t e, M r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (ih r hr (Finset.mem_filter.mp hr).1).2
    rw [heq, ← hanging_score t M e he]
    exact chosen

theorem array_upper (t : PhyloTree) (weight : Pair → ℕ) (M : Address → ℕ)
    (hM : Array t weight M) {v : Address} (hv : v ∈ t.nodes)
    (F : Finset Pair) (hF : FeasibleBelow t v F) : value weight F ≤ M v := by
  generalize hn : remainingDepth t v = n
  induction n using Nat.strong_induction_on generalizing v F with
  | h n ih =>
    obtain ⟨subtree, hnode⟩ := (PhyloTree.mem_nodes_iff _ _).mp hv
    have hrec := hM v hv
    rw [hnode] at hrec
    cases subtree with
    | leaf a =>
      rw [feasible_leaf_empty hnode hF, value]
      simp
    | fork l r =>
      change M v = max (M (v ++ [false]) + M (v ++ [true])) (s t weight M v) at hrec
      by_cases hroot : ∃ e ∈ F, EdgeAbove.target e = v
      · obtain ⟨e, he, htarget⟩ := hroot
        have hae := (Finset.mem_filter.mp (hF.1.1 he)).2
        let branches := fun r => restrictBelow r (F.erase e)
        have hbranch : ∀ r ∈ hanging t e, FeasibleBelow t r (branches r) := by
          intro r hr
          exact restrict_feasible (feasible_subset hF (Finset.erase_subset _ _))
        have hupper : ∀ r ∈ hanging t e, value weight (branches r) ≤ M r := by
          intro r hr
          have hgeo := frontier_below (EdgeAbove.footprint_region t e hae) hr
          have hrv := htarget ▸ hgeo
          have hrnode := (Finset.mem_filter.mp hr).1
          apply ih (remainingDepth t r)
            (hn ▸ remainingDepth_lt hrnode hrv.1 hrv.2) hrnode (branches r)
            (hbranch r hr) rfl
        have hpart := gall_partition hF he htarget
        have hval : value weight F ≤ weight e + sdp t M e := by
          rw [hpart, value_gall hae weight branches hbranch, hanging_score t M e hae]
          exact Nat.add_le_add_left (Finset.sum_le_sum hupper) _
        have hpair : e ∈ pairsAt t v := Finset.mem_filter.mpr ⟨hF.1.1 he, htarget⟩
        have hsup : weight e + sdp t M e ≤ s t weight M v := by
          unfold s
          exact Finset.le_sup (f := fun f : Pair => weight f + sdp t M f) hpair
        rw [hrec]
        exact hval.trans (hsup.trans (le_max_right _ _))
      · have hnoroot : ∀ e ∈ F, EdgeAbove.target e ≠ v := by
          intro e he heq
          exact hroot ⟨e, he, heq⟩
        have hL := restrict_feasible (r := v ++ [false]) hF
        have hR := restrict_feasible (r := v ++ [true]) hF
        have upperChild (b : Bool) :
            value weight (restrictBelow (v ++ [b]) F) ≤ M (v ++ [b]) := by
          have hchild := PhyloTree.child_mem_nodes hnode b
          have hlt := remainingDepth_lt hchild (List.prefix_append _ _) (by simp)
          apply ih (remainingDepth t (v ++ [b])) (hn ▸ hlt) hchild
            (restrictBelow (v ++ [b]) F) (restrict_feasible hF) rfl
        have hpart := fork_partition hF hnoroot
        have hval : value weight F ≤ M (v ++ [false]) + M (v ++ [true]) := by
          conv_lhs => rw [hpart]
          rw [value, Finset.sum_union (fork_disjoint hL hR)]
          exact Nat.add_le_add (upperChild false) (upperChild true)
        rw [hrec]
        exact hval.trans (le_max_left _ _)


/-- The actual decomposition and strong-induction argument of Theorem 1 for
weighted cycle footprints. No decomposition or optimality hypothesis is added.
The graph bridge and Lemma 1 turn these weights into the paper's quartet score. -/
theorem trace_optimal (t : PhyloTree) (weight : Pair → ℕ) (M : Address → ℕ)
    (hM : Array t weight M) {v : Address} {E : Finset Pair}
    (hv : v ∈ t.nodes) (trace : Trace t weight M v E) :
    FeasibleBelow t v E ∧ value weight E = M v ∧
      ∀ F, FeasibleBelow t v F → value weight F ≤ M v := by
  exact ⟨(trace_correct t weight M hM hv trace).1,
    (trace_correct t weight M hM hv trace).2, fun F hF => array_upper t weight M hM hv F hF⟩

/-- Finite bottom-up rounds. Once the depth bound is reached, the values
stabilize; the construction therefore makes no optimality assumption. -/
noncomputable def bottomUp (t : PhyloTree) (weight : Pair → ℕ) : ℕ → Address → ℕ
  | 0, _ => 0
  | n + 1, v =>
    match t.nodeAt v with
    | some (.fork _ _) => max (bottomUp t weight n (v ++ [false]) +
        bottomUp t weight n (v ++ [true]))
        ((pairsAt t v).sup (fun e => weight e + ∑ r ∈ hanging t e, bottomUp t weight n r))
    | _ => 0

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

/-- The bottom-up recurrence and backtracking have an instance for every
nonnegative weight function; the main algorithm statement is not vacuous. -/
theorem exists_array_trace (t : PhyloTree) (weight : Pair → ℕ) :
    ∃ M, Array t weight M ∧ ∃ E, Trace t weight M [] E := by
  exact ⟨_, bottomUp_array t weight,
    exists_trace t weight _ (bottomUp_array t weight) (PhyloTree.root_mem_nodes t)⟩


end Camus.DynamicProgramming
