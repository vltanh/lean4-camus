module

public import Camus.Restriction.Correctness

/-!
# Section 2.4: the array exists

The recurrence of `Camus/Restriction/Defs.lean` defines the rows at a vertex from rows strictly
below it, so an array satisfying it exists: `BudgetDP.bottomUp` evaluates the recurrence round
after round, and after more rounds than the depth of `T` the rows no longer change. Since the rows
are correct (`BudgetDP.array_correct`), a row is nonempty exactly when its budget is feasible.

## Main results

* `BudgetDP.exists_array`: for every tree `T` and edge weights `w` there is an array satisfying the
  recurrence.
* `BudgetDP.row_nonempty_iff`: `M[v][k]` is nonempty iff some feasible family of exactly `k` edges
  has its targets in `T_v`.
-/

@[expose] public section

namespace Camus.BudgetDP

open DynamicProgramming

/-- The knapsack over `rs` depends only on the rows of the subtrees in `rs`. -/
 theorem forest_congr {M N : Address → ℕ → Finset ℕ} {rs : List Address}
    (h : ∀ r ∈ rs, ∀ k, M r k = N r k) : ∀ k, forest M rs k = forest N rs k := by
  induction rs with
  | nil => intro k; rfl
  | cons r rs ih =>
    intro k
    have hr : M r = N r := funext (h r (by simp))
    have ht : forest M rs = forest N rs := funext (ih (fun s hs=>h s (by simp [hs])))
    simp only [forest,hr,ht]

/-- The candidate values at `v` depend only on the rows at the vertices strictly below `v`. -/
 theorem cases_congr (t : PhyloTree) (w : Pair → ℕ) {M N : Address → ℕ → Finset ℕ}
    {v : Address} (hv : v ∈ t.nodes)
    (h : ∀ r ∈ t.nodes, v <+: r → v ≠ r → ∀ k, M r k=N r k) :
    ∀ k, cases t w M v k = cases t w N v k := by
  classical
  obtain ⟨sub,hnode⟩ := (t.mem_nodes_iff v).mp hv
  cases sub with
  | leaf a => intro k; simp [cases,hnode]
  | fork l r =>
    have hc (b : Bool) : M (v++[b]) = N (v++[b]) :=
      funext (h _ (PhyloTree.child_mem_nodes hnode b) (List.prefix_append _ _) (by simp))
    have hf e (he : e ∈ pairsAt t v) : forest M (hanging t e).toList = forest N (hanging t e).toList
        := by
      obtain ⟨hec,het⟩ := Finset.mem_filter.mp he
      have hae := (Finset.mem_filter.mp hec).2
      apply funext
      apply forest_congr
      intro r hr
      have hr' : r ∈ hanging t e := Finset.mem_toList.mp hr
      have hgeo := frontier_below (EdgeAbove.footprint_region t e hae) hr'
      exact h r (Finset.mem_filter.mp hr').1 (het ▸ hgeo.1) (het ▸ hgeo.2)
    intro k
    simp only [cases,hnode,hc false,hc true]
    congr 1
    split_ifs
    · rfl
    · apply Finset.biUnion_congr rfl
      intro e he
      rw [hf e he]

/-- `n` rounds of the recurrence, starting from empty rows: round `n + 1` sets every row to `best`
of its candidate values computed from the rows of round `n`. -/
noncomputable def bottomUp (t : PhyloTree) (w : Pair → ℕ) : ℕ → Address → ℕ → Finset ℕ
  | 0, _, _ => ∅
  | n+1, v, k => best (cases t w (bottomUp t w n) v k)

/-- The rows at `v` are the same after any two numbers of rounds larger than
`remainingDepth t v`, which bounds the height of `T_v`. -/
 theorem bottomUp_stable (t : PhyloTree) (w : Pair → ℕ) {v : Address}
    (hv : v ∈ t.nodes) {a b : ℕ} (ha : remainingDepth t v < a)
    (hb : remainingDepth t v < b) : ∀ k, bottomUp t w a v k = bottomUp t w b v k := by
  generalize hn : remainingDepth t v = n at ha hb
  induction n using Nat.strong_induction_on generalizing v a b with
  | h n ih =>
    cases a with
    | zero => omega
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        have hsub r (hr : r ∈ t.nodes) (hvr : v <+: r) (hne : v ≠ r) :
            ∀ k, bottomUp t w a r k = bottomUp t w b r k := by
          have hlt := remainingDepth_lt hr hvr hne
          exact ih (remainingDepth t r) (hn ▸ hlt) hr rfl (by omega) (by omega)
        intro k
        simp only [bottomUp]
        rw [cases_congr t w hv hsub k]

/-- Section 2.4: for every tree `T` and edge weights `w` there is an array `M` satisfying the
recurrence (`BudgetDP.Array t w M`): `bottomUp` after more rounds than the depth of `T`. -/
 theorem exists_array (t : PhyloTree) (w : Pair → ℕ) : ∃ M, Array t w M := by
  let K := t.nodes.sup List.length + 1
  let M := bottomUp t w K
  refine ⟨M,?_⟩
  intro v hv k
  have hbound : remainingDepth t v < K := by unfold remainingDepth K; omega
  have hs := bottomUp_stable t w hv hbound (show remainingDepth t v < K+1 by omega) k
  exact hs

/-- Section 2.4: if `M` satisfies the recurrence, the row `M[v][k]` is nonempty iff some feasible
family of exactly `k` edges has all its targets in `T_v`. Rows of impossible budgets are empty,
rather than holding the value `0`. -/
 theorem row_nonempty_iff (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (hM : Array t w M) {v : Address} (hv : v ∈ t.nodes) (k : ℕ) :
    (M v k).Nonempty ↔ ∃ E, FeasibleBelow t v E ∧ E.card=k := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨E,hE,hEk,_⟩ := (array_correct t w M hM hv).1 k z hz
    exact ⟨E,hE,hEk⟩
  · rintro ⟨E,hE,hEk⟩
    obtain ⟨z,hz,_⟩ := (array_correct t w M hM hv).2 E hE
    rw [hEk] at hz
    exact ⟨z,hz⟩

end Camus.BudgetDP
