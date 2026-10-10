module

public import Camus.Restriction.Defs

/-!
# Section 2.4: the knapsack over the hanging subtrees

In the gall case of the recurrence (`BudgetDP.cases`), the budget left after the edge with target
`v` is distributed over the subtrees hanging off its cycle. This file shows that the knapsack
`BudgetDP.forest`, which keeps only the maximum after each convolution, loses nothing: its values
are values of distributions (`forest_sound`) and dominate all of them (`forest_upper`). It then
lifts this to families of added edges: every value of the knapsack row is attained by feasible
families in the hanging subtrees with the right total size (`forest_attainable`), and any feasible
families in the hanging subtrees are dominated by a value of the row of their total size
(`forest_dominates`).

## Main results

* `BudgetDP.mem_allocations`: the values of `allocations` are the sums over the distributions of
  the budget.
* `BudgetDP.forest_sound`, `BudgetDP.forest_upper`: `forest` is contained in `allocations` and
  dominates it.
* `BudgetDP.forest_attainable`, `BudgetDP.forest_dominates`: the same for feasible edge families.
* `BudgetDP.card_gall`: the edge with target `v` and the families below it have `1 + Σ` edges.
-/

@[expose] public section

namespace Camus.BudgetDP

open DynamicProgramming

/-- For a list `rs` without repetition, the values of `allocations M rs k` are the sums
`Σ_{r ∈ rs} s r` over the budgets `b` with `Σ_{r ∈ rs} b r = k` and the choices
`s r ∈ M r (b r)`. -/
 theorem mem_allocations {M : Address → ℕ → Finset ℕ} {rs : List Address}
    (hrs : rs.Nodup) {k z : ℕ} : z ∈ allocations M rs k ↔
      ∃ b s : Address → ℕ,
        (∑ r ∈ rs.toFinset, b r) = k ∧
        (∑ r ∈ rs.toFinset, s r) = z ∧
        ∀ r ∈ rs.toFinset, s r ∈ M r (b r) := by
  classical
  induction rs generalizing k z with
  | nil =>
    simp only [allocations,List.toFinset_nil,Finset.sum_empty,Finset.notMem_empty]
    constructor
    · intro h
      split_ifs at h with hk
      · have hz : z=0 := Finset.mem_singleton.mp h
        exact ⟨fun _=>0,fun _=>0,hk.symm,hz.symm,by simp⟩
      · exact (Finset.notMem_empty _ h).elim
    · rintro ⟨b,s,hk,hz,_⟩
      simp [←hk,←hz]
  | cons r rs ih =>
    have hrnot : r ∉ rs.toFinset := by simpa using (List.nodup_cons.mp hrs).1
    have htail := (List.nodup_cons.mp hrs).2
    simp only [allocations,mem_convolution]
    constructor
    · rintro ⟨i,j,a,c,hij,ha,hc,hac⟩
      obtain ⟨b,s,hb,hs,hm⟩ := (ih htail).mp hc
      let b' := Function.update b r i
      let s' := Function.update s r a
      have hb' : ∀ x ∈ rs.toFinset, b' x = b x := by
        intro x hx
        have hne : x ≠ r := by intro h; exact hrnot (h ▸ hx)
        exact Function.update_of_ne hne _ _
      have hs' : ∀ x ∈ rs.toFinset, s' x = s x := by
        intro x hx
        have hne : x ≠ r := by intro h; exact hrnot (h ▸ hx)
        exact Function.update_of_ne hne _ _
      refine ⟨b',s',?_,?_,?_⟩
      · rw [List.toFinset_cons,Finset.sum_insert hrnot]
        rw [show b' r = i by simp [b']]
        rw [Finset.sum_congr rfl hb',hb,hij]
      · rw [List.toFinset_cons,Finset.sum_insert hrnot]
        rw [show s' r = a by simp [s']]
        rw [Finset.sum_congr rfl hs',hs,hac]
      · intro x hx
        rw [List.toFinset_cons] at hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simpa [b',s'] using ha
        · rw [hs' x hx,hb' x hx]
          exact hm x hx
    · rintro ⟨b,s,hb,hs,hm⟩
      refine ⟨b r,∑ x ∈ rs.toFinset, b x,s r,∑ x ∈ rs.toFinset, s x,?_,?_,?_,?_⟩
      · simpa [List.toFinset_cons,Finset.sum_insert hrnot] using hb
      · exact hm r (by simp)
      · exact (ih htail).mpr ⟨b,s,rfl,rfl,fun x hx=>hm x (by simp [hx])⟩
      · simpa [List.toFinset_cons,Finset.sum_insert hrnot] using hs

/-- Every value of the knapsack row is the value of a distribution of the budget. -/
 theorem forest_sound {M : Address → ℕ → Finset ℕ} {rs : List Address}
    {k z : ℕ} (hz : z ∈ forest M rs k) : z ∈ allocations M rs k := by
  induction rs generalizing k z with
  | nil => exact hz
  | cons r rs ih =>
    obtain ⟨i,j,a,b,hij,ha,hb,hab⟩ := mem_convolution.mp (mem_best.mp hz).1
    exact mem_convolution.mpr ⟨i,j,a,b,hij,ha,ih hb,hab⟩

/-- The value of every distribution of the budget is at most a value of the knapsack row: keeping
only the maximum after each convolution loses no maximum. -/
 theorem forest_upper {M : Address → ℕ → Finset ℕ} {rs : List Address}
    {k z : ℕ} (hz : z ∈ allocations M rs k) : ∃ m ∈ forest M rs k, z ≤ m := by
  induction rs generalizing k z with
  | nil => exact ⟨z,hz,le_rfl⟩
  | cons r rs ih =>
    obtain ⟨i,j,a,b,hij,ha,hb,hab⟩ := mem_convolution.mp hz
    obtain ⟨c,hc,hbc⟩ := ih hb
    have hcandidate : a+c ∈ convolution (M r) (forest M rs) k :=
      mem_convolution.mpr ⟨i,j,a,c,hij,ha,hc,rfl⟩
    obtain ⟨m,hm,hle⟩ := exists_best_ge hcandidate
    exact ⟨m,hm,hab ▸ (Nat.add_le_add_left hbc a).trans hle⟩

/-- Attainment for the knapsack. Assume that every value `z` of a row `M[r][k]` of a subtree `r`
hanging off the cycle of `e` is the value of a feasible family of exactly `k` edges below `r`. Then
every value `z` of row `k` of the knapsack is the total value of feasible families `F r` below the
hanging subtrees `r`, with `k` edges in total. -/
 theorem forest_attainable {t : PhyloTree} {M : Address → ℕ → Finset ℕ}
    {e : Pair} (_he : EdgeAbove.Admissible t e) (w : Pair → ℕ)
    (hM : ∀ r ∈ hanging t e, ∀ k z, z ∈ M r k →
      ∃ F, FeasibleBelow t r F ∧ F.card = k ∧ value w F = z)
    {k z : ℕ} (hz : z ∈ forest M (hanging t e).toList k) :
    ∃ F : Address → Finset Pair,
      (∀ r ∈ hanging t e, FeasibleBelow t r (F r)) ∧
      (∑ r ∈ hanging t e, (F r).card) = k ∧
      (∑ r ∈ hanging t e, value w (F r)) = z := by
  classical
  obtain ⟨b,s,hb,hs,hm⟩ := (mem_allocations (Finset.nodup_toList _)).mp (forest_sound hz)
  simp only [Finset.toList_toFinset] at hb hs hm
  have hex r (hr : r ∈ hanging t e) := hM r hr (b r) (s r) (hm r hr)
  let F := fun r => if hr : r ∈ hanging t e then (hex r hr).choose else ∅
  have hF r (hr : r ∈ hanging t e) :
      FeasibleBelow t r (F r) ∧ (F r).card = b r ∧ value w (F r) = s r := by
    simpa only [F,dite_eq_left hr] using (hex r hr).choose_spec
  exact ⟨F,fun r hr=>(hF r hr).1,
    (Finset.sum_congr rfl (fun r hr=>(hF r hr).2.1)).trans hb,
    (Finset.sum_congr rfl (fun r hr=>(hF r hr).2.2)).trans hs⟩

/-- Domination for the knapsack. Assume that every feasible family below a subtree `r` hanging off
the cycle of `e` has value at most some value of the row of `r` of its size. Then any feasible
families `F r` below the hanging subtrees have total value at most some value of the knapsack row
of their total size. -/
 theorem forest_dominates {t : PhyloTree} {M : Address → ℕ → Finset ℕ}
    {e : Pair} (_he : EdgeAbove.Admissible t e) (w : Pair → ℕ)
    (hM : ∀ r ∈ hanging t e, ∀ F, FeasibleBelow t r F →
      ∃ z ∈ M r F.card, value w F ≤ z)
    (F : Address → Finset Pair) (hF : ∀ r ∈ hanging t e, FeasibleBelow t r (F r)) :
    ∃ z ∈ forest M (hanging t e).toList (∑ r ∈ hanging t e, (F r).card),
      (∑ r ∈ hanging t e, value w (F r)) ≤ z := by
  classical
  have hex r (hr : r ∈ hanging t e) := hM r hr (F r) (hF r hr)
  let s := fun r => if hr : r ∈ hanging t e then (hex r hr).choose else 0
  have hs r (hr : r ∈ hanging t e) : s r ∈ M r (F r).card ∧ value w (F r) ≤ s r := by
    simpa only [s,dite_eq_left hr] using (hex r hr).choose_spec
  have ha : (∑ r ∈ hanging t e, s r) ∈
      allocations M (hanging t e).toList (∑ r ∈ hanging t e, (F r).card) := by
    apply (mem_allocations (Finset.nodup_toList _)).mpr
    simp only [Finset.toList_toFinset]
    exact ⟨fun r=>(F r).card,s,rfl,rfl,fun r hr=>(hs r hr).1⟩
  obtain ⟨z,hz,hle⟩ := forest_upper ha
  exact ⟨z,hz,(Finset.sum_le_sum (fun r hr=>(hs r hr).2)).trans hle⟩

/-- Feasible families below distinct hanging subtrees are disjoint, so their union has
`Σ_r |F r|` edges. -/
 theorem card_forest {t : PhyloTree} {e : Pair} (he : EdgeAbove.Admissible t e)
    (F : Address → Finset Pair) (hF : ∀ r ∈ hanging t e, FeasibleBelow t r (F r)) :
    ((hanging t e).biUnion F).card = ∑ r ∈ hanging t e, (F r).card := by
  exact Finset.card_biUnion (forest_disjoint (EdgeAbove.footprint_region t e he) F hF)

/-- The edge `e` together with feasible families `F r` below the subtrees hanging off its cycle has
`1 + Σ_r |F r|` edges. -/
 theorem card_gall {t : PhyloTree} {e : Pair} (he : EdgeAbove.Admissible t e)
    (F : Address → Finset Pair) (hF : ∀ r ∈ hanging t e, FeasibleBelow t r (F r)) :
    (insert e ((hanging t e).biUnion F)).card = 1 + ∑ r ∈ hanging t e, (F r).card := by
  rw [Finset.card_insert_of_notMem (gall_not_mem_forest he F hF),card_forest he F hF]
  omega

end Camus.BudgetDP
