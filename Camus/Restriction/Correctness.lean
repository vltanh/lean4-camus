module

public import Camus.Restriction.Forest

/-!
# Section 2.4: correctness of the recurrence

An array `M` satisfying the recurrence of `Camus/Restriction/Defs.lean` is correct at every vertex
`v` (`BudgetDP.Correct`): every value of the row `M[v][k]` is the value of a feasible family of
exactly `k` added edges with targets in `T_v` (attainment), and every such family has value at most
a value of the row of its size (domination). The proof is a strong induction from the leaves up,
with the two cases of the proof of Theorem 1: no edge of the family has target `v`, and the family
splits between the two children (`DynamicProgramming.fork_partition`); or an edge `e` has target
`v`, which is then the only one (Lemma 2), and the other edges lie below the subtrees hanging off
the cycle of `e` (`DynamicProgramming.gall_partition`).

## Main results

* `BudgetDP.array_correct`: attainment and domination at every vertex.
* `BudgetDP.exact_optimal`: every value `z` of `M[v][k]` is the value of a feasible family of
  exactly `k` edges below `v`, and no feasible family of exactly `k` edges below `v` has a larger
  value.
-/

@[expose] public section

namespace Camus.BudgetDP

open DynamicProgramming

/-- Correctness of the rows at `v`. Attainment: every value `z` of `M[v][k]` is the value
`Σ_{e ∈ F} w e` of a feasible family `F` of exactly `k` edges with targets in `T_v`. Domination:
every feasible family `F` with targets in `T_v` has value at most some value of `M[v][|F|]`. -/
def Correct (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (v : Address) : Prop :=
  (∀ k z, z ∈ M v k → ∃ F, FeasibleBelow t v F ∧ F.card=k ∧ value w F=z) ∧
  (∀ F, FeasibleBelow t v F → ∃ z ∈ M v F.card, value w F ≤ z)

/-- Attainment at `v`, given correctness strictly below `v`: every candidate value of
`cases t w M v k` is the value of a feasible family of exactly `k` edges with targets in `T_v`. -/
 theorem cases_attainable (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    {v : Address} (hv : v ∈ t.nodes)
    (ih : ∀ r ∈ t.nodes, v <+: r → v ≠ r → Correct t w M r)
    {k z : ℕ} (hz : z ∈ cases t w M v k) :
    ∃ F, FeasibleBelow t v F ∧ F.card=k ∧ value w F=z := by
  classical
  obtain ⟨sub,hnode⟩ := (t.mem_nodes_iff v).mp hv
  cases sub with
  | leaf a =>
    simp only [cases,hnode] at hz
    split_ifs at hz with hk
    · have hz' : z=0 := Finset.mem_singleton.mp hz
      exact ⟨∅,feasible_empty t v,by simpa using hk.symm,by simp [value,hz']⟩
    · exact (Finset.notMem_empty _ hz).elim
  | fork l r =>
    have hchild (b : Bool) : Correct t w M (v++[b]) :=
      ih _ (PhyloTree.child_mem_nodes hnode b) (List.prefix_append _ _) (by simp)
    simp only [cases,hnode] at hz
    rcases Finset.mem_union.mp hz with hfork | hgall
    -- no edge with target `v`: join families attaining the two children's rows
    · obtain ⟨i,j,a,b,hij,ha,hb,hab⟩ := mem_convolution.mp hfork
      obtain ⟨L,hL,hLc,hLv⟩ := (hchild false).1 i a ha
      obtain ⟨R,hR,hRc,hRv⟩ := (hchild true).1 j b hb
      refine ⟨L∪R,fork_feasible hL hR,?_,?_⟩
      · rw [Finset.card_union_of_disjoint (fork_disjoint hL hR),hLc,hRc,hij]
      · rw [value,Finset.sum_union (fork_disjoint hL hR)]
        exact (congrArg₂ (·+·) hLv hRv).trans hab
    -- an edge `e` with target `v`: add it to families attaining the knapsack row of the subtrees
    -- hanging off its cycle
    · split_ifs at hgall with hk
      · exact (Finset.notMem_empty _ hgall).elim
      · obtain ⟨e,he,hz⟩ := Finset.mem_biUnion.mp hgall
        obtain ⟨c,hc,hcz⟩ := Finset.mem_image.mp hz
        obtain ⟨hec,het⟩ := Finset.mem_filter.mp he
        have hae := (Finset.mem_filter.mp hec).2
        have hhang r (hr : r ∈ hanging t e) : Correct t w M r := by
          have hgeo := frontier_below (EdgeAbove.footprint_region t e hae) hr
          exact ih r (Finset.mem_filter.mp hr).1 (het ▸ hgeo.1) (het ▸ hgeo.2)
        obtain ⟨F,hF,hFc,hFv⟩ := forest_attainable hae w (fun r hr=>(hhang r hr).1) hc
        refine ⟨insert e ((hanging t e).biUnion F),het ▸ gall_feasible hae F hF,?_,?_⟩
        · rw [card_gall hae F hF,hFc]
          omega
        · rw [value_gall hae w F hF,hFv,hcz]

/-- Domination at `v`, given correctness strictly below `v`: every feasible family `F` with targets
in `T_v` has value at most some candidate value of `cases t w M v |F|`. -/
 theorem cases_dominates (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    {v : Address} (hv : v ∈ t.nodes)
    (ih : ∀ r ∈ t.nodes, v <+: r → v ≠ r → Correct t w M r)
    (F : Finset Pair) (hF : FeasibleBelow t v F) :
    ∃ z ∈ cases t w M v F.card, value w F ≤ z := by
  classical
  obtain ⟨sub,hnode⟩ := (t.mem_nodes_iff v).mp hv
  cases sub with
  | leaf a =>
    have hf := feasible_leaf_empty hnode hF
    subst F
    exact ⟨0,by simp [cases,hnode],by simp [value]⟩
  | fork l r =>
    have hchild (b : Bool) : Correct t w M (v++[b]) :=
      ih _ (PhyloTree.child_mem_nodes hnode b) (List.prefix_append _ _) (by simp)
    by_cases hroot : ∃ e ∈ F, EdgeAbove.target e=v
    -- an edge `e` of `F` has target `v`: it is the only one (Lemma 2), and the other edges lie
    -- below the subtrees hanging off its cycle
    · obtain ⟨e,he,het⟩ := hroot
      have hae := (Finset.mem_filter.mp (hF.1.1 he)).2
      let branches := fun r => restrictBelow r (F.erase e)
      have hbranches r (_hr : r ∈ hanging t e) : FeasibleBelow t r (branches r) :=
        restrict_feasible (feasible_subset hF (Finset.erase_subset _ _))
      have hhang r (hr : r ∈ hanging t e) : Correct t w M r := by
        have hgeo := frontier_below (EdgeAbove.footprint_region t e hae) hr
        exact ih r (Finset.mem_filter.mp hr).1 (het ▸ hgeo.1) (het ▸ hgeo.2)
      obtain ⟨c,hc,hcle⟩ := forest_dominates hae w (fun r hr=>(hhang r hr).2)
        branches hbranches
      have hpart := gall_partition hF he het
      have hcard : F.card = 1 + ∑ r ∈ hanging t e, (branches r).card := by
        conv_lhs => rw [hpart]
        exact card_gall hae branches hbranches
      have hpos : F.card ≠ 0 := by omega
      refine ⟨w e+c,?_,?_⟩
      · simp only [cases,hnode,ite_eq_right hpos]
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨e,Finset.mem_filter.mpr ⟨hF.1.1 he,het⟩,?_⟩
        apply Finset.mem_image.mpr
        exact ⟨c,by simpa [show F.card-1=∑ r ∈ hanging t e, (branches r).card by omega] using hc,rfl⟩
      · conv_lhs => rw [hpart]
        rw [value_gall hae w branches hbranches]
        exact Nat.add_le_add_left hcle _
    -- no edge of `F` has target `v`: `F` splits between the two children
    · have hno : ∀ e ∈ F, EdgeAbove.target e ≠ v := by
        intro e he ht
        exact hroot ⟨e,he,ht⟩
      let L := restrictBelow (v++[false]) F
      let R := restrictBelow (v++[true]) F
      have hL : FeasibleBelow t (v++[false]) L := restrict_feasible hF
      have hR : FeasibleBelow t (v++[true]) R := restrict_feasible hF
      obtain ⟨a,ha,haL⟩ := (hchild false).2 L hL
      obtain ⟨b,hb,hbR⟩ := (hchild true).2 R hR
      have hpart : F=L∪R := fork_partition hF hno
      have hcard : L.card+R.card=F.card := by rw [hpart,Finset.card_union_of_disjoint (fork_disjoint hL hR)]
      refine ⟨a+b,?_,?_⟩
      · simp only [cases,hnode]
        apply Finset.mem_union_left
        exact mem_convolution.mpr ⟨L.card,R.card,a,b,hcard,ha,hb,rfl⟩
      · rw [hpart,value,Finset.sum_union (fork_disjoint hL hR)]
        exact Nat.add_le_add haL hbR

/-- Section 2.4: if `M` satisfies the recurrence, its rows are correct (`Correct`) at every vertex
of `T`. Strong induction from the leaves up, with the two cases of the proof of Theorem 1. -/
 theorem array_correct (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (hM : Array t w M) {v : Address} (hv : v ∈ t.nodes) : Correct t w M v := by
  generalize hn : remainingDepth t v = n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    have hsub r (hr : r ∈ t.nodes) (hvr : v <+: r) (hne : v ≠ r) : Correct t w M r :=
      ih (remainingDepth t r) (hn ▸ remainingDepth_lt hr hvr hne) hr rfl
    constructor
    · intro k z hz
      rw [hM v hv k] at hz
      exact cases_attainable t w M hv hsub (mem_best.mp hz).1
    · intro F hF
      obtain ⟨z,hz,hlez⟩ := cases_dominates t w M hv hsub F hF
      obtain ⟨m,hm,hzm⟩ := exists_best_ge hz
      exact ⟨m,by rw [hM v hv F.card]; exact hm,hlez.trans hzm⟩

/-- Section 2.4, for families of added edges: if `M` satisfies the recurrence, every value `z` of
`M[v][k]` is the value of a feasible family `E` of exactly `k` edges with targets in `T_v`, and
every feasible family of exactly `k` edges with targets in `T_v` has value at most `z`. -/
 theorem exact_optimal (t : PhyloTree) (w : Pair → ℕ) (M : Address → ℕ → Finset ℕ)
    (hM : Array t w M) {v : Address} (hv : v ∈ t.nodes) {k z : ℕ} (hz : z ∈ M v k) :
    ∃ E, FeasibleBelow t v E ∧ E.card=k ∧ value w E=z ∧
      ∀ F, FeasibleBelow t v F → F.card=k → value w F ≤ z := by
  obtain ⟨E,hE,hEk,hEz⟩ := (array_correct t w M hM hv).1 k z hz
  refine ⟨E,hE,hEk,hEz,?_⟩
  intro F hF hFk
  obtain ⟨m,hm,hlem⟩ := (array_correct t w M hM hv).2 F hF
  rw [hFk,hM v hv k] at hm
  have hmax := (mem_best.mp (hM v hv k ▸ hz)).2 m (mem_best.mp hm).1
  exact hlem.trans hmax

end Camus.BudgetDP
