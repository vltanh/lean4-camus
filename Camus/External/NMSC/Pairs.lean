module

public import Camus.External.NMSC.FourComponents

/-!
# A pair of taxa that stays together

Section 3.3 of CAMUS expects, for four taxa on which the network displays one quartet `xy|zw`, that
`xy|zw` is strictly the most probable quartet. This file proves the lower bound behind it when the
pair `x, y` hangs below a cut edge and stays together until it meets a third lineage: below a child
of a tree node (`Brooqs.Net.tree_pair_bound`) or from a node of a side of a cycle
(`Brooqs.Net.cycle_pair_bound`). With the four lineages relabelled so that the pair is `0, 1`, the
expected score `Brooqs.expectedScore` of the forest at the tree node or at the top node of the cycle
is at least `1/3 + (2/3) (1 - e^{-b})`, `b` the length of the edge above the pair; so the quartet CF
of `xy|zw` exceeds `1/3`.

## Main results

* `Brooqs.IsForestDist`, `Brooqs.Net.isForestDist`, `Brooqs.Side.isForestDist`: probability
  distributions on good forests with given lineages.
* `Brooqs.expectedScore_vecMul_nice`, `Brooqs.expectedScore_forestUnion`,
  `Brooqs.quartetScore_union_ge`, `Brooqs.expectedScore_union_ge`: expected scores.
* `Brooqs.pairProb_ge`: the pair has coalesced along the edge above it with probability at least
  `1 - e^{-b}`.
* `Brooqs.steps_bound`, `Brooqs.arm_bound`, `Brooqs.Side.pair_bound`: the bound along a side, after
  the pair has entered it.
* `Brooqs.Net.cycle_pair_bound`, `Brooqs.Net.tree_pair_bound`, `Brooqs.Net.tree_pair_bound'`: the
  bound at the top of a cycle and at a tree node.

## Proof

Until a third lineage joins the pair, only the two lineages of the pair can coalesce: a cluster of
two lineages is then `{0, 1}`, or `{2, 3}` among the other lineages, both on the side of the split
`{0, 1} | {2, 3}`, so the score is at least `1/3`, and `1` once the pair has coalesced
(`Brooqs.quartetScore_union_ge`). Once a third lineage has joined, the rest of the process is a
nice kernel and the expected score stays (`Brooqs.NiceKernel.score`). Along a side, the pair enters
at its node, possibly joining lineages that arrived from below (`Brooqs.arm_bound`); then the
forests of the networks hanging above it join one by one (`Brooqs.steps_bound`), and at the top node
of the cycle the forest of the other side joins. At a cycle, the bound holds for each choice of
sides at the hybrid node, whose lineages are not those of the pair, and the choices are weighted by
probabilities adding up to `1`.
-/

@[expose] public noncomputable section

namespace Brooqs

open Finset Matrix

universe u

/-! ### Distributions of forests of the four lineages -/

/-- `μ` is a probability distribution on good forests whose lineages are `T`. -/
structure IsForestDist (μ : Finset (Finset (Fin 4)) → ℝ) (T : Finset (Fin 4)) : Prop where
  nonneg : ∀ F, 0 ≤ μ F
  sum_eq_one : ∑ F, μ F = 1
  support : ∀ F, μ F ≠ 0 → IsGood F ∧ ADR11.lineages F = T

namespace IsForestDist

variable {μ ν : Finset (Finset (Fin 4)) → ℝ} {T T' : Finset (Fin 4)}

theorem single {F : Finset (Finset (Fin 4))} (hF : IsGood F) :
    IsForestDist (Pi.single F 1) (ADR11.lineages F) := by
  refine ⟨fun G => ?_, by simp, fun G hG => ?_⟩
  · rw [Pi.single_apply]
    split_ifs <;> norm_num
  · obtain rfl : G = F := by
      by_contra h
      exact hG (Pi.single_eq_of_ne h 1)
    exact ⟨hF, rfl⟩

/-- A nice kernel sends a distribution on good forests on lineages `T` disjoint from the added
lineages `S` to a distribution on good forests on `T ∪ S`. -/
theorem vecMul_nice {S : Finset (Fin 4)}
    {Φ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ} (h : IsForestDist μ T)
    (hΦ : NiceKernel S Φ) (hΦ0 : ∀ F G, IsGood F → 0 ≤ Φ F G) (hd : Disjoint T S) :
    IsForestDist (μ ᵥ* Φ) (T ∪ S) := by
  refine ⟨fun G => ?_, ?_, fun G hG => ?_⟩
  · simp only [vecMul, dotProduct]
    refine sum_nonneg fun F _ => ?_
    by_cases hF : μ F = 0
    · rw [hF, zero_mul]
    · exact mul_nonneg (h.nonneg F) (hΦ0 F G (h.support F hF).1)
  · simp only [vecMul, dotProduct]
    rw [sum_comm, ← h.sum_eq_one]
    refine sum_congr rfl fun F _ => ?_
    rw [← mul_sum]
    by_cases hF : μ F = 0
    · rw [hF, zero_mul]
    · obtain ⟨hFg, hFl⟩ := h.support F hF
      rw [hΦ.sum_eq_one F hFg (hFl ▸ hd), mul_one]
  · simp only [vecMul, dotProduct] at hG
    obtain ⟨F, -, hF⟩ := exists_ne_zero_of_sum_ne_zero hG
    obtain ⟨hFg, hFl⟩ := h.support F (left_ne_zero_of_mul hF)
    obtain ⟨hGg, -, hGl⟩ := hΦ.support F hFg (hFl ▸ hd) G (right_ne_zero_of_mul hF)
    exact ⟨hGg, by rw [hGl, hFl]⟩

theorem kT (h : IsForestDist μ T) {t : ℝ} (ht : 0 ≤ t) :
    IsForestDist (μ ᵥ* kingmanTransition t) T := by
  have := h.vecMul_nice (niceKernel_kingmanTransition t) (fun F G _ => by
    rw [kingmanTransition_eq_adr11]
    exact ADR11.kingmanTransition_nonneg ht F G) (disjoint_empty_right _)
  rwa [union_empty] at this

/-- Adding an independent forest is a nice kernel. -/
theorem niceKernel (h : IsForestDist μ T) : NiceKernel T (unionKernel μ) :=
  niceKernel_unionKernel h.sum_eq_one h.support

theorem unionKernel_nonneg (h : IsForestDist μ T) (F G : Finset (Finset (Fin 4))) :
    0 ≤ unionKernel μ F G :=
  sum_nonneg fun E _ => by
    split_ifs
    · exact h.nonneg E
    · exact le_rfl

theorem union (hμ : IsForestDist μ T) (hν : IsForestDist ν T') (hd : Disjoint T T') :
    IsForestDist (forestUnion μ ν) (T ∪ T') := by
  rw [forestUnion_eq_vecMul]
  exact hμ.vecMul_nice hν.niceKernel (fun F G _ => hν.unionKernel_nonneg F G) hd

/-- A distribution on forests without lineages is the point mass at the empty forest. -/
theorem eq_single_empty (h : IsForestDist μ ∅) : μ = Pi.single ∅ 1 := by
  have hsupp : ∀ F, μ F ≠ 0 → F = ∅ := by
    intro F hF
    obtain ⟨hFg, hFl⟩ := h.support F hF
    rw [eq_empty_iff_forall_notMem]
    intro A hA
    obtain ⟨l, hl⟩ := hFg.1.1 A hA
    have := ADR11.subset_lineages hA hl
    rw [hFl] at this
    exact notMem_empty l this
  have h0 : μ ∅ = 1 := by
    rw [← h.sum_eq_one, Fintype.sum_eq_single ∅ fun F hF => by
      by_contra h'
      exact hF (hsupp F h')]
  funext F
  rw [Pi.single_apply]
  split_ifs with hF
  · rw [hF, h0]
  · by_contra h'
    exact hF (hsupp F h')

end IsForestDist

/-! ### Expected scores -/

/-- The expected score of a random forest of the four lineages. -/
def expectedScore (μ : Finset (Finset (Fin 4)) → ℝ) : ℝ := ∑ G, μ G * quartetScore G

/-- After a nice kernel, the expected score of a random good forest of at least three lineages,
none added by the kernel, is its expected score. -/
theorem expectedScore_vecMul_nice {S : Finset (Fin 4)}
    {Φ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ} (hΦ : NiceKernel S Φ)
    {ρ : Finset (Finset (Fin 4)) → ℝ}
    (hρ : ∀ F, ρ F ≠ 0 → IsGood F ∧ Disjoint (ADR11.lineages F) S ∧ 3 ≤ #(ADR11.lineages F)) :
    expectedScore (ρ ᵥ* Φ) = expectedScore ρ := by
  unfold expectedScore
  simp only [vecMul, dotProduct, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun F _ => ?_
  by_cases hF : ρ F = 0
  · simp [hF]
  obtain ⟨hFg, hFS, hF3⟩ := hρ F hF
  simp only [mul_assoc, ← mul_sum]
  rw [hΦ.score hFg hFS hF3]

/-- The expected score of the union of two independent random forests. -/
theorem expectedScore_forestUnion (μ ν : Finset (Finset (Fin 4)) → ℝ) :
    expectedScore (forestUnion μ ν) = ∑ F, ∑ F', μ F * ν F' * quartetScore (F ∪ F') := by
  unfold expectedScore forestUnion
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun F _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun F' _ => ?_
  rw [Fintype.sum_eq_single (F ∪ F') fun G hG => by rw [ite_eq_right (Ne.symm hG), zero_mul]]
  rw [ite_eq_left rfl]

/-- The score of the union of a forest on the lineages `0, 1` and a forest on the lineages
`2, 3` is at least `1/3`, and `1` if `0` and `1` have coalesced: its clusters of two lineages
can only be `{0, 1}` and `{2, 3}`, both on the side of the split `{0, 1} | {2, 3}`. -/
theorem quartetScore_union_ge {F F' : Finset (Finset (Fin 4))}
    (hF : ∀ C ∈ F, C ⊆ {0, 1}) (hF' : ∀ C ∈ F', C ⊆ {2, 3}) :
    1 / 3 + 2 / 3 * (if ({0, 1} : Finset (Fin 4)) ∈ F then 1 else 0) ≤ quartetScore (F ∪ F') := by
  have htwo : ∀ C : Finset (Fin 4), C ⊆ {0, 1} → #C = 2 → C = {0, 1} := by decide
  have htwo' : ∀ C : Finset (Fin 4), C ⊆ {2, 3} → #C = 2 → C = {2, 3} := by decide
  have key : (∃ C ∈ F ∪ F', #C = 2) →
      ({0, 1} : Finset (Fin 4)) ∈ F ∪ F' ∨ ({2, 3} : Finset (Fin 4)) ∈ F ∪ F' := by
    rintro ⟨C, hC, hC2⟩
    rcases mem_union.1 hC with hC | hC
    · left
      rw [← htwo C (hF C hC) hC2]
      exact mem_union_left _ hC
    · right
      rw [← htwo' C (hF' C hC) hC2]
      exact mem_union_right _ hC
  unfold quartetScore
  by_cases h1 : ({0, 1} : Finset (Fin 4)) ∈ F
  · rw [ite_eq_left (Or.inl (mem_union_left _ h1)), ite_eq_left h1]
    norm_num
  · rw [ite_eq_right h1]
    by_cases h2 : ({0, 1} : Finset (Fin 4)) ∈ F ∪ F' ∨ ({2, 3} : Finset (Fin 4)) ∈ F ∪ F'
    · rw [ite_eq_left h2]
      norm_num
    · rw [ite_eq_right h2, ite_eq_right (fun h => h2 (key h))]
      norm_num

/-! ### The forests of networks and sides -/

section Nets

variable {X : Type u} [DecidableEq X]

/-- The lineages sampled from the taxa of a network. -/
def Net.lin (s : Fin 4 → X) (M : Net X) : Finset (Fin 4) := univ.filter fun l => s l ∈ M.taxa

/-- The lineages sampled from the taxa below a side. -/
def Side.lin (s : Fin 4 → X) (S : Side X) : Finset (Fin 4) := univ.filter fun l => s l ∈ S.taxa

/-- The forest at the root of a metric network with distinct leaf labels. -/
theorem Net.isForestDist {M : Net X} (hM : M.IsMetric) (hMn : M.leaves.Nodup) (s : Fin 4 → X) :
    IsForestDist (M.forestDist s) (M.lin s) := by
  refine ⟨Net.forestDist_nonneg hM s, ?_, fun F hF => ?_⟩
  · rw [Net.forestDist_eq]
    exact Net.forestDistOf_single_sum M hMn (sampledAt s) (fun _ _ => isGood_singletons _)
      (fun _ _ _ _ hab => disjoint_lineages_sampledAt s hab)
  · obtain ⟨h1, -, h3⟩ := Net.forestDist_support hMn s hF
    exact ⟨h1, h3⟩

private theorem pr_lineages_sampledAt (s : Fin 4 → X) (x : X) :
    ADR11.lineages (sampledAt s x) = univ.filter fun l => s l = x :=
  lineages_singletons _

/-- The forest at the top of a metric side with distinct leaf labels, when a good forest `E` on
other lineages takes its hybrid edge. -/
theorem Side.isForestDist {S : Side X} (hS : S.IsMetric) (hSn : S.leaves.Nodup) (s : Fin 4 → X)
    {E : Finset (Finset (Fin 4))} (hE : IsGood E) (hEd : Disjoint (ADR11.lineages E) (S.lin s)) :
    IsForestDist (S.forestDist s E) (ADR11.lineages E ∪ S.lin s) := by
  have hdisj : ∀ a ∈ S.leaves, Disjoint (ADR11.lineages E) (ADR11.lineages (sampledAt s a)) := by
    intro a ha
    refine hEd.mono_right fun l hl => ?_
    rw [pr_lineages_sampledAt, mem_filter] at hl
    simp only [Side.lin, mem_filter, mem_univ, true_and, Side.taxa, List.mem_toFinset, hl.2]
    exact ha
  refine ⟨Side.forestDist_nonneg hS s E, ?_, fun F hF => ?_⟩
  · rw [Side.forestDist_eq]
    exact Side.forestDistOf_single_sum S hSn (sampledAt s) (fun _ _ => isGood_singletons _)
      (fun _ _ _ _ hab => disjoint_lineages_sampledAt s hab) hE hdisj
  · rw [Side.forestDist_eq] at hF
    obtain ⟨h1, -, -, h4⟩ := Side.forestDistOf_single_support S hSn (sampledAt s)
      (fun _ _ => isGood_singletons _) (fun _ _ _ _ hab => disjoint_lineages_sampledAt s hab) hE
      hdisj hF
    refine ⟨h1, ?_⟩
    rw [h4]
    congr 1
    ext l
    simp [pr_lineages_sampledAt, Side.lin, Side.taxa]

end Nets

/-! ### The probability that the lineages `0` and `1` have coalesced -/

/-- The probability that a random forest has the cluster `{0, 1}`. -/
def pairProb (μ : Finset (Finset (Fin 4)) → ℝ) : ℝ :=
  ∑ F, μ F * if ({0, 1} : Finset (Fin 4)) ∈ F then 1 else 0

/-- A nice kernel never removes a cluster, so the probability of the cluster `{0, 1}` does not
decrease. -/
theorem pairProb_vecMul_nice {μ : Finset (Finset (Fin 4)) → ℝ} {T S : Finset (Fin 4)}
    (hμ : IsForestDist μ T) {Φ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ}
    (hΦ : NiceKernel S Φ) (hΦ0 : ∀ F G, IsGood F → 0 ≤ Φ F G) (hd : Disjoint T S) :
    pairProb μ ≤ pairProb (μ ᵥ* Φ) := by
  unfold pairProb
  simp only [vecMul, dotProduct, sum_mul]
  rw [sum_comm]
  refine sum_le_sum fun F _ => ?_
  by_cases hF : μ F = 0
  · simp [hF]
  obtain ⟨hFg, hFl⟩ := hμ.support F hF
  split_ifs with h01
  · -- the cluster stays
    rw [mul_one]
    calc μ F = ∑ G, μ F * Φ F G := by rw [← mul_sum, hΦ.sum_eq_one F hFg (hFl ▸ hd), mul_one]
      _ = ∑ G, μ F * Φ F G * (if ({0, 1} : Finset (Fin 4)) ∈ G then 1 else 0) := by
          refine sum_congr rfl fun G _ => ?_
          by_cases hG : Φ F G = 0
          · simp [hG]
          · rw [ite_eq_left ((hΦ.support F hFg (hFl ▸ hd) G hG).2.1 h01), mul_one]
      _ ≤ _ := le_rfl
  · rw [mul_zero]
    exact sum_nonneg fun G _ => mul_nonneg (mul_nonneg (hμ.nonneg F) (hΦ0 F G hFg))
      (by split_ifs <;> norm_num)

private theorem pr_pair_forest : ∀ A : Finset (Fin 4), A ⊆ {0, 1} → A.Nonempty → A ≠ {0, 1} →
    A = {0} ∨ A = {1} := by
  decide

/-- **The coalescence of a pair.** If the lineages sampled from the taxa of `M` are exactly `0`
and `1`, after the edge of length `t ≥ 0` above `M` they have coalesced with probability at least
`1 - e^{-t}`. -/
theorem pairProb_ge {X : Type u} [DecidableEq X] {M : Net X} (hM : M.IsMetric)
    (hMn : M.leaves.Nodup) {s : Fin 4 → X} (hlin : M.lin s = {0, 1}) (t : ℝ) :
    1 - Real.exp (-t) ≤ pairProb (M.forestDist s ᵥ* kingmanTransition t) := by
  have hμ := Net.isForestDist hM hMn s
  rw [hlin] at hμ
  -- for each forest at the root of `M`, the cluster `{0, 1}` after the edge
  have hrow : ∀ E, M.forestDist s E ≠ 0 → 1 - Real.exp (-t) ≤
      ∑ G, kingmanTransition t E G * (if ({0, 1} : Finset (Fin 4)) ∈ G then 1 else 0) := by
    intro E hE
    obtain ⟨hEg, hsing, hEl⟩ := Net.forestDist_support hMn s hE
    have h0 : ({0} : Finset (Fin 4)) ∈ E := hsing 0 (by
      have : (0 : Fin 4) ∈ M.lin s := by rw [hlin]; simp
      simpa [Net.lin] using this)
    have h1 : ({1} : Finset (Fin 4)) ∈ E := hsing 1 (by
      have : (1 : Fin 4) ∈ M.lin s := by rw [hlin]; simp
      simpa [Net.lin] using this)
    have hEl' : ADR11.lineages E = {0, 1} := by rw [hEl]; exact hlin
    by_cases h01 : ({0, 1} : Finset (Fin 4)) ∈ E
    · -- the lineages have coalesced below: they stay coalesced
      have hsum : ∑ G, kingmanTransition t E G *
          (if ({0, 1} : Finset (Fin 4)) ∈ G then 1 else 0) = ∑ G, kingmanTransition t E G := by
        refine sum_congr rfl fun G _ => ?_
        by_cases hG : kingmanTransition t E G = 0
        · simp [hG]
        · rw [ite_eq_left ((kingmanTransition_support hEg hG).2.1 h01), mul_one]
      rw [hsum, kingmanTransition_row_sum hEg.1 t]
      linarith [Real.exp_pos (-t)]
    · -- the lineages arrive apart: `E = {{0}, {1}}`
      have hE01 : E = {{0}, {1}} := by
        ext A
        simp only [mem_insert, mem_singleton]
        constructor
        · intro hA
          exact pr_pair_forest A (fun l hl => hEl' ▸ ADR11.subset_lineages hA hl)
            (hEg.1.1 A hA) (fun h => h01 (h ▸ hA))
        · rintro (rfl | rfl)
          · exact h0
          · exact h1
      subst hE01
      have hroots : roots ({{0}, {1}} : Finset (Finset (Fin 4))) = {{0}, {1}} := by decide
      have hk := single_vecMul_kingmanTransition_two hEg.1 (A := {0}) (B := {1}) (by decide)
        hroots t
      have hrow : ∀ G, kingmanTransition t ({{0}, {1}} : Finset (Finset (Fin 4))) G =
          ((Real.exp (-t) • Pi.single ({{0}, {1}} : Finset (Finset (Fin 4))) (1 : ℝ) +
            (1 - Real.exp (-t)) • Pi.single (insert ({0} ∪ {1}) {{0}, {1}} :
              Finset (Finset (Fin 4))) (1 : ℝ)) : Finset (Finset (Fin 4)) → ℝ) G := by
        intro G
        rw [← hk, single_one_vecMul]
        rfl
      have hval : ∑ G, kingmanTransition t ({{0}, {1}} : Finset (Finset (Fin 4))) G *
          (if ({0, 1} : Finset (Fin 4)) ∈ G then 1 else 0) = 1 - Real.exp (-t) := by
        simp only [hrow, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib]
        rw [Fintype.sum_eq_single ({{0}, {1}} : Finset (Finset (Fin 4))) (fun G hG => by
            rw [Pi.single_eq_of_ne hG]
            ring),
          Fintype.sum_eq_single (insert ({0} ∪ {1}) {{0}, {1}} : Finset (Finset (Fin 4)))
            (fun G hG => by
              rw [Pi.single_eq_of_ne hG]
              ring),
          Pi.single_eq_same, Pi.single_eq_same, ite_eq_right h01, ite_eq_left (by decide)]
        ring
      rw [hval]
  calc 1 - Real.exp (-t) = ∑ E, M.forestDist s E * (1 - Real.exp (-t)) := by
        rw [← sum_mul, hμ.sum_eq_one, one_mul]
    _ ≤ ∑ E, M.forestDist s E * ∑ G, kingmanTransition t E G *
          (if ({0, 1} : Finset (Fin 4)) ∈ G then 1 else 0) := by
        refine sum_le_sum fun E _ => ?_
        by_cases hE : M.forestDist s E = 0
        · simp [hE]
        · exact mul_le_mul_of_nonneg_left (hrow E hE) (hμ.nonneg E)
    _ = pairProb (M.forestDist s ᵥ* kingmanTransition t) := by
        unfold pairProb
        simp only [vecMul, dotProduct, sum_mul, mul_sum, mul_assoc]
        exact sum_comm

/-! ### After the pair has entered a side -/

/-- The kernel of a list of steps: at each step a forest with distribution `n.1` joins, and the
lineages travel along an edge of length `n.2`. -/
def stepsKernel : List ((Finset (Finset (Fin 4)) → ℝ) × ℝ) →
    Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ
  | [] => 1
  | n :: rest => unionKernel n.1 * kingmanTransition n.2 * stepsKernel rest

/-- The steps `L` add forests on pairwise disjoint sets of lineages within `T`, and the forest
`ν` added at the end adds lineages within what remains. -/
def Steps (ν : Finset (Finset (Fin 4)) → ℝ) :
    Finset (Fin 4) → List ((Finset (Finset (Fin 4)) → ℝ) × ℝ) → Prop
  | T, [] => ∃ T', T' ⊆ T ∧ IsForestDist ν T'
  | T, n :: rest => 0 ≤ n.2 ∧ ∃ T', T' ⊆ T ∧ IsForestDist n.1 T' ∧ Steps ν (T \ T') rest

theorem Steps.mono {ν : Finset (Finset (Fin 4)) → ℝ} :
    ∀ {L : List ((Finset (Finset (Fin 4)) → ℝ) × ℝ)} {T T' : Finset (Fin 4)}, Steps ν T L →
      T ⊆ T' → Steps ν T' L
  | [], _, _, ⟨U, hU, hν⟩, h => ⟨U, hU.trans h, hν⟩
  | _ :: _, _, _, ⟨hn, U, hU, hd, hrest⟩, h =>
      ⟨hn, U, hU.trans h, hd, Steps.mono hrest (sdiff_subset_sdiff h subset_rfl)⟩

private theorem pr_kT_nonneg {t : ℝ} (ht : 0 ≤ t) (F G : Finset (Finset (Fin 4))) :
    0 ≤ kingmanTransition t F G := by
  rw [kingmanTransition_eq_adr11]
  exact ADR11.kingmanTransition_nonneg ht F G

private theorem pr_mul_nonneg {A B : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ}
    (hA : ∀ F G, 0 ≤ A F G) (hB : ∀ F G, 0 ≤ B F G) (F G : Finset (Finset (Fin 4))) :
    0 ≤ (A * B) F G := by
  rw [Matrix.mul_apply]
  exact sum_nonneg fun H _ => mul_nonneg (hA F H) (hB H G)

/-- The steps followed by the forest `ν` act by a nice kernel with nonnegative entries, adding
lineages within `T`. -/
theorem Steps.nice {ν : Finset (Finset (Fin 4)) → ℝ} :
    ∀ {L : List ((Finset (Finset (Fin 4)) → ℝ) × ℝ)} {T : Finset (Fin 4)}, Steps ν T L →
      ∃ S ⊆ T, NiceKernel S (stepsKernel L * unionKernel ν) ∧
        ∀ F G, 0 ≤ (stepsKernel L * unionKernel ν) F G
  | [], T, ⟨U, hU, hν⟩ => by
      refine ⟨U, hU, ?_, fun F G => ?_⟩
      · rw [stepsKernel, Matrix.one_mul]
        exact hν.niceKernel
      · rw [stepsKernel, Matrix.one_mul]
        exact hν.unionKernel_nonneg F G
  | n :: rest, T, ⟨hn, U, hU, hd, hrest⟩ => by
      obtain ⟨S, hS, hnice, hnn⟩ := Steps.nice hrest
      have hdisj : Disjoint U S := disjoint_of_subset_right hS disjoint_sdiff
      have h1 := (hd.niceKernel.mul (niceKernel_kingmanTransition n.2)
        (disjoint_empty_right _))
      rw [union_empty] at h1
      have h2 := h1.mul hnice hdisj
      refine ⟨U ∪ S, union_subset hU (hS.trans sdiff_subset), ?_, fun F G => ?_⟩
      · simp only [stepsKernel, Matrix.mul_assoc] at h2 ⊢
        exact h2
      · simp only [stepsKernel, Matrix.mul_assoc]
        exact pr_mul_nonneg hd.unionKernel_nonneg
          (pr_mul_nonneg (pr_kT_nonneg hn) hnn) F G

/-- The expected score of the union of a forest on the lineages `0, 1` and an independent forest
on lineages among `2, 3`. -/
theorem expectedScore_union_ge {α ν : Finset (Finset (Fin 4)) → ℝ} {T : Finset (Fin 4)}
    (hα : IsForestDist α {0, 1}) (hν : IsForestDist ν T) (hT : T ⊆ {2, 3}) :
    1 / 3 + 2 / 3 * pairProb α ≤ expectedScore (forestUnion α ν) := by
  rw [expectedScore_forestUnion]
  calc 1 / 3 + 2 / 3 * pairProb α =
        ∑ F, ∑ F', α F * ν F' * (1 / 3 + 2 / 3 *
          (if ({0, 1} : Finset (Fin 4)) ∈ F then 1 else 0)) := by
        simp only [← sum_mul, ← mul_sum, hν.sum_eq_one, mul_one, mul_add, sum_add_distrib,
          pairProb, ← mul_assoc]
        rw [hα.sum_eq_one, mul_sum]
        congr 1
        · ring
        · exact sum_congr rfl fun F _ => by ring
    _ ≤ _ := by
        refine sum_le_sum fun F _ => sum_le_sum fun F' _ => ?_
        by_cases hF : α F = 0
        · simp [hF]
        by_cases hF' : ν F' = 0
        · simp [hF']
        obtain ⟨-, hFl⟩ := hα.support F hF
        obtain ⟨-, hF'l⟩ := hν.support F' hF'
        refine mul_le_mul_of_nonneg_left (quartetScore_union_ge (fun C hC => ?_)
          (fun C hC => ?_)) (mul_nonneg (hα.nonneg F) (hν.nonneg F'))
        · intro l hl
          rw [← hFl]
          exact ADR11.subset_lineages hC hl
        · intro l hl
          exact hT (hF'l ▸ ADR11.subset_lineages hC hl)

private theorem pr_disj01 {T : Finset (Fin 4)} (hT : T ⊆ {2, 3}) :
    Disjoint ({0, 1} : Finset (Fin 4)) T :=
  disjoint_of_subset_right hT (by decide)

private theorem pr_card3 {U : Finset (Fin 4)} (hU : U.Nonempty)
    (hd : Disjoint ({0, 1} : Finset (Fin 4)) U) :
    3 ≤ #(({0, 1} : Finset (Fin 4)) ∪ U) := by
  rw [card_union_of_disjoint hd]
  have := hU.card_pos
  have h2 : #({0, 1} : Finset (Fin 4)) = 2 := by decide
  omega

/-- **The steps after the pair.** Two lineages `0, 1` travel up along the steps `L` (forests on
lineages among `2, 3` join them), and a forest `ν` on lineages among `2, 3` joins at the end: the
expected score is at least `1/3`, more by `2/3` of the probability that `0` and `1` have already
coalesced. Until a third lineage joins, only `0` and `1` can coalesce; once it has joined, the
expected score stays (`Brooqs.NiceKernel.score`). -/
theorem steps_bound : ∀ (L : List ((Finset (Finset (Fin 4)) → ℝ) × ℝ)) {T : Finset (Fin 4)}
    {α ν : Finset (Finset (Fin 4)) → ℝ}, T ⊆ {2, 3} → IsForestDist α {0, 1} → Steps ν T L →
      1 / 3 + 2 / 3 * pairProb α ≤ expectedScore (forestUnion (α ᵥ* stepsKernel L) ν)
  | [], _, _, _, hT, hα, ⟨U, hU, hν⟩ => by
      rw [stepsKernel, vecMul_one]
      exact expectedScore_union_ge hα hν (hU.trans hT)
  | n :: rest, T, α, ν, hT, hα, ⟨hn, U, hU, hd, hrest⟩ => by
      have heq : α ᵥ* stepsKernel (n :: rest) =
          (forestUnion α n.1 ᵥ* kingmanTransition n.2) ᵥ* stepsKernel rest := by
        rw [stepsKernel, forestUnion_eq_vecMul, vecMul_vecMul, vecMul_vecMul, Matrix.mul_assoc]
      rw [heq]
      by_cases hU0 : U = ∅
      · -- no lineage joins at this step
        subst hU0
        rw [hd.eq_single_empty, forestUnion_single_empty]
        rw [sdiff_empty] at hrest
        have hmono := pairProb_vecMul_nice hα (niceKernel_kingmanTransition n.2)
          (fun F G _ => pr_kT_nonneg hn F G) (disjoint_empty_right _)
        exact le_trans (by linarith) (steps_bound rest hT (hα.kT hn) hrest)
      · -- a third lineage joins: from here the process is a nice kernel
        obtain ⟨S, hS, hnice, -⟩ := Steps.nice hrest
        have hΦ : NiceKernel S (kingmanTransition n.2 * (stepsKernel rest * unionKernel ν)) := by
          have := (niceKernel_kingmanTransition n.2).mul hnice (disjoint_empty_left _)
          rwa [empty_union] at this
        have hdU := pr_disj01 (hU.trans hT)
        have hu := hα.union hd hdU
        rw [forestUnion_eq_vecMul (_ ᵥ* _), vecMul_vecMul, vecMul_vecMul,
          expectedScore_vecMul_nice hΦ fun F hF => ?_]
        · exact expectedScore_union_ge hα hd (hU.trans hT)
        · obtain ⟨hFg, hFl⟩ := hu.support F hF
          refine ⟨hFg, ?_, ?_⟩
          · rw [hFl]
            refine disjoint_union_left.2 ⟨(pr_disj01 hT).mono_right (hS.trans sdiff_subset),
              disjoint_of_subset_right hS disjoint_sdiff⟩
          · rw [hFl]
            exact pr_card3 (nonempty_iff_ne_empty.2 hU0) hdU

/-- **The node where the pair enters.** At a node of a side, the forest `β` arriving from below
(on lineages among `2, 3`) and the forest `P` of the pair `0, 1` join; then the lineages travel
along an edge of length `e ≥ 0` and the steps `L`, and a forest `ν` joins at the end. If `β` has a
lineage, three lineages are together at the node and the expected score stays; otherwise the pair
travels on alone (`Brooqs.steps_bound`). -/
theorem arm_bound {β P ν : Finset (Finset (Fin 4)) → ℝ} {Tβ T : Finset (Fin 4)} {e : ℝ}
    {L : List ((Finset (Finset (Fin 4)) → ℝ) × ℝ)} (hβ : IsForestDist β Tβ)
    (hTβ : Tβ ⊆ {2, 3}) (hP : IsForestDist P {0, 1}) (he : 0 ≤ e) (hT : T ⊆ {2, 3})
    (hTd : Disjoint T Tβ) (hL : Steps ν T L) :
    1 / 3 + 2 / 3 * pairProb P ≤
      expectedScore
        (forestUnion ((forestUnion β P ᵥ* kingmanTransition e) ᵥ* stepsKernel L) ν) := by
  by_cases hTβ0 : Tβ = ∅
  · subst hTβ0
    rw [hβ.eq_single_empty, forestUnion_comm (Pi.single ∅ 1) P, forestUnion_single_empty]
    have hmono := pairProb_vecMul_nice hP (niceKernel_kingmanTransition e)
      (fun F G _ => pr_kT_nonneg he F G) (disjoint_empty_right _)
    exact le_trans (by linarith) (steps_bound L hT (hP.kT he) hL)
  · obtain ⟨S, hS, hnice, -⟩ := Steps.nice hL
    have hΦ : NiceKernel S (kingmanTransition e * (stepsKernel L * unionKernel ν)) := by
      have := (niceKernel_kingmanTransition e).mul hnice (disjoint_empty_left _)
      rwa [empty_union] at this
    have hd := pr_disj01 hTβ
    have hu := hβ.union hP hd.symm
    rw [forestUnion_eq_vecMul (_ ᵥ* _), vecMul_vecMul, vecMul_vecMul,
      expectedScore_vecMul_nice hΦ fun F hF => ?_, forestUnion_comm β P]
    · exact expectedScore_union_ge hP hβ hTβ
    · obtain ⟨hFg, hFl⟩ := hu.support F hF
      refine ⟨hFg, ?_, ?_⟩
      · rw [hFl]
        exact disjoint_union_left.2 ⟨(hTd.symm.mono_right hS), (pr_disj01 hT).mono_right hS⟩
      · rw [hFl, union_comm]
        exact pr_card3 (nonempty_iff_ne_empty.2 hTβ0) hd

/-! ### Along a side and at a cycle -/

section Sides

variable {X : Type u} [DecidableEq X]

private theorem pr_sub23 : ∀ T : Finset (Fin 4), Disjoint ({0, 1} : Finset (Fin 4)) T →
    T ⊆ {2, 3} := by
  decide

private theorem pr_lin_node (s : Fin 4 → X) (ℓ b : ℝ) (M : Net X) (S : Side X) :
    (Side.node ℓ b M S).lin s = M.lin s ∪ S.lin s := by
  ext l
  simp [Side.lin, Net.lin, Side.taxa_node]

private theorem pr_lin_disjoint {s : Fin 4 → X} {A B : Finset X} (h : Disjoint A B) :
    Disjoint (univ.filter fun l => s l ∈ A) (univ.filter fun l => s l ∈ B) :=
  disjoint_filter.2 fun _ _ ha hb => disjoint_left.1 h ha hb

private theorem pr_lin_mono {s : Fin 4 → X} {A B : Finset X} (h : A ⊆ B) :
    (univ.filter fun l => s l ∈ A) ⊆ (univ.filter fun l => s l ∈ B) := fun l hl => by
  simp only [mem_filter, mem_univ, true_and] at hl ⊢
  exact h hl

private theorem pr_disjoint_toFinset {l₁ l₂ : List X} (h : (l₁ ++ l₂).Nodup) :
    Disjoint l₁.toFinset l₂.toFinset := by
  rw [disjoint_left]
  intro a ha hb
  exact (List.nodup_append.1 h).2.2 a (List.mem_toFinset.1 ha) a (List.mem_toFinset.1 hb) rfl

/-- **Along a side.** If the lineages sampled from the network of a node `n₀` of the side `S` are
exactly `0` and `1`, then for a forest `E` on lineages among `2, 3` taking the hybrid edge of `S`,
followed by steps `L` and a forest `ν`, the expected score is at least
`1/3 + (2/3) (1 - e^{-b})`, where `b` is the length of the pendant edge of `n₀`. -/
theorem Side.pair_bound (s : Fin 4 → X) : ∀ (S : Side X), S.IsMetric → S.leaves.Nodup →
    ∀ (n₀ : ℝ × ℝ × Net X), n₀ ∈ S.nodes → n₀.2.2.lin s = {0, 1} →
    ∀ {E : Finset (Finset (Fin 4))} {T : Finset (Fin 4)} {ν : Finset (Finset (Fin 4)) → ℝ}
      {L : List ((Finset (Finset (Fin 4)) → ℝ) × ℝ)}, IsGood E →
      ADR11.lineages E ⊆ {2, 3} → Disjoint (ADR11.lineages E) (S.lin s) → T ⊆ {2, 3} →
      Disjoint T (ADR11.lineages E ∪ S.lin s) → Steps ν T L →
      1 / 3 + 2 / 3 * (1 - Real.exp (-n₀.2.1)) ≤
        expectedScore (forestUnion (S.forestDist s E ᵥ* stepsKernel L) ν)
  | .hyb _, _, _, n₀, hn₀, _, _, _, _, _, _, _, _, _, _, _ => by
      simp [Side.nodes] at hn₀
  | .node ℓ b M S, hS, hSn, n₀, hn₀, hlin, E, T, ν, L, hE, hE23, hEd, hT, hTd, hL => by
      obtain ⟨hℓ, hb, hM, hS'⟩ := hS
      have hSn' : (M.leaves ++ S.leaves).Nodup := hSn
      have hMn : M.leaves.Nodup := (List.nodup_append.1 hSn').1
      have hS'n : S.leaves.Nodup := (List.nodup_append.1 hSn').2.1
      have hMS : Disjoint (M.lin s) (S.lin s) :=
        pr_lin_disjoint (pr_disjoint_toFinset hSn')
      rw [pr_lin_node] at hEd hTd
      have hdef : (Side.node ℓ b M S).forestDist s E =
          forestUnion (S.forestDist s E) (M.forestDist s ᵥ* kingmanTransition b) ᵥ*
            kingmanTransition ℓ := rfl
      simp only [Side.nodes, List.mem_cons] at hn₀
      rcases hn₀ with rfl | hn₀
      · -- the pair hangs from this node
        have hSlin : S.lin s ⊆ {2, 3} := pr_sub23 _ (by rw [← hlin]; exact hMS)
        have hβ := Side.isForestDist hS' hS'n s hE (hEd.mono_right subset_union_right)
        have hP : IsForestDist (M.forestDist s ᵥ* kingmanTransition b) {0, 1} := by
          have := (Net.isForestDist hM hMn s).kT hb.le
          rwa [hlin] at this
        have h := arm_bound hβ (union_subset hE23 hSlin) hP hℓ.le hT
          (hTd.mono_right (union_subset_union subset_rfl subset_union_right)) hL
        rw [hdef]
        have hpp := pairProb_ge hM hMn hlin b
        exact le_trans (by linarith) h
      · -- the pair hangs below: this node is one more step after the pair
        have hn₀S : n₀.2.2.lin s ⊆ S.lin s := pr_lin_mono fun x hx =>
          Side.mem_taxa_iff.2 ⟨n₀, hn₀, hx⟩
        have hMlin : M.lin s ⊆ {2, 3} := pr_sub23 _ (by
          rw [← hlin]
          exact (hMS.mono_right hn₀S).symm)
        have hQ := (Net.isForestDist hM hMn s).kT hb.le
        have hstep : forestUnion (S.forestDist s E) (M.forestDist s ᵥ* kingmanTransition b) ᵥ*
            kingmanTransition ℓ ᵥ* stepsKernel L =
            S.forestDist s E ᵥ* stepsKernel ((M.forestDist s ᵥ* kingmanTransition b, ℓ) :: L) := by
          rw [stepsKernel, forestUnion_eq_vecMul, vecMul_vecMul, vecMul_vecMul, Matrix.mul_assoc]
        rw [hdef, hstep]
        refine Side.pair_bound s S hS' hS'n n₀ hn₀ hlin hE hE23
          (hEd.mono_right subset_union_right) (union_subset hT hMlin) ?_
          ⟨hℓ.le, M.lin s, subset_union_right, hQ, Steps.mono hL ?_⟩
        · refine disjoint_union_left.2 ⟨hTd.mono_right (union_subset_union subset_rfl
            subset_union_right), disjoint_union_right.2 ⟨?_, hMS⟩⟩
          exact (hEd.mono_right subset_union_left).symm
        · intro l hl
          rw [mem_sdiff]
          exact ⟨mem_union_left _ hl, fun h => disjoint_left.1 hTd hl
            (mem_union_right _ (mem_union_left _ h))⟩

/-- The expected score at the top node of a cycle: over the forest arriving below the hybrid
node, the choices of sides of its roots, and the two sides. -/
theorem expectedScore_cycle (s : Fin 4 → X) (γ ℓ : ℝ) (S₁ S₂ : Side X) (H : Net X) :
    expectedScore ((Net.cycle γ S₁ S₂ ℓ H).forestDist s) =
      ∑ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) *
          expectedScore (forestUnion (S₁.forestDist s (forestBelow F A))
            (S₂.forestDist s (forestBelow F (roots F \ A)))) := by
  unfold expectedScore
  simp only [Net.forestDist, sum_mul, mul_sum, mul_assoc]
  rw [sum_comm]
  refine sum_congr rfl fun F _ => ?_
  rw [sum_comm]

private theorem pr_weights (γ : ℝ) (R : Finset (Finset (Fin 4))) :
    ∑ A ∈ R.powerset, γ ^ #A * (1 - γ) ^ #(R \ A) = 1 := by
  have h := sum_pow_mul_eq_add_pow γ (1 - γ) R
  rw [show γ + (1 - γ) = 1 by ring, one_pow] at h
  refine (sum_congr rfl fun A hA => ?_).trans h
  rw [card_sdiff_of_subset (mem_powerset.1 hA)]

/-- **A pair hanging from a side of a cycle.** If the lineages sampled from the network of a node
`n₀` of a side of the cycle at the top of `C` are exactly `0` and `1`, the expected score of the
forest at the top node of the cycle is at least `1/3 + (2/3) (1 - e^{-b})`, where `b` is the length
of the pendant edge of `n₀`: whatever the lineages below the hybrid node do, the pair travels up its
side and meets a third lineage, or reaches the top node, without separating. -/
theorem Net.cycle_pair_bound (s : Fin 4 → X) {γ ℓ : ℝ} {S₁ S₂ : Side X} {H : Net X}
    (hC : (Net.cycle γ S₁ S₂ ℓ H).IsMetric) (hCn : (Net.cycle γ S₁ S₂ ℓ H).leaves.Nodup)
    (n₀ : ℝ × ℝ × Net X) (hn₀ : n₀ ∈ S₁.nodes ∨ n₀ ∈ S₂.nodes) (hlin : n₀.2.2.lin s = {0, 1}) :
    1 / 3 + 2 / 3 * (1 - Real.exp (-n₀.2.1)) ≤
      expectedScore ((Net.cycle γ S₁ S₂ ℓ H).forestDist s) := by
  obtain ⟨hγ0, hγ1, hℓ, hS₁, hS₂, hH, -⟩ := hC
  have hCn' : (S₁.leaves ++ S₂.leaves ++ H.leaves).Nodup := hCn
  have h12 : (S₁.leaves ++ S₂.leaves).Nodup := (List.nodup_append.1 hCn').1
  have hS₁n : S₁.leaves.Nodup := (List.nodup_append.1 h12).1
  have hS₂n : S₂.leaves.Nodup := (List.nodup_append.1 h12).2.1
  have hHn : H.leaves.Nodup := (List.nodup_append.1 hCn').2.1
  have d12 : Disjoint (S₁.lin s) (S₂.lin s) := pr_lin_disjoint (pr_disjoint_toFinset h12)
  have dT : Disjoint (S₁.leaves ++ S₂.leaves).toFinset H.leaves.toFinset :=
    pr_disjoint_toFinset hCn'
  have d1H : Disjoint (S₁.lin s) (H.lin s) := pr_lin_disjoint (dT.mono_left fun x hx => by
    simp only [Side.taxa, List.mem_toFinset, List.toFinset_append, mem_union] at hx ⊢
    exact Or.inl hx)
  have d2H : Disjoint (S₂.lin s) (H.lin s) := pr_lin_disjoint (dT.mono_left fun x hx => by
    simp only [Side.taxa, List.mem_toFinset, List.toFinset_append, mem_union] at hx ⊢
    exact Or.inr hx)
  -- the lineages of the pair lie below the side of `n₀`
  have hn₀S : ∀ {S : Side X}, n₀ ∈ S.nodes → n₀.2.2.lin s ⊆ S.lin s := fun hn =>
    pr_lin_mono fun x hx => Side.mem_taxa_iff.2 ⟨n₀, hn, hx⟩
  have hH23 : H.lin s ⊆ {2, 3} := pr_sub23 _ (by
    rw [← hlin]
    rcases hn₀ with hn | hn
    · exact d1H.mono_left (hn₀S hn)
    · exact d2H.mono_left (hn₀S hn))
  have hμ := (Net.isForestDist hH hHn s).kT hℓ.le
  -- the bound for each choice of sides at the hybrid node
  have hterm : ∀ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F ≠ 0 →
      ∀ A ∈ (roots F).powerset, 1 / 3 + 2 / 3 * (1 - Real.exp (-n₀.2.1)) ≤
        expectedScore (forestUnion (S₁.forestDist s (forestBelow F A))
          (S₂.forestDist s (forestBelow F (roots F \ A)))) := by
    intro F hF A hA
    obtain ⟨hFg, hFl⟩ := hμ.support F hF
    obtain ⟨-, hFd⟩ := forestBelow_union hFg (mem_powerset.1 hA)
    have hE₁ := isGood_forestBelow (A := A) hFg
    have hE₂ := isGood_forestBelow (A := roots F \ A) hFg
    have hl₁ : ADR11.lineages (forestBelow F A) ⊆ H.lin s :=
      hFl ▸ ADR11.lineages_mono (filter_subset _ _)
    have hl₂ : ADR11.lineages (forestBelow F (roots F \ A)) ⊆ H.lin s :=
      hFl ▸ ADR11.lineages_mono (filter_subset _ _)
    rcases hn₀ with hn | hn
    · -- the pair hangs from `S₁`; `S₂` brings the forest `ν`
      have hS₂23 : S₂.lin s ⊆ {2, 3} := pr_sub23 _ (by
        rw [← hlin]
        exact (d12.mono_left (hn₀S hn)))
      have h := Side.pair_bound s S₁ hS₁ hS₁n n₀ hn hlin (L := [])
        (T := ADR11.lineages (forestBelow F (roots F \ A)) ∪ S₂.lin s)
        (ν := S₂.forestDist s (forestBelow F (roots F \ A))) hE₁ (hl₁.trans hH23)
        (d1H.symm.mono_left hl₁) (union_subset (hl₂.trans hH23) hS₂23)
        (disjoint_union_left.2 ⟨disjoint_union_right.2 ⟨hFd.symm, d1H.symm.mono_left hl₂⟩,
          disjoint_union_right.2 ⟨d2H.mono_right hl₁, d12.symm⟩⟩)
        ⟨_, subset_rfl, Side.isForestDist hS₂ hS₂n s hE₂ (d2H.symm.mono_left hl₂)⟩
      rwa [stepsKernel, vecMul_one] at h
    · -- the pair hangs from `S₂`; `S₁` brings the forest `ν`
      have hS₁23 : S₁.lin s ⊆ {2, 3} := pr_sub23 _ (by
        rw [← hlin]
        exact (d12.symm.mono_left (hn₀S hn)))
      have h := Side.pair_bound s S₂ hS₂ hS₂n n₀ hn hlin (L := [])
        (T := ADR11.lineages (forestBelow F A) ∪ S₁.lin s)
        (ν := S₁.forestDist s (forestBelow F A)) hE₂ (hl₂.trans hH23)
        (d2H.symm.mono_left hl₂) (union_subset (hl₁.trans hH23) hS₁23)
        (disjoint_union_left.2 ⟨disjoint_union_right.2 ⟨hFd, d2H.symm.mono_left hl₁⟩,
          disjoint_union_right.2 ⟨d1H.mono_right hl₂, d12⟩⟩)
        ⟨_, subset_rfl, Side.isForestDist hS₁ hS₁n s hE₁ (d1H.symm.mono_left hl₁)⟩
      rwa [stepsKernel, vecMul_one, forestUnion_comm] at h
  rw [expectedScore_cycle]
  calc 1 / 3 + 2 / 3 * (1 - Real.exp (-n₀.2.1)) =
        ∑ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset,
          γ ^ #A * (1 - γ) ^ #(roots F \ A) * (1 / 3 + 2 / 3 * (1 - Real.exp (-n₀.2.1))) := by
        simp only [← sum_mul, pr_weights, one_mul, hμ.sum_eq_one]
    _ ≤ _ := by
        refine sum_le_sum fun F _ => ?_
        by_cases hF : (H.forestDist s ᵥ* kingmanTransition ℓ) F = 0
        · simp [hF]
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun A hA => ?_) (hμ.nonneg F)
        exact mul_le_mul_of_nonneg_left (hterm F hF A hA)
          (mul_nonneg (pow_nonneg hγ0.le _) (pow_nonneg (by linarith) _))

/-- **A pair below a child of a tree node.** If the lineages sampled from the left child `C₁` of a
tree node are exactly `0` and `1`, the expected score of the forest at the tree node is at least
`1/3 + (2/3) (1 - e^{-ℓ₁})`: the pair has coalesced along the edge above `C₁`, or reaches the node
as two lineages that meet the others there. -/
theorem Net.tree_pair_bound (s : Fin 4 → X) {ℓ₁ ℓ₂ : ℝ} {C₁ C₂ : Net X}
    (hC : (Net.tree ℓ₁ C₁ ℓ₂ C₂).IsMetric) (hCn : (Net.tree ℓ₁ C₁ ℓ₂ C₂).leaves.Nodup)
    (hlin : C₁.lin s = {0, 1}) :
    1 / 3 + 2 / 3 * (1 - Real.exp (-ℓ₁)) ≤
      expectedScore ((Net.tree ℓ₁ C₁ ℓ₂ C₂).forestDist s) := by
  obtain ⟨hℓ₁, hℓ₂, hC₁, hC₂⟩ := hC
  have hCn' : (C₁.leaves ++ C₂.leaves).Nodup := hCn
  have hC₁n : C₁.leaves.Nodup := (List.nodup_append.1 hCn').1
  have hC₂n : C₂.leaves.Nodup := (List.nodup_append.1 hCn').2.1
  have hd : Disjoint (C₁.lin s) (C₂.lin s) := pr_lin_disjoint (pr_disjoint_toFinset hCn')
  have hα := (Net.isForestDist hC₁ hC₁n s).kT hℓ₁.le
  rw [hlin] at hα
  have h := expectedScore_union_ge hα ((Net.isForestDist hC₂ hC₂n s).kT hℓ₂.le)
    (pr_sub23 _ (hlin ▸ hd))
  have hpp := pairProb_ge hC₁ hC₁n hlin ℓ₁
  exact le_trans (by linarith) h

/-- The same when the pair hangs below the right child of the tree node. -/
theorem Net.tree_pair_bound' (s : Fin 4 → X) {ℓ₁ ℓ₂ : ℝ} {C₁ C₂ : Net X}
    (hC : (Net.tree ℓ₁ C₁ ℓ₂ C₂).IsMetric) (hCn : (Net.tree ℓ₁ C₁ ℓ₂ C₂).leaves.Nodup)
    (hlin : C₂.lin s = {0, 1}) :
    1 / 3 + 2 / 3 * (1 - Real.exp (-ℓ₂)) ≤
      expectedScore ((Net.tree ℓ₁ C₁ ℓ₂ C₂).forestDist s) := by
  obtain ⟨hℓ₁, hℓ₂, hC₁, hC₂⟩ := hC
  have hCn' : (C₁.leaves ++ C₂.leaves).Nodup := hCn
  have hCn'' : (C₂.leaves ++ C₁.leaves).Nodup := List.nodup_append_comm.1 hCn'
  have h := Net.tree_pair_bound s (ℓ₁ := ℓ₂) (ℓ₂ := ℓ₁) (C₁ := C₂) (C₂ := C₁)
    ⟨hℓ₂, hℓ₁, hC₂, hC₁⟩ hCn'' hlin
  have heq : (Net.tree ℓ₁ C₁ ℓ₂ C₂).forestDist s = (Net.tree ℓ₂ C₂ ℓ₁ C₁).forestDist s :=
    forestUnion_comm _ _
  rwa [heq]

end Sides

end Brooqs
