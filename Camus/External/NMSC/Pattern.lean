module

public import Camus.External.NMSC.Pairs

/-!
# The CF pattern of four taxa under the NMSC

Section 3.3 of CAMUS designs Quartet Filtering (Algorithm 1) for gene trees that evolve down a
level-1 network `N` under the NMSC: on four taxa, keep the most frequent quartet tree, and the
second if the distribution is not "suggestive of an ILS-only scenario"; "the motivation for this
approach is that we do not want to include quartet trees that are not in Q(Nr). On the other hand,
we do not want to eliminate these quartet trees." This presumes a pattern of the quartet CFs on the
four taxa (`Brooqs.RegularPattern`, `Brooqs.Net.RegularOn`): if `N` displays one of the three
quartets on them, it is strictly the most probable and the two others are equally probable; if `N`
displays two, the third is strictly the least probable.

This file proves the pattern for every set of four taxa of a metric network with distinct leaf
labels except in one configuration (`Brooqs.Net.regularOn_of_not_anomalous`): a cycle with two of
the four taxa below its hybrid node and the two others in two other components
(`Brooqs.Net.Anomalous`), where the pattern can fail (`Brooqs.net32_anomaly`). In every
configuration, `N` displays one or two of the three quartets, the two undisplayed quartets have
equal positive CFs when `N` displays one, and the undisplayed quartet is strictly the least probable
when `N` displays two (`Brooqs.Net.weakPattern`).

## Main results

* `Brooqs.Net.quartetCF_pos`: every quartet has a positive CF.
* `Brooqs.Net.DisplaysSplit`, `Brooqs.Net.displays_iff_split`,
  `Brooqs.Net.displaysSplit_iff_of_subnet`: displayed splits, and those of a pair below a cut edge.
* `Brooqs.Net.regularOn_of_pair`, `Brooqs.Net.weakPattern_of_pair`: the pattern for a pair below a
  cut edge.
* `Brooqs.Net.children`, `Brooqs.Net.exists_minimal`: the minimal subnetwork holding at least three
  of the four taxa.
* `Brooqs.Net.Anomalous`: the anomalous configuration.
* `Brooqs.Net.pattern_cases`, `Brooqs.Net.regularOn_of_not_anomalous`, `Brooqs.WeakPattern`,
  `Brooqs.Net.weakPattern`: the pattern.

## Proof

Take the minimal subnetwork `C` holding at least three of the four taxa
(`Brooqs.Net.exists_minimal`); each of its children holds at most two.
* `C` is a tree node: one child holds exactly two of the taxa, which stay together until they meet
  the others at `C` (`Brooqs.Net.tree_pair_bound`).
* `C` is the top node of a cycle and a network hanging from a side holds two of the taxa: they stay
  together along the side (`Brooqs.Net.cycle_pair_bound`).
* `C` is the top node of a cycle and the network below its hybrid node holds two of the taxa, the
  sides at most one each: the anomalous configuration. The two lineages may take different sides at
  the hybrid node.
* Otherwise the four taxa lie in four distinct components of the cycle
  (`Brooqs.Net.Cycle.regularOn_of_components`).
For a pair held by a subnetwork, `N` displays only the quartet of the pair
(`Brooqs.Net.displaysSplit_iff_of_subnet`), the two other quartets have equal CFs by
exchangeability (`Brooqs.Net.splitCF_swap`), and the three CFs add up to `1`
(`Brooqs.Net.splitCF_sum`), so the CF of the pair is the largest iff it exceeds `1/3`.
-/

@[expose] public noncomputable section

namespace Brooqs

open Finset Matrix

universe u

variable {X : Type u} [DecidableEq X]

/-! ### Positivity of the quartet CFs -/

/-- The forest of the singletons of a set of lineages. -/
private abbrev pt_sing (T : Finset (Fin 4)) : Finset (Finset (Fin 4)) := T.image fun l => {l}

private theorem pt_kT_diag_pos (T : Finset (Fin 4)) (t : ℝ) :
    0 < kingmanTransition t (pt_sing T) (pt_sing T) := by
  rw [kingmanTransition_eq_adr11, ADR11.kingmanTransition_apply_self (isGood_singletons T).1]
  exact Real.exp_pos _

private theorem pt_kT_nonneg {t : ℝ} (ht : 0 ≤ t) (F G : Finset (Finset (Fin 4))) :
    0 ≤ kingmanTransition t F G := by
  rw [kingmanTransition_eq_adr11]
  exact ADR11.kingmanTransition_nonneg ht F G

/-- A term of a sum of nonnegative terms bounds it below. -/
private theorem pt_vecMul_ge {μ : Finset (Finset (Fin 4)) → ℝ}
    {M : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ} (hμ : ∀ F, 0 ≤ μ F)
    (hM : ∀ F G, 0 ≤ M F G) (F G : Finset (Finset (Fin 4))) : μ F * M F G ≤ (μ ᵥ* M) G := by
  simp only [vecMul, dotProduct]
  exact single_le_sum (f := fun F => μ F * M F G) (fun F _ => mul_nonneg (hμ F) (hM F G))
    (mem_univ F)

private theorem pt_vecMul_ge_nonneg {μ : Finset (Finset (Fin 4)) → ℝ}
    {M : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ} (hμ : ∀ F, 0 ≤ μ F)
    (hM : ∀ F G, 0 ≤ M F G) (G : Finset (Finset (Fin 4))) : 0 ≤ (μ ᵥ* M) G := by
  simp only [vecMul, dotProduct]
  exact sum_nonneg fun F _ => mul_nonneg (hμ F) (hM F G)

private theorem pt_forestUnion_nonneg {μ ν : Finset (Finset (Fin 4)) → ℝ} (hμ : ∀ F, 0 ≤ μ F)
    (hν : ∀ F, 0 ≤ ν F) (G : Finset (Finset (Fin 4))) : 0 ≤ forestUnion μ ν G :=
  sum_nonneg fun F _ => sum_nonneg fun F' _ => by
    split_ifs
    · exact mul_nonneg (hμ F) (hν F')
    · exact le_rfl

private theorem pt_forestUnion_ge {μ ν : Finset (Finset (Fin 4)) → ℝ} (hμ : ∀ F, 0 ≤ μ F)
    (hν : ∀ F, 0 ≤ ν F) (F F' : Finset (Finset (Fin 4))) :
    μ F * ν F' ≤ forestUnion μ ν (F ∪ F') := by
  unfold forestUnion
  have h1 := single_le_sum (f := fun F'' => if F ∪ F'' = F ∪ F' then μ F * ν F'' else 0)
    (fun F'' _ => by split_ifs <;> [exact mul_nonneg (hμ F) (hν F''); exact le_rfl])
    (mem_univ F')
  simp only [ite_true] at h1
  refine h1.trans (single_le_sum (f := fun F₀ => ∑ F'', if F₀ ∪ F'' = F ∪ F' then
    μ F₀ * ν F'' else 0) (fun F₀ _ => sum_nonneg fun F'' _ => by
      split_ifs <;> [exact mul_nonneg (hμ F₀) (hν F''); exact le_rfl]) (mem_univ F))

private theorem pt_roots_sing (T : Finset (Fin 4)) : roots (pt_sing T) = pt_sing T := by
  refine subset_antisymm (ADR11.roots_subset _) fun A hA =>
    ADR11.mem_roots.2 ⟨hA, fun B hB hAB => ?_⟩
  obtain ⟨l, -, rfl⟩ := mem_image.1 hA
  obtain ⟨m, -, rfl⟩ := mem_image.1 hB
  rw [singleton_subset_singleton.1 hAB]

private theorem pt_sing_union (A B : Finset (Fin 4)) : pt_sing (A ∪ B) = pt_sing A ∪ pt_sing B :=
  image_union _ _

private theorem pt_forestBelow_self (F : Finset (Finset (Fin 4))) : forestBelow F F = F := by
  ext B
  simp only [mem_forestBelow]
  exact ⟨fun h => h.1, fun h => ⟨h, B, h, subset_rfl⟩⟩

private theorem pt_forestBelow_empty (F : Finset (Finset (Fin 4))) : forestBelow F ∅ = ∅ := by
  ext B
  simp [mem_forestBelow]

private theorem pt_lin_leaf (s : Fin 4 → X) (x : X) :
    pt_sing ((Net.leaf x).lin s) = sampledAt s x := by
  unfold Net.lin sampledAt
  congr 1
  ext l
  simp [Net.taxa_leaf]

private theorem pt_lin_tree (s : Fin 4 → X) (ℓ₁ ℓ₂ : ℝ) (N₁ N₂ : Net X) :
    (Net.tree ℓ₁ N₁ ℓ₂ N₂).lin s = N₁.lin s ∪ N₂.lin s := by
  ext l
  simp [Net.lin, Net.taxa_tree]

private theorem pt_lin_cycle (s : Fin 4 → X) (γ ℓ : ℝ) (S₁ S₂ : Side X) (H : Net X) :
    (Net.cycle γ S₁ S₂ ℓ H).lin s = (H.lin s ∪ S₁.lin s) ∪ (∅ ∪ S₂.lin s) := by
  ext l
  simp only [Net.lin, Side.lin, Net.taxa_cycle, mem_filter, mem_univ, true_and, mem_union,
    notMem_empty, false_or]
  tauto

private theorem pt_lin_node (s : Fin 4 → X) (ℓ b : ℝ) (M : Net X) (S : Side X)
    (T : Finset (Fin 4)) :
    T ∪ (Side.node ℓ b M S).lin s = (T ∪ S.lin s) ∪ M.lin s := by
  ext l
  simp only [Side.lin, Net.lin, Side.taxa_node, mem_filter, mem_univ, true_and, mem_union]
  tauto

mutual
/-- With positive probability, no two lineages coalesce below the root of a metric network. -/
private theorem pt_net_pos : ∀ {N : Net X}, N.IsMetric → N.leaves.Nodup →
    ∀ s : Fin 4 → X, 0 < N.forestDist s (pt_sing (N.lin s))
  | .leaf x, _, _, s => by
      simp only [Net.forestDist, pt_lin_leaf, ite_true]
      norm_num
  | .tree ℓ₁ N₁ ℓ₂ N₂, hN, hNn, s => by
      have hNn' : (N₁.leaves ++ N₂.leaves).Nodup := hNn
      have h1 := pt_net_pos hN.2.2.1 (List.nodup_append.1 hNn').1 s
      have h2 := pt_net_pos hN.2.2.2 (List.nodup_append.1 hNn').2.1 s
      have hk1 := pt_vecMul_ge (Net.forestDist_nonneg hN.2.2.1 s) (pt_kT_nonneg hN.1.le)
        (pt_sing (N₁.lin s)) (pt_sing (N₁.lin s))
      have hk2 := pt_vecMul_ge (Net.forestDist_nonneg hN.2.2.2 s) (pt_kT_nonneg hN.2.1.le)
        (pt_sing (N₂.lin s)) (pt_sing (N₂.lin s))
      have d1 := pt_kT_diag_pos (N₁.lin s) ℓ₁
      have d2 := pt_kT_diag_pos (N₂.lin s) ℓ₂
      have hu := pt_forestUnion_ge
        (fun F => pt_vecMul_ge_nonneg (Net.forestDist_nonneg hN.2.2.1 s) (pt_kT_nonneg hN.1.le) F)
        (fun F => pt_vecMul_ge_nonneg (Net.forestDist_nonneg hN.2.2.2 s) (pt_kT_nonneg hN.2.1.le)
          F) (pt_sing (N₁.lin s)) (pt_sing (N₂.lin s))
      rw [pt_lin_tree, pt_sing_union]
      show 0 < forestUnion _ _ _
      exact lt_of_lt_of_le (mul_pos (lt_of_lt_of_le (mul_pos h1 d1) hk1)
        (lt_of_lt_of_le (mul_pos h2 d2) hk2)) hu
  | .cycle γ S₁ S₂ ℓ H, hN, hNn, s => by
      obtain ⟨hγ0, hγ1, hℓ, hS₁, hS₂, hH, -⟩ := hN
      have hNn' : (S₁.leaves ++ S₂.leaves ++ H.leaves).Nodup := hNn
      have h12 : (S₁.leaves ++ S₂.leaves).Nodup := (List.nodup_append.1 hNn').1
      have hS₁n : S₁.leaves.Nodup := (List.nodup_append.1 h12).1
      have hS₂n : S₂.leaves.Nodup := (List.nodup_append.1 h12).2.1
      have hHn : H.leaves.Nodup := (List.nodup_append.1 hNn').2.1
      have dT : Disjoint (S₁.leaves ++ S₂.leaves).toFinset H.leaves.toFinset := by
        rw [disjoint_left]
        intro a ha hb
        exact (List.nodup_append.1 hNn').2.2 a (List.mem_toFinset.1 ha) a
          (List.mem_toFinset.1 hb) rfl
      have dH1 : Disjoint (H.lin s) (S₁.lin s) := disjoint_filter.2 fun l _ h1 h2 =>
        disjoint_left.1 dT (by simp only [Side.taxa, List.mem_toFinset] at h2 ⊢; simp [h2]) h1
      have h0 := pt_net_pos hH hHn s
      have hμ := pt_vecMul_ge (Net.forestDist_nonneg hH s) (pt_kT_nonneg hℓ.le)
        (pt_sing (H.lin s)) (pt_sing (H.lin s))
      have dμ := pt_kT_diag_pos (H.lin s) ℓ
      have hside₁ := pt_side_pos hS₁ hS₁n s (H.lin s) dH1
      have hside₂ := pt_side_pos hS₂ hS₂n s ∅ (disjoint_empty_left _)
      have hU := pt_forestUnion_ge (Side.forestDist_nonneg hS₁ s (pt_sing (H.lin s)))
        (Side.forestDist_nonneg hS₂ s ∅) (pt_sing (H.lin s ∪ S₁.lin s)) (pt_sing (∅ ∪ S₂.lin s))
      have hw : 0 < γ ^ #(roots (pt_sing (H.lin s))) *
          (1 - γ) ^ #(roots (pt_sing (H.lin s)) \ roots (pt_sing (H.lin s))) := by
        rw [sdiff_self, bot_eq_empty, card_empty, pow_zero, mul_one]
        exact pow_pos hγ0 _
      rw [pt_lin_cycle, pt_sing_union]
      show 0 < ∑ F, _
      refine lt_of_lt_of_le ?_ (single_le_sum (f := fun F => (H.forestDist s ᵥ*
          kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset, γ ^ #A * (1 - γ) ^ #(roots F \ A) *
          forestUnion (S₁.forestDist s (forestBelow F A))
            (S₂.forestDist s (forestBelow F (roots F \ A)))
            (pt_sing (H.lin s ∪ S₁.lin s) ∪ pt_sing (∅ ∪ S₂.lin s)))
        (fun F _ => mul_nonneg (pt_vecMul_ge_nonneg (Net.forestDist_nonneg hH s)
          (pt_kT_nonneg hℓ.le) F) (sum_nonneg fun A _ => mul_nonneg (mul_nonneg
            (pow_nonneg hγ0.le _) (pow_nonneg (by linarith) _)) (pt_forestUnion_nonneg
              (Side.forestDist_nonneg hS₁ s _) (Side.forestDist_nonneg hS₂ s _) _)))
        (mem_univ (pt_sing (H.lin s))))
      refine mul_pos (lt_of_lt_of_le (mul_pos h0 dμ) hμ) (lt_of_lt_of_le ?_ (single_le_sum
        (f := fun A => γ ^ #A * (1 - γ) ^ #(roots (pt_sing (H.lin s)) \ A) *
          forestUnion (S₁.forestDist s (forestBelow (pt_sing (H.lin s)) A))
            (S₂.forestDist s (forestBelow (pt_sing (H.lin s)) (roots (pt_sing (H.lin s)) \ A)))
            (pt_sing (H.lin s ∪ S₁.lin s) ∪ pt_sing (∅ ∪ S₂.lin s)))
        (fun A _ => mul_nonneg (mul_nonneg (pow_nonneg hγ0.le _) (pow_nonneg (by linarith) _))
          (pt_forestUnion_nonneg (Side.forestDist_nonneg hS₁ s _)
            (Side.forestDist_nonneg hS₂ s _) _))
        (mem_powerset.2 (subset_refl (roots (pt_sing (H.lin s)))))))
      rw [sdiff_self, bot_eq_empty, pt_forestBelow_empty, pt_roots_sing, pt_forestBelow_self]
      rw [pt_roots_sing] at hw
      rw [sdiff_self, bot_eq_empty] at hw
      refine mul_pos hw (lt_of_lt_of_le (mul_pos hside₁ ?_) hU)
      simpa [pt_sing] using hside₂

/-- With positive probability, no two lineages coalesce along a metric side. -/
private theorem pt_side_pos : ∀ {S : Side X}, S.IsMetric → S.leaves.Nodup →
    ∀ (s : Fin 4 → X) (T : Finset (Fin 4)), Disjoint T (S.lin s) →
      0 < S.forestDist s (pt_sing T) (pt_sing (T ∪ S.lin s))
  | .hyb ℓ, _, _, s, T, _ => by
      have : (Side.hyb ℓ : Side X).lin s = ∅ := by
        ext l
        simp [Side.lin, Side.taxa_hyb]
      rw [this, union_empty]
      exact pt_kT_diag_pos T ℓ
  | .node ℓ b M S, hS, hSn, s, T, hT => by
      obtain ⟨hℓ, hb, hM, hS'⟩ := hS
      have hSn' : (M.leaves ++ S.leaves).Nodup := hSn
      have hMn : M.leaves.Nodup := (List.nodup_append.1 hSn').1
      have hS'n : S.leaves.Nodup := (List.nodup_append.1 hSn').2.1
      have hT' : Disjoint T (S.lin s) := hT.mono_right fun l hl => by
        simp only [Side.lin, mem_filter, mem_univ, true_and, Side.taxa_node, mem_union] at hl ⊢
        exact Or.inr hl
      have h1 := pt_side_pos hS' hS'n s T hT'
      have h2 := pt_net_pos hM hMn s
      have hk2 := pt_vecMul_ge (Net.forestDist_nonneg hM s) (pt_kT_nonneg hb.le)
        (pt_sing (M.lin s)) (pt_sing (M.lin s))
      have d2 := pt_kT_diag_pos (M.lin s) b
      have hu := pt_forestUnion_ge (Side.forestDist_nonneg hS' s (pt_sing T))
        (fun F => pt_vecMul_ge_nonneg (Net.forestDist_nonneg hM s) (pt_kT_nonneg hb.le) F)
        (pt_sing (T ∪ S.lin s)) (pt_sing (M.lin s))
      have hk := pt_vecMul_ge (pt_forestUnion_nonneg (Side.forestDist_nonneg hS' s (pt_sing T))
        (fun F => pt_vecMul_ge_nonneg (Net.forestDist_nonneg hM s) (pt_kT_nonneg hb.le) F))
        (pt_kT_nonneg hℓ.le) (pt_sing (T ∪ S.lin s) ∪ pt_sing (M.lin s))
        (pt_sing (T ∪ S.lin s) ∪ pt_sing (M.lin s))
      have dk := pt_kT_diag_pos ((T ∪ S.lin s) ∪ M.lin s) ℓ
      rw [pt_sing_union] at dk
      rw [pt_lin_node, pt_sing_union]
      show 0 < (forestUnion (S.forestDist s (pt_sing T))
        (M.forestDist s ᵥ* kingmanTransition b) ᵥ* kingmanTransition ℓ) _
      exact lt_of_lt_of_le (mul_pos (lt_of_lt_of_le (mul_pos h1
        (lt_of_lt_of_le (mul_pos h2 d2) hk2)) hu) dk) hk
end

omit [DecidableEq X] in
theorem Net.self_mem_subnets (N : Net X) : N ∈ N.subnets := by
  cases N <;> simp [Net.subnets]

private theorem pt_quartetScore_nonneg (F : Finset (Finset (Fin 4))) : 0 ≤ quartetScore F := by
  unfold quartetScore
  split_ifs <;> norm_num

/-- **Positivity.** Under the NMSC on a metric network with distinct leaf labels, every quartet on
four taxa of the network has a positive CF: with positive probability no two of the four lineages
coalesce below the root, and then each quartet has probability `1/3` above it. -/
theorem Net.quartetCF_pos {N : Net X} (hN : N.WellFormed) {a b c e : X} (ha : a ∈ N.taxa)
    (hb : b ∈ N.taxa) (hc : c ∈ N.taxa) (he : e ∈ N.taxa) : 0 < N.quartetCF a b c e := by
  set s : Fin 4 → X := ![a, b, c, e]
  have hsN : ∀ l, s l ∈ N.taxa := fun l => by fin_cases l <;> assumption
  have hlin : N.lin s = univ := filter_true_of_mem fun l _ => hsN l
  have h3 : 3 ≤ #(univ.filter fun l => s l ∈ N.taxa) := by
    change 3 ≤ #(N.lin s)
    rw [hlin]
    decide
  rw [show N.quartetCF a b c e = N.quartetCF (s 0) (s 1) (s 2) (s 3) from rfl,
    quartetCF_eq_sum_subnet N hN.2 N.self_mem_subnets s hsN h3]
  have hpos := pt_net_pos hN.1 hN.2 s
  rw [hlin] at hpos
  have hq : quartetScore (pt_sing univ) = 1 / 3 := by
    have h1 : ¬(({0, 1} : Finset (Fin 4)) ∈ pt_sing univ ∨
        ({2, 3} : Finset (Fin 4)) ∈ pt_sing univ) := by
      decide
    have h2 : ¬∃ C ∈ pt_sing univ, #C = 2 := by decide
    unfold quartetScore
    rw [ite_eq_right h1, ite_eq_right h2]
  refine lt_of_lt_of_le (by rw [hq]; positivity) (single_le_sum (f := fun F =>
    N.forestDist s F * quartetScore F) (fun F _ => mul_nonneg (Net.forestDist_nonneg hN.1 s F)
      (pt_quartetScore_nonneg F)) (mem_univ (pt_sing univ)))

/-! ### Displayed splits -/

/-- `N` displays the split `A | Aᶜ` of the four lineages sampled by `s`: a displayed tree of `N`
has a cluster whose trace on the four lineages is `A` or `Aᶜ`. -/
def Net.DisplaysSplit (N : Net X) (s : Fin 4 → X) (A : Finset (Fin 4)) : Prop :=
  ∃ K ∈ N.displayed, ∃ C ∈ K,
    (univ.filter fun l => s l ∈ C) = A ∨ (univ.filter fun l => s l ∈ C) = Aᶜ

private theorem pt_pattern : ∀ i j k l : Fin 4, Function.Injective ![i, j, k, l] →
    ∀ P : Finset (Fin 4), (P = {i, j} ↔ i ∈ P ∧ j ∈ P ∧ k ∉ P ∧ l ∉ P) ∧
      (P = {i, j}ᶜ ↔ k ∈ P ∧ l ∈ P ∧ i ∉ P ∧ j ∉ P) := by
  decide

/-- `N` displays the quartet `s i s j | s k s l` iff it displays the split `{i, j}`. -/
theorem Net.displays_iff_split (N : Net X) (s : Fin 4 → X) {i j k l : Fin 4}
    (h : Function.Injective ![i, j, k, l]) :
    N.Displays (s i) (s j) (s k) (s l) ↔ N.DisplaysSplit s {i, j} := by
  simp only [Net.Displays, Net.DisplaysSplit, geneTreeDisplays, decide_eq_true_eq]
  refine exists_congr fun K => and_congr_right fun _ => exists_congr fun C =>
    and_congr_right fun _ => ?_
  obtain ⟨h1, h2⟩ := pt_pattern i j k l h (univ.filter fun m => s m ∈ C)
  simp only [mem_filter, mem_univ, true_and] at h1 h2
  rw [h1, h2]

/-- If a subnetwork `M` of `N` holds exactly the lineages `P` (two of the four), the splits of two
lineages that `N` displays are `P | Pᶜ` only. -/
theorem Net.displaysSplit_iff_of_subnet {N : Net X} (hN : N.leaves.Nodup) {M : Net X}
    (hM : M ∈ N.subnets) {s : Fin 4 → X} {P : Finset (Fin 4)} (hP : #P = 2) (hMP : M.lin s = P)
    {Q : Finset (Fin 4)} (hQ : #Q = 2) : N.DisplaysSplit s Q ↔ Q = P ∨ Q = Pᶜ := by
  have hpat : (univ.filter fun l => s l ∈ M.taxa) = P := hMP
  have hc2 : ∀ A : Finset (Fin 4), #A = 2 → #Aᶜ = 2 := fun A hA => by
    rw [card_compl, hA, Fintype.card_fin]
  constructor
  · rintro ⟨K, hK, C, hC, hCQ⟩
    have htr : #(univ.filter fun l => s l ∈ C) = 2 := by
      rcases hCQ with h | h <;> rw [h]
      · exact hQ
      · exact hc2 Q hQ
    -- the trace of `C` is `P` or `Pᶜ`
    have key : (univ.filter fun l => s l ∈ C) = P ∨ (univ.filter fun l => s l ∈ C) = Pᶜ := by
      rcases Net.compatible_of_mem_subnets hN hM K hK C hC with hsub | hsup | hdis
      · left
        refine eq_of_subset_of_card_le (fun l hl => ?_) (by rw [htr, hP])
        rw [← hpat]
        simp only [mem_filter, mem_univ, true_and] at hl ⊢
        exact hsub hl
      · left
        refine (eq_of_subset_of_card_le (fun l hl => ?_) (by rw [htr, hP])).symm
        rw [← hpat] at hl
        simp only [mem_filter, mem_univ, true_and] at hl ⊢
        exact hsup hl
      · right
        refine eq_of_subset_of_card_le (fun l hl => ?_) (by rw [htr, hc2 P hP])
        rw [mem_compl, ← hpat]
        simp only [mem_filter, mem_univ, true_and] at hl ⊢
        exact fun h => disjoint_left.1 hdis hl h
    rcases hCQ with h | h <;> rcases key with h' | h'
    · exact Or.inl (h.symm.trans h')
    · exact Or.inr (h.symm.trans h')
    · exact Or.inr (by rw [← compl_compl Q, ← h, h'])
    · exact Or.inl (compl_injective (h.symm.trans h'))
  · intro hQP
    obtain ⟨K, hK⟩ := List.exists_mem_of_ne_nil _ (Net.displayed_ne_nil N)
    refine ⟨K, hK, M.taxa, Net.taxa_mem_of_mem_subnets hM K hK, ?_⟩
    rw [hpat]
    rcases hQP with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (compl_compl _).symm

/-! ### The pattern for a pair below a cut edge -/

/-- The splits of the three quartets `ab|ce`, `ac|be`, `ae|bc` of `Brooqs.Net.cf3`. -/
def splitOf3 : Fin 3 → Finset (Fin 4) := ![{0, 1}, {0, 2}, {0, 3}]

theorem Net.cf3_eq_splitCF (N : Net X) (s : Fin 4 → X) (u : Fin 3) :
    N.cf3 (s 0) (s 1) (s 2) (s 3) u = N.splitCF s (splitOf3 u) := by
  fin_cases u
  · exact N.quartetCF_eq_splitCF_of s (i := 0) (j := 1) (k := 2) (l := 3) (by decide)
  · exact N.quartetCF_eq_splitCF_of s (i := 0) (j := 2) (k := 1) (l := 3) (by decide)
  · exact N.quartetCF_eq_splitCF_of s (i := 0) (j := 3) (k := 1) (l := 2) (by decide)

theorem Net.disp3_iff_split (N : Net X) (s : Fin 4 → X) (u : Fin 3) :
    N.disp3 (s 0) (s 1) (s 2) (s 3) u ↔ N.DisplaysSplit s (splitOf3 u) := by
  fin_cases u
  · exact N.displays_iff_split s (i := 0) (j := 1) (k := 2) (l := 3) (by decide)
  · exact N.displays_iff_split s (i := 0) (j := 2) (k := 1) (l := 3) (by decide)
  · exact N.displays_iff_split s (i := 0) (j := 3) (k := 1) (l := 2) (by decide)

private theorem pt_pair_facts : ∀ i j : Fin 4, i ≠ j →
    (∃ t : Fin 3, (splitOf3 t = {i, j} ∨ splitOf3 t = {i, j}ᶜ) ∧
      ∀ u : Fin 3, (splitOf3 u = {i, j} ∨ splitOf3 u = {i, j}ᶜ) → u = t) ∧
    ∀ u u' : Fin 3, ¬(splitOf3 u = {i, j} ∨ splitOf3 u = {i, j}ᶜ) →
      ¬(splitOf3 u' = {i, j} ∨ splitOf3 u' = {i, j}ᶜ) →
      u = u' ∨ (splitOf3 u').map (Equiv.swap i j).toEmbedding = splitOf3 u ∨
        (splitOf3 u').map (Equiv.swap i j).toEmbedding = (splitOf3 u)ᶜ := by
  decide

private theorem pt_card_split : ∀ u : Fin 3, #(splitOf3 u) = 2 := by decide

private theorem pt_sum3 (f : Fin 3 → ℝ) : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
    f a + f b + f c = f 0 + f 1 + f 2 := by
  intro a b c hab hac hbc
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all <;> ring

private theorem pt_other : ∀ a b : Fin 3, ∃ u : Fin 3, u ≠ a ∧ u ≠ b := by
  decide

/-- **A pair below a cut edge.** If a subnetwork `M` of `N` holds exactly the lineages `i` and `j`
of the four, the split `{i, j}` has CF above `1/3`, then the four taxa have the pattern that
Quartet Filtering presumes: `N` displays only the quartet of the split `{i, j}`, the two other
quartets have equal CFs (exchangeability, `Brooqs.Net.splitCF_swap`), hence each
`(1 - CF)/2 < 1/3`. -/
theorem Net.regularOn_of_pair {N : Net X} (hN : N.WellFormed) {s : Fin 4 → X}
    (hsN : ∀ l, s l ∈ N.taxa) {M : Net X} (hM : M ∈ N.subnets) {i j : Fin 4} (hij : i ≠ j)
    (hMP : M.lin s = {i, j}) (hgt : 1 / 3 < N.splitCF s {i, j}) :
    N.RegularOn (s 0) (s 1) (s 2) (s 3) := by
  obtain ⟨⟨t, ht, htu⟩, hcross⟩ := pt_pair_facts i j hij
  have hP2 : #({i, j} : Finset (Fin 4)) = 2 := card_pair hij
  have hdisp : ∀ u, N.disp3 (s 0) (s 1) (s 2) (s 3) u ↔
      (splitOf3 u = {i, j} ∨ splitOf3 u = {i, j}ᶜ) := fun u => by
    rw [Net.disp3_iff_split]
    exact Net.displaysSplit_iff_of_subnet hN.2 hM hP2 hMP (pt_card_split u)
  have hin : ∀ l, s l ∈ M.taxa ↔ l = i ∨ l = j := fun l => by
    have : l ∈ M.lin s ↔ l ∈ ({i, j} : Finset (Fin 4)) := by rw [hMP]
    simpa [Net.lin] using this
  have hcf : ∀ u, N.cf3 (s 0) (s 1) (s 2) (s 3) u = N.splitCF s (splitOf3 u) :=
    Net.cf3_eq_splitCF N s
  have hcft : N.cf3 (s 0) (s 1) (s 2) (s 3) t = N.splitCF s {i, j} := by
    rw [hcf]
    rcases ht with h | h
    · rw [h]
    · rw [h, Net.splitCF_compl]
  -- the two other quartets have equal CFs
  have heq : ∀ u u', u ≠ t → u' ≠ t →
      N.cf3 (s 0) (s 1) (s 2) (s 3) u = N.cf3 (s 0) (s 1) (s 2) (s 3) u' := by
    intro u u' hu hu'
    rcases hcross u u' (fun h => hu (htu u h)) (fun h => hu' (htu u' h)) with rfl | h | h
    · rfl
    · rw [hcf, hcf, ← h, Net.splitCF_swap hN.2 hM hsN hin]
    · rw [hcf, hcf, ← Net.splitCF_compl, ← h, Net.splitCF_swap hN.2 hM hsN hin]
  have hsum : N.cf3 (s 0) (s 1) (s 2) (s 3) 0 + N.cf3 (s 0) (s 1) (s 2) (s 3) 1 +
      N.cf3 (s 0) (s 1) (s 2) (s 3) 2 = 1 := by
    rw [hcf, hcf, hcf]
    exact Net.splitCF_sum hN.2 hsN
  refine Or.inl ⟨t, (hdisp t).2 ht, fun u hu hd => hu (htu u ((hdisp u).1 hd)), fun u hu => ?_,
    heq, fun u => ?_⟩
  · -- the two others share `1 - CF(t)`, so each is below `1/3 < CF(t)`
    obtain ⟨u', hu't, hu'u⟩ := pt_other t u
    have h3 := pt_sum3 (N.cf3 (s 0) (s 1) (s 2) (s 3)) t u u' (Ne.symm hu) (Ne.symm hu't)
      (Ne.symm hu'u)
    rw [hsum, heq u' u hu't hu, hcft] at h3
    rw [hcft]
    linarith
  · fin_cases u <;> exact Net.quartetCF_pos hN (hsN _) (hsN _) (hsN _) (hsN _)

/-- The part of `Brooqs.RegularPattern` that holds for every network: if the network displays one
quartet, the two others have equal positive CFs; if it displays two, the third is strictly the
least probable. The strict inequality for one displayed quartet is missing. -/
def WeakPattern (disp : Fin 3 → Prop) (cf : Fin 3 → ℝ) : Prop :=
  (∃ s₁, disp s₁ ∧ (∀ s, s ≠ s₁ → ¬ disp s) ∧
      (∀ s s', s ≠ s₁ → s' ≠ s₁ → cf s = cf s') ∧ ∀ s, 0 < cf s) ∨
  (∃ s₃, ¬ disp s₃ ∧ (∀ s, s ≠ s₃ → disp s) ∧ ∀ s, s ≠ s₃ → cf s₃ < cf s)

theorem RegularPattern.weak {disp : Fin 3 → Prop} {cf : Fin 3 → ℝ}
    (h : RegularPattern disp cf) : WeakPattern disp cf := by
  rcases h with ⟨s₁, h1, h2, -, h4, h5⟩ | h
  · exact Or.inl ⟨s₁, h1, h2, h4, h5⟩
  · exact Or.inr h

/-- **A pair below a cut edge, without the bound.** If a subnetwork `M` of `N` holds exactly the
lineages `i` and `j`, `N` displays only the quartet of the split `{i, j}`, and the two other
quartets have equal positive CFs. -/
theorem Net.weakPattern_of_pair {N : Net X} (hN : N.WellFormed) {s : Fin 4 → X}
    (hsN : ∀ l, s l ∈ N.taxa) {M : Net X} (hM : M ∈ N.subnets) {i j : Fin 4} (hij : i ≠ j)
    (hMP : M.lin s = {i, j}) :
    WeakPattern (N.disp3 (s 0) (s 1) (s 2) (s 3)) (N.cf3 (s 0) (s 1) (s 2) (s 3)) := by
  obtain ⟨⟨t, ht, htu⟩, hcross⟩ := pt_pair_facts i j hij
  have hP2 : #({i, j} : Finset (Fin 4)) = 2 := card_pair hij
  have hdisp : ∀ u, N.disp3 (s 0) (s 1) (s 2) (s 3) u ↔
      (splitOf3 u = {i, j} ∨ splitOf3 u = {i, j}ᶜ) := fun u => by
    rw [Net.disp3_iff_split]
    exact Net.displaysSplit_iff_of_subnet hN.2 hM hP2 hMP (pt_card_split u)
  have hin : ∀ l, s l ∈ M.taxa ↔ l = i ∨ l = j := fun l => by
    have : l ∈ M.lin s ↔ l ∈ ({i, j} : Finset (Fin 4)) := by rw [hMP]
    simpa [Net.lin] using this
  have hcf : ∀ u, N.cf3 (s 0) (s 1) (s 2) (s 3) u = N.splitCF s (splitOf3 u) :=
    Net.cf3_eq_splitCF N s
  refine Or.inl ⟨t, (hdisp t).2 ht, fun u hu hd => hu (htu u ((hdisp u).1 hd)),
    fun u u' hu hu' => ?_, fun u => ?_⟩
  · rcases hcross u u' (fun h => hu (htu u h)) (fun h => hu' (htu u' h)) with rfl | h | h
    · rfl
    · rw [hcf, hcf, ← h, Net.splitCF_swap hN.2 hM hsN hin]
    · rw [hcf, hcf, ← Net.splitCF_compl, ← h, Net.splitCF_swap hN.2 hM hsN hin]
  · fin_cases u <;> exact Net.quartetCF_pos hN (hsN _) (hsN _) (hsN _) (hsN _)

/-! ### The minimal subnetwork holding three of the four taxa -/

/-- The children of a network: the networks below the cut edges at its root (the two children of
a tree node; the network below the hybrid node and the networks hanging from the sides of a
cycle). -/
def Net.children : Net X → List (Net X)
  | .leaf _ => []
  | .tree _ N₁ _ N₂ => [N₁, N₂]
  | .cycle _ S₁ S₂ _ H => H :: (S₁.nodes.map (·.2.2) ++ S₂.nodes.map (·.2.2))

omit [DecidableEq X] in
private theorem pt_pendant_mem_subnets : ∀ {S : Side X} {n : ℝ × ℝ × Net X}, n ∈ S.nodes →
    n.2.2 ∈ S.subnets
  | .hyb _, n, hn => by simp [Side.nodes] at hn
  | .node ℓ b M S, n, hn => by
      simp only [Side.nodes, List.mem_cons] at hn
      simp only [Side.subnets, List.mem_append]
      rcases hn with rfl | hn
      · exact Or.inl M.self_mem_subnets
      · exact Or.inr (pt_pendant_mem_subnets hn)

omit [DecidableEq X] in
mutual
/-- A subnetwork of a subnetwork is a subnetwork. -/
theorem Net.mem_subnets_trans : ∀ {N C D : Net X}, C ∈ N.subnets → D ∈ C.subnets →
    D ∈ N.subnets
  | .leaf _, C, D, hC, hD => by
      simp only [Net.subnets, List.mem_singleton] at hC
      subst hC
      exact hD
  | .tree ℓ₁ N₁ ℓ₂ N₂, C, D, hC, hD => by
      simp only [Net.subnets, List.mem_cons, List.mem_append] at hC ⊢
      rcases hC with rfl | hC | hC
      · simpa [Net.subnets] using hD
      · exact Or.inr (Or.inl (Net.mem_subnets_trans hC hD))
      · exact Or.inr (Or.inr (Net.mem_subnets_trans hC hD))
  | .cycle γ S₁ S₂ ℓ H, C, D, hC, hD => by
      simp only [Net.subnets, List.mem_cons, List.mem_append] at hC ⊢
      rcases hC with rfl | (hC | hC) | hC
      · simp only [Net.subnets, List.mem_cons, List.mem_append] at hD
        exact hD
      · exact Or.inr (Or.inl (Or.inl (Side.mem_subnets_trans hC hD)))
      · exact Or.inr (Or.inl (Or.inr (Side.mem_subnets_trans hC hD)))
      · exact Or.inr (Or.inr (Net.mem_subnets_trans hC hD))

/-- The same for the networks hanging from a side. -/
theorem Side.mem_subnets_trans : ∀ {S : Side X} {C D : Net X}, C ∈ S.subnets → D ∈ C.subnets →
    D ∈ S.subnets
  | .hyb _, C, D, hC, _ => by simp [Side.subnets] at hC
  | .node ℓ b M S, C, D, hC, hD => by
      simp only [Side.subnets, List.mem_append] at hC ⊢
      rcases hC with hC | hC
      · exact Or.inl (Net.mem_subnets_trans hC hD)
      · exact Or.inr (Side.mem_subnets_trans hC hD)
end

omit [DecidableEq X] in
theorem Net.mem_subnets_of_mem_children {N D : Net X} (hD : D ∈ N.children) :
    D ∈ N.subnets := by
  cases N with
  | leaf x => simp [Net.children] at hD
  | tree ℓ₁ N₁ ℓ₂ N₂ =>
      simp only [Net.children, List.mem_cons, List.not_mem_nil, or_false] at hD
      simp only [Net.subnets, List.mem_cons, List.mem_append]
      rcases hD with rfl | rfl
      · exact Or.inr (Or.inl D.self_mem_subnets)
      · exact Or.inr (Or.inr D.self_mem_subnets)
  | cycle γ S₁ S₂ ℓ H =>
      simp only [Net.children, List.mem_cons, List.mem_append, List.mem_map] at hD
      simp only [Net.subnets, List.mem_cons, List.mem_append]
      rcases hD with rfl | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
      · exact Or.inr (Or.inr D.self_mem_subnets)
      · exact Or.inr (Or.inl (Or.inl (pt_pendant_mem_subnets hn)))
      · exact Or.inr (Or.inl (Or.inr (pt_pendant_mem_subnets hn)))

omit [DecidableEq X] in
private theorem pt_leaves_ne_nil : ∀ N : Net X, N.leaves ≠ []
  | .leaf _ => by simp [Net.leaves]
  | .tree _ N₁ _ _ => by simp [Net.leaves, pt_leaves_ne_nil N₁]
  | .cycle _ _ _ _ N => by simp [Net.leaves, pt_leaves_ne_nil N]

omit [DecidableEq X] in
private theorem pt_pendant_length {S : Side X} {n : ℝ × ℝ × Net X} (hn : n ∈ S.nodes) :
    n.2.2.leaves.length ≤ S.leaves.length :=
  (Side.leaves_sublist_of_mem_subnets (pt_pendant_mem_subnets hn)).length_le

omit [DecidableEq X] in
/-- The children of a metric network have fewer leaves. -/
theorem Net.length_lt_of_mem_children {N D : Net X} (hN : N.IsMetric) (hD : D ∈ N.children) :
    D.leaves.length < N.leaves.length := by
  cases N with
  | leaf x => simp [Net.children] at hD
  | tree ℓ₁ N₁ ℓ₂ N₂ =>
      simp only [Net.children, List.mem_cons, List.not_mem_nil, or_false] at hD
      have h1 := List.length_pos_of_ne_nil (pt_leaves_ne_nil N₁)
      have h2 := List.length_pos_of_ne_nil (pt_leaves_ne_nil N₂)
      simp only [Net.leaves, List.length_append]
      rcases hD with rfl | rfl <;> omega
  | cycle γ S₁ S₂ ℓ H =>
      obtain ⟨-, -, -, -, -, -, hnodes⟩ := hN
      have hH := List.length_pos_of_ne_nil (pt_leaves_ne_nil H)
      simp only [Net.children, List.mem_cons, List.mem_append, List.mem_map] at hD
      simp only [Net.leaves, List.length_append]
      rcases hD with rfl | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
      · -- one side has a node, whose network has a leaf
        rcases hnodes with h | h <;>
        · obtain ⟨n, hn⟩ := List.exists_mem_of_ne_nil _ h
          have := List.length_pos_of_ne_nil (pt_leaves_ne_nil n.2.2)
          have := pt_pendant_length hn
          omega
      · have := pt_pendant_length hn
        omega
      · have := pt_pendant_length hn
        omega

/-- **The minimal subnetwork.** If at least three of the four lineages are sampled from the taxa
of a metric network `N`, some subnetwork holds at least three of them while each of its children
holds at most two. -/
theorem Net.exists_minimal {N : Net X} (hN : N.IsMetric) (s : Fin 4 → X)
    (h3 : 3 ≤ #(N.lin s)) :
    ∃ C ∈ N.subnets, 3 ≤ #(C.lin s) ∧ ∀ D ∈ C.children, #(D.lin s) ≤ 2 := by
  classical
  have hex : ∃ n, ∃ C ∈ N.subnets, 3 ≤ #(C.lin s) ∧ C.leaves.length = n :=
    ⟨_, N, N.self_mem_subnets, h3, rfl⟩
  obtain ⟨C, hC, hC3, hCn⟩ := Nat.find_spec hex
  refine ⟨C, hC, hC3, fun D hD => ?_⟩
  by_contra hlt
  have hDlt := Net.length_lt_of_mem_children (Net.isMetric_of_mem_subnets hC hN) hD
  rw [hCn] at hDlt
  exact Nat.find_min hex hDlt ⟨D, Net.mem_subnets_trans hC (Net.mem_subnets_of_mem_children hD),
    by omega, rfl⟩

/-! ### The pattern -/

private theorem pt_lin_disjoint {s : Fin 4 → X} {A B : Finset X} (h : Disjoint A B) :
    Disjoint (univ.filter fun l => s l ∈ A) (univ.filter fun l => s l ∈ B) :=
  disjoint_filter.2 fun _ _ ha hb => disjoint_left.1 h ha hb

private theorem pt_disjoint_toFinset {l₁ l₂ : List X} (h : (l₁ ++ l₂).Nodup) :
    Disjoint l₁.toFinset l₂.toFinset := by
  rw [disjoint_left]
  intro a ha hb
  exact (List.nodup_append.1 h).2.2 a (List.mem_toFinset.1 ha) a (List.mem_toFinset.1 hb) rfl

omit [DecidableEq X] in
/-- The edges above the nodes of a metric side have positive lengths. -/
private theorem pt_side_nodes_pos : ∀ {S : Side X}, S.IsMetric → ∀ {n : ℝ × ℝ × Net X},
    n ∈ S.nodes → 0 < n.1 ∧ 0 < n.2.1
  | .hyb _, _, n, hn => by simp [Side.nodes] at hn
  | .node ℓ b M S, hS, n, hn => by
      simp only [Side.nodes, List.mem_cons] at hn
      rcases hn with rfl | hn
      · exact ⟨hS.1, hS.2.1⟩
      · exact pt_side_nodes_pos hS.2.2.2 hn

private theorem pt_perm : ∀ i j : Fin 4, i ≠ j →
    ((Equiv.swap 0 i) * (Equiv.swap 1 ((Equiv.swap 0 i) j))) 0 = i ∧
      ((Equiv.swap 0 i) * (Equiv.swap 1 ((Equiv.swap 0 i) j))) 1 = j := by
  decide

/-- Relabelling a pair to the lineages `0, 1`: if the expected score at a subnetwork `C` holding at
least three of the lineages exceeds `1/3` whenever a subnetwork `M` holds exactly the lineages
`0, 1`, then the split CF of the pair that `M` holds exceeds `1/3`. -/
private theorem pt_pair_gt {N : Net X} (hN : N.leaves.Nodup) {s : Fin 4 → X}
    (hsN : ∀ l, s l ∈ N.taxa) {C M : Net X} (hC : C ∈ N.subnets) (hC3 : 3 ≤ #(C.lin s))
    {i j : Fin 4} (hij : i ≠ j) (hMP : M.lin s = {i, j})
    (hb : ∀ s' : Fin 4 → X, M.lin s' = {0, 1} → 1 / 3 < expectedScore (C.forestDist s')) :
    1 / 3 < N.splitCF s {i, j} := by
  obtain ⟨σ, h0, h1⟩ : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := ⟨_, pt_perm i j hij⟩
  set s' := s ∘ σ
  have hlin' : ∀ T : Net X, T.lin s' = (T.lin s).map σ.symm.toEmbedding := fun T => by
    ext l
    simp only [Net.lin, mem_filter, mem_univ, true_and, mem_map_equiv, Equiv.symm_symm, s',
      Function.comp_apply]
  have hM' : M.lin s' = {0, 1} := by
    rw [hlin', hMP]
    ext l
    simp only [mem_map_equiv, Equiv.symm_symm, mem_insert, mem_singleton]
    rw [← h0, ← h1, σ.injective.eq_iff, σ.injective.eq_iff]
  have hC3' : 3 ≤ #(univ.filter fun l => s' l ∈ C.taxa) := by
    change 3 ≤ #(C.lin s')
    rw [hlin', card_map]
    exact hC3
  have hsN' : ∀ l, s' l ∈ N.taxa := fun l => hsN _
  have hsplit : N.splitCF s {i, j} = N.quartetCF (s' 0) (s' 1) (s' 2) (s' 3) := by
    have hs' : ![s' 0, s' 1, s' 2, s' 3] = s' := by
      funext m
      fin_cases m <;> rfl
    rw [Net.quartetCF_eq_splitCF, hs', Net.splitCF_comp]
    congr 1
    ext l
    simp only [mem_map_equiv, mem_insert, mem_singleton, Equiv.symm_apply_eq, h0, h1]
  rw [hsplit, quartetCF_eq_sum_subnet N hN hC s' hsN' hC3']
  exact hb s' hM'

/-- **The anomalous configuration** of the four taxa sampled by `s`: a cycle `Ω` of `N` has exactly
two of them below its hybrid node, at least three below its top node, and at most one in each
network hanging from its sides. The four taxa then induce a 3₂-cycle in the terms of Ané, Fogg,
Allman, Baños and Rhodes (2024): two of them below the hybrid node of a 3-cycle, the two others in
two other components. (`Brooqs.net32_anomaly` shows that the CF pattern can fail there.) -/
def Net.Anomalous (N : Net X) (s : Fin 4 → X) : Prop :=
  ∃ Ω : N.Cycle, #(Ω.below.lin s) = 2 ∧ 3 ≤ #(Ω.top.lin s) ∧
    ∀ n ∈ Ω.side₁.nodes ++ Ω.side₂.nodes, #(n.2.2.lin s) ≤ 1

/-- Every taxon of `N` lies in a component of each cycle. -/
theorem Net.Cycle.exists_component {N : Net X} (Ω : N.Cycle) {t : X}
    (ht : t ∈ N.taxa) : ∃ i < Ω.size, t ∈ Ω.component i := by
  have hsz := Ω.size_ge
  by_cases htop : t ∈ Ω.top.taxa
  · have htaxa : Ω.top.taxa = Ω.side₁.taxa ∪ Ω.side₂.taxa ∪ Ω.below.taxa :=
      Net.taxa_cycle _ _ _ _ _
    rw [htaxa, mem_union, mem_union] at htop
    rcases htop with (h | h) | h
    · obtain ⟨n, hn, htn⟩ := Side.mem_taxa_iff.1 h
      obtain ⟨j, hj, hjn⟩ := Ω.exists_component_of_mem_nodes (Or.inl hn)
      exact ⟨j, hj, hjn ▸ htn⟩
    · obtain ⟨n, hn, htn⟩ := Side.mem_taxa_iff.1 h
      obtain ⟨j, hj, hjn⟩ := Ω.exists_component_of_mem_nodes (Or.inr hn)
      exact ⟨j, hj, hjn ▸ htn⟩
    · exact ⟨0, by omega, Ω.component_zero ▸ h⟩
  · have hne : Ω.top ≠ N := fun h => htop (by rw [h]; exact ht)
    refine ⟨Ω.side₁.nodes.length + 1, by rw [Ω.size_of_top_ne hne]; omega, ?_⟩
    rw [Ω.component_root hne]
    exact mem_sdiff.2 ⟨ht, htop⟩

private theorem pt_two_le {A : Finset X} {s : Fin 4 → X} {l l' : Fin 4} (hll' : l ≠ l')
    (hl : s l ∈ A) (hl' : s l' ∈ A) : 2 ≤ #(univ.filter fun m => s m ∈ A) := by
  rw [← card_pair hll']
  exact card_le_card fun m hm => by
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl <;> simpa

/-- The cases of the pattern: the four taxa have the pattern `Brooqs.Net.RegularOn`, or they are in
the anomalous configuration, with two of them held by a subnetwork (below the hybrid node of a
cycle).

The proof takes the minimal subnetwork `C` holding at least three of the four taxa
(`Brooqs.Net.exists_minimal`). If a child of `C` holds two of them, they stay together until they
meet a third lineage, and their CF exceeds `1/3` (`Brooqs.Net.tree_pair_bound`,
`Brooqs.Net.cycle_pair_bound`), unless they lie below the hybrid node of a cycle with the two
others in two other components, the anomalous configuration; otherwise the four taxa lie in four
distinct components of a cycle (`Brooqs.Net.Cycle.regularOn_of_components`). -/
theorem Net.pattern_cases {N : Net X} (hN : N.WellFormed) {s : Fin 4 → X}
    (hs : Function.Injective s) (hsN : ∀ l, s l ∈ N.taxa) :
    N.RegularOn (s 0) (s 1) (s 2) (s 3) ∨
      (N.Anomalous s ∧ ∃ M ∈ N.subnets, ∃ i j, i ≠ j ∧ M.lin s = {i, j}) := by
  have hlinN : N.lin s = univ := filter_true_of_mem fun l _ => hsN l
  obtain ⟨C, hC, hC3, hch⟩ := Net.exists_minimal hN.1 s (by rw [hlinN]; decide)
  have hCm := Net.isMetric_of_mem_subnets hC hN.1
  have hCn : C.leaves.Nodup := (Net.leaves_sublist_of_mem_subnets hC).nodup hN.2
  -- a pair in a child of `C`, with the bound on the expected score at `C`
  have hpair : ∀ {M : Net X}, M ∈ C.children → #(M.lin s) = 2 →
      (∀ s' : Fin 4 → X, M.lin s' = {0, 1} → 1 / 3 < expectedScore (C.forestDist s')) →
      N.RegularOn (s 0) (s 1) (s 2) (s 3) ∨
        (N.Anomalous s ∧ ∃ M ∈ N.subnets, ∃ i j, i ≠ j ∧ M.lin s = {i, j}) := by
    intro M hM hM2 hb
    obtain ⟨i, j, hij, hMij⟩ := card_eq_two.1 hM2
    exact Or.inl (Net.regularOn_of_pair hN hsN (Net.mem_subnets_trans hC
      (Net.mem_subnets_of_mem_children hM)) hij hMij (pt_pair_gt hN.2 hsN hC hC3 hij hMij hb))
  have hexp : ∀ {t : ℝ}, 0 < t → 1 / 3 < 1 / 3 + 2 / 3 * (1 - Real.exp (-t)) := fun ht => by
    have := Real.exp_lt_one_iff.2 (neg_neg_of_pos ht)
    linarith
  cases C with
  | leaf x =>
      -- a leaf holds at most one lineage
      exfalso
      have : #((Net.leaf x).lin s) ≤ 1 := card_le_one.2 fun a ha b hb => by
        simp only [Net.lin, Net.taxa_leaf, mem_filter, mem_singleton, mem_univ, true_and] at ha hb
        exact hs (ha.trans hb.symm)
      omega
  | tree ℓ₁ C₁ ℓ₂ C₂ =>
      obtain ⟨hℓ₁, hℓ₂, hC₁m, hC₂m⟩ := hCm
      have hCn' : (C₁.leaves ++ C₂.leaves).Nodup := hCn
      have hd : Disjoint (C₁.lin s) (C₂.lin s) := pt_lin_disjoint (pt_disjoint_toFinset hCn')
      have hcard : #((Net.tree ℓ₁ C₁ ℓ₂ C₂).lin s) = #(C₁.lin s) + #(C₂.lin s) := by
        rw [pt_lin_tree, card_union_of_disjoint hd]
      have h1 := hch C₁ (by simp [Net.children])
      have h2 := hch C₂ (by simp [Net.children])
      by_cases hc1 : #(C₁.lin s) = 2
      · exact hpair (by simp [Net.children]) hc1 fun s' hs' =>
          lt_of_lt_of_le (hexp hℓ₁) (Net.tree_pair_bound s' ⟨hℓ₁, hℓ₂, hC₁m, hC₂m⟩ hCn hs')
      · have hc2 : #(C₂.lin s) = 2 := by omega
        exact hpair (by simp [Net.children]) hc2 fun s' hs' =>
          lt_of_lt_of_le (hexp hℓ₂) (Net.tree_pair_bound' s' ⟨hℓ₁, hℓ₂, hC₁m, hC₂m⟩ hCn hs')
  | cycle γ S₁ S₂ ℓ H =>
      set Ω : N.Cycle := ⟨γ, S₁, S₂, ℓ, H, hC⟩
      have hpend : ∀ n ∈ S₁.nodes ++ S₂.nodes, n.2.2 ∈ (Net.cycle γ S₁ S₂ ℓ H).children :=
        fun n hn => by
          simp only [Net.children, List.mem_cons, List.mem_append, List.mem_map] at hn ⊢
          rcases hn with hn | hn
          · exact Or.inr (Or.inl ⟨n, hn, rfl⟩)
          · exact Or.inr (Or.inr ⟨n, hn, rfl⟩)
      by_cases hp2 : ∃ n ∈ S₁.nodes ++ S₂.nodes, #(n.2.2.lin s) = 2
      · -- a pair hangs from a side of the cycle
        obtain ⟨n, hn, hn2⟩ := hp2
        refine hpair (hpend n hn) hn2 fun s' hs' => lt_of_lt_of_le (hexp ?_)
          (Net.cycle_pair_bound s' hCm hCn n (List.mem_append.1 hn) hs')
        obtain ⟨-, -, -, hS₁, hS₂, -, -⟩ := hCm
        rcases List.mem_append.1 hn with hn | hn
        · exact (pt_side_nodes_pos hS₁ hn).2
        · exact (pt_side_nodes_pos hS₂ hn).2
      · have hle1 : ∀ n ∈ S₁.nodes ++ S₂.nodes, #(n.2.2.lin s) ≤ 1 := fun n hn => by
          have ha : #(n.2.2.lin s) ≤ 2 := hch n.2.2 (hpend n hn)
          have hb : #(n.2.2.lin s) ≠ 2 := fun h => hp2 ⟨n, hn, h⟩
          omega
        by_cases hH2 : #(H.lin s) = 2
        · -- the anomalous configuration
          obtain ⟨i, j, hij, hHij⟩ := card_eq_two.1 hH2
          exact Or.inr ⟨⟨Ω, hH2, hC3, hle1⟩, H, Net.mem_subnets_trans hC
            (Net.mem_subnets_of_mem_children (by simp [Net.children])), i, j, hij, hHij⟩
        · -- four distinct components
          have hH1 : #(Ω.below.lin s) ≤ 1 := by
            have := hch H (by simp [Net.children])
            change #(H.lin s) ≤ 1
            omega
          choose pos hlt hpos using fun l => Ω.exists_component (hsN l)
          refine Or.inl (Ω.regularOn_of_components hN (pos := pos) (fun l l' hll' => ?_) hlt hpos)
          by_contra hne
          by_cases hb : s l ∈ Ω.below.taxa
          · have h0 := (Ω.mem_below_iff hN.2 (hpos l)).1 hb
            have hb' : s l' ∈ Ω.below.taxa := (Ω.mem_below_iff hN.2 (hpos l')).2 (hll' ▸ h0)
            have := pt_two_le hne hb hb'
            change 2 ≤ #(Ω.below.lin s) at this
            omega
          by_cases hside : s l ∈ Ω.side₁.taxa ∨ s l ∈ Ω.side₂.taxa
          · obtain ⟨n, hn, htn⟩ : ∃ n ∈ Ω.side₁.nodes ++ Ω.side₂.nodes, s l ∈ n.2.2.taxa := by
              rcases hside with h | h
              · obtain ⟨n, hn, htn⟩ := Side.mem_taxa_iff.1 h
                exact ⟨n, List.mem_append_left _ hn, htn⟩
              · obtain ⟨n, hn, htn⟩ := Side.mem_taxa_iff.1 h
                exact ⟨n, List.mem_append_right _ hn, htn⟩
            obtain ⟨j, -, hj⟩ := Ω.exists_component_of_mem_nodes (List.mem_append.1 hn)
            have hjl := Ω.eq_of_mem_component hN.2 (hpos l) (hj ▸ htn)
            have htn' : s l' ∈ n.2.2.taxa := hj ▸ hjl ▸ hll' ▸ hpos l'
            have := pt_two_le hne htn htn'
            have := hle1 n hn
            change 2 ≤ #(n.2.2.lin s) at *
            omega
          · -- both lie outside the cycle, in the component of the root
            have hnt : s l ∉ Ω.top.taxa := by
              have htaxa : Ω.top.taxa = Ω.side₁.taxa ∪ Ω.side₂.taxa ∪ Ω.below.taxa :=
                Net.taxa_cycle _ _ _ _ _
              rw [htaxa, mem_union, mem_union]
              tauto
            have h1 := (Ω.mem_top_iff hN.2 (hlt l) (hpos l)).not.1 hnt
            have hnt' : s l' ∉ Ω.top.taxa := fun h =>
              h1 ((Ω.mem_top_iff hN.2 (hlt l') (hpos l')).1 h |>.imp id (fun h' => hll' ▸ h'))
            have hsub : Ω.top.lin s ⊆ univ \ {l, l'} := fun m hm => by
              simp only [Net.lin, mem_filter, mem_univ, true_and] at hm
              simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton]
              rintro (rfl | rfl)
              · exact hnt hm
              · exact hnt' hm
            have := card_le_card hsub
            rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
              card_pair hne] at this
            change 3 ≤ #(Ω.top.lin s) at hC3
            omega

/-- **The CF pattern of Section 3.3.** Under the NMSC on a metric network `N` with distinct leaf
labels, four distinct taxa of `N` that are not in the anomalous configuration
(`Brooqs.Net.Anomalous`) have the pattern that Quartet Filtering presumes (`Brooqs.Net.RegularOn`):
if `N` displays one of the three quartets on them, it is strictly the most probable and the two
others are equally probable; if it displays two, the third is strictly the least probable. -/
theorem Net.regularOn_of_not_anomalous {N : Net X} (hN : N.WellFormed) {s : Fin 4 → X}
    (hs : Function.Injective s) (hsN : ∀ l, s l ∈ N.taxa) (hna : ¬ N.Anomalous s) :
    N.RegularOn (s 0) (s 1) (s 2) (s 3) :=
  (Net.pattern_cases hN hs hsN).resolve_right fun h => hna h.1

/-- **What holds for every network.** For four distinct taxa of a metric network with distinct leaf
labels: `N` displays one or two of the three quartets on them; if one, the two others have equal
positive CFs; if two, the third is strictly the least probable. Only the strict inequality for one
displayed quartet needs the configuration not to be anomalous (`Brooqs.net32_anomaly`). -/
theorem Net.weakPattern {N : Net X} (hN : N.WellFormed) {s : Fin 4 → X}
    (hs : Function.Injective s) (hsN : ∀ l, s l ∈ N.taxa) :
    WeakPattern (N.disp3 (s 0) (s 1) (s 2) (s 3)) (N.cf3 (s 0) (s 1) (s 2) (s 3)) := by
  rcases Net.pattern_cases hN hs hsN with h | ⟨-, M, hM, i, j, hij, hMij⟩
  · exact h.weak
  · exact Net.weakPattern_of_pair hN hsN hM hij hMij

end Brooqs
