module

public import Camus.External.NMSC.Displayed

/-!
# A 3-cycle above two taxa: an anomalous network

Section 3.3 of CAMUS motivates Quartet Filtering (Algorithm 1) by the distribution of quartet trees
under the NMSC: "The motivation for this approach is that we do not want to include quartet trees
that are not in Q(Nr). On the other hand, we do not want to eliminate these quartet trees." This
file computes the quartet CFs of the network `N₃₂` (`Brooqs.net32`): a 3-cycle whose hybrid
component holds two taxa `x` and `y`, with a third taxon `z` hanging from one side of the cycle and
a fourth taxon `w` outside it, a 3₂-cycle in the terms of Ané, Fogg, Allman, Baños and Rhodes
(2024), whom Section 3.3 cites. `N₃₂` displays only `xy|zw` of the three quartets on these taxa,
but for some edge lengths the CF of `xy|zw` is strictly smaller than the CFs of `xz|yw` and `xw|yz`
(`Brooqs.net32_anomaly`): a quartet in Q(N_r) is less probable than the quartets on the same taxa
that are not.

## Main results

* `Brooqs.net32`, `Brooqs.net32_wellFormed`: the network.
* `Brooqs.net32_quartetCF`: its quartet CFs on `x, y, z, w`, for all edge lengths and `γ`.
* `Brooqs.net32_displays`: it displays `xy|zw` and neither `xz|yw` nor `xw|yz`.
* `Brooqs.net32_anomaly`: for `γ = 1/2`, `ℓ = h₁ = h₂ = 1/20` and `L = 3`,
  `CF(xy|zw) < CF(xz|yw) = CF(xw|yz)`.
* `Brooqs.net32_long`: with `ℓ = 3` instead, `CF(xz|yw) = CF(xw|yz) < CF(xy|zw)`: the anomaly
  depends on the edge lengths.

## Proof

A quartet CF is the expected score of the forest at the top node of the cycle
(`Brooqs.quartetCF_eq_sum_top`). The lineages of `x` and `y` reach the hybrid node apart with
probability `e^{-ℓ}`, and then each takes the side `S₁` with probability `γ`, independently; this
gives six placements, whose expected scores are computed one by one (`tc_ES_both₁` and the lemmas
after it). Once three lineages are together without a cluster of two, the score is `1/3`
(`Brooqs.NiceKernel.score`). When the lineages of `x` and `y` take different sides, the one on `S₁`
meets the lineage of `z`, and the two coalesce along the edge of length `L` with probability
`1 - e^{-L}`, which gives `xz|yw` or `xw|yz`.
-/

@[expose] public noncomputable section

namespace Brooqs

open Finset Matrix

universe u

/-! ### Small facts about forests of the four lineages -/

private theorem tc_vecMul_single_apply (F : Finset (Finset (Fin 4)))
    (Φ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ)
    (G : Finset (Finset (Fin 4))) :
    (Pi.single F 1 ᵥ* Φ) G = Φ F G := by
  rw [single_one_vecMul]
  rfl

private theorem tc_row (Φ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ)
    (F : Finset (Finset (Fin 4))) : Φ F = Pi.single F 1 ᵥ* Φ := by
  funext G
  rw [tc_vecMul_single_apply]

/-- The expected score of a random forest. -/
private def tc_ES (μ : Finset (Finset (Fin 4)) → ℝ) : ℝ := ∑ G, μ G * quartetScore G

private theorem tc_ES_add (μ ν : Finset (Finset (Fin 4)) → ℝ) :
    tc_ES (μ + ν) = tc_ES μ + tc_ES ν := by
  simp only [tc_ES, Pi.add_apply, add_mul, sum_add_distrib]

private theorem tc_ES_smul (c : ℝ) (μ : Finset (Finset (Fin 4)) → ℝ) :
    tc_ES (c • μ) = c * tc_ES μ := by
  simp only [tc_ES, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]

private theorem tc_ES_single (F : Finset (Finset (Fin 4))) :
    tc_ES (Pi.single F 1) = quartetScore F := by
  simp [tc_ES, Pi.single_apply]

/-- After a nice kernel, the expected score of a good forest of at least three lineages is its
score. -/
private theorem tc_ES_nice {S : Finset (Fin 4)}
    {Φ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ} (hΦ : NiceKernel S Φ)
    {F : Finset (Finset (Fin 4))} (hF : IsGood F) (hFS : Disjoint (ADR11.lineages F) S)
    (h3 : 3 ≤ #(ADR11.lineages F)) : tc_ES (Pi.single F 1 ᵥ* Φ) = quartetScore F := by
  simp only [tc_ES, tc_vecMul_single_apply]
  exact hΦ.score hF hFS h3

private theorem tc_forestUnion_add_right (μ ν ν' : Finset (Finset (Fin 4)) → ℝ) :
    forestUnion μ (ν + ν') = forestUnion μ ν + forestUnion μ ν' := by
  rw [forestUnion_comm, forestUnion_add_left, forestUnion_comm ν, forestUnion_comm ν']

private theorem tc_forestUnion_smul_right (c : ℝ) (μ ν : Finset (Finset (Fin 4)) → ℝ) :
    forestUnion μ (c • ν) = c • forestUnion μ ν := by
  rw [forestUnion_comm, forestUnion_smul_left, forestUnion_comm]

/-- A forest with at most one cluster does not change. -/
private theorem tc_kT_le_one {F : Finset (Finset (Fin 4))} (hF : ADR11.IsForest F)
    (h : #F ≤ 1) (t : ℝ) : Pi.single F 1 ᵥ* kingmanTransition t = Pi.single F 1 :=
  single_vecMul_kingmanTransition hF ((card_le_card (ADR11.roots_subset F)).trans h) t

private theorem tc_isForest_single (i : Fin 4) : ADR11.IsForest ({{i}} : Finset (Finset (Fin 4))) :=
  by simpa using (isGood_singletons ({i} : Finset (Fin 4))).1

private theorem tc_isGood_pair (i j : Fin 4) :
    IsGood ({{i}, {j}} : Finset (Finset (Fin 4))) := by
  have := isGood_singletons ({i, j} : Finset (Fin 4))
  simpa [image_insert] using this

/-- Two lineages `i ≠ j` that have not coalesced: after a time `t` they are still apart with
probability `e^{-t}`. -/
private theorem tc_kT_two {i j : Fin 4} (hij : i ≠ j) (t : ℝ) :
    Pi.single ({{i}, {j}} : Finset (Finset (Fin 4))) 1 ᵥ* kingmanTransition t =
      Real.exp (-t) • Pi.single ({{i}, {j}} : Finset (Finset (Fin 4))) 1 +
        (1 - Real.exp (-t)) • Pi.single (insert ({i} ∪ {j}) {{i}, {j}}) 1 := by
  have hroots : roots ({{i}, {j}} : Finset (Finset (Fin 4))) = {{i}, {j}} := by
    revert i j
    decide
  exact single_vecMul_kingmanTransition_two (tc_isGood_pair i j).1
    (by simpa using hij) hroots t

/-- The score of a forest whose only cluster of two lineages is `C`: `1` if `C` is a side of the
split `{0, 1} | {2, 3}`, `0` otherwise. -/
private def tc_ps (C : Finset (Fin 4)) : ℝ := if C = {0, 1} ∨ C = {2, 3} then 1 else 0

/-- Three lineages that have not coalesced have score `1/3`. -/
private theorem tc_score_three {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    quartetScore ({{a}, {b}} ∪ {{c}}) = 1 / 3 := by
  have D : ¬(({0, 1} : Finset (Fin 4)) ∈ ({{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4))) ∨
      ({2, 3} : Finset (Fin 4)) ∈ ({{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4)))) ∧
      ¬∃ C ∈ ({{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4))), #C = 2 := by
    revert a b c
    decide
  unfold quartetScore
  rw [ite_eq_right D.1, ite_eq_right D.2]

/-- Three lineages of which `a` and `b` have coalesced: the score of the pair `{a, b}`. -/
private theorem tc_score_merged {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    quartetScore (insert ({a} ∪ {b}) {{a}, {b}} ∪ {{c}}) = tc_ps ({a} ∪ {b}) := by
  have D1 : (({0, 1} : Finset (Fin 4)) ∈ (insert ({a} ∪ {b}) {{a}, {b}} ∪ {{c}} :
      Finset (Finset (Fin 4))) ∨
      ({2, 3} : Finset (Fin 4)) ∈ (insert ({a} ∪ {b}) {{a}, {b}} ∪ {{c}} :
        Finset (Finset (Fin 4)))) ↔ ({a} ∪ {b} = ({0, 1} : Finset (Fin 4)) ∨
          {a} ∪ {b} = ({2, 3} : Finset (Fin 4))) := by
    revert a b c
    decide
  have D2 : ∃ C ∈ (insert ({a} ∪ {b}) {{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4))), #C = 2 := by
    revert a b c
    decide
  unfold quartetScore tc_ps
  rw [if_congr D1 rfl rfl, ite_eq_left D2]

/-! ### The network -/

variable {X : Type u} [DecidableEq X]

/-- A 3-cycle whose hybrid component holds two taxa: the top node of the cycle has the side `S₁`,
an edge of length `L` to a node with a pendant leaf `z` followed by the hybrid edge of length `h₁`
and inheritance probability `γ`, and the side `S₂`, a single hybrid edge of length `h₂` with
inheritance probability `1 - γ`; below the hybrid node, an edge of length `ℓ` leads to a tree node
with the leaves `x` and `y`. The lengths of the pendant edges of the leaves are `1`. -/
def cycle32 (γ ℓ h₁ h₂ L : ℝ) (x y z : X) : Net X :=
  .cycle γ (.node L 1 (.leaf z) (.hyb h₁)) (.hyb h₂) ℓ (.tree 1 (.leaf x) 1 (.leaf y))

private theorem tc_sampledAt {s : Fin 4 → X} (hs : Function.Injective s) (i : Fin 4) :
    sampledAt s (s i) = {{i}} := by
  unfold sampledAt
  have : (univ.filter fun l => s l = s i) = {i} := by
    ext l
    simp [hs.eq_iff]
  rw [this, image_singleton]

private theorem tc_leaf {s : Fin 4 → X} (hs : Function.Injective s) (i : Fin 4) :
    (Net.leaf (s i)).forestDist s = Pi.single {{i}} 1 := by
  funext G
  simp only [Net.forestDist, tc_sampledAt hs i, Pi.single_apply]

private theorem tc_leaf_kT {s : Fin 4 → X} (hs : Function.Injective s) (i : Fin 4) (t : ℝ) :
    (Net.leaf (s i)).forestDist s ᵥ* kingmanTransition t = Pi.single {{i}} 1 := by
  rw [tc_leaf hs i]
  exact tc_kT_le_one (tc_isForest_single i) (by simp) t

/-- Below the hybrid node: the two lineages `i` and `j`, coalesced along the edge of length `ℓ`
with probability `1 - e^{-ℓ}`. -/
private theorem tc_below {s : Fin 4 → X} (hs : Function.Injective s) {i j : Fin 4} (hij : i ≠ j)
    (ℓ : ℝ) :
    (Net.tree 1 (.leaf (s i)) 1 (.leaf (s j))).forestDist s ᵥ* kingmanTransition ℓ =
      Real.exp (-ℓ) • Pi.single ({{i}, {j}} : Finset (Finset (Fin 4))) 1 +
        (1 - Real.exp (-ℓ)) • Pi.single (insert ({i} ∪ {j}) {{i}, {j}}) 1 := by
  show forestUnion ((Net.leaf (s i)).forestDist s ᵥ* kingmanTransition 1)
    ((Net.leaf (s j)).forestDist s ᵥ* kingmanTransition 1) ᵥ* kingmanTransition ℓ = _
  rw [tc_leaf_kT hs i, tc_leaf_kT hs j, forestUnion_single_single,
    show ({{i}} ∪ {{j}} : Finset (Finset (Fin 4))) = {{i}, {j}} from rfl, tc_kT_two hij]

/-! ### The two sides -/

/-- The side `S₁`: the forest `E` takes the hybrid edge, the lineage `k` of the pendant leaf joins
it, and the lineages travel along the edge of length `L` to the top node. -/
private theorem tc_side₁ {s : Fin 4 → X} (hs : Function.Injective s) (k : Fin 4) (h₁ L : ℝ)
    (E : Finset (Finset (Fin 4))) :
    (Side.node L 1 (.leaf (s k)) (.hyb h₁)).forestDist s E =
      forestUnion (Pi.single E 1 ᵥ* kingmanTransition h₁) (Pi.single {{k}} 1) ᵥ*
        kingmanTransition L := by
  show forestUnion (kingmanTransition h₁ E) ((Net.leaf (s k)).forestDist s ᵥ* kingmanTransition 1)
    ᵥ* kingmanTransition L = _
  rw [tc_leaf_kT hs k, tc_row (kingmanTransition h₁) E]

private theorem tc_side₂ (s : Fin 4 → X) (h₂ : ℝ) (E : Finset (Finset (Fin 4))) :
    (Side.hyb h₂ : Side X).forestDist s E = Pi.single E 1 ᵥ* kingmanTransition h₂ := by
  show kingmanTransition h₂ E = _
  rw [tc_row (kingmanTransition h₂) E]

private theorem tc_isGood_of {F : Finset (Finset (Fin 4))} (h1 : ∀ A ∈ F, A.Nonempty)
    (h2 : ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (h3 : ∀ A ∈ F, 2 ≤ #A → ∃ B ∈ F, ∃ C ∈ F, Disjoint B C ∧ B ∪ C = A) : IsGood F :=
  ⟨⟨h1, h2⟩, h3⟩

/-- The forests of three lineages `a, b, c` with or without the cluster `{a, b}` are good, on the
three lineages. -/
private theorem tc_three_good {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    IsGood ({{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4))) ∧
      #(ADR11.lineages ({{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4)))) = 3 ∧
      IsGood (insert ({a} ∪ {b}) {{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4))) ∧
      #(ADR11.lineages (insert ({a} ∪ {b}) {{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4)))) = 3 := by
  refine ⟨tc_isGood_of ?_ ?_ ?_, ?_, tc_isGood_of ?_ ?_ ?_, ?_⟩
  all_goals
    revert a b c
    decide

/-- The cluster `{a, b}` is the only root of the forest of `a` and `b` that have coalesced. -/
private theorem tc_merged_le_one {a b : Fin 4} (hab : a ≠ b) :
    ADR11.IsForest (insert ({a} ∪ {b}) {{a}, {b}} : Finset (Finset (Fin 4))) ∧
      #(roots (insert ({a} ∪ {b}) {{a}, {b}} : Finset (Finset (Fin 4)))) ≤ 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  all_goals
    revert a b
    decide

/-- A forest that has coalesced into one tree does not change. -/
private theorem tc_kT_merged {a b : Fin 4} (hab : a ≠ b) (t : ℝ) :
    Pi.single (insert ({a} ∪ {b}) {{a}, {b}} : Finset (Finset (Fin 4))) 1 ᵥ*
      kingmanTransition t = Pi.single (insert ({a} ∪ {b}) {{a}, {b}}) 1 :=
  single_vecMul_kingmanTransition (tc_merged_le_one hab).1 (tc_merged_le_one hab).2 t

private theorem tc_kT_empty (t : ℝ) :
    Pi.single (∅ : Finset (Finset (Fin 4))) 1 ᵥ* kingmanTransition t = Pi.single ∅ 1 :=
  tc_kT_le_one ADR11.isForest_empty (by simp) t

private theorem tc_kT_single (i : Fin 4) (t : ℝ) :
    Pi.single ({{i}} : Finset (Finset (Fin 4))) 1 ᵥ* kingmanTransition t = Pi.single {{i}} 1 :=
  tc_kT_le_one (tc_isForest_single i) (by simp) t

/-! ### The expected scores of the six placements -/

section Placements

variable {s : Fin 4 → X} (hs : Function.Injective s) {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
  (hjk : j ≠ k) (h₁ h₂ L : ℝ)
include hs hij hik hjk

/-- The lineages `i, j` both take the side `S₂`. -/
private theorem tc_ES_both₂ :
    tc_ES (forestUnion ((Side.node L 1 (.leaf (s k)) (.hyb h₁)).forestDist s ∅)
      ((Side.hyb h₂ : Side X).forestDist s {{i}, {j}})) =
      Real.exp (-h₂) / 3 + (1 - Real.exp (-h₂)) * tc_ps ({i} ∪ {j}) := by
  rw [tc_side₁ hs k h₁ L, tc_side₂ s h₂, tc_kT_empty, forestUnion_single_single, empty_union,
    tc_kT_single, tc_kT_two hij, tc_forestUnion_add_right, tc_forestUnion_smul_right,
    tc_forestUnion_smul_right, forestUnion_single_single, forestUnion_single_single, tc_ES_add,
    tc_ES_smul, tc_ES_smul, tc_ES_single, tc_ES_single, union_comm, tc_score_three hij hik hjk,
    union_comm, tc_score_merged hij hik hjk]
  ring

/-- The lineage `j` takes the side `S₁` and meets `k`; the lineage `i` takes the side `S₂`. -/
private theorem tc_ES_split_j :
    tc_ES (forestUnion ((Side.node L 1 (.leaf (s k)) (.hyb h₁)).forestDist s {{j}})
      ((Side.hyb h₂ : Side X).forestDist s {{i}})) =
      Real.exp (-L) / 3 + (1 - Real.exp (-L)) * tc_ps ({j} ∪ {k}) := by
  rw [tc_side₁ hs k h₁ L, tc_side₂ s h₂, tc_kT_single, forestUnion_single_single,
    show ({{j}} ∪ {{k}} : Finset (Finset (Fin 4))) = {{j}, {k}} from rfl, tc_kT_two hjk,
    tc_kT_single, forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left,
    forestUnion_single_single, forestUnion_single_single, tc_ES_add, tc_ES_smul, tc_ES_smul,
    tc_ES_single, tc_ES_single, tc_score_three hjk hij.symm hik.symm,
    tc_score_merged hjk hij.symm hik.symm]
  ring

/-- The lineage `i` takes the side `S₁` and meets `k`; the lineage `j` takes the side `S₂`. -/
private theorem tc_ES_split_i :
    tc_ES (forestUnion ((Side.node L 1 (.leaf (s k)) (.hyb h₁)).forestDist s {{i}})
      ((Side.hyb h₂ : Side X).forestDist s {{j}})) =
      Real.exp (-L) / 3 + (1 - Real.exp (-L)) * tc_ps ({i} ∪ {k}) := by
  rw [tc_side₁ hs k h₁ L, tc_side₂ s h₂, tc_kT_single, forestUnion_single_single,
    show ({{i}} ∪ {{k}} : Finset (Finset (Fin 4))) = {{i}, {k}} from rfl, tc_kT_two hik,
    tc_kT_single, forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left,
    forestUnion_single_single, forestUnion_single_single, tc_ES_add, tc_ES_smul, tc_ES_smul,
    tc_ES_single, tc_ES_single, tc_score_three hik hij hjk.symm,
    tc_score_merged hik hij hjk.symm]
  ring

/-- The lineages `i, j` both take the side `S₁` and meet `k`. -/
private theorem tc_ES_both₁ :
    tc_ES (forestUnion ((Side.node L 1 (.leaf (s k)) (.hyb h₁)).forestDist s {{i}, {j}})
      ((Side.hyb h₂ : Side X).forestDist s ∅)) =
      Real.exp (-h₁) / 3 + (1 - Real.exp (-h₁)) * tc_ps ({i} ∪ {j}) := by
  obtain ⟨g1, -, g2, -⟩ := tc_three_good hij hik hjk
  obtain ⟨-, l1, -, l2⟩ := tc_three_good hij hik hjk
  have hnice := niceKernel_kingmanTransition L
  rw [tc_side₁ hs k h₁ L, tc_side₂ s h₂, tc_kT_empty, forestUnion_single_empty, tc_kT_two hij,
    forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left, forestUnion_single_single,
    forestUnion_single_single, add_vecMul, smul_vecMul, smul_vecMul, tc_ES_add, tc_ES_smul,
    tc_ES_smul, tc_ES_nice hnice g1 (disjoint_empty_right _) l1.ge,
    tc_ES_nice hnice g2 (disjoint_empty_right _) l2.ge, tc_score_three hij hik hjk,
    tc_score_merged hij hik hjk]
  ring

/-- The lineages `i, j` have coalesced below the hybrid node and take the side `S₂`. -/
private theorem tc_ES_merged₂ :
    tc_ES (forestUnion ((Side.node L 1 (.leaf (s k)) (.hyb h₁)).forestDist s ∅)
      ((Side.hyb h₂ : Side X).forestDist s (insert ({i} ∪ {j}) {{i}, {j}}))) =
      tc_ps ({i} ∪ {j}) := by
  rw [tc_side₁ hs k h₁ L, tc_side₂ s h₂, tc_kT_empty, forestUnion_single_single, empty_union,
    tc_kT_single, tc_kT_merged hij, forestUnion_single_single, tc_ES_single, union_comm,
    tc_score_merged hij hik hjk]

/-- The lineages `i, j` have coalesced below the hybrid node and take the side `S₁`. -/
private theorem tc_ES_merged₁ :
    tc_ES (forestUnion ((Side.node L 1 (.leaf (s k)) (.hyb h₁)).forestDist s
      (insert ({i} ∪ {j}) {{i}, {j}})) ((Side.hyb h₂ : Side X).forestDist s ∅)) =
      tc_ps ({i} ∪ {j}) := by
  obtain ⟨-, -, g2, l2⟩ := tc_three_good hij hik hjk
  rw [tc_side₁ hs k h₁ L, tc_side₂ s h₂, tc_kT_empty, forestUnion_single_empty, tc_kT_merged hij,
    forestUnion_single_single,
    tc_ES_nice (niceKernel_kingmanTransition L) g2 (disjoint_empty_right _) l2.ge,
    tc_score_merged hij hik hjk]

end Placements

/-! ### The hybrid node -/

/-- The expected score after the cycle kernel: the sides of the roots chosen at the hybrid node,
weighted by their probabilities. -/
private theorem tc_ES_cycle (γ : ℝ) (μ : Finset (Finset (Fin 4)) → ℝ)
    (U : Finset (Finset (Fin 4)) → Finset (Finset (Fin 4)) → Finset (Finset (Fin 4)) → ℝ) :
    tc_ES (fun G => ∑ F, μ F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) * U F A G) =
      ∑ F, μ F * ∑ A ∈ (roots F).powerset, γ ^ #A * (1 - γ) ^ #(roots F \ A) * tc_ES (U F A) := by
  unfold tc_ES
  simp only [sum_mul, mul_sum, mul_assoc]
  rw [sum_comm]
  refine sum_congr rfl fun F _ => ?_
  rw [sum_comm]

private theorem tc_sum_mix (a b : ℝ) (F₁ F₂ : Finset (Finset (Fin 4)))
    (g : Finset (Finset (Fin 4)) → ℝ) :
    ∑ F, ((a • Pi.single F₁ 1 + b • Pi.single F₂ 1 : Finset (Finset (Fin 4)) → ℝ) F) * g F =
      a * g F₁ + b * g F₂ := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib, Pi.single_apply,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

/-- Two lineages `i, j` that have not coalesced reach the hybrid node: each takes the side `S₁`
with probability `γ`, independently. -/
private theorem tc_sum_apart (γ : ℝ) {i j : Fin 4} (hij : i ≠ j)
    (V : Finset (Finset (Fin 4)) → Finset (Finset (Fin 4)) → ℝ) :
    ∑ A ∈ (roots ({{i}, {j}} : Finset (Finset (Fin 4)))).powerset,
        γ ^ #A * (1 - γ) ^ #(roots ({{i}, {j}} : Finset (Finset (Fin 4))) \ A) *
          V (forestBelow {{i}, {j}} A)
            (forestBelow {{i}, {j}} (roots ({{i}, {j}} : Finset (Finset (Fin 4))) \ A)) =
      (1 - γ) ^ 2 * V ∅ {{i}, {j}} + γ * (1 - γ) * V {{i}} {{j}} +
        γ * (1 - γ) * V {{j}} {{i}} + γ ^ 2 * V {{i}, {j}} ∅ := by
  have e : roots ({{i}, {j}} : Finset (Finset (Fin 4))) = {{i}, {j}} ∧
      (({{i}, {j}} : Finset (Finset (Fin 4)))).powerset = {∅, {{i}}, {{j}}, {{i}, {j}}} ∧
      ∅ ∉ ({{{i}}, {{j}}, {{i}, {j}}} : Finset (Finset (Finset (Fin 4)))) ∧
      {{i}} ∉ ({{{j}}, {{i}, {j}}} : Finset (Finset (Finset (Fin 4)))) ∧
      {{j}} ∉ ({{{i}, {j}}} : Finset (Finset (Finset (Fin 4)))) ∧
      #({{i}, {j}} : Finset (Finset (Fin 4))) = 2 ∧
      ({{i}, {j}} : Finset (Finset (Fin 4))) \ {{i}} = {{j}} ∧
      ({{i}, {j}} : Finset (Finset (Fin 4))) \ {{j}} = {{i}} ∧
      ({{i}, {j}} : Finset (Finset (Fin 4))) \ {{i}, {j}} = ∅ ∧
      forestBelow ({{i}, {j}} : Finset (Finset (Fin 4))) ∅ = ∅ ∧
      forestBelow ({{i}, {j}} : Finset (Finset (Fin 4))) {{i}} = {{i}} ∧
      forestBelow ({{i}, {j}} : Finset (Finset (Fin 4))) {{j}} = {{j}} ∧
      forestBelow ({{i}, {j}} : Finset (Finset (Fin 4))) {{i}, {j}} = {{i}, {j}} := by
    revert i j
    decide
  obtain ⟨e1, e2, n1, n2, n3, c2, d1, d2, d3, f0, f1, f2, f3⟩ := e
  rw [e1, e2, sum_insert n1, sum_insert n2, sum_insert n3, sum_singleton, sdiff_empty, d1, d2, d3,
    f0, f1, f2, f3, c2]
  simp only [card_empty, card_singleton, pow_zero, pow_one, one_mul, mul_one]
  ring

/-- The lineages `i, j` have coalesced below the hybrid node: their tree takes the side `S₁` with
probability `γ`. -/
private theorem tc_sum_merged (γ : ℝ) {i j : Fin 4} (hij : i ≠ j)
    (V : Finset (Finset (Fin 4)) → Finset (Finset (Fin 4)) → ℝ) :
    ∑ A ∈ (roots (insert ({i} ∪ {j}) {{i}, {j}} : Finset (Finset (Fin 4)))).powerset,
        γ ^ #A * (1 - γ) ^ #(roots (insert ({i} ∪ {j}) {{i}, {j}} : Finset (Finset (Fin 4))) \ A) *
          V (forestBelow (insert ({i} ∪ {j}) {{i}, {j}}) A)
            (forestBelow (insert ({i} ∪ {j}) {{i}, {j}})
              (roots (insert ({i} ∪ {j}) {{i}, {j}} : Finset (Finset (Fin 4))) \ A)) =
      (1 - γ) * V ∅ (insert ({i} ∪ {j}) {{i}, {j}}) +
        γ * V (insert ({i} ∪ {j}) {{i}, {j}}) ∅ := by
  have e : roots (insert ({i} ∪ {j}) {{i}, {j}} : Finset (Finset (Fin 4))) = {{i} ∪ {j}} ∧
      ({{i} ∪ {j}} : Finset (Finset (Fin 4))).powerset = {∅, {{i} ∪ {j}}} ∧
      forestBelow (insert ({i} ∪ {j}) {{i}, {j}} : Finset (Finset (Fin 4))) ∅ = ∅ ∧
      forestBelow (insert ({i} ∪ {j}) {{i}, {j}} : Finset (Finset (Fin 4))) {{i} ∪ {j}} =
        insert ({i} ∪ {j}) {{i}, {j}} := by
    revert i j
    decide
  obtain ⟨e1, e2, f0, f1⟩ := e
  rw [e1, e2, sum_pair (by simp), sdiff_empty, sdiff_self, bot_eq_empty, f0, f1]
  simp only [card_empty, card_singleton, pow_zero, pow_one, one_mul, mul_one]

/-- The expected score at the top node of the 3-cycle, for the lineages `i, j` below the hybrid
node and `k` on the side `S₁`. -/
private theorem tc_cycle_ES {s : Fin 4 → X} (hs : Function.Injective s) {i j k : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (γ ℓ h₁ h₂ L : ℝ) :
    tc_ES ((cycle32 γ ℓ h₁ h₂ L (s i) (s j) (s k)).forestDist s) =
      Real.exp (-ℓ) * ((1 - γ) ^ 2 *
          (Real.exp (-h₂) / 3 + (1 - Real.exp (-h₂)) * tc_ps ({i} ∪ {j})) +
        γ * (1 - γ) * (Real.exp (-L) / 3 + (1 - Real.exp (-L)) * tc_ps ({i} ∪ {k})) +
        γ * (1 - γ) * (Real.exp (-L) / 3 + (1 - Real.exp (-L)) * tc_ps ({j} ∪ {k})) +
        γ ^ 2 * (Real.exp (-h₁) / 3 + (1 - Real.exp (-h₁)) * tc_ps ({i} ∪ {j}))) +
      (1 - Real.exp (-ℓ)) * tc_ps ({i} ∪ {j}) := by
  set S₁ : Side X := .node L 1 (.leaf (s k)) (.hyb h₁)
  set S₂ : Side X := .hyb h₂
  set H : Net X := .tree 1 (.leaf (s i)) 1 (.leaf (s j))
  have hdef : (cycle32 γ ℓ h₁ h₂ L (s i) (s j) (s k)).forestDist s = fun G =>
      ∑ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) *
          (fun F A => forestUnion (S₁.forestDist s (forestBelow F A))
            (S₂.forestDist s (forestBelow F (roots F \ A)))) F A G := rfl
  have hV₁ := tc_sum_apart γ hij fun E E' => tc_ES (forestUnion (S₁.forestDist s E)
    (S₂.forestDist s E'))
  have hV₂ := tc_sum_merged γ hij fun E E' => tc_ES (forestUnion (S₁.forestDist s E)
    (S₂.forestDist s E'))
  rw [hdef, tc_ES_cycle, tc_below hs hij, tc_sum_mix, hV₁, hV₂,
    tc_ES_both₂ hs hij hik hjk h₁ h₂ L, tc_ES_split_i hs hij hik hjk h₁ h₂ L,
    tc_ES_split_j hs hij hik hjk h₁ h₂ L, tc_ES_both₁ hs hij hik hjk h₁ h₂ L,
    tc_ES_merged₂ hs hij hik hjk h₁ h₂ L, tc_ES_merged₁ hs hij hik hjk h₁ h₂ L]
  ring

/-! ### The network and its quartet concordance factors -/

/-- The network `N₃₂`: the root has the 3-cycle `cycle32` and a leaf `w` as its children, with
edges of length `1`. -/
def net32 (γ ℓ h₁ h₂ L : ℝ) (x y z w : X) : Net X :=
  .tree 1 (cycle32 γ ℓ h₁ h₂ L x y z) 1 (.leaf w)

/-- The cycle of `N₃₂`. -/
def net32Cycle (γ ℓ h₁ h₂ L : ℝ) (x y z w : X) : (net32 γ ℓ h₁ h₂ L x y z w).Cycle where
  γ := γ
  side₁ := .node L 1 (.leaf z) (.hyb h₁)
  side₂ := .hyb h₂
  ℓ := ℓ
  below := .tree 1 (.leaf x) 1 (.leaf y)
  mem := by simp [net32, cycle32, Net.subnets]

omit [DecidableEq X] in
theorem net32_leaves (γ ℓ h₁ h₂ L : ℝ) (x y z w : X) :
    (net32 γ ℓ h₁ h₂ L x y z w).leaves = [z, x, y, w] := by
  simp [net32, cycle32, Net.leaves, Side.leaves]

private theorem tc_cf {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ L : ℝ) {s : Fin 4 → X}
    (hs : Function.Injective s) {i j k m : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hsi : s i = x) (hsj : s j = y) (hsk : s k = z) (hsm : s m = w)
    (hcover : ∀ l, l = i ∨ l = j ∨ l = k ∨ l = m) :
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF (s 0) (s 1) (s 2) (s 3) =
      Real.exp (-ℓ) * ((1 - γ) ^ 2 *
          (Real.exp (-h₂) / 3 + (1 - Real.exp (-h₂)) * tc_ps ({i} ∪ {j})) +
        γ * (1 - γ) * (Real.exp (-L) / 3 + (1 - Real.exp (-L)) * tc_ps ({i} ∪ {k})) +
        γ * (1 - γ) * (Real.exp (-L) / 3 + (1 - Real.exp (-L)) * tc_ps ({j} ∪ {k})) +
        γ ^ 2 * (Real.exp (-h₁) / 3 + (1 - Real.exp (-h₁)) * tc_ps ({i} ∪ {j}))) +
      (1 - Real.exp (-ℓ)) * tc_ps ({i} ∪ {j}) := by
  have hN : (net32 γ ℓ h₁ h₂ L x y z w).leaves.Nodup := by
    rw [net32_leaves]
    simp [hxy, hxw, hyw, hzw, Ne.symm hxz, Ne.symm hyz]
  have hsN : ∀ l, s l ∈ (net32 γ ℓ h₁ h₂ L x y z w).taxa := by
    intro l
    simp only [Net.taxa, net32_leaves, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
      or_false]
    rcases hcover l with rfl | rfl | rfl | rfl <;> simp [hsi, hsj, hsk, hsm]
  have htop : (net32Cycle γ ℓ h₁ h₂ L x y z w).top = cycle32 γ ℓ h₁ h₂ L (s i) (s j) (s k) := by
    rw [hsi, hsj, hsk]
    rfl
  have h3 : 3 ≤ #(univ.filter fun l => s l ∈ (net32Cycle γ ℓ h₁ h₂ L x y z w).top.taxa) := by
    have hsub : ({i, j, k} : Finset (Fin 4)) ⊆
        univ.filter fun l => s l ∈ (net32Cycle γ ℓ h₁ h₂ L x y z w).top.taxa := by
      intro l hl
      rw [htop]
      simp only [mem_insert, mem_singleton] at hl
      simp only [mem_filter, mem_univ, true_and, Net.taxa, cycle32, Net.leaves, Side.leaves,
        List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rcases hl with rfl | rfl | rfl <;> simp
    refine le_trans ?_ (card_le_card hsub)
    rw [card_insert_of_notMem (by simp [hij, hik]), card_pair hjk]
  rw [quartetCF_eq_sum_top _ hN (net32Cycle γ ℓ h₁ h₂ L x y z w) s hsN h3, htop]
  exact tc_cycle_ES hs hij hik hjk γ ℓ h₁ h₂ L

omit [DecidableEq X] in
private theorem tc_inj4 {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) : Function.Injective ![x, y, z, w] := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [eq_comm]

/-- **The quartet CFs of `N₃₂`.** Under the NMSC on `N₃₂`, with `u = e^{-ℓ}`, `v₁ = e^{-h₁}`,
`v₂ = e^{-h₂}` and `λ = e^{-L}`:
* `CF(xy|zw) = 1 - u + u (γ² (1 - 2v₁/3) + (1 - γ)² (1 - 2v₂/3) + 2γ(1 - γ) λ/3)`;
* `CF(xz|yw) = CF(xw|yz) = u (γ² v₁/3 + (1 - γ)² v₂/3 + γ(1 - γ)(1 - λ/3))`.

The lineages of `x` and `y` reach the hybrid node apart with probability `u`; then each takes a
side independently. If they take different sides, the one on `S₁` meets `z` and the edge of
length `L` lets them coalesce, which favours `xz|yw` or `xw|yz`. -/
theorem net32_quartetCF {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ L : ℝ) :
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w = 1 - Real.exp (-ℓ) + Real.exp (-ℓ) *
        (γ ^ 2 * (1 - 2 / 3 * Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - 2 / 3 * Real.exp (-h₂)) +
          2 * γ * (1 - γ) * (Real.exp (-L) / 3)) ∧
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w = Real.exp (-ℓ) *
        (γ ^ 2 * (Real.exp (-h₁) / 3) + (1 - γ) ^ 2 * (Real.exp (-h₂) / 3) +
          γ * (1 - γ) * (1 - Real.exp (-L) / 3)) ∧
    (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x w y z = Real.exp (-ℓ) *
        (γ ^ 2 * (Real.exp (-h₁) / 3) + (1 - γ) ^ 2 * (Real.exp (-h₂) / 3) +
          γ * (1 - γ) * (1 - Real.exp (-L) / 3)) := by
  have p01 : tc_ps ({0} ∪ {1}) = 1 := by rw [tc_ps, ite_eq_left (by decide)]
  have p02 : tc_ps ({0} ∪ {2}) = 0 := by rw [tc_ps, ite_eq_right (by decide)]
  have p12 : tc_ps ({1} ∪ {2}) = 0 := by rw [tc_ps, ite_eq_right (by decide)]
  have p03 : tc_ps ({0} ∪ {3}) = 0 := by rw [tc_ps, ite_eq_right (by decide)]
  have p21 : tc_ps ({2} ∪ {1}) = 0 := by rw [tc_ps, ite_eq_right (by decide)]
  have p23 : tc_ps ({2} ∪ {3}) = 1 := by rw [tc_ps, ite_eq_left (by decide)]
  refine ⟨?_, ?_, ?_⟩
  · have h := tc_cf hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ L (tc_inj4 hxy hxz hxw hyz hyw hzw)
      (i := 0) (j := 1) (k := 2) (m := 3) (by decide) (by decide) (by decide) rfl rfl rfl rfl
      (by decide)
    rw [p01, p02, p12] at h
    change (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x y z w = _ at h
    rw [h]
    ring
  · have h := tc_cf hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ L
      (tc_inj4 hxz hxy hxw (Ne.symm hyz) hzw hyw)
      (i := 0) (j := 2) (k := 1) (m := 3) (by decide) (by decide) (by decide) rfl rfl rfl rfl
      (by decide)
    rw [p02, p01, p21] at h
    change (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x z y w = _ at h
    rw [h]
    ring
  · have h := tc_cf hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ L
      (tc_inj4 hxw hxy hxz (Ne.symm hyw) (Ne.symm hzw) hyz)
      (i := 0) (j := 2) (k := 3) (m := 1) (by decide) (by decide) (by decide) rfl rfl rfl rfl
      (by decide)
    rw [p02, p03, p23] at h
    change (net32 γ ℓ h₁ h₂ L x y z w).quartetCF x w y z = _ at h
    rw [h]
    ring

/-- `N₃₂` displays `xy|zw` and neither `xz|yw` nor `xw|yz`: the taxa `x` and `y` lie below the
hybrid node, in every displayed tree. -/
theorem net32_displays {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ L : ℝ) :
    (net32 γ ℓ h₁ h₂ L x y z w).Displays x y z w ∧
      ¬ (net32 γ ℓ h₁ h₂ L x y z w).Displays x z y w ∧
      ¬ (net32 γ ℓ h₁ h₂ L x y z w).Displays x w y z := by
  have hN : (net32 γ ℓ h₁ h₂ L x y z w).leaves.Nodup := by
    rw [net32_leaves]
    simp [hxy, hxw, hyw, hzw, Ne.symm hxz, Ne.symm hyz]
  have hM : (Net.tree 1 (.leaf x) 1 (.leaf y) : Net X) ∈ (net32 γ ℓ h₁ h₂ L x y z w).subnets := by
    simp [net32, cycle32, Net.subnets]
  refine Net.displays_of_subnet hN hM ?_ ?_ ?_ ?_ <;>
    simp [Net.taxa_tree, Net.taxa_leaf, Ne.symm hxz, Ne.symm hxw, Ne.symm hyz, Ne.symm hyw]

omit [DecidableEq X] in
/-- `N₃₂` is a metric network with distinct leaf labels when its edge lengths are positive and
`0 < γ < 1`. -/
theorem net32_wellFormed {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) {γ ℓ h₁ h₂ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hℓ : 0 < ℓ)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hL : 0 < L) :
    (net32 γ ℓ h₁ h₂ L x y z w).WellFormed := by
  refine ⟨?_, ?_⟩
  · simp [net32, cycle32, Net.IsMetric, Side.IsMetric, Side.nodes, hγ0, hγ1, hℓ, hh₁, hh₂, hL]
  · rw [net32_leaves]
    simp [hxy, hxw, hyw, hzw, Ne.symm hxz, Ne.symm hyz]

/-- **An anomalous network.** For `γ = 1/2`, `ℓ = h₁ = h₂ = 1/20` and `L = 3`, the quartet `xy|zw`,
the only one of the three quartets on `x, y, z, w` that `N₃₂` displays (`net32_displays`), has a
strictly smaller CF than the two others, which have equal CFs: about `0.231` against `0.385`. -/
theorem net32_anomaly {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) :
    (net32 (1 / 2) (1 / 20) (1 / 20) (1 / 20) 3 x y z w).quartetCF x y z w <
        (net32 (1 / 2) (1 / 20) (1 / 20) (1 / 20) 3 x y z w).quartetCF x z y w ∧
      (net32 (1 / 2) (1 / 20) (1 / 20) (1 / 20) 3 x y z w).quartetCF x z y w =
        (net32 (1 / 2) (1 / 20) (1 / 20) (1 / 20) 3 x y z w).quartetCF x w y z := by
  obtain ⟨h1, h2, h3⟩ := net32_quartetCF hxy hxz hxw hyz hyw hzw (1 / 2) (1 / 20) (1 / 20)
    (1 / 20) 3
  rw [h1, h2, h3]
  refine ⟨?_, rfl⟩
  -- `u = e^{-1/20} ≥ 19/20` and `λ = e^{-3} ≤ 1/4`
  have hu1 : (19 / 20 : ℝ) ≤ Real.exp (-(1 / 20)) := by
    have := Real.add_one_le_exp (-(1 / 20 : ℝ))
    linarith
  have hu2 : Real.exp (-(1 / 20 : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have hv0 : 0 < Real.exp (-3 : ℝ) := Real.exp_pos _
  have hv1 : Real.exp (-3 : ℝ) ≤ 1 / 4 := by
    have h4 : (4 : ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp (3 : ℝ)
      linarith
    have hk : Real.exp (-3 : ℝ) * Real.exp 3 = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith
  nlinarith [mul_le_mul hu1 hu1 (by norm_num) (by linarith), mul_le_mul hu2 hv1 hv0.le zero_le_one]

/-- **The anomaly depends on the edge lengths.** With the parameters of `net32_anomaly` but an edge
of length `ℓ = 3` below the hybrid node, the quartet `xy|zw` that `N₃₂` displays has strictly the
largest CF, and the two others have equal CFs: about `0.960` against `0.020`. -/
theorem net32_long {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) :
    (net32 (1 / 2) 3 (1 / 20) (1 / 20) 3 x y z w).quartetCF x z y w <
        (net32 (1 / 2) 3 (1 / 20) (1 / 20) 3 x y z w).quartetCF x y z w ∧
      (net32 (1 / 2) 3 (1 / 20) (1 / 20) 3 x y z w).quartetCF x z y w =
        (net32 (1 / 2) 3 (1 / 20) (1 / 20) 3 x y z w).quartetCF x w y z := by
  obtain ⟨h1, h2, h3⟩ := net32_quartetCF hxy hxz hxw hyz hyw hzw (1 / 2) 3 (1 / 20) (1 / 20) 3
  rw [h1, h2, h3]
  refine ⟨?_, rfl⟩
  -- `e^{-3} ≤ 1/4` and `e^{-1/20} ≤ 1`
  have e3 : Real.exp (-3 : ℝ) ≤ 1 / 4 := by
    have h4 : (4 : ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp (3 : ℝ)
      linarith
    have hk : Real.exp (-3 : ℝ) * Real.exp 3 = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith [Real.exp_pos (-3 : ℝ)]
  have e3p := Real.exp_pos (-3 : ℝ)
  have ehp := Real.exp_pos (-(1 / 20 : ℝ))
  have eh1 : Real.exp (-(1 / 20 : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  nlinarith [mul_pos e3p ehp, mul_le_mul_of_nonneg_left eh1 e3p.le]

end Brooqs
