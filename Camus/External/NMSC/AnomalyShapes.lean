module

public import Camus.External.NMSC.AnomalyRegion

/-!
# The 3₂-cycle with the four taxa below the top node of its cycle

The anomalous configuration (`Brooqs.Net.Anomalous`) asks for two of the four taxa below the hybrid
node of a cycle and the two others in two other components of the cycle: a 3₂-cycle in the terms
of Ané, Fogg, Allman, Baños and Rhodes (2024). `N₃₂` (`Brooqs.net32`) has the fourth taxon `w`
outside the cycle, above its top node. When the four taxa are all below the top node, `z` and `w`
hang from the two sides of the cycle (`Brooqs.net32Sides`) or from two nodes of one side
(`Brooqs.net32OneSide`). This file computes the quartet CFs of these two networks for all
parameters: they are those of `N₃₂` with other parameters, so their anomaly zones are those of
`Brooqs.net32_anomalous_iff` with these parameters.

* `net32Sides`: the root is the top node of a 3-cycle; its side `S₁` is an edge of length `a` to the
  node of `z`, then the hybrid edge of length `h₁` and inheritance probability `γ`; its side `S₂` is
  an edge of length `b` to the node of `w`, then the hybrid edge of length `h₂`; below the hybrid
  node, an edge of length `ℓ` leads to the cherry of `x` and `y`. Its CFs are those of `N₃₂` with
  `L = a + b` (`Brooqs.net32Sides_quartetCF`).
* `net32OneSide`: the side `S₁` is an edge of length `a` to the node of `z`, an edge of length `b`
  to the node of `w`, then the hybrid edge of length `h₁` and inheritance probability `γ`; the side
  `S₂` is the hybrid edge of length `h₂`. Its CFs are those of `N₃₂` with `a + h₂` for `h₂` and `b`
  for `L` (`Brooqs.net32OneSide_quartetCF`).

These are cases of Proposition 3 of Ané et al. (2024): the quartet CFs of a network depend only on
its semidirected network, in which the root is suppressed. A semidirected 3₂-cycle is given by the
length `t` of the edge below its hybrid node, the length `s₀` of the tree edge of the cycle, between
the nodes of the two other taxa, and the lengths `s₁`, `s₂` and inheritance probabilities
`γ₁ = γ`, `γ₂ = 1 - γ` of its hybrid edges; `N₃₂` with `ℓ = t`, `L = s₀`, `h₁ = s₁`, `h₂ = s₂`
gives each of them with positive parameters. Rooting the semidirected 3₂-cycle on the pendant edge
of a taxon gives `N₃₂`, on its tree edge gives `net32Sides` (`s₀ = a + b`), and on a hybrid edge
gives `net32OneSide` (the hybrid edge from the node of `z` has length `s₂ = a + h₂`, and `s₀ = b`),
each up to the exchange of the two sides of the cycle (with `γ` and `1 - γ`) and of the names `z`
and `w`. The side-exchanged networks have the same quartet CFs (`Brooqs.Net.SideSwap.quartetCF_eq`
with `Brooqs.Net.SideSwap.swap_top`, in `Camus/External/NMSC/Swap.lean`).

## Main results

* `Brooqs.net32Sides`, `Brooqs.net32Sides_wellFormed`, `Brooqs.net32Sides_displays`: `z` and `w`
  on the two sides.
* `Brooqs.net32Sides_quartetCF`, `Brooqs.net32Sides_anomalous_iff`,
  `Brooqs.net32Sides_regular_iff`: its CFs are those of `N₃₂` with `L = a + b`, and its two zones.
* `Brooqs.net32OneSide`, `Brooqs.net32OneSide_wellFormed`, `Brooqs.net32OneSide_displays`: `z` and
  `w` on one side.
* `Brooqs.net32OneSide_quartetCF`, `Brooqs.net32OneSide_anomalous_iff`,
  `Brooqs.net32OneSide_regular_iff`: its CFs are those of `N₃₂` with `a + h₂` for `h₂` and `b` for
  `L`, and its two zones.

## Proof

As for `N₃₂` (`ThreeCycle.lean`, whose lemmas on forests of the four lineages are repeated here,
since they are private there): a quartet CF is the expected score of the forest at the top node
(`Brooqs.quartetCF_eq_sum_top`), here the root, and the lineages of `x` and `y`, if they have not
coalesced below the hybrid node, take the sides independently; the six placements are computed one
by one. In `net32Sides`, when one takes `S₁` and the other `S₂`, they meet `z` and `w`
respectively, and coalesce with them along the edges of lengths `a` and `b` with probabilities
`1 - e^{-a}` and `1 - e^{-b}`; either coalescence gives the same split, so none happens with
probability `e^{-a} e^{-b} = e^{-(a + b)}`. In `net32OneSide`, when both take `S₂`, the lineages of
`z` and `w` can coalesce along the edge of length `a`, which gives the split `xy|zw` as a
coalescence of `x` and `y` does, so neither happens with probability `e^{-a} e^{-h₂}`. When three
lineages travel together, the expected score is unchanged by the rest of the process
(`Brooqs.NiceKernel.score`), which here can add the lineage of a pendant leaf or of the other side
(`Brooqs.niceKernel_unionKernel`).
-/

@[expose] public noncomputable section

namespace Brooqs

open Finset Matrix

universe u

/-! ### Small facts about forests of the four lineages (as in `ThreeCycle.lean`) -/

private theorem ts_vecMul_single_apply (F : Finset (Finset (Fin 4)))
    (Φ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ)
    (G : Finset (Finset (Fin 4))) :
    (Pi.single F 1 ᵥ* Φ) G = Φ F G := by
  rw [single_one_vecMul]
  rfl

private theorem ts_row (Φ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ)
    (F : Finset (Finset (Fin 4))) : Φ F = Pi.single F 1 ᵥ* Φ := by
  funext G
  rw [ts_vecMul_single_apply]

/-- The expected score of a random forest. -/
private def ts_ES (μ : Finset (Finset (Fin 4)) → ℝ) : ℝ := ∑ G, μ G * quartetScore G

private theorem ts_ES_add (μ ν : Finset (Finset (Fin 4)) → ℝ) :
    ts_ES (μ + ν) = ts_ES μ + ts_ES ν := by
  simp only [ts_ES, Pi.add_apply, add_mul, sum_add_distrib]

private theorem ts_ES_smul (c : ℝ) (μ : Finset (Finset (Fin 4)) → ℝ) :
    ts_ES (c • μ) = c * ts_ES μ := by
  simp only [ts_ES, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]

private theorem ts_ES_single (F : Finset (Finset (Fin 4))) :
    ts_ES (Pi.single F 1) = quartetScore F := by
  simp [ts_ES, Pi.single_apply]

/-- After a nice kernel, the expected score of a good forest of at least three lineages is its
score. -/
private theorem ts_ES_nice {S : Finset (Fin 4)}
    {Φ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ} (hΦ : NiceKernel S Φ)
    {F : Finset (Finset (Fin 4))} (hF : IsGood F) (hFS : Disjoint (ADR11.lineages F) S)
    (h3 : 3 ≤ #(ADR11.lineages F)) : ts_ES (Pi.single F 1 ᵥ* Φ) = quartetScore F := by
  simp only [ts_ES, ts_vecMul_single_apply]
  exact hΦ.score hF hFS h3

private theorem ts_forestUnion_add_right (μ ν ν' : Finset (Finset (Fin 4)) → ℝ) :
    forestUnion μ (ν + ν') = forestUnion μ ν + forestUnion μ ν' := by
  rw [forestUnion_comm, forestUnion_add_left, forestUnion_comm ν, forestUnion_comm ν']

private theorem ts_forestUnion_smul_right (c : ℝ) (μ ν : Finset (Finset (Fin 4)) → ℝ) :
    forestUnion μ (c • ν) = c • forestUnion μ ν := by
  rw [forestUnion_comm, forestUnion_smul_left, forestUnion_comm]

/-- A forest with at most one cluster does not change. -/
private theorem ts_kT_le_one {F : Finset (Finset (Fin 4))} (hF : ADR11.IsForest F)
    (h : #F ≤ 1) (t : ℝ) : Pi.single F 1 ᵥ* kingmanTransition t = Pi.single F 1 :=
  single_vecMul_kingmanTransition hF ((card_le_card (ADR11.roots_subset F)).trans h) t

private theorem ts_isForest_single (i : Fin 4) : ADR11.IsForest ({{i}} : Finset (Finset (Fin 4))) :=
  by simpa using (isGood_singletons ({i} : Finset (Fin 4))).1

private theorem ts_isGood_pair (i j : Fin 4) :
    IsGood ({{i}, {j}} : Finset (Finset (Fin 4))) := by
  have := isGood_singletons ({i, j} : Finset (Fin 4))
  simpa [image_insert] using this

/-- Two lineages `i ≠ j` that have not coalesced: after a time `t` they are still apart with
probability `e^{-t}`. -/
private theorem ts_kT_two {i j : Fin 4} (hij : i ≠ j) (t : ℝ) :
    Pi.single ({{i}, {j}} : Finset (Finset (Fin 4))) 1 ᵥ* kingmanTransition t =
      Real.exp (-t) • Pi.single ({{i}, {j}} : Finset (Finset (Fin 4))) 1 +
        (1 - Real.exp (-t)) • Pi.single (insert ({i} ∪ {j}) {{i}, {j}}) 1 := by
  have hroots : roots ({{i}, {j}} : Finset (Finset (Fin 4))) = {{i}, {j}} := by
    revert i j
    decide
  exact single_vecMul_kingmanTransition_two (ts_isGood_pair i j).1
    (by simpa using hij) hroots t

/-- The score of a forest whose only cluster of two lineages is `C`: `1` if `C` is a side of the
split `{0, 1} | {2, 3}`, `0` otherwise. -/
private def ts_ps (C : Finset (Fin 4)) : ℝ := if C = {0, 1} ∨ C = {2, 3} then 1 else 0

/-- Three lineages that have not coalesced have score `1/3`. -/
private theorem ts_score_three {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    quartetScore ({{a}, {b}} ∪ {{c}}) = 1 / 3 := by
  have D : ¬(({0, 1} : Finset (Fin 4)) ∈ ({{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4))) ∨
      ({2, 3} : Finset (Fin 4)) ∈ ({{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4)))) ∧
      ¬∃ C ∈ ({{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4))), #C = 2 := by
    revert a b c
    decide
  unfold quartetScore
  rw [ite_eq_right D.1, ite_eq_right D.2]

/-- Three lineages of which `a` and `b` have coalesced: the score of the pair `{a, b}`. -/
private theorem ts_score_merged {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    quartetScore (insert ({a} ∪ {b}) {{a}, {b}} ∪ {{c}}) = ts_ps ({a} ∪ {b}) := by
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
  unfold quartetScore ts_ps
  rw [if_congr D1 rfl rfl, ite_eq_left D2]

variable {X : Type u} [DecidableEq X]

private theorem ts_sampledAt {s : Fin 4 → X} (hs : Function.Injective s) (i : Fin 4) :
    sampledAt s (s i) = {{i}} := by
  unfold sampledAt
  have : (univ.filter fun l => s l = s i) = {i} := by
    ext l
    simp [hs.eq_iff]
  rw [this, image_singleton]

private theorem ts_leaf {s : Fin 4 → X} (hs : Function.Injective s) (i : Fin 4) :
    (Net.leaf (s i)).forestDist s = Pi.single {{i}} 1 := by
  funext G
  simp only [Net.forestDist, ts_sampledAt hs i, Pi.single_apply]

private theorem ts_leaf_kT {s : Fin 4 → X} (hs : Function.Injective s) (i : Fin 4) (t : ℝ) :
    (Net.leaf (s i)).forestDist s ᵥ* kingmanTransition t = Pi.single {{i}} 1 := by
  rw [ts_leaf hs i]
  exact ts_kT_le_one (ts_isForest_single i) (by simp) t

/-- Below the hybrid node: the two lineages `i` and `j`, coalesced along the edge of length `ℓ`
with probability `1 - e^{-ℓ}`. -/
private theorem ts_below {s : Fin 4 → X} (hs : Function.Injective s) {i j : Fin 4} (hij : i ≠ j)
    (ℓ : ℝ) :
    (Net.tree 1 (.leaf (s i)) 1 (.leaf (s j))).forestDist s ᵥ* kingmanTransition ℓ =
      Real.exp (-ℓ) • Pi.single ({{i}, {j}} : Finset (Finset (Fin 4))) 1 +
        (1 - Real.exp (-ℓ)) • Pi.single (insert ({i} ∪ {j}) {{i}, {j}}) 1 := by
  show forestUnion ((Net.leaf (s i)).forestDist s ᵥ* kingmanTransition 1)
    ((Net.leaf (s j)).forestDist s ᵥ* kingmanTransition 1) ᵥ* kingmanTransition ℓ = _
  rw [ts_leaf_kT hs i, ts_leaf_kT hs j, forestUnion_single_single,
    show ({{i}} ∪ {{j}} : Finset (Finset (Fin 4))) = {{i}, {j}} from rfl, ts_kT_two hij]

/-- The side `S₁`: the forest `E` takes the hybrid edge, the lineage `k` of the pendant leaf joins
it, and the lineages travel along the edge of length `L` to the top node. -/
private theorem ts_side₁ {s : Fin 4 → X} (hs : Function.Injective s) (k : Fin 4) (h₁ L : ℝ)
    (E : Finset (Finset (Fin 4))) :
    (Side.node L 1 (.leaf (s k)) (.hyb h₁)).forestDist s E =
      forestUnion (Pi.single E 1 ᵥ* kingmanTransition h₁) (Pi.single {{k}} 1) ᵥ*
        kingmanTransition L := by
  show forestUnion (kingmanTransition h₁ E) ((Net.leaf (s k)).forestDist s ᵥ* kingmanTransition 1)
    ᵥ* kingmanTransition L = _
  rw [ts_leaf_kT hs k, ts_row (kingmanTransition h₁) E]

private theorem ts_isGood_of {F : Finset (Finset (Fin 4))} (h1 : ∀ A ∈ F, A.Nonempty)
    (h2 : ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (h3 : ∀ A ∈ F, 2 ≤ #A → ∃ B ∈ F, ∃ C ∈ F, Disjoint B C ∧ B ∪ C = A) : IsGood F :=
  ⟨⟨h1, h2⟩, h3⟩

/-- The forests of three lineages `a, b, c` with or without the cluster `{a, b}` are good, on the
three lineages. -/
private theorem ts_three_good {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    IsGood ({{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4))) ∧
      #(ADR11.lineages ({{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4)))) = 3 ∧
      IsGood (insert ({a} ∪ {b}) {{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4))) ∧
      #(ADR11.lineages (insert ({a} ∪ {b}) {{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4)))) = 3 := by
  refine ⟨ts_isGood_of ?_ ?_ ?_, ?_, ts_isGood_of ?_ ?_ ?_, ?_⟩
  all_goals
    revert a b c
    decide

/-- The cluster `{a, b}` is the only root of the forest of `a` and `b` that have coalesced. -/
private theorem ts_merged_le_one {a b : Fin 4} (hab : a ≠ b) :
    ADR11.IsForest (insert ({a} ∪ {b}) {{a}, {b}} : Finset (Finset (Fin 4))) ∧
      #(roots (insert ({a} ∪ {b}) {{a}, {b}} : Finset (Finset (Fin 4)))) ≤ 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  all_goals
    revert a b
    decide

/-- A forest that has coalesced into one tree does not change. -/
private theorem ts_kT_merged {a b : Fin 4} (hab : a ≠ b) (t : ℝ) :
    Pi.single (insert ({a} ∪ {b}) {{a}, {b}} : Finset (Finset (Fin 4))) 1 ᵥ*
      kingmanTransition t = Pi.single (insert ({a} ∪ {b}) {{a}, {b}}) 1 :=
  single_vecMul_kingmanTransition (ts_merged_le_one hab).1 (ts_merged_le_one hab).2 t

private theorem ts_kT_empty (t : ℝ) :
    Pi.single (∅ : Finset (Finset (Fin 4))) 1 ᵥ* kingmanTransition t = Pi.single ∅ 1 :=
  ts_kT_le_one ADR11.isForest_empty (by simp) t

private theorem ts_kT_single (i : Fin 4) (t : ℝ) :
    Pi.single ({{i}} : Finset (Finset (Fin 4))) 1 ᵥ* kingmanTransition t = Pi.single {{i}} 1 :=
  ts_kT_le_one (ts_isForest_single i) (by simp) t

/-- The expected score after the cycle kernel: the sides of the roots chosen at the hybrid node,
weighted by their probabilities. -/
private theorem ts_ES_cycle (γ : ℝ) (μ : Finset (Finset (Fin 4)) → ℝ)
    (U : Finset (Finset (Fin 4)) → Finset (Finset (Fin 4)) → Finset (Finset (Fin 4)) → ℝ) :
    ts_ES (fun G => ∑ F, μ F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) * U F A G) =
      ∑ F, μ F * ∑ A ∈ (roots F).powerset, γ ^ #A * (1 - γ) ^ #(roots F \ A) * ts_ES (U F A) := by
  unfold ts_ES
  simp only [sum_mul, mul_sum, mul_assoc]
  rw [sum_comm]
  refine sum_congr rfl fun F _ => ?_
  rw [sum_comm]

private theorem ts_sum_mix (a b : ℝ) (F₁ F₂ : Finset (Finset (Fin 4)))
    (g : Finset (Finset (Fin 4)) → ℝ) :
    ∑ F, ((a • Pi.single F₁ 1 + b • Pi.single F₂ 1 : Finset (Finset (Fin 4)) → ℝ) F) * g F =
      a * g F₁ + b * g F₂ := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib, Pi.single_apply,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

/-- Two lineages `i, j` that have not coalesced reach the hybrid node: each takes the side `S₁`
with probability `γ`, independently. -/
private theorem ts_sum_apart (γ : ℝ) {i j : Fin 4} (hij : i ≠ j)
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
private theorem ts_sum_merged (γ : ℝ) {i j : Fin 4} (hij : i ≠ j)
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

/-! ### Four lineages at the top node -/

/-- The forest of the single lineage `k` is good, with the lineage `k`. -/
private theorem ts_single_facts (k : Fin 4) :
    IsGood ({{k}} : Finset (Finset (Fin 4))) ∧
      ADR11.lineages ({{k}} : Finset (Finset (Fin 4))) = {k} := by
  refine ⟨by simpa using isGood_singletons ({k} : Finset (Fin 4)), ?_⟩
  simp [ADR11.lineages]

/-- A good forest `F` of three lineages travels along an edge of length `t` and is then joined by
the lineage `k`: the expected score is the score of `F`. -/
private theorem ts_ES_union {F : Finset (Finset (Fin 4))} (hF : IsGood F) {k : Fin 4}
    (hk : Disjoint (ADR11.lineages F) {k}) (h3 : 3 ≤ #(ADR11.lineages F)) (t : ℝ) :
    ts_ES (forestUnion (Pi.single F 1 ᵥ* kingmanTransition t) (Pi.single {{k}} 1)) =
      quartetScore F := by
  have hu : NiceKernel {k} (unionKernel (Pi.single ({{k}} : Finset (Finset (Fin 4))) 1)) := by
    refine niceKernel_unionKernel (by simp) fun E hE => ?_
    have hE' : E = {{k}} := by
      by_contra hne
      exact hE (by simp [hne])
    subst hE'
    exact ts_single_facts k
  have hnice := (niceKernel_kingmanTransition t).mul hu (disjoint_empty_left _)
  rw [empty_union] at hnice
  rw [forestUnion_eq_vecMul, vecMul_vecMul]
  simp only [ts_ES, ts_vecMul_single_apply]
  exact hnice.score hF hk h3

/-- The lineages of the forests of three lineages `a, b, c`, with or without the cluster `{a, b}`,
do not contain a fourth lineage `d`. -/
private theorem ts_three_disjoint {a b c d : Fin 4} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hcd : c ≠ d) :
    Disjoint (ADR11.lineages ({{a}, {b}} ∪ {{c}} : Finset (Finset (Fin 4)))) {d} ∧
      Disjoint (ADR11.lineages (insert ({a} ∪ {b}) {{a}, {b}} ∪ {{c}} :
        Finset (Finset (Fin 4)))) {d} := by
  revert a b c d
  decide

/-- The forest `F` has a cluster of two lineages, and the cluster `{0, 1}` or `{2, 3}` iff `C` is
one of them. -/
private abbrev ts_merged4 (F : Finset (Finset (Fin 4))) (C : Finset (Fin 4)) : Prop :=
  ((({0, 1} : Finset (Fin 4)) ∈ F ∨ ({2, 3} : Finset (Fin 4)) ∈ F) ↔
    (C = ({0, 1} : Finset (Fin 4)) ∨ C = ({2, 3} : Finset (Fin 4)))) ∧ ∃ D ∈ F, #D = 2

/-- The scores of the forests of four lineages `i, k, j, m` in which only `{i, k}` and `{j, m}` can
have coalesced: `1/3` if neither has, the score of the split `{i, k} | {j, m}` otherwise. -/
private theorem ts_score_four {i j k m : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (him : i ≠ m)
    (hjk : j ≠ k) (hjm : j ≠ m) (hkm : k ≠ m) :
    quartetScore ({{i}, {k}} ∪ {{j}, {m}}) = 1 / 3 ∧
      quartetScore (insert ({i} ∪ {k}) {{i}, {k}} ∪ {{j}, {m}}) = ts_ps ({i} ∪ {k}) ∧
      quartetScore ({{i}, {k}} ∪ insert ({j} ∪ {m}) {{j}, {m}}) = ts_ps ({i} ∪ {k}) ∧
      quartetScore (insert ({i} ∪ {k}) {{i}, {k}} ∪ insert ({j} ∪ {m}) {{j}, {m}}) =
        ts_ps ({i} ∪ {k}) := by
  have D : (¬(({0, 1} : Finset (Fin 4)) ∈ ({{i}, {k}} ∪ {{j}, {m}} : Finset (Finset (Fin 4))) ∨
      ({2, 3} : Finset (Fin 4)) ∈ ({{i}, {k}} ∪ {{j}, {m}} : Finset (Finset (Fin 4)))) ∧
      ¬∃ C ∈ ({{i}, {k}} ∪ {{j}, {m}} : Finset (Finset (Fin 4))), #C = 2) ∧
      ts_merged4 (insert ({i} ∪ {k}) {{i}, {k}} ∪ {{j}, {m}}) ({i} ∪ {k}) ∧
      ts_merged4 ({{i}, {k}} ∪ insert ({j} ∪ {m}) {{j}, {m}}) ({i} ∪ {k}) ∧
      ts_merged4 (insert ({i} ∪ {k}) {{i}, {k}} ∪ insert ({j} ∪ {m}) {{j}, {m}}) ({i} ∪ {k}) := by
    revert i j k m
    decide
  obtain ⟨D0, D1, D2, D3⟩ := D
  have hval : ∀ F : Finset (Finset (Fin 4)),
      ((({0, 1} : Finset (Fin 4)) ∈ F ∨ ({2, 3} : Finset (Fin 4)) ∈ F) ↔
        ({i} ∪ {k} = ({0, 1} : Finset (Fin 4)) ∨ {i} ∪ {k} = ({2, 3} : Finset (Fin 4)))) →
      (∃ C ∈ F, #C = 2) → quartetScore F = ts_ps ({i} ∪ {k}) := by
    intro F h1 h2
    unfold quartetScore ts_ps
    rw [if_congr h1 rfl rfl, ite_eq_left h2]
  refine ⟨?_, hval _ D1.1 D1.2, hval _ D2.1 D2.2, hval _ D3.1 D3.2⟩
  unfold quartetScore
  rw [ite_eq_right D0.1, ite_eq_right D0.2]

/-! ### The expected scores of the six placements -/

/-- Three lineages `p, q` (from below the hybrid node) and `c` (a pendant leaf) travel along an
edge of length `t` and are joined by the lineage `d` of the other side: the expected score is
`e^{-h}/3 + (1 - e^{-h})` times the score of `{p, q}`, where `h` is the length of the hybrid edge
on which `p` and `q` can coalesce. -/
private theorem ts_ES_pair_side {p q c d : Fin 4} (hpq : p ≠ q) (hpc : p ≠ c) (hpd : p ≠ d)
    (hqc : q ≠ c) (hqd : q ≠ d) (hcd : c ≠ d) (h t : ℝ) :
    ts_ES (forestUnion (forestUnion (Pi.single {{p}, {q}} 1 ᵥ* kingmanTransition h)
        (Pi.single {{c}} 1) ᵥ* kingmanTransition t) (Pi.single {{d}} 1)) =
      Real.exp (-h) / 3 + (1 - Real.exp (-h)) * ts_ps ({p} ∪ {q}) := by
  obtain ⟨g1, l1, g2, l2⟩ := ts_three_good hpq hpc hqc
  obtain ⟨d1, d2⟩ := ts_three_disjoint hpq hpd hqd hcd
  rw [ts_kT_two hpq, forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left,
    forestUnion_single_single, forestUnion_single_single, add_vecMul, smul_vecMul, smul_vecMul,
    forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left, ts_ES_add, ts_ES_smul,
    ts_ES_smul, ts_ES_union g1 d1 l1.ge, ts_ES_union g2 d2 l2.ge, ts_score_three hpq hpc hqc,
    ts_score_merged hpq hpc hqc]
  ring

/-- The cluster `{p, q}` with a third lineage `c` travels along an edge of length `t` and is joined
by the lineage `d`: the expected score is the score of `{p, q}`. -/
private theorem ts_ES_merged_side {p q c d : Fin 4} (hpq : p ≠ q) (hpc : p ≠ c) (hpd : p ≠ d)
    (hqc : q ≠ c) (hqd : q ≠ d) (hcd : c ≠ d) (h t : ℝ) :
    ts_ES (forestUnion (forestUnion (Pi.single (insert ({p} ∪ {q}) {{p}, {q}}) 1 ᵥ*
        kingmanTransition h) (Pi.single {{c}} 1) ᵥ* kingmanTransition t) (Pi.single {{d}} 1)) =
      ts_ps ({p} ∪ {q}) := by
  obtain ⟨-, -, g2, l2⟩ := ts_three_good hpq hpc hqc
  obtain ⟨-, d2⟩ := ts_three_disjoint hpq hpd hqd hcd
  rw [ts_kT_merged hpq, forestUnion_single_single, ts_ES_union g2 d2 l2.ge,
    ts_score_merged hpq hpc hqc]

section Placements

variable {s : Fin 4 → X} (hs : Function.Injective s) {i j k m : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
  (him : i ≠ m) (hjk : j ≠ k) (hjm : j ≠ m) (hkm : k ≠ m) (h₁ h₂ a b : ℝ)
include hs hij hik him hjk hjm hkm

/-- The lineages `i, j` both take the side `S₂`, where they meet `m`; the side `S₁` brings `k`. -/
private theorem ts_ES_both₂ :
    ts_ES (forestUnion ((Side.node a 1 (.leaf (s k)) (.hyb h₁)).forestDist s ∅)
      ((Side.node b 1 (.leaf (s m)) (.hyb h₂)).forestDist s {{i}, {j}})) =
      Real.exp (-h₂) / 3 + (1 - Real.exp (-h₂)) * ts_ps ({i} ∪ {j}) := by
  rw [ts_side₁ hs k h₁ a, ts_side₁ hs m h₂ b, ts_kT_empty, forestUnion_single_single, empty_union,
    ts_kT_single, forestUnion_comm]
  exact ts_ES_pair_side hij him hik hjm hjk (Ne.symm hkm) h₂ b

/-- The lineages `i, j` both take the side `S₁`, where they meet `k`; the side `S₂` brings `m`. -/
private theorem ts_ES_both₁ :
    ts_ES (forestUnion ((Side.node a 1 (.leaf (s k)) (.hyb h₁)).forestDist s {{i}, {j}})
      ((Side.node b 1 (.leaf (s m)) (.hyb h₂)).forestDist s ∅)) =
      Real.exp (-h₁) / 3 + (1 - Real.exp (-h₁)) * ts_ps ({i} ∪ {j}) := by
  rw [ts_side₁ hs k h₁ a, ts_side₁ hs m h₂ b, ts_kT_empty (t := h₂), forestUnion_single_single,
    empty_union, ts_kT_single]
  exact ts_ES_pair_side hij hik him hjk hjm hkm h₁ a

/-- The lineages `i, j` have coalesced below the hybrid node and take the side `S₂`. -/
private theorem ts_ES_merged₂ :
    ts_ES (forestUnion ((Side.node a 1 (.leaf (s k)) (.hyb h₁)).forestDist s ∅)
      ((Side.node b 1 (.leaf (s m)) (.hyb h₂)).forestDist s (insert ({i} ∪ {j}) {{i}, {j}}))) =
      ts_ps ({i} ∪ {j}) := by
  rw [ts_side₁ hs k h₁ a, ts_side₁ hs m h₂ b, ts_kT_empty, forestUnion_single_single, empty_union,
    ts_kT_single, forestUnion_comm]
  exact ts_ES_merged_side hij him hik hjm hjk (Ne.symm hkm) h₂ b

/-- The lineages `i, j` have coalesced below the hybrid node and take the side `S₁`. -/
private theorem ts_ES_merged₁ :
    ts_ES (forestUnion ((Side.node a 1 (.leaf (s k)) (.hyb h₁)).forestDist s
      (insert ({i} ∪ {j}) {{i}, {j}})) ((Side.node b 1 (.leaf (s m)) (.hyb h₂)).forestDist s ∅)) =
      ts_ps ({i} ∪ {j}) := by
  rw [ts_side₁ hs k h₁ a, ts_side₁ hs m h₂ b, ts_kT_empty (t := h₂), forestUnion_single_single,
    empty_union, ts_kT_single]
  exact ts_ES_merged_side hij hik him hjk hjm hkm h₁ a

/-- The lineage `i` takes the side `S₁` and meets `k`; the lineage `j` takes the side `S₂` and meets
`m`. -/
private theorem ts_ES_split_i :
    ts_ES (forestUnion ((Side.node a 1 (.leaf (s k)) (.hyb h₁)).forestDist s {{i}})
      ((Side.node b 1 (.leaf (s m)) (.hyb h₂)).forestDist s {{j}})) =
      Real.exp (-a) * Real.exp (-b) / 3 +
        (1 - Real.exp (-a) * Real.exp (-b)) * ts_ps ({i} ∪ {k}) := by
  obtain ⟨e0, e1, e2, e3⟩ := ts_score_four hij hik him hjk hjm hkm
  rw [ts_side₁ hs k h₁ a, ts_side₁ hs m h₂ b, ts_kT_single, ts_kT_single,
    forestUnion_single_single, forestUnion_single_single,
    show ({{i}} ∪ {{k}} : Finset (Finset (Fin 4))) = {{i}, {k}} from rfl,
    show ({{j}} ∪ {{m}} : Finset (Finset (Fin 4))) = {{j}, {m}} from rfl, ts_kT_two hik,
    ts_kT_two hjm, forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left,
    ts_forestUnion_add_right, ts_forestUnion_add_right, ts_forestUnion_smul_right,
    ts_forestUnion_smul_right, ts_forestUnion_smul_right, ts_forestUnion_smul_right,
    forestUnion_single_single, forestUnion_single_single, forestUnion_single_single,
    forestUnion_single_single, ts_ES_add, ts_ES_smul, ts_ES_smul, ts_ES_add, ts_ES_add,
    ts_ES_smul, ts_ES_smul, ts_ES_smul, ts_ES_smul, ts_ES_single, ts_ES_single, ts_ES_single,
    ts_ES_single, e0, e1, e2, e3]
  ring

end Placements

/-! ### The network -/

/-- The 3₂-cycle rooted at the top node of its cycle, `net32Sides`: the root is the top node of a
3-cycle whose side `S₁` is an edge of length `a` to a node with the pendant leaf `z`, followed by
the hybrid edge of length `h₁` and inheritance probability `γ`, and whose side `S₂` is an edge of
length `b` to a node with the pendant leaf `w`, followed by the hybrid edge of length `h₂` and
inheritance probability `1 - γ`; below the hybrid node, an edge of length `ℓ` leads to a tree node
with the leaves `x` and `y`. The pendant edges of the leaves have length `1`. -/
def net32Sides (γ ℓ h₁ h₂ a b : ℝ) (x y z w : X) : Net X :=
  .cycle γ (.node a 1 (.leaf z) (.hyb h₁)) (.node b 1 (.leaf w) (.hyb h₂)) ℓ
    (.tree 1 (.leaf x) 1 (.leaf y))

/-- The cycle of `net32Sides`, at its root. -/
def net32SidesCycle (γ ℓ h₁ h₂ a b : ℝ) (x y z w : X) :
    (net32Sides γ ℓ h₁ h₂ a b x y z w).Cycle where
  γ := γ
  side₁ := .node a 1 (.leaf z) (.hyb h₁)
  side₂ := .node b 1 (.leaf w) (.hyb h₂)
  ℓ := ℓ
  below := .tree 1 (.leaf x) 1 (.leaf y)
  mem := by simp [net32Sides, Net.subnets]

omit [DecidableEq X] in
theorem net32Sides_leaves (γ ℓ h₁ h₂ a b : ℝ) (x y z w : X) :
    (net32Sides γ ℓ h₁ h₂ a b x y z w).leaves = [z, w, x, y] := by
  simp [net32Sides, Net.leaves, Side.leaves]

omit [DecidableEq X] in
/-- `net32Sides` is a metric network with distinct leaf labels when its edge lengths are positive
and `0 < γ < 1`. -/
theorem net32Sides_wellFormed {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) {γ ℓ h₁ h₂ a b : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hℓ : 0 < ℓ)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (ha : 0 < a) (hb : 0 < b) :
    (net32Sides γ ℓ h₁ h₂ a b x y z w).WellFormed := by
  refine ⟨?_, ?_⟩
  · simp [net32Sides, Net.IsMetric, Side.IsMetric, Side.nodes, hγ0, hγ1, hℓ, hh₁, hh₂, ha, hb]
  · rw [net32Sides_leaves]
    simp [hxy, hzw, Ne.symm hxz, Ne.symm hyz, Ne.symm hxw, Ne.symm hyw]

/-- The expected score at the top node of `net32Sides`, for the lineages `i, j` below the hybrid
node, `k` on the side `S₁` and `m` on the side `S₂`. -/
private theorem ts_cycle_ES {s : Fin 4 → X} (hs : Function.Injective s) {i j k m : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (him : i ≠ m) (hjk : j ≠ k) (hjm : j ≠ m) (hkm : k ≠ m)
    (γ ℓ h₁ h₂ a b : ℝ) :
    ts_ES ((net32Sides γ ℓ h₁ h₂ a b (s i) (s j) (s k) (s m)).forestDist s) =
      Real.exp (-ℓ) * ((1 - γ) ^ 2 *
          (Real.exp (-h₂) / 3 + (1 - Real.exp (-h₂)) * ts_ps ({i} ∪ {j})) +
        γ * (1 - γ) * (Real.exp (-a) * Real.exp (-b) / 3 +
          (1 - Real.exp (-a) * Real.exp (-b)) * ts_ps ({i} ∪ {k})) +
        γ * (1 - γ) * (Real.exp (-a) * Real.exp (-b) / 3 +
          (1 - Real.exp (-a) * Real.exp (-b)) * ts_ps ({j} ∪ {k})) +
        γ ^ 2 * (Real.exp (-h₁) / 3 + (1 - Real.exp (-h₁)) * ts_ps ({i} ∪ {j}))) +
      (1 - Real.exp (-ℓ)) * ts_ps ({i} ∪ {j}) := by
  set S₁ : Side X := .node a 1 (.leaf (s k)) (.hyb h₁)
  set S₂ : Side X := .node b 1 (.leaf (s m)) (.hyb h₂)
  set H : Net X := .tree 1 (.leaf (s i)) 1 (.leaf (s j))
  have hdef : (net32Sides γ ℓ h₁ h₂ a b (s i) (s j) (s k) (s m)).forestDist s = fun G =>
      ∑ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) *
          (fun F A => forestUnion (S₁.forestDist s (forestBelow F A))
            (S₂.forestDist s (forestBelow F (roots F \ A)))) F A G := rfl
  have hV₁ := ts_sum_apart γ hij fun E E' => ts_ES (forestUnion (S₁.forestDist s E)
    (S₂.forestDist s E'))
  have hV₂ := ts_sum_merged γ hij fun E E' => ts_ES (forestUnion (S₁.forestDist s E)
    (S₂.forestDist s E'))
  rw [hdef, ts_ES_cycle, ts_below hs hij, ts_sum_mix, hV₁, hV₂,
    ts_ES_both₂ hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES_split_i hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES_split_i hs hij.symm hjk hjm hik him hkm h₁ h₂ a b,
    ts_ES_both₁ hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES_merged₂ hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES_merged₁ hs hij hik him hjk hjm hkm h₁ h₂ a b]
  ring

omit [DecidableEq X] in
private theorem ts_inj4 {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) : Function.Injective ![x, y, z, w] := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [eq_comm]

/-- Four distinct lineages are all the lineages. -/
private theorem ts_cover {i j k m : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (him : i ≠ m) (hjk : j ≠ k)
    (hjm : j ≠ m) (hkm : k ≠ m) : ∀ l, l = i ∨ l = j ∨ l = k ∨ l = m := by
  revert i j k m
  decide

private theorem ts_cf {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ a b : ℝ) {s : Fin 4 → X}
    (hs : Function.Injective s) {i j k m : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (him : i ≠ m)
    (hjk : j ≠ k) (hjm : j ≠ m) (hkm : k ≠ m)
    (hsi : s i = x) (hsj : s j = y) (hsk : s k = z) (hsm : s m = w) :
    (net32Sides γ ℓ h₁ h₂ a b x y z w).quartetCF (s 0) (s 1) (s 2) (s 3) =
      Real.exp (-ℓ) * ((1 - γ) ^ 2 *
          (Real.exp (-h₂) / 3 + (1 - Real.exp (-h₂)) * ts_ps ({i} ∪ {j})) +
        γ * (1 - γ) * (Real.exp (-a) * Real.exp (-b) / 3 +
          (1 - Real.exp (-a) * Real.exp (-b)) * ts_ps ({i} ∪ {k})) +
        γ * (1 - γ) * (Real.exp (-a) * Real.exp (-b) / 3 +
          (1 - Real.exp (-a) * Real.exp (-b)) * ts_ps ({j} ∪ {k})) +
        γ ^ 2 * (Real.exp (-h₁) / 3 + (1 - Real.exp (-h₁)) * ts_ps ({i} ∪ {j}))) +
      (1 - Real.exp (-ℓ)) * ts_ps ({i} ∪ {j}) := by
  have hcover : ∀ l, l = i ∨ l = j ∨ l = k ∨ l = m := ts_cover hij hik him hjk hjm hkm
  have hN : (net32Sides γ ℓ h₁ h₂ a b x y z w).leaves.Nodup := by
    rw [net32Sides_leaves]
    simp [hxy, hzw, Ne.symm hxz, Ne.symm hyz, Ne.symm hxw, Ne.symm hyw]
  have hsN : ∀ l, s l ∈ (net32Sides γ ℓ h₁ h₂ a b x y z w).taxa := by
    intro l
    simp only [Net.taxa, net32Sides_leaves, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
      or_false]
    rcases hcover l with rfl | rfl | rfl | rfl <;> simp [hsi, hsj, hsk, hsm]
  have htop : (net32SidesCycle γ ℓ h₁ h₂ a b x y z w).top =
      net32Sides γ ℓ h₁ h₂ a b (s i) (s j) (s k) (s m) := by
    rw [hsi, hsj, hsk, hsm]
    rfl
  have h3 : 3 ≤ #(univ.filter fun l => s l ∈ (net32SidesCycle γ ℓ h₁ h₂ a b x y z w).top.taxa) := by
    have hsub : ({i, j, k} : Finset (Fin 4)) ⊆
        univ.filter fun l => s l ∈ (net32SidesCycle γ ℓ h₁ h₂ a b x y z w).top.taxa := by
      intro l hl
      rw [htop]
      simp only [mem_insert, mem_singleton] at hl
      simp only [mem_filter, mem_univ, true_and, Net.taxa, net32Sides, Net.leaves, Side.leaves,
        List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rcases hl with rfl | rfl | rfl <;> simp
    refine le_trans ?_ (card_le_card hsub)
    rw [card_insert_of_notMem (by simp [hij, hik]), card_pair hjk]
  rw [quartetCF_eq_sum_top _ hN (net32SidesCycle γ ℓ h₁ h₂ a b x y z w) s hsN h3, htop]
  exact ts_cycle_ES hs hij hik him hjk hjm hkm γ ℓ h₁ h₂ a b

/-- **The quartet CFs of `net32Sides`.** For all parameters, the quartet CFs of `net32Sides` on
`x, y, z, w` are those of `N₃₂` (`Brooqs.net32_quartetCF`) with `L = a + b`: the edge of length
`L` between the node of `z` and the top node of `N₃₂`, where `w` hangs, becomes the path of length
`a + b` between the nodes of `z` and `w` through the root. -/
theorem net32Sides_quartetCF {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ a b : ℝ) :
    (net32Sides γ ℓ h₁ h₂ a b x y z w).quartetCF x y z w =
        (net32 γ ℓ h₁ h₂ (a + b) x y z w).quartetCF x y z w ∧
      (net32Sides γ ℓ h₁ h₂ a b x y z w).quartetCF x z y w =
        (net32 γ ℓ h₁ h₂ (a + b) x y z w).quartetCF x z y w ∧
      (net32Sides γ ℓ h₁ h₂ a b x y z w).quartetCF x w y z =
        (net32 γ ℓ h₁ h₂ (a + b) x y z w).quartetCF x w y z := by
  obtain ⟨n0, n1, n2⟩ := net32_quartetCF hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ (a + b)
  have hab : Real.exp (-(a + b)) = Real.exp (-a) * Real.exp (-b) := by
    rw [neg_add, Real.exp_add]
  rw [n0, n1, n2, hab]
  have p01 : ts_ps ({0} ∪ {1}) = 1 := by rw [ts_ps, ite_eq_left (by decide)]
  have p02 : ts_ps ({0} ∪ {2}) = 0 := by rw [ts_ps, ite_eq_right (by decide)]
  have p12 : ts_ps ({1} ∪ {2}) = 0 := by rw [ts_ps, ite_eq_right (by decide)]
  have p03 : ts_ps ({0} ∪ {3}) = 0 := by rw [ts_ps, ite_eq_right (by decide)]
  have p21 : ts_ps ({2} ∪ {1}) = 0 := by rw [ts_ps, ite_eq_right (by decide)]
  have p23 : ts_ps ({2} ∪ {3}) = 1 := by rw [ts_ps, ite_eq_left (by decide)]
  refine ⟨?_, ?_, ?_⟩
  · have h := ts_cf hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ a b (ts_inj4 hxy hxz hxw hyz hyw hzw)
      (i := 0) (j := 1) (k := 2) (m := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl rfl rfl rfl
    rw [p01, p02, p12] at h
    change (net32Sides γ ℓ h₁ h₂ a b x y z w).quartetCF x y z w = _ at h
    rw [h]
    ring
  · have h := ts_cf hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ a b
      (ts_inj4 hxz hxy hxw (Ne.symm hyz) hzw hyw)
      (i := 0) (j := 2) (k := 1) (m := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl rfl rfl rfl
    rw [p02, p01, p21] at h
    change (net32Sides γ ℓ h₁ h₂ a b x y z w).quartetCF x z y w = _ at h
    rw [h]
    ring
  · have h := ts_cf hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ a b
      (ts_inj4 hxw hxy hxz (Ne.symm hyw) (Ne.symm hzw) hyz)
      (i := 0) (j := 2) (k := 3) (m := 1) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl rfl rfl rfl
    rw [p02, p03, p23] at h
    change (net32Sides γ ℓ h₁ h₂ a b x y z w).quartetCF x w y z = _ at h
    rw [h]
    ring

/-- `net32Sides` displays `xy|zw` and neither `xz|yw` nor `xw|yz`: the taxa `x` and `y` lie below
the hybrid node, in every displayed tree. -/
theorem net32Sides_displays {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ a b : ℝ) :
    (net32Sides γ ℓ h₁ h₂ a b x y z w).Displays x y z w ∧
      ¬ (net32Sides γ ℓ h₁ h₂ a b x y z w).Displays x z y w ∧
      ¬ (net32Sides γ ℓ h₁ h₂ a b x y z w).Displays x w y z := by
  have hN : (net32Sides γ ℓ h₁ h₂ a b x y z w).leaves.Nodup := by
    rw [net32Sides_leaves]
    simp [hxy, hzw, Ne.symm hxz, Ne.symm hyz, Ne.symm hxw, Ne.symm hyw]
  have hM : (Net.tree 1 (.leaf x) 1 (.leaf y) : Net X) ∈
      (net32Sides γ ℓ h₁ h₂ a b x y z w).subnets := by
    simp [net32Sides, Net.subnets]
  refine Net.displays_of_subnet hN hM ?_ ?_ ?_ ?_ <;>
    simp [Net.taxa_tree, Net.taxa_leaf, Ne.symm hxz, Ne.symm hxw, Ne.symm hyz, Ne.symm hyw]

/-- **The anomaly zone of `net32Sides`.** For all parameters, the quartet `xy|zw` that
`net32Sides` displays has a strictly smaller CF than `xz|yw` (and `xw|yz`) iff
`γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-h₂}) + (e^ℓ - 1) < γ(1 - γ)(1 - e^{-(a + b)})`. -/
theorem net32Sides_anomalous_iff {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ a b : ℝ) :
    (net32Sides γ ℓ h₁ h₂ a b x y z w).quartetCF x y z w <
        (net32Sides γ ℓ h₁ h₂ a b x y z w).quartetCF x z y w ↔
      γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) + (Real.exp ℓ - 1) <
        γ * (1 - γ) * (1 - Real.exp (-(a + b))) := by
  obtain ⟨e0, e1, -⟩ := net32Sides_quartetCF hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ a b
  rw [e0, e1]
  exact net32_anomalous_iff hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ (a + b)

/-- **The regular zone of `net32Sides`.** For all parameters, the quartet `xy|zw` that
`net32Sides` displays has a strictly larger CF than `xz|yw` and `xw|yz` iff
`γ(1 - γ)(1 - e^{-(a + b)}) < γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-h₂}) + (e^ℓ - 1)`. -/
theorem net32Sides_regular_iff {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ a b : ℝ) :
    (net32Sides γ ℓ h₁ h₂ a b x y z w).quartetCF x z y w <
        (net32Sides γ ℓ h₁ h₂ a b x y z w).quartetCF x y z w ↔
      γ * (1 - γ) * (1 - Real.exp (-(a + b))) <
        γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-h₂)) + (Real.exp ℓ - 1) := by
  obtain ⟨e0, e1, -⟩ := net32Sides_quartetCF hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ a b
  rw [e0, e1]
  exact net32_regular_iff hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ (a + b)

/-! ### `z` and `w` on one side of the cycle -/

private theorem ts_side₂ (s : Fin 4 → X) (h₂ : ℝ) (E : Finset (Finset (Fin 4))) :
    (Side.hyb h₂ : Side X).forestDist s E = Pi.single E 1 ᵥ* kingmanTransition h₂ := by
  show kingmanTransition h₂ E = _
  rw [ts_row (kingmanTransition h₂) E]

/-- A side with two nodes: the forest `E` takes the hybrid edge, the lineage `m` of the lower
pendant leaf joins it, the lineages travel along the edge of length `b`, the lineage `k` of the
upper pendant leaf joins them, and they travel along the edge of length `a` to the top node. -/
private theorem ts_side_two {s : Fin 4 → X} (hs : Function.Injective s) (k m : Fin 4)
    (h₁ a b : ℝ) (E : Finset (Finset (Fin 4))) :
    (Side.node a 1 (.leaf (s k)) (.node b 1 (.leaf (s m)) (.hyb h₁))).forestDist s E =
      forestUnion (forestUnion (Pi.single E 1 ᵥ* kingmanTransition h₁) (Pi.single {{m}} 1) ᵥ*
        kingmanTransition b) (Pi.single {{k}} 1) ᵥ* kingmanTransition a := by
  show forestUnion ((Side.node b 1 (.leaf (s m)) (.hyb h₁)).forestDist s E)
    ((Net.leaf (s k)).forestDist s ᵥ* kingmanTransition 1) ᵥ* kingmanTransition a = _
  rw [ts_leaf_kT hs k, ts_side₁ hs m h₁ b E]

/-- A good forest `F` of three lineages travels along an edge of length `t`, is joined by the
lineage `k`, and travels along an edge of length `t'`: the expected score is the score of `F`. -/
private theorem ts_ES_union_two {F : Finset (Finset (Fin 4))} (hF : IsGood F) {k : Fin 4}
    (hk : Disjoint (ADR11.lineages F) {k}) (h3 : 3 ≤ #(ADR11.lineages F)) (t t' : ℝ) :
    ts_ES (forestUnion (Pi.single F 1 ᵥ* kingmanTransition t) (Pi.single {{k}} 1) ᵥ*
      kingmanTransition t') = quartetScore F := by
  have hu : NiceKernel {k} (unionKernel (Pi.single ({{k}} : Finset (Finset (Fin 4))) 1)) := by
    refine niceKernel_unionKernel (by simp) fun E hE => ?_
    have hE' : E = {{k}} := by
      by_contra hne
      exact hE (by simp [hne])
    subst hE'
    exact ts_single_facts k
  have hu' := hu.mul (niceKernel_kingmanTransition t') (disjoint_empty_right _)
  rw [union_empty] at hu'
  have hnice := (niceKernel_kingmanTransition t).mul hu' (disjoint_empty_left _)
  rw [empty_union] at hnice
  rw [forestUnion_eq_vecMul, vecMul_vecMul, vecMul_vecMul]
  simp only [ts_ES, ts_vecMul_single_apply]
  exact hnice.score hF hk h3

/-- The splits `{m, k} | {i, j}` and `{i, j} | {m, k}` have the same score. -/
private theorem ts_ps_compl {i j k m : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (him : i ≠ m)
    (hjk : j ≠ k) (hjm : j ≠ m) (hkm : k ≠ m) : ts_ps ({m} ∪ {k}) = ts_ps ({i} ∪ {j}) := by
  have h : ({m} ∪ {k} = ({0, 1} : Finset (Fin 4)) ∨ {m} ∪ {k} = ({2, 3} : Finset (Fin 4))) ↔
      ({i} ∪ {j} = ({0, 1} : Finset (Fin 4)) ∨ {i} ∪ {j} = ({2, 3} : Finset (Fin 4))) := by
    revert i j k m
    decide
  unfold ts_ps
  rw [if_congr h rfl rfl]

section PlacementsOneSide

variable {s : Fin 4 → X} (hs : Function.Injective s) {i j k m : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
  (him : i ≠ m) (hjk : j ≠ k) (hjm : j ≠ m) (hkm : k ≠ m) (h₁ h₂ a b : ℝ)
include hs hij hik him hjk hjm hkm

omit hij hik him hjk hjm in
/-- The side `S₁` without lineages from below the hybrid node brings `k` and `m`, which coalesce
along the edge of length `a` with probability `1 - e^{-a}`. -/
private theorem ts_side_two_empty :
    (Side.node a 1 (.leaf (s k)) (.node b 1 (.leaf (s m)) (.hyb h₁))).forestDist s ∅ =
      Real.exp (-a) • Pi.single ({{m}, {k}} : Finset (Finset (Fin 4))) 1 +
        (1 - Real.exp (-a)) • Pi.single (insert ({m} ∪ {k}) {{m}, {k}}) 1 := by
  rw [ts_side_two hs k m h₁ a b, ts_kT_empty, forestUnion_single_single, empty_union,
    ts_kT_single, forestUnion_single_single,
    show ({{m}} ∪ {{k}} : Finset (Finset (Fin 4))) = {{m}, {k}} from rfl, ts_kT_two hkm.symm]

/-- The lineages `i, j` both take the side `S₂`. -/
private theorem ts_ES1_both₂ :
    ts_ES (forestUnion
      ((Side.node a 1 (.leaf (s k)) (.node b 1 (.leaf (s m)) (.hyb h₁))).forestDist s ∅)
      ((Side.hyb h₂ : Side X).forestDist s {{i}, {j}})) =
      Real.exp (-a) * Real.exp (-h₂) / 3 +
        (1 - Real.exp (-a) * Real.exp (-h₂)) * ts_ps ({i} ∪ {j}) := by
  obtain ⟨e0, e1, e2, e3⟩ := ts_score_four him.symm hkm.symm hjm.symm hik hij hjk.symm
  rw [ts_side_two_empty hs hkm h₁ a b, ts_side₂, ts_kT_two hij,
    forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left,
    ts_forestUnion_add_right, ts_forestUnion_add_right, ts_forestUnion_smul_right,
    ts_forestUnion_smul_right, ts_forestUnion_smul_right, ts_forestUnion_smul_right,
    forestUnion_single_single, forestUnion_single_single, forestUnion_single_single,
    forestUnion_single_single, ts_ES_add, ts_ES_smul, ts_ES_smul, ts_ES_add, ts_ES_add,
    ts_ES_smul, ts_ES_smul, ts_ES_smul, ts_ES_smul, ts_ES_single, ts_ES_single, ts_ES_single,
    ts_ES_single, e0, e1, e2, e3, ts_ps_compl hij hik him hjk hjm hkm]
  ring

/-- The lineages `i, j` both take the side `S₁`, where they meet `m` and then `k`. -/
private theorem ts_ES1_both₁ :
    ts_ES (forestUnion
      ((Side.node a 1 (.leaf (s k)) (.node b 1 (.leaf (s m)) (.hyb h₁))).forestDist s {{i}, {j}})
      ((Side.hyb h₂ : Side X).forestDist s ∅)) =
      Real.exp (-h₁) / 3 + (1 - Real.exp (-h₁)) * ts_ps ({i} ∪ {j}) := by
  obtain ⟨g1, l1, g2, l2⟩ := ts_three_good hij him hjm
  obtain ⟨d1, d2⟩ := ts_three_disjoint hij hik hjk hkm.symm
  rw [ts_side_two hs k m h₁ a b, ts_side₂, ts_kT_empty (t := h₂), forestUnion_single_empty,
    ts_kT_two hij, forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left,
    forestUnion_single_single, forestUnion_single_single, add_vecMul, smul_vecMul, smul_vecMul,
    forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left, add_vecMul, smul_vecMul,
    smul_vecMul, ts_ES_add, ts_ES_smul, ts_ES_smul, ts_ES_union_two g1 d1 l1.ge,
    ts_ES_union_two g2 d2 l2.ge, ts_score_three hij him hjm, ts_score_merged hij him hjm]
  ring

/-- The lineage `i` takes the side `S₁`, where it meets `m` and then `k`; the lineage `j` takes the
side `S₂`. -/
private theorem ts_ES1_split_i :
    ts_ES (forestUnion
      ((Side.node a 1 (.leaf (s k)) (.node b 1 (.leaf (s m)) (.hyb h₁))).forestDist s {{i}})
      ((Side.hyb h₂ : Side X).forestDist s {{j}})) =
      Real.exp (-b) / 3 + (1 - Real.exp (-b)) * ts_ps ({i} ∪ {m}) := by
  obtain ⟨g1, l1, g2, l2⟩ := ts_three_good him hik hkm.symm
  obtain ⟨d1, d2⟩ := ts_three_disjoint him hij hjm.symm hjk.symm
  rw [ts_side_two hs k m h₁ a b, ts_side₂, ts_kT_single, ts_kT_single, forestUnion_single_single,
    show ({{i}} ∪ {{m}} : Finset (Finset (Fin 4))) = {{i}, {m}} from rfl, ts_kT_two him,
    forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left,
    forestUnion_single_single, forestUnion_single_single, add_vecMul, smul_vecMul, smul_vecMul,
    forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left, ts_ES_add, ts_ES_smul,
    ts_ES_smul, ts_ES_union g1 d1 l1.ge, ts_ES_union g2 d2 l2.ge, ts_score_three him hik hkm.symm,
    ts_score_merged him hik hkm.symm]
  ring

/-- The lineages `i, j` have coalesced below the hybrid node and take the side `S₂`. -/
private theorem ts_ES1_merged₂ :
    ts_ES (forestUnion
      ((Side.node a 1 (.leaf (s k)) (.node b 1 (.leaf (s m)) (.hyb h₁))).forestDist s ∅)
      ((Side.hyb h₂ : Side X).forestDist s (insert ({i} ∪ {j}) {{i}, {j}}))) =
      ts_ps ({i} ∪ {j}) := by
  obtain ⟨-, -, e2, e3⟩ := ts_score_four him.symm hkm.symm hjm.symm hik hij hjk.symm
  rw [ts_side_two_empty hs hkm h₁ a b, ts_side₂, ts_kT_merged hij,
    forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left,
    forestUnion_single_single, forestUnion_single_single, ts_ES_add, ts_ES_smul, ts_ES_smul,
    ts_ES_single, ts_ES_single, e2, e3, ts_ps_compl hij hik him hjk hjm hkm]
  ring

/-- The lineages `i, j` have coalesced below the hybrid node and take the side `S₁`. -/
private theorem ts_ES1_merged₁ :
    ts_ES (forestUnion
      ((Side.node a 1 (.leaf (s k)) (.node b 1 (.leaf (s m)) (.hyb h₁))).forestDist s
        (insert ({i} ∪ {j}) {{i}, {j}})) ((Side.hyb h₂ : Side X).forestDist s ∅)) =
      ts_ps ({i} ∪ {j}) := by
  obtain ⟨-, -, g2, l2⟩ := ts_three_good hij him hjm
  obtain ⟨-, d2⟩ := ts_three_disjoint hij hik hjk hkm.symm
  rw [ts_side_two hs k m h₁ a b, ts_side₂, ts_kT_empty (t := h₂), forestUnion_single_empty,
    ts_kT_merged hij, forestUnion_single_single, ts_ES_union_two g2 d2 l2.ge,
    ts_score_merged hij him hjm]

end PlacementsOneSide

/-- The 3₂-cycle with `z` and `w` on one side of the cycle: the root is the top node of a 3-cycle
whose side `S₁` is an edge of length `a` to a node with the pendant leaf `z`, an edge of length `b`
to a node with the pendant leaf `w`, and the hybrid edge of length `h₁` and inheritance probability
`γ`, and whose side `S₂` is a hybrid edge of length `h₂` and inheritance probability `1 - γ`;
below the hybrid node, an edge of length `ℓ` leads to a tree node with the leaves `x` and `y`. The
pendant edges of the leaves have length `1`. -/
def net32OneSide (γ ℓ h₁ h₂ a b : ℝ) (x y z w : X) : Net X :=
  .cycle γ (.node a 1 (.leaf z) (.node b 1 (.leaf w) (.hyb h₁))) (.hyb h₂) ℓ
    (.tree 1 (.leaf x) 1 (.leaf y))

/-- The cycle of `net32OneSide`, at its root. -/
def net32OneSideCycle (γ ℓ h₁ h₂ a b : ℝ) (x y z w : X) :
    (net32OneSide γ ℓ h₁ h₂ a b x y z w).Cycle where
  γ := γ
  side₁ := .node a 1 (.leaf z) (.node b 1 (.leaf w) (.hyb h₁))
  side₂ := .hyb h₂
  ℓ := ℓ
  below := .tree 1 (.leaf x) 1 (.leaf y)
  mem := by simp [net32OneSide, Net.subnets]

omit [DecidableEq X] in
theorem net32OneSide_leaves (γ ℓ h₁ h₂ a b : ℝ) (x y z w : X) :
    (net32OneSide γ ℓ h₁ h₂ a b x y z w).leaves = [z, w, x, y] := by
  simp [net32OneSide, Net.leaves, Side.leaves]

omit [DecidableEq X] in
/-- `net32OneSide` is a metric network with distinct leaf labels when its edge lengths are positive
and `0 < γ < 1`. -/
theorem net32OneSide_wellFormed {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) {γ ℓ h₁ h₂ a b : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hℓ : 0 < ℓ) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (ha : 0 < a) (hb : 0 < b) :
    (net32OneSide γ ℓ h₁ h₂ a b x y z w).WellFormed := by
  refine ⟨?_, ?_⟩
  · simp [net32OneSide, Net.IsMetric, Side.IsMetric, Side.nodes, hγ0, hγ1, hℓ, hh₁, hh₂, ha, hb]
  · rw [net32OneSide_leaves]
    simp [hxy, hzw, Ne.symm hxz, Ne.symm hyz, Ne.symm hxw, Ne.symm hyw]

/-- The expected score at the top node of `net32OneSide`, for the lineages `i, j` below the hybrid
node and `k`, `m` on the side `S₁`. -/
private theorem ts1_cycle_ES {s : Fin 4 → X} (hs : Function.Injective s) {i j k m : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (him : i ≠ m) (hjk : j ≠ k) (hjm : j ≠ m) (hkm : k ≠ m)
    (γ ℓ h₁ h₂ a b : ℝ) :
    ts_ES ((net32OneSide γ ℓ h₁ h₂ a b (s i) (s j) (s k) (s m)).forestDist s) =
      Real.exp (-ℓ) * ((1 - γ) ^ 2 * (Real.exp (-a) * Real.exp (-h₂) / 3 +
          (1 - Real.exp (-a) * Real.exp (-h₂)) * ts_ps ({i} ∪ {j})) +
        γ * (1 - γ) * (Real.exp (-b) / 3 + (1 - Real.exp (-b)) * ts_ps ({i} ∪ {m})) +
        γ * (1 - γ) * (Real.exp (-b) / 3 + (1 - Real.exp (-b)) * ts_ps ({j} ∪ {m})) +
        γ ^ 2 * (Real.exp (-h₁) / 3 + (1 - Real.exp (-h₁)) * ts_ps ({i} ∪ {j}))) +
      (1 - Real.exp (-ℓ)) * ts_ps ({i} ∪ {j}) := by
  set S₁ : Side X := .node a 1 (.leaf (s k)) (.node b 1 (.leaf (s m)) (.hyb h₁))
  set S₂ : Side X := .hyb h₂
  set H : Net X := .tree 1 (.leaf (s i)) 1 (.leaf (s j))
  have hdef : (net32OneSide γ ℓ h₁ h₂ a b (s i) (s j) (s k) (s m)).forestDist s = fun G =>
      ∑ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) *
          (fun F A => forestUnion (S₁.forestDist s (forestBelow F A))
            (S₂.forestDist s (forestBelow F (roots F \ A)))) F A G := rfl
  have hV₁ := ts_sum_apart γ hij fun E E' => ts_ES (forestUnion (S₁.forestDist s E)
    (S₂.forestDist s E'))
  have hV₂ := ts_sum_merged γ hij fun E E' => ts_ES (forestUnion (S₁.forestDist s E)
    (S₂.forestDist s E'))
  rw [hdef, ts_ES_cycle, ts_below hs hij, ts_sum_mix, hV₁, hV₂,
    ts_ES1_both₂ hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES1_split_i hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES1_split_i hs hij.symm hjk hjm hik him hkm h₁ h₂ a b,
    ts_ES1_both₁ hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES1_merged₂ hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES1_merged₁ hs hij hik him hjk hjm hkm h₁ h₂ a b]
  ring

private theorem ts1_cf {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ a b : ℝ) {s : Fin 4 → X}
    (hs : Function.Injective s) {i j k m : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (him : i ≠ m)
    (hjk : j ≠ k) (hjm : j ≠ m) (hkm : k ≠ m)
    (hsi : s i = x) (hsj : s j = y) (hsk : s k = z) (hsm : s m = w) :
    (net32OneSide γ ℓ h₁ h₂ a b x y z w).quartetCF (s 0) (s 1) (s 2) (s 3) =
      Real.exp (-ℓ) * ((1 - γ) ^ 2 * (Real.exp (-a) * Real.exp (-h₂) / 3 +
          (1 - Real.exp (-a) * Real.exp (-h₂)) * ts_ps ({i} ∪ {j})) +
        γ * (1 - γ) * (Real.exp (-b) / 3 + (1 - Real.exp (-b)) * ts_ps ({i} ∪ {m})) +
        γ * (1 - γ) * (Real.exp (-b) / 3 + (1 - Real.exp (-b)) * ts_ps ({j} ∪ {m})) +
        γ ^ 2 * (Real.exp (-h₁) / 3 + (1 - Real.exp (-h₁)) * ts_ps ({i} ∪ {j}))) +
      (1 - Real.exp (-ℓ)) * ts_ps ({i} ∪ {j}) := by
  have hcover : ∀ l, l = i ∨ l = j ∨ l = k ∨ l = m := ts_cover hij hik him hjk hjm hkm
  have hN : (net32OneSide γ ℓ h₁ h₂ a b x y z w).leaves.Nodup := by
    rw [net32OneSide_leaves]
    simp [hxy, hzw, Ne.symm hxz, Ne.symm hyz, Ne.symm hxw, Ne.symm hyw]
  have hsN : ∀ l, s l ∈ (net32OneSide γ ℓ h₁ h₂ a b x y z w).taxa := by
    intro l
    simp only [Net.taxa, net32OneSide_leaves, List.mem_toFinset, List.mem_cons,
      List.not_mem_nil, or_false]
    rcases hcover l with rfl | rfl | rfl | rfl <;> simp [hsi, hsj, hsk, hsm]
  have htop : (net32OneSideCycle γ ℓ h₁ h₂ a b x y z w).top =
      net32OneSide γ ℓ h₁ h₂ a b (s i) (s j) (s k) (s m) := by
    rw [hsi, hsj, hsk, hsm]
    rfl
  have h3 : 3 ≤ #(univ.filter fun l =>
      s l ∈ (net32OneSideCycle γ ℓ h₁ h₂ a b x y z w).top.taxa) := by
    have hsub : ({i, j, k} : Finset (Fin 4)) ⊆
        univ.filter fun l => s l ∈ (net32OneSideCycle γ ℓ h₁ h₂ a b x y z w).top.taxa := by
      intro l hl
      rw [htop]
      simp only [mem_insert, mem_singleton] at hl
      simp only [mem_filter, mem_univ, true_and, Net.taxa, net32OneSide, Net.leaves,
        Side.leaves, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false]
      rcases hl with rfl | rfl | rfl <;> simp
    refine le_trans ?_ (card_le_card hsub)
    rw [card_insert_of_notMem (by simp [hij, hik]), card_pair hjk]
  rw [quartetCF_eq_sum_top _ hN (net32OneSideCycle γ ℓ h₁ h₂ a b x y z w) s hsN h3, htop]
  exact ts1_cycle_ES hs hij hik him hjk hjm hkm γ ℓ h₁ h₂ a b

/-- **The quartet CFs of the 3₂-cycle with `z` and `w` on one side.** For all parameters, the
quartet CFs of `net32OneSide` on `x, y, z, w` are those of `N₃₂` (`Brooqs.net32_quartetCF`) with
`h₂ + a` for `h₂` and `b` for `L`: in the semidirected network, where the root is suppressed, the
edge of length `a` and the hybrid edge of length `h₂` form one hybrid edge from the node of `z` to
the hybrid node, the edge of length `b` joins the nodes of `z` and `w`, and `w` takes the place of
the `z` of `N₃₂`, next to the hybrid edge of inheritance probability `γ`. -/
theorem net32OneSide_quartetCF {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ a b : ℝ) :
    (net32OneSide γ ℓ h₁ h₂ a b x y z w).quartetCF x y z w =
        (net32 γ ℓ h₁ (a + h₂) b x y z w).quartetCF x y z w ∧
      (net32OneSide γ ℓ h₁ h₂ a b x y z w).quartetCF x z y w =
        (net32 γ ℓ h₁ (a + h₂) b x y z w).quartetCF x z y w ∧
      (net32OneSide γ ℓ h₁ h₂ a b x y z w).quartetCF x w y z =
        (net32 γ ℓ h₁ (a + h₂) b x y z w).quartetCF x w y z := by
  obtain ⟨n0, n1, n2⟩ := net32_quartetCF hxy hxz hxw hyz hyw hzw γ ℓ h₁ (a + h₂) b
  have hah : Real.exp (-(a + h₂)) = Real.exp (-a) * Real.exp (-h₂) := by
    rw [neg_add, Real.exp_add]
  rw [n0, n1, n2, hah]
  have p01 : ts_ps ({0} ∪ {1}) = 1 := by rw [ts_ps, ite_eq_left (by decide)]
  have p02 : ts_ps ({0} ∪ {2}) = 0 := by rw [ts_ps, ite_eq_right (by decide)]
  have p03 : ts_ps ({0} ∪ {3}) = 0 := by rw [ts_ps, ite_eq_right (by decide)]
  have p13 : ts_ps ({1} ∪ {3}) = 0 := by rw [ts_ps, ite_eq_right (by decide)]
  have p21 : ts_ps ({2} ∪ {1}) = 0 := by rw [ts_ps, ite_eq_right (by decide)]
  have p23 : ts_ps ({2} ∪ {3}) = 1 := by rw [ts_ps, ite_eq_left (by decide)]
  refine ⟨?_, ?_, ?_⟩
  · have h := ts1_cf hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ a b (ts_inj4 hxy hxz hxw hyz hyw hzw)
      (i := 0) (j := 1) (k := 2) (m := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl rfl rfl rfl
    rw [p01, p03, p13] at h
    change (net32OneSide γ ℓ h₁ h₂ a b x y z w).quartetCF x y z w = _ at h
    rw [h]
    ring
  · have h := ts1_cf hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ a b
      (ts_inj4 hxz hxy hxw (Ne.symm hyz) hzw hyw)
      (i := 0) (j := 2) (k := 1) (m := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl rfl rfl rfl
    rw [p02, p03, p23] at h
    change (net32OneSide γ ℓ h₁ h₂ a b x y z w).quartetCF x z y w = _ at h
    rw [h]
    ring
  · have h := ts1_cf hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ a b
      (ts_inj4 hxw hxy hxz (Ne.symm hyw) (Ne.symm hzw) hyz)
      (i := 0) (j := 2) (k := 3) (m := 1) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl rfl rfl rfl
    rw [p02, p01, p21] at h
    change (net32OneSide γ ℓ h₁ h₂ a b x y z w).quartetCF x w y z = _ at h
    rw [h]
    ring

/-- `net32OneSide` displays `xy|zw` and neither `xz|yw` nor `xw|yz`. -/
theorem net32OneSide_displays {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ a b : ℝ) :
    (net32OneSide γ ℓ h₁ h₂ a b x y z w).Displays x y z w ∧
      ¬ (net32OneSide γ ℓ h₁ h₂ a b x y z w).Displays x z y w ∧
      ¬ (net32OneSide γ ℓ h₁ h₂ a b x y z w).Displays x w y z := by
  have hN : (net32OneSide γ ℓ h₁ h₂ a b x y z w).leaves.Nodup := by
    rw [net32OneSide_leaves]
    simp [hxy, hzw, Ne.symm hxz, Ne.symm hyz, Ne.symm hxw, Ne.symm hyw]
  have hM : (Net.tree 1 (.leaf x) 1 (.leaf y) : Net X) ∈
      (net32OneSide γ ℓ h₁ h₂ a b x y z w).subnets := by
    simp [net32OneSide, Net.subnets]
  refine Net.displays_of_subnet hN hM ?_ ?_ ?_ ?_ <;>
    simp [Net.taxa_tree, Net.taxa_leaf, Ne.symm hxz, Ne.symm hxw, Ne.symm hyz, Ne.symm hyw]

/-- **The anomaly zone of the 3₂-cycle with `z` and `w` on one side.** For all parameters, the
quartet `xy|zw` that `net32OneSide` displays has a strictly smaller CF than `xz|yw` (and `xw|yz`)
iff `γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-(a + h₂)}) + (e^ℓ - 1) < γ(1 - γ)(1 - e^{-b})`. -/
theorem net32OneSide_anomalous_iff {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ a b : ℝ) :
    (net32OneSide γ ℓ h₁ h₂ a b x y z w).quartetCF x y z w <
        (net32OneSide γ ℓ h₁ h₂ a b x y z w).quartetCF x z y w ↔
      γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-(a + h₂))) +
        (Real.exp ℓ - 1) < γ * (1 - γ) * (1 - Real.exp (-b)) := by
  obtain ⟨e0, e1, -⟩ := net32OneSide_quartetCF hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ a b
  rw [e0, e1]
  exact net32_anomalous_iff hxy hxz hxw hyz hyw hzw γ ℓ h₁ (a + h₂) b

/-- **The regular zone of the 3₂-cycle with `z` and `w` on one side.** For all parameters, the
quartet `xy|zw` that `net32OneSide` displays has a strictly larger CF than `xz|yw` and `xw|yz` iff
`γ(1 - γ)(1 - e^{-b}) < γ²(1 - e^{-h₁}) + (1 - γ)²(1 - e^{-(a + h₂)}) + (e^ℓ - 1)`. -/
theorem net32OneSide_regular_iff {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (γ ℓ h₁ h₂ a b : ℝ) :
    (net32OneSide γ ℓ h₁ h₂ a b x y z w).quartetCF x z y w <
        (net32OneSide γ ℓ h₁ h₂ a b x y z w).quartetCF x y z w ↔
      γ * (1 - γ) * (1 - Real.exp (-b)) <
        γ ^ 2 * (1 - Real.exp (-h₁)) + (1 - γ) ^ 2 * (1 - Real.exp (-(a + h₂))) +
          (Real.exp ℓ - 1) := by
  obtain ⟨e0, e1, -⟩ := net32OneSide_quartetCF hxy hxz hxw hyz hyw hzw γ ℓ h₁ h₂ a b
  rw [e0, e1]
  exact net32_regular_iff hxy hxz hxw hyz hyw hzw γ ℓ h₁ (a + h₂) b

/-! ### The top node of a cycle, from the forests arriving along its sides

The computations above, for any network `H` below the hybrid node, from which the lineages `0` and
`1` arrive apart with any probability `p`, and for any sides that act on the forests as those of
`N₃₂`, `net32Sides` or `net32OneSide`: `Brooqs.expectedScore_top_outside`,
`Brooqs.expectedScore_top_sides`, `Brooqs.expectedScore_top_oneSide`. They serve the anomalous
configuration in an arbitrary network (`AnomalyGeneral.lean`). -/

/-! The six placements of the lineages `i, j` when the fourth lineage is outside the cycle, as in
`ThreeCycle.lean`. -/

section PlacementsThree

variable {s : Fin 4 → X} (hs : Function.Injective s) {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
  (hjk : j ≠ k) (h₁ h₂ L : ℝ)
include hs hij hik hjk

/-- The lineages `i, j` both take the side `S₂`. -/
private theorem ts3_both₂ :
    ts_ES (forestUnion ((Side.node L 1 (.leaf (s k)) (.hyb h₁)).forestDist s ∅)
      ((Side.hyb h₂ : Side X).forestDist s {{i}, {j}})) =
      Real.exp (-h₂) / 3 + (1 - Real.exp (-h₂)) * ts_ps ({i} ∪ {j}) := by
  rw [ts_side₁ hs k h₁ L, ts_side₂ s h₂, ts_kT_empty, forestUnion_single_single, empty_union,
    ts_kT_single, ts_kT_two hij, ts_forestUnion_add_right, ts_forestUnion_smul_right,
    ts_forestUnion_smul_right, forestUnion_single_single, forestUnion_single_single, ts_ES_add,
    ts_ES_smul, ts_ES_smul, ts_ES_single, ts_ES_single, union_comm, ts_score_three hij hik hjk,
    union_comm, ts_score_merged hij hik hjk]
  ring

/-- The lineage `j` takes the side `S₁` and meets `k`; the lineage `i` takes the side `S₂`. -/
private theorem ts3_split_j :
    ts_ES (forestUnion ((Side.node L 1 (.leaf (s k)) (.hyb h₁)).forestDist s {{j}})
      ((Side.hyb h₂ : Side X).forestDist s {{i}})) =
      Real.exp (-L) / 3 + (1 - Real.exp (-L)) * ts_ps ({j} ∪ {k}) := by
  rw [ts_side₁ hs k h₁ L, ts_side₂ s h₂, ts_kT_single, forestUnion_single_single,
    show ({{j}} ∪ {{k}} : Finset (Finset (Fin 4))) = {{j}, {k}} from rfl, ts_kT_two hjk,
    ts_kT_single, forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left,
    forestUnion_single_single, forestUnion_single_single, ts_ES_add, ts_ES_smul, ts_ES_smul,
    ts_ES_single, ts_ES_single, ts_score_three hjk hij.symm hik.symm,
    ts_score_merged hjk hij.symm hik.symm]
  ring

/-- The lineage `i` takes the side `S₁` and meets `k`; the lineage `j` takes the side `S₂`. -/
private theorem ts3_split_i :
    ts_ES (forestUnion ((Side.node L 1 (.leaf (s k)) (.hyb h₁)).forestDist s {{i}})
      ((Side.hyb h₂ : Side X).forestDist s {{j}})) =
      Real.exp (-L) / 3 + (1 - Real.exp (-L)) * ts_ps ({i} ∪ {k}) := by
  rw [ts_side₁ hs k h₁ L, ts_side₂ s h₂, ts_kT_single, forestUnion_single_single,
    show ({{i}} ∪ {{k}} : Finset (Finset (Fin 4))) = {{i}, {k}} from rfl, ts_kT_two hik,
    ts_kT_single, forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left,
    forestUnion_single_single, forestUnion_single_single, ts_ES_add, ts_ES_smul, ts_ES_smul,
    ts_ES_single, ts_ES_single, ts_score_three hik hij hjk.symm,
    ts_score_merged hik hij hjk.symm]
  ring

/-- The lineages `i, j` both take the side `S₁` and meet `k`. -/
private theorem ts3_both₁ :
    ts_ES (forestUnion ((Side.node L 1 (.leaf (s k)) (.hyb h₁)).forestDist s {{i}, {j}})
      ((Side.hyb h₂ : Side X).forestDist s ∅)) =
      Real.exp (-h₁) / 3 + (1 - Real.exp (-h₁)) * ts_ps ({i} ∪ {j}) := by
  obtain ⟨g1, -, g2, -⟩ := ts_three_good hij hik hjk
  obtain ⟨-, l1, -, l2⟩ := ts_three_good hij hik hjk
  have hnice := niceKernel_kingmanTransition L
  rw [ts_side₁ hs k h₁ L, ts_side₂ s h₂, ts_kT_empty, forestUnion_single_empty, ts_kT_two hij,
    forestUnion_add_left, forestUnion_smul_left, forestUnion_smul_left, forestUnion_single_single,
    forestUnion_single_single, add_vecMul, smul_vecMul, smul_vecMul, ts_ES_add, ts_ES_smul,
    ts_ES_smul, ts_ES_nice hnice g1 (disjoint_empty_right _) l1.ge,
    ts_ES_nice hnice g2 (disjoint_empty_right _) l2.ge, ts_score_three hij hik hjk,
    ts_score_merged hij hik hjk]
  ring

/-- The lineages `i, j` have coalesced below the hybrid node and take the side `S₂`. -/
private theorem ts3_merged₂ :
    ts_ES (forestUnion ((Side.node L 1 (.leaf (s k)) (.hyb h₁)).forestDist s ∅)
      ((Side.hyb h₂ : Side X).forestDist s (insert ({i} ∪ {j}) {{i}, {j}}))) =
      ts_ps ({i} ∪ {j}) := by
  rw [ts_side₁ hs k h₁ L, ts_side₂ s h₂, ts_kT_empty, forestUnion_single_single, empty_union,
    ts_kT_single, ts_kT_merged hij, forestUnion_single_single, ts_ES_single, union_comm,
    ts_score_merged hij hik hjk]

/-- The lineages `i, j` have coalesced below the hybrid node and take the side `S₁`. -/
private theorem ts3_merged₁ :
    ts_ES (forestUnion ((Side.node L 1 (.leaf (s k)) (.hyb h₁)).forestDist s
      (insert ({i} ∪ {j}) {{i}, {j}})) ((Side.hyb h₂ : Side X).forestDist s ∅)) =
      ts_ps ({i} ∪ {j}) := by
  obtain ⟨-, -, g2, l2⟩ := ts_three_good hij hik hjk
  rw [ts_side₁ hs k h₁ L, ts_side₂ s h₂, ts_kT_empty, forestUnion_single_empty, ts_kT_merged hij,
    forestUnion_single_single,
    ts_ES_nice (niceKernel_kingmanTransition L) g2 (disjoint_empty_right _) l2.ge,
    ts_score_merged hij hik hjk]

end PlacementsThree

/-- The values of `ts_ps` for the lineages `0, 1` below the hybrid node and a third lineage `k`. -/
private theorem ts_ps_values {k : Fin 4} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    ts_ps ({0} ∪ {1}) = 1 ∧ ts_ps ({0} ∪ {k}) = 0 ∧ ts_ps ({1} ∪ {k}) = 0 ∧
      ts_ps ({k} ∪ {0}) = 0 := by
  have D : ∀ k : Fin 4, k ≠ 0 → k ≠ 1 →
      ¬({0} ∪ {k} = ({0, 1} : Finset (Fin 4)) ∨ {0} ∪ {k} = ({2, 3} : Finset (Fin 4))) ∧
      ¬({1} ∪ {k} = ({0, 1} : Finset (Fin 4)) ∨ {1} ∪ {k} = ({2, 3} : Finset (Fin 4))) ∧
      ¬({k} ∪ {0} = ({0, 1} : Finset (Fin 4)) ∨ {k} ∪ {0} = ({2, 3} : Finset (Fin 4))) := by
    decide
  obtain ⟨d0, d1, d2⟩ := D k hk0 hk1
  refine ⟨by rw [ts_ps, ite_eq_left (by decide)], ?_, ?_, ?_⟩
  · rw [ts_ps, ite_eq_right d0]
  · rw [ts_ps, ite_eq_right d1]
  · rw [ts_ps, ite_eq_right d2]

/-- The expected score at the top node of a cycle with the side `S₁` bringing `k` and the side `S₂`
bringing no lineage, when the lineages `i, j` arrive at the hybrid node apart with probability
`p`. -/
private theorem ts3_cycle_ES_gen {s : Fin 4 → X} (hs : Function.Injective s) {i j k : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (γ ℓ h₁ h₂ L p : ℝ) (H : Net X)
    (hH : H.forestDist s ᵥ* kingmanTransition ℓ =
      p • Pi.single ({{i}, {j}} : Finset (Finset (Fin 4))) 1 +
        (1 - p) • Pi.single (insert ({i} ∪ {j}) {{i}, {j}}) 1) :
    ts_ES ((Net.cycle γ (.node L 1 (.leaf (s k)) (.hyb h₁)) (.hyb h₂) ℓ H).forestDist s) =
      p * ((1 - γ) ^ 2 * (Real.exp (-h₂) / 3 + (1 - Real.exp (-h₂)) * ts_ps ({i} ∪ {j})) +
        γ * (1 - γ) * (Real.exp (-L) / 3 + (1 - Real.exp (-L)) * ts_ps ({i} ∪ {k})) +
        γ * (1 - γ) * (Real.exp (-L) / 3 + (1 - Real.exp (-L)) * ts_ps ({j} ∪ {k})) +
        γ ^ 2 * (Real.exp (-h₁) / 3 + (1 - Real.exp (-h₁)) * ts_ps ({i} ∪ {j}))) +
      (1 - p) * ts_ps ({i} ∪ {j}) := by
  set S₁ : Side X := .node L 1 (.leaf (s k)) (.hyb h₁)
  set S₂ : Side X := .hyb h₂
  have hdef : (Net.cycle γ S₁ S₂ ℓ H).forestDist s = fun G =>
      ∑ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) *
          (fun F A => forestUnion (S₁.forestDist s (forestBelow F A))
            (S₂.forestDist s (forestBelow F (roots F \ A)))) F A G := rfl
  have hV₁ := ts_sum_apart γ hij fun E E' => ts_ES (forestUnion (S₁.forestDist s E)
    (S₂.forestDist s E'))
  have hV₂ := ts_sum_merged γ hij fun E E' => ts_ES (forestUnion (S₁.forestDist s E)
    (S₂.forestDist s E'))
  rw [hdef, ts_ES_cycle, hH, ts_sum_mix, hV₁, hV₂, ts3_both₂ hs hij hik hjk h₁ h₂ L,
    ts3_split_i hs hij hik hjk h₁ h₂ L, ts3_split_j hs hij hik hjk h₁ h₂ L,
    ts3_both₁ hs hij hik hjk h₁ h₂ L, ts3_merged₂ hs hij hik hjk h₁ h₂ L,
    ts3_merged₁ hs hij hik hjk h₁ h₂ L]
  ring

/-- The expected score at the top node of a cycle with the side `S₁` bringing `k` and the side `S₂`
bringing `m`, when the lineages `i, j` arrive at the hybrid node apart with probability `p`. -/
private theorem ts_cycle_ES_gen {s : Fin 4 → X} (hs : Function.Injective s) {i j k m : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (him : i ≠ m) (hjk : j ≠ k) (hjm : j ≠ m) (hkm : k ≠ m)
    (γ ℓ h₁ h₂ a b p : ℝ) (H : Net X)
    (hH : H.forestDist s ᵥ* kingmanTransition ℓ =
      p • Pi.single ({{i}, {j}} : Finset (Finset (Fin 4))) 1 +
        (1 - p) • Pi.single (insert ({i} ∪ {j}) {{i}, {j}}) 1) :
    ts_ES ((Net.cycle γ (.node a 1 (.leaf (s k)) (.hyb h₁)) (.node b 1 (.leaf (s m)) (.hyb h₂)) ℓ
      H).forestDist s) =
      p * ((1 - γ) ^ 2 *
          (Real.exp (-h₂) / 3 + (1 - Real.exp (-h₂)) * ts_ps ({i} ∪ {j})) +
        γ * (1 - γ) * (Real.exp (-a) * Real.exp (-b) / 3 +
          (1 - Real.exp (-a) * Real.exp (-b)) * ts_ps ({i} ∪ {k})) +
        γ * (1 - γ) * (Real.exp (-a) * Real.exp (-b) / 3 +
          (1 - Real.exp (-a) * Real.exp (-b)) * ts_ps ({j} ∪ {k})) +
        γ ^ 2 * (Real.exp (-h₁) / 3 + (1 - Real.exp (-h₁)) * ts_ps ({i} ∪ {j}))) +
      (1 - p) * ts_ps ({i} ∪ {j}) := by
  set S₁ : Side X := .node a 1 (.leaf (s k)) (.hyb h₁)
  set S₂ : Side X := .node b 1 (.leaf (s m)) (.hyb h₂)
  have hdef : (Net.cycle γ S₁ S₂ ℓ H).forestDist s = fun G =>
      ∑ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) *
          (fun F A => forestUnion (S₁.forestDist s (forestBelow F A))
            (S₂.forestDist s (forestBelow F (roots F \ A)))) F A G := rfl
  have hV₁ := ts_sum_apart γ hij fun E E' => ts_ES (forestUnion (S₁.forestDist s E)
    (S₂.forestDist s E'))
  have hV₂ := ts_sum_merged γ hij fun E E' => ts_ES (forestUnion (S₁.forestDist s E)
    (S₂.forestDist s E'))
  rw [hdef, ts_ES_cycle, hH, ts_sum_mix, hV₁, hV₂,
    ts_ES_both₂ hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES_split_i hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES_split_i hs hij.symm hjk hjm hik him hkm h₁ h₂ a b,
    ts_ES_both₁ hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES_merged₂ hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES_merged₁ hs hij hik him hjk hjm hkm h₁ h₂ a b]
  ring

/-- The expected score at the top node of a cycle whose side `S₁` brings `m` and then `k`, and
whose side `S₂` brings no lineage, when the lineages `i, j` arrive at the hybrid node apart with
probability `p`. -/
private theorem ts1_cycle_ES_gen {s : Fin 4 → X} (hs : Function.Injective s) {i j k m : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (him : i ≠ m) (hjk : j ≠ k) (hjm : j ≠ m) (hkm : k ≠ m)
    (γ ℓ h₁ h₂ a b p : ℝ) (H : Net X)
    (hH : H.forestDist s ᵥ* kingmanTransition ℓ =
      p • Pi.single ({{i}, {j}} : Finset (Finset (Fin 4))) 1 +
        (1 - p) • Pi.single (insert ({i} ∪ {j}) {{i}, {j}}) 1) :
    ts_ES ((Net.cycle γ (.node a 1 (.leaf (s k)) (.node b 1 (.leaf (s m)) (.hyb h₁))) (.hyb h₂) ℓ
      H).forestDist s) =
      p * ((1 - γ) ^ 2 * (Real.exp (-a) * Real.exp (-h₂) / 3 +
          (1 - Real.exp (-a) * Real.exp (-h₂)) * ts_ps ({i} ∪ {j})) +
        γ * (1 - γ) * (Real.exp (-b) / 3 + (1 - Real.exp (-b)) * ts_ps ({i} ∪ {m})) +
        γ * (1 - γ) * (Real.exp (-b) / 3 + (1 - Real.exp (-b)) * ts_ps ({j} ∪ {m})) +
        γ ^ 2 * (Real.exp (-h₁) / 3 + (1 - Real.exp (-h₁)) * ts_ps ({i} ∪ {j}))) +
      (1 - p) * ts_ps ({i} ∪ {j}) := by
  set S₁ : Side X := .node a 1 (.leaf (s k)) (.node b 1 (.leaf (s m)) (.hyb h₁))
  set S₂ : Side X := .hyb h₂
  have hdef : (Net.cycle γ S₁ S₂ ℓ H).forestDist s = fun G =>
      ∑ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) *
          (fun F A => forestUnion (S₁.forestDist s (forestBelow F A))
            (S₂.forestDist s (forestBelow F (roots F \ A)))) F A G := rfl
  have hV₁ := ts_sum_apart γ hij fun E E' => ts_ES (forestUnion (S₁.forestDist s E)
    (S₂.forestDist s E'))
  have hV₂ := ts_sum_merged γ hij fun E E' => ts_ES (forestUnion (S₁.forestDist s E)
    (S₂.forestDist s E'))
  rw [hdef, ts_ES_cycle, hH, ts_sum_mix, hV₁, hV₂,
    ts_ES1_both₂ hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES1_split_i hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES1_split_i hs hij.symm hjk hjm hik him hkm h₁ h₂ a b,
    ts_ES1_both₁ hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES1_merged₂ hs hij hik him hjk hjm hkm h₁ h₂ a b,
    ts_ES1_merged₁ hs hij hik him hjk hjm hkm h₁ h₂ a b]
  ring

/-- **The top node of a cycle with one of the four taxa on a side, one outside.** Let the lineages
`0` and `1` arrive at the hybrid node of the cycle `cycle γ S₁ S₂ ℓ H` apart with probability `p`,
and coalesced otherwise (`hH`). Let the side `S₁` bring the lineage `k` (`k = 2` or `3`): a forest
`E` that takes its hybrid edge travels for a time `h₁`, is joined by `k`, and travels for a time `L`
to the top node (`hS₁`). Let the side `S₂` bring no lineage: `E` travels for a time `h₂` (`hS₂`).
Then the expected score of the forest at the top node, which is the CF of `01|23` when the fourth
lineage is outside the cycle (`Brooqs.quartetCF_eq_sum_top`), is
`1 - p + p (γ²(1 - 2/3 e^{-h₁}) + (1 - γ)²(1 - 2/3 e^{-h₂}) + 2γ(1 - γ) e^{-L}/3)`: the CF of
`xy|zw` of `N₃₂` (`Brooqs.net32_quartetCF`) with `p` in place of `e^{-ℓ}`. -/
theorem expectedScore_top_outside {s : Fin 4 → X} (hs : Function.Injective s) {k : Fin 4}
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) (γ ℓ h₁ h₂ L p : ℝ) (S₁ S₂ : Side X) (H : Net X)
    (hH : H.forestDist s ᵥ* kingmanTransition ℓ =
      p • Pi.single ({{0}, {1}} : Finset (Finset (Fin 4))) 1 +
        (1 - p) • Pi.single (insert ({0} ∪ {1}) {{0}, {1}}) 1)
    (hS₁ : ∀ E, S₁.forestDist s E = forestUnion (Pi.single E 1 ᵥ* kingmanTransition h₁)
      (Pi.single {{k}} 1) ᵥ* kingmanTransition L)
    (hS₂ : ∀ E, S₂.forestDist s E = Pi.single E 1 ᵥ* kingmanTransition h₂) :
    ∑ F, (Net.cycle γ S₁ S₂ ℓ H).forestDist s F * quartetScore F =
      1 - p + p * (γ ^ 2 * (1 - 2 / 3 * Real.exp (-h₁)) +
        (1 - γ) ^ 2 * (1 - 2 / 3 * Real.exp (-h₂)) + 2 * γ * (1 - γ) * (Real.exp (-L) / 3)) := by
  have hcyc : (Net.cycle γ S₁ S₂ ℓ H).forestDist s =
      (Net.cycle γ (.node L 1 (.leaf (s k)) (.hyb h₁)) (.hyb h₂) ℓ H).forestDist s := by
    funext G
    show ∑ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) * forestUnion (S₁.forestDist s (forestBelow F A))
          (S₂.forestDist s (forestBelow F (roots F \ A))) G =
      ∑ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) * forestUnion
          ((Side.node L 1 (.leaf (s k)) (.hyb h₁) : Side X).forestDist s (forestBelow F A))
          ((Side.hyb h₂ : Side X).forestDist s (forestBelow F (roots F \ A))) G
    simp only [hS₁, hS₂, ts_side₁ hs, ts_side₂]
  have h := ts3_cycle_ES_gen hs (i := 0) (j := 1) (k := k) (by decide) hk0.symm hk1.symm γ ℓ h₁ h₂
    L p H hH
  obtain ⟨p01, p0k, p1k, -⟩ := ts_ps_values hk0 hk1
  rw [p01, p0k, p1k] at h
  change ts_ES _ = _
  rw [hcyc, h]
  ring

/-- **The top node of a cycle with two of the four taxa on its two sides.** As
`Brooqs.expectedScore_top_outside`, with the side `S₁` bringing the lineage `k` after a time `h₁`
and travelling for a time `a`, and the side `S₂` bringing the lineage `m` after a time `h₂` and
travelling for a time `b` (`{k, m} = {2, 3}`). The expected score at the top node, the CF of
`01|23`, is that of `N₃₂` with `L = a + b` and `p` in place of `e^{-ℓ}`. -/
theorem expectedScore_top_sides {s : Fin 4 → X} (hs : Function.Injective s) {k m : Fin 4}
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) (hkm : k ≠ m)
    (γ ℓ h₁ h₂ a b p : ℝ) (S₁ S₂ : Side X) (H : Net X)
    (hH : H.forestDist s ᵥ* kingmanTransition ℓ =
      p • Pi.single ({{0}, {1}} : Finset (Finset (Fin 4))) 1 +
        (1 - p) • Pi.single (insert ({0} ∪ {1}) {{0}, {1}}) 1)
    (hS₁ : ∀ E, S₁.forestDist s E = forestUnion (Pi.single E 1 ᵥ* kingmanTransition h₁)
      (Pi.single {{k}} 1) ᵥ* kingmanTransition a)
    (hS₂ : ∀ E, S₂.forestDist s E = forestUnion (Pi.single E 1 ᵥ* kingmanTransition h₂)
      (Pi.single {{m}} 1) ᵥ* kingmanTransition b) :
    ∑ F, (Net.cycle γ S₁ S₂ ℓ H).forestDist s F * quartetScore F =
      1 - p + p * (γ ^ 2 * (1 - 2 / 3 * Real.exp (-h₁)) +
        (1 - γ) ^ 2 * (1 - 2 / 3 * Real.exp (-h₂)) +
          2 * γ * (1 - γ) * (Real.exp (-(a + b)) / 3)) := by
  have hcyc : (Net.cycle γ S₁ S₂ ℓ H).forestDist s =
      (Net.cycle γ (.node a 1 (.leaf (s k)) (.hyb h₁)) (.node b 1 (.leaf (s m)) (.hyb h₂)) ℓ
        H).forestDist s := by
    funext G
    show ∑ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) * forestUnion (S₁.forestDist s (forestBelow F A))
          (S₂.forestDist s (forestBelow F (roots F \ A))) G =
      ∑ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) * forestUnion
          ((Side.node a 1 (.leaf (s k)) (.hyb h₁) : Side X).forestDist s (forestBelow F A))
          ((Side.node b 1 (.leaf (s m)) (.hyb h₂) : Side X).forestDist s
            (forestBelow F (roots F \ A))) G
    simp only [hS₁, hS₂, ts_side₁ hs]
  have h := ts_cycle_ES_gen hs (i := 0) (j := 1) (k := k) (m := m) (by decide) hk0.symm hm0.symm
    hk1.symm hm1.symm hkm γ ℓ h₁ h₂ a b p H hH
  obtain ⟨p01, p0k, p1k, -⟩ := ts_ps_values hk0 hk1
  have hab : Real.exp (-(a + b)) = Real.exp (-a) * Real.exp (-b) := by
    rw [neg_add, Real.exp_add]
  rw [p01, p0k, p1k] at h
  change ts_ES _ = _
  rw [hcyc, h, hab]
  ring

/-- **The top node of a cycle with two of the four taxa on one side.** As
`Brooqs.expectedScore_top_outside`, with the side `S₁` bringing the lineage `m` after a time `h₁`,
then the lineage `k` after a further time `b`, and travelling for a time `a` to the top node, and
the side `S₂` bringing no lineage (`{k, m} = {2, 3}`). The expected score at the top node, the CF of
`01|23`, is that of `N₃₂` with `a + h₂` for `h₂`, `b` for `L` and `p` in place of `e^{-ℓ}`. -/
theorem expectedScore_top_oneSide {s : Fin 4 → X} (hs : Function.Injective s) {k m : Fin 4}
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) (hkm : k ≠ m)
    (γ ℓ h₁ h₂ a b p : ℝ) (S₁ S₂ : Side X) (H : Net X)
    (hH : H.forestDist s ᵥ* kingmanTransition ℓ =
      p • Pi.single ({{0}, {1}} : Finset (Finset (Fin 4))) 1 +
        (1 - p) • Pi.single (insert ({0} ∪ {1}) {{0}, {1}}) 1)
    (hS₁ : ∀ E, S₁.forestDist s E = forestUnion (forestUnion
      (Pi.single E 1 ᵥ* kingmanTransition h₁) (Pi.single {{m}} 1) ᵥ* kingmanTransition b)
        (Pi.single {{k}} 1) ᵥ* kingmanTransition a)
    (hS₂ : ∀ E, S₂.forestDist s E = Pi.single E 1 ᵥ* kingmanTransition h₂) :
    ∑ F, (Net.cycle γ S₁ S₂ ℓ H).forestDist s F * quartetScore F =
      1 - p + p * (γ ^ 2 * (1 - 2 / 3 * Real.exp (-h₁)) +
        (1 - γ) ^ 2 * (1 - 2 / 3 * Real.exp (-(a + h₂))) +
          2 * γ * (1 - γ) * (Real.exp (-b) / 3)) := by
  have hcyc : (Net.cycle γ S₁ S₂ ℓ H).forestDist s =
      (Net.cycle γ (.node a 1 (.leaf (s k)) (.node b 1 (.leaf (s m)) (.hyb h₁))) (.hyb h₂) ℓ
        H).forestDist s := by
    funext G
    show ∑ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) * forestUnion (S₁.forestDist s (forestBelow F A))
          (S₂.forestDist s (forestBelow F (roots F \ A))) G =
      ∑ F, (H.forestDist s ᵥ* kingmanTransition ℓ) F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) * forestUnion
          ((Side.node a 1 (.leaf (s k)) (.node b 1 (.leaf (s m)) (.hyb h₁)) : Side X).forestDist s
            (forestBelow F A))
          ((Side.hyb h₂ : Side X).forestDist s (forestBelow F (roots F \ A))) G
    simp only [hS₁, hS₂, ts_side_two hs, ts_side₂]
  have h := ts1_cycle_ES_gen hs (i := 0) (j := 1) (k := k) (m := m) (by decide) hk0.symm hm0.symm
    hk1.symm hm1.symm hkm γ ℓ h₁ h₂ a b p H hH
  obtain ⟨p01, -, -, -⟩ := ts_ps_values hk0 hk1
  obtain ⟨-, p0m, p1m, -⟩ := ts_ps_values hm0 hm1
  have hah : Real.exp (-(a + h₂)) = Real.exp (-a) * Real.exp (-h₂) := by
    rw [neg_add, Real.exp_add]
  rw [p01, p0m, p1m] at h
  change ts_ES _ = _
  rw [hcyc, h, hah]
  ring

end Brooqs
