module

public import Camus.External.NMSC.Sampling
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Independent gene trees under the NMSC

Sections 3.3 and 3.4 of CAMUS take gene trees that evolve down a level-1 network under the NMSC,
independently. This file shows that the gene tree distribution of the NMSC on a metric network with
distinct leaf labels is a probability distribution (`Brooqs.Net.geneTreeDist_nonneg`,
`Brooqs.Net.geneTreeDist_sum`), and builds sequences of independent gene trees with this law on the
product space (`Brooqs.Net.genes`, with `MeasureTheory.Measure.infinitePi`), as
`Camus/Pipelines/Coalescent/Sampling.lean` does for the multispecies coalescent.

## Main results

* `Brooqs.Net.forestDist_nonneg`, `Brooqs.Net.geneTreeDist_nonneg`,
  `Brooqs.Net.geneTreeDist_sum`: the NMSC gives probability distributions.
* `Brooqs.Net.geneLaw`: the law of the gene tree, with one lineage per taxon.
* `Brooqs.Net.genes`, `Brooqs.Net.genes_iIndepFun`, `Brooqs.Net.genes_identDistrib`,
  `Brooqs.Net.genes_law`: independent gene trees with that law.
-/

@[expose] public noncomputable section

namespace Brooqs

open Finset Matrix MeasureTheory ProbabilityTheory

universe u

section Nonneg

variable {L : Type*} [Fintype L] [DecidableEq L]

omit [DecidableEq L] in
private theorem gl_vecMul_nonneg {μ : Finset (Finset L) → ℝ}
    {M : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ} (hμ : ∀ F, 0 ≤ μ F)
    (hM : ∀ F G, 0 ≤ M F G) (G : Finset (Finset L)) : 0 ≤ (μ ᵥ* M) G :=
  sum_nonneg fun F _ => mul_nonneg (hμ F) (hM F G)

private theorem gl_forestUnion_nonneg {μ ν : Finset (Finset L) → ℝ} (hμ : ∀ F, 0 ≤ μ F)
    (hν : ∀ F, 0 ≤ ν F) (G : Finset (Finset L)) : 0 ≤ forestUnion μ ν G :=
  sum_nonneg fun F _ => sum_nonneg fun F' _ => by
    split_ifs
    · exact mul_nonneg (hμ F) (hν F')
    · exact le_rfl

private theorem gl_kT_nonneg {t : ℝ} (ht : 0 < t) (F G : Finset (Finset L)) :
    0 ≤ kingmanTransition t F G := by
  rw [kingmanTransition_eq_adr11]
  exact ADR11.kingmanTransition_nonneg ht.le F G

variable {X : Type u} [DecidableEq X]

mutual
/-- On a metric network, the NMSC gives nonnegative probabilities. -/
theorem Net.forestDist_nonneg : ∀ {N : Net X}, N.IsMetric → ∀ (s : L → X) G,
    0 ≤ N.forestDist s G
  | .leaf x, _, s, G => by
      simp only [Net.forestDist]
      split_ifs <;> norm_num
  | .tree ℓ₁ N₁ ℓ₂ N₂, hN, s, G =>
      gl_forestUnion_nonneg
        (gl_vecMul_nonneg (Net.forestDist_nonneg hN.2.2.1 s) (gl_kT_nonneg hN.1))
        (gl_vecMul_nonneg (Net.forestDist_nonneg hN.2.2.2 s) (gl_kT_nonneg hN.2.1)) G
  | .cycle γ S₁ S₂ ℓ N, hN, s, G => by
      obtain ⟨hγ0, hγ1, hℓ, hS₁, hS₂, hN', -⟩ := hN
      refine sum_nonneg fun F _ => mul_nonneg
        (gl_vecMul_nonneg (Net.forestDist_nonneg hN' s) (gl_kT_nonneg hℓ) F)
        (sum_nonneg fun A _ => mul_nonneg (mul_nonneg (pow_nonneg hγ0.le _)
          (pow_nonneg (by linarith) _)) ?_)
      exact gl_forestUnion_nonneg (Side.forestDist_nonneg hS₁ s _)
        (Side.forestDist_nonneg hS₂ s _) G

/-- The same along a metric side. -/
theorem Side.forestDist_nonneg : ∀ {S : Side X}, S.IsMetric → ∀ (s : L → X) F G,
    0 ≤ S.forestDist s F G
  | .hyb _, hS, _, F, G => gl_kT_nonneg hS F G
  | .node _ _ _ _, hS, s, F, G =>
      gl_vecMul_nonneg (gl_forestUnion_nonneg (Side.forestDist_nonneg hS.2.2.2 s F)
        (gl_vecMul_nonneg (Net.forestDist_nonneg hS.2.2.1 s) (gl_kT_nonneg hS.2.1)))
        (gl_kT_nonneg hS.1) G
end

/-- The forests at the root of a network with distinct leaf labels are good. -/
theorem Net.isGood_of_forestDist_ne_zero {N : Net X} (hN : N.leaves.Nodup) (s : L → X)
    {F : Finset (Finset L)} (hF : N.forestDist s F ≠ 0) : IsGood F := by
  rw [Net.forestDist_eq] at hF
  exact (Net.forestDistOf_single_support N hN (sampledAt s) (fun _ _ => isGood_singletons _)
    (fun _ _ _ _ hab => disjoint_lineages_sampledAt s hab) hF).1

/-- The NMSC on a metric network with distinct leaf labels gives nonnegative probabilities to the
gene trees. -/
theorem Net.geneTreeDist_nonneg {N : Net X} (hN : N.WellFormed) (s : L → X)
    (G : Finset (Finset L)) : 0 ≤ N.geneTreeDist s G := by
  refine sum_nonneg fun F _ => ?_
  by_cases hF : N.forestDist s F = 0
  · rw [hF, zero_mul]
  · refine mul_nonneg (Net.forestDist_nonneg hN.1 s F) ?_
    rw [kingmanAbsorption_eq_adr11]
    exact ADR11.kingmanAbsorption_nonneg (Net.isGood_of_forestDist_ne_zero hN.2 s hF).1 G

/-- The probabilities of the gene trees sum to `1`. -/
theorem Net.geneTreeDist_sum {N : Net X} (hN : N.leaves.Nodup) (s : L → X) :
    ∑ G, N.geneTreeDist s G = 1 := by
  have h1 : ∑ F, N.forestDist s F = 1 := by
    rw [Net.forestDist_eq]
    exact Net.forestDistOf_single_sum N hN (sampledAt s) (fun _ _ => isGood_singletons _)
      (fun _ _ _ _ hab => disjoint_lineages_sampledAt s hab)
  rw [← h1]
  unfold Net.geneTreeDist
  simp only [vecMul, dotProduct]
  rw [sum_comm]
  refine sum_congr rfl fun F _ => ?_
  rw [← mul_sum]
  by_cases hF : N.forestDist s F = 0
  · rw [hF, zero_mul]
  · rw [kingmanAbsorption_row_sum (Net.isGood_of_forestDist_ne_zero hN s hF).1, mul_one]

end Nonneg

/-! ### Independent gene trees -/

section Genes

variable {X : Type u} [Fintype X] [DecidableEq X] [MeasurableSpace (Finset (Finset X))]

/-- The law of the gene tree of the NMSC on the metric network `N` with distinct leaf labels, one
lineage per taxon: the probability measure on the rooted gene trees (their clusters) with masses
`N.geneTreeDist id`. -/
def Net.geneLaw (N : Net X) (hN : N.WellFormed) : Measure (Finset (Finset X)) :=
  (PMF.ofFintype (fun G => ENNReal.ofReal (N.geneTreeDist id G)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun G _ => Net.geneTreeDist_nonneg hN id G,
      Net.geneTreeDist_sum hN.2 id, ENNReal.ofReal_one])).toMeasure

instance (N : Net X) (hN : N.WellFormed) : IsProbabilityMeasure (N.geneLaw hN) := by
  unfold Net.geneLaw
  infer_instance

theorem Net.geneLaw_real_singleton [MeasurableSingletonClass (Finset (Finset X))] (N : Net X)
    (hN : N.WellFormed) (G : Finset (Finset X)) :
    (N.geneLaw hN).real {G} = N.geneTreeDist id G := by
  rw [measureReal_def, Net.geneLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton G),
    PMF.ofFintype_apply, ENNReal.toReal_ofReal (Net.geneTreeDist_nonneg hN id G)]

/-- Independent gene trees under the NMSC on `N`: the product law on the sequences of gene trees,
under which the coordinates are the gene trees. -/
def Net.genes (N : Net X) (hN : N.WellFormed) : Measure (ℕ → Finset (Finset X)) :=
  Measure.infinitePi fun _ => N.geneLaw hN

instance (N : Net X) (hN : N.WellFormed) : IsProbabilityMeasure (N.genes hN) := by
  unfold Net.genes
  infer_instance

/-- Under `N.genes hN`, the gene trees are independent. -/
theorem Net.genes_iIndepFun (N : Net X) (hN : N.WellFormed) :
    iIndepFun (fun n (ω : ℕ → Finset (Finset X)) => ω n) (N.genes hN) :=
  iIndepFun_infinitePi (P := fun _ => N.geneLaw hN) (X := fun _ => id) fun _ => measurable_id

theorem Net.genes_map (N : Net X) (hN : N.WellFormed) (n : ℕ) :
    (N.genes hN).map (fun ω => ω n) = N.geneLaw hN :=
  Measure.infinitePi_map_eval _ n

/-- Under `N.genes hN`, the gene trees are identically distributed. -/
theorem Net.genes_identDistrib (N : Net X) (hN : N.WellFormed) (n : ℕ) :
    IdentDistrib (fun ω : ℕ → Finset (Finset X) => ω n) (fun ω => ω 0) (N.genes hN) (N.genes hN)
    where
  aemeasurable_fst := (measurable_pi_apply n).aemeasurable
  aemeasurable_snd := (measurable_pi_apply 0).aemeasurable
  map_eq := by rw [Net.genes_map, Net.genes_map]

/-- Under `N.genes hN`, the first gene tree has the law of the NMSC on `N`. -/
theorem Net.genes_law [MeasurableSingletonClass (Finset (Finset X))] (N : Net X)
    (hN : N.WellFormed) (G : Finset (Finset X)) :
    (N.genes hN).real ((fun ω : ℕ → Finset (Finset X) => ω 0) ⁻¹' {G}) = N.geneTreeDist id G := by
  rw [measureReal_def, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton G),
    Net.genes_map, ← measureReal_def, Net.geneLaw_real_singleton]

end Genes

end Brooqs
