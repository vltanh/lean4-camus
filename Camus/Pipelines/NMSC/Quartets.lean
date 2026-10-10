module

public import Camus.External.NMSC.GeneLaw
public import Camus.External.NMSC.ThreeCycle
public import Camus.Pipelines.Coalescent

/-!
# Section 3.3: quartet trees of gene trees under the NMSC

Section 3.3 takes gene trees that evolve down a level-1 network `N` under the NMSC, and the multiset
`Q` of the quartet trees that they induce. This file relates the model of `Camus/External/NMSC/` to
the quartet trees of CAMUS, on taxa that are natural numbers (`L : Finset ℕ`). A gene tree, given
by its clusters, induces a quartet tree (`Coalescent.Induces`, as for the gene trees of the
multispecies coalescent) iff it displays the quartet in the sense of the model
(`induces_iff_geneTreeDisplays`), so the probability that a gene tree induces a quartet tree is a
quartet CF (`quartetProb_eq_quartetCF`). `DisplaysQuartet N q` is `q ∈ Q(N_r)`, and
`DisplaysTree N T` says that the tree `T` of CAMUS is a displayed tree of `N`, as an unrooted tree.

## Main results

* `NMSC.DisplaysQuartet`, `NMSC.DisplaysTree`: Q(N_r) and the displayed trees T(N).
* `NMSC.quartetProb`, `NMSC.quartetProb_eq_quartetCF`, `NMSC.measureReal_induces`: the
  probability that a gene tree induces a quartet tree, and its quartet CF.
* `NMSC.induces_iff_geneTreeDisplays`, `NMSC.displaysQuartet_iff`: the quartet trees of CAMUS and
  the quartets of the model.
-/

@[expose] public noncomputable section

namespace Camus

namespace NMSC

open Finset Filter Topology MeasureTheory ProbabilityTheory Coalescent

variable {L : Finset ℕ}

/-- `N` displays the quartet tree `q` of CAMUS, `q ∈ Q(N_r)` (Definition 1): some displayed tree of
`N` induces `q`. -/
def DisplaysQuartet (N : Brooqs.Net L) (q : Quartet) : Prop :=
  ∃ K ∈ N.displayed, Induces K q

/-- The tree `T` of CAMUS is a displayed tree of `N`, as an unrooted tree (`T ∈ T(N)`): some
displayed tree of `N` induces exactly the quartet trees that `T` induces. -/
def DisplaysTree (N : Brooqs.Net L) (T : PhyloTree) : Prop :=
  ∃ K ∈ N.displayed, ∀ q, Induces K q ↔ q.induced T = true

/-- The probability that the gene tree of the NMSC on `N`, with one lineage per taxon, induces the
quartet tree `q`. -/
def quartetProb (N : Brooqs.Net L) (q : Quartet) : ℝ :=
  ∑ G, if Induces G q then N.geneTreeDist id G else 0

private theorem nq_pattern : ∀ P : Finset (Fin 4),
    (P = side 0 ∨ P = (side 0)ᶜ ↔
      (0 ∈ P ∧ 1 ∈ P ∧ 2 ∉ P ∧ 3 ∉ P) ∨ (2 ∈ P ∧ 3 ∈ P ∧ 0 ∉ P ∧ 1 ∉ P)) ∧
    (P = side 1 ∨ P = (side 1)ᶜ ↔
      (0 ∈ P ∧ 2 ∈ P ∧ 1 ∉ P ∧ 3 ∉ P) ∨ (1 ∈ P ∧ 3 ∈ P ∧ 0 ∉ P ∧ 2 ∉ P)) ∧
    (P = side 2 ∨ P = (side 2)ᶜ ↔
      (0 ∈ P ∧ 3 ∈ P ∧ 1 ∉ P ∧ 2 ∉ P) ∨ (1 ∈ P ∧ 2 ∈ P ∧ 0 ∉ P ∧ 3 ∉ P)) := by
  decide

/-- A family `G` of clusters (or of sides of splits) induces the quartet tree of topology `s` on
the four taxa `t 0 < t 1 < t 2 < t 3` of `k` iff it displays it in the sense of
`Brooqs.geneTreeDisplays`: `t 0 t 1 | t 2 t 3` for `s = 0`, `t 0 t 2 | t 1 t 3` for `s = 1` and
`t 0 t 3 | t 1 t 2` for `s = 2`. -/
theorem induces_iff_geneTreeDisplays (k : QuartetKey) (hk : keyTaxa k ⊆ L)
    (G : Finset (Finset L)) :
    (Induces G (k.quartet 0) ↔ Brooqs.geneTreeDisplays G (keyTaxon k hk 0) (keyTaxon k hk 1)
      (keyTaxon k hk 2) (keyTaxon k hk 3) = true) ∧
    (Induces G (k.quartet 1) ↔ Brooqs.geneTreeDisplays G (keyTaxon k hk 0) (keyTaxon k hk 2)
      (keyTaxon k hk 1) (keyTaxon k hk 3) = true) ∧
    (Induces G (k.quartet 2) ↔ Brooqs.geneTreeDisplays G (keyTaxon k hk 0) (keyTaxon k hk 3)
      (keyTaxon k hk 1) (keyTaxon k hk 2) = true) := by
  simp only [Induces, taxa_quartet, hk, true_and, Brooqs.geneTreeDisplays, decide_eq_true_eq,
    cutBy_iff k hk]
  refine ⟨?_, ?_, ?_⟩ <;> refine exists_congr fun A => and_congr_right fun _ => ?_
  · simpa using (nq_pattern (univ.filter fun i => keyTaxon k hk i ∈ A)).1
  · simpa using (nq_pattern (univ.filter fun i => keyTaxon k hk i ∈ A)).2.1
  · simpa using (nq_pattern (univ.filter fun i => keyTaxon k hk i ∈ A)).2.2

/-- The quartet trees of CAMUS on the four taxa of `k` that `N` displays are those of
`Brooqs.Net.Displays`. -/
theorem displaysQuartet_iff (N : Brooqs.Net L) (k : QuartetKey) (hk : keyTaxa k ⊆ L) :
    (DisplaysQuartet N (k.quartet 0) ↔
      N.Displays (keyTaxon k hk 0) (keyTaxon k hk 1) (keyTaxon k hk 2) (keyTaxon k hk 3)) ∧
    (DisplaysQuartet N (k.quartet 1) ↔
      N.Displays (keyTaxon k hk 0) (keyTaxon k hk 2) (keyTaxon k hk 1) (keyTaxon k hk 3)) ∧
    (DisplaysQuartet N (k.quartet 2) ↔
      N.Displays (keyTaxon k hk 0) (keyTaxon k hk 3) (keyTaxon k hk 1) (keyTaxon k hk 2)) := by
  simp only [DisplaysQuartet, Brooqs.Net.Displays]
  refine ⟨?_, ?_, ?_⟩ <;> refine exists_congr fun K => and_congr_right fun _ => ?_
  · exact (induces_iff_geneTreeDisplays k hk K).1
  · exact (induces_iff_geneTreeDisplays k hk K).2.1
  · exact (induces_iff_geneTreeDisplays k hk K).2.2

private theorem nq_sum_congr (N : Brooqs.Net L) {P Q : Finset (Finset L) → Prop}
    [DecidablePred P] [DecidablePred Q] (h : ∀ G, P G ↔ Q G) :
    (∑ G, if P G then N.geneTreeDist id G else 0) =
      ∑ G, if Q G then N.geneTreeDist id G else 0 :=
  sum_congr rfl fun G _ => if_congr (h G) rfl rfl

/-- The probability that a gene tree of the NMSC on `N` induces a quartet tree on the four taxa
`t 0 < t 1 < t 2 < t 3` of `k` is the quartet CF of the corresponding split
(`Brooqs.quartetCF_eq_displays`, the sampling consistency of the coalescent). -/
theorem quartetProb_eq_quartetCF (N : Brooqs.Net L) (hN : N.leaves.Nodup) (k : QuartetKey)
    (hk : keyTaxa k ⊆ L) :
    quartetProb N (k.quartet 0) =
      N.quartetCF (keyTaxon k hk 0) (keyTaxon k hk 1) (keyTaxon k hk 2) (keyTaxon k hk 3) ∧
    quartetProb N (k.quartet 1) =
      N.quartetCF (keyTaxon k hk 0) (keyTaxon k hk 2) (keyTaxon k hk 1) (keyTaxon k hk 3) ∧
    quartetProb N (k.quartet 2) =
      N.quartetCF (keyTaxon k hk 0) (keyTaxon k hk 3) (keyTaxon k hk 1) (keyTaxon k hk 2) := by
  have hne : ∀ i j : Fin 4, i ≠ j → keyTaxon k hk i ≠ keyTaxon k hk j :=
    fun i j h h' => h ((keyTaxon k hk).injective h')
  refine ⟨?_, ?_, ?_⟩
  · rw [Brooqs.quartetCF_eq_displays N hN (hne 0 1 (by decide)) (hne 0 2 (by decide))
      (hne 0 3 (by decide)) (hne 1 2 (by decide)) (hne 1 3 (by decide)) (hne 2 3 (by decide))]
    exact nq_sum_congr N fun G => (induces_iff_geneTreeDisplays k hk G).1
  · rw [Brooqs.quartetCF_eq_displays N hN (hne 0 2 (by decide)) (hne 0 1 (by decide))
      (hne 0 3 (by decide)) (hne 2 1 (by decide)) (hne 2 3 (by decide)) (hne 1 3 (by decide))]
    exact nq_sum_congr N fun G => (induces_iff_geneTreeDisplays k hk G).2.1
  · rw [Brooqs.quartetCF_eq_displays N hN (hne 0 3 (by decide)) (hne 0 1 (by decide))
      (hne 0 2 (by decide)) (hne 3 1 (by decide)) (hne 3 2 (by decide)) (hne 1 2 (by decide))]
    exact nq_sum_congr N fun G => (induces_iff_geneTreeDisplays k hk G).2.2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]

/-- If the gene tree `G0` has the law of the NMSC on `N`, the probability that it induces `q` is
`quartetProb N q`. -/
theorem measureReal_induces (N : Brooqs.Net L) (G0 : Ω → Finset (Finset L))
    (hG0 : AEMeasurable G0 P) (hlaw : ∀ T, P.real (G0 ⁻¹' {T}) = N.geneTreeDist id T)
    (q : Quartet) : P.real {ω | Induces (G0 ω) q} = quartetProb N q := by
  have hmap : ∀ S : Set (Finset (Finset L)), P.real (G0 ⁻¹' S) = (P.map G0).real S := fun S => by
    rw [measureReal_def, measureReal_def,
      Measure.map_apply_of_aemeasurable hG0 MeasurableSet.of_discrete]
  have hset : {ω | Induces (G0 ω) q} =
      G0 ⁻¹' ↑(univ.filter fun T : Finset (Finset L) => Induces T q) := by
    ext ω
    simp
  rw [hset, hmap, ← sum_measureReal_singleton, sum_filter]
  refine sum_congr rfl fun T _ => ?_
  split_ifs
  · rw [← hmap, hlaw]
  · rfl

end NMSC

end Camus
