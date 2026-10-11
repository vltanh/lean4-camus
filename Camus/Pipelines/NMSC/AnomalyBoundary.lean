module

public import Camus.Pipelines.NMSC.AnomalyGeneral

/-!
# Section 3.3: Quartet Filtering on the boundary of the anomaly zone

On four taxa in the anomalous configuration, Quartet Filtering (Algorithm 1) eventually fails in
the anomaly zone and eventually keeps exactly the quartet tree of Q(N_r) outside it
(`NMSC.anomalous_filterQuartets`). On the boundary of the zone the three quartet trees on the four
taxa are equally probable (`NMSC.anomalous_filterQuartets_boundary`): Algorithm 1 eventually keeps
the copies of a single quartet tree, the most frequent one, but which one keeps changing. This file
proves that it does not almost surely end up keeping the quartet tree of Q(N_r)
(`NMSC.not_ae_filterQuartets_of_equal`): the event that, for all large numbers of genes, Algorithm
1 returns on the four taxa exactly the copies of the quartet tree of Q(N_r) has probability less
than `1`.

## Main results

* `NMSC.induces_unique`: a good forest induces at most one quartet tree on four taxa.
* `NMSC.prob_counts_eq`: when the three quartet trees are equally probable, the probability that a
  given quartet tree is a most frequent one among the first `n` gene trees does not depend on it.
* `NMSC.not_ae_filterQuartets_of_equal`: on four taxa whose three quartet trees have probability
  `1/3` and on which the network displays one of them, Algorithm 1 does not almost surely end up
  returning exactly the copies of the displayed one.
* `NMSC.anomalous_not_ae_filterQuartets_boundary`: the same in the anomalous configuration, on the
  boundary of the anomaly zone.

## Proof

If, almost surely, for all large `n`, Algorithm 1 keeps exactly the copies of the displayed quartet
tree `d`, then `d` is eventually a most frequent quartet tree (Algorithm 1 keeps all the copies of
a most frequent one), so the probability `P(A_n^d)` that it is a most frequent one tends to `1`. The
quartet trees of the gene trees on the four taxa are independent and uniform on the three, so
`P(A_n^u)` is the same for the three quartet trees `u`: the law of the first `n` of them is
invariant under any permutation of the three (`NMSC.prob_counts_eq`). Then the probability that the
three are most frequent at once tends to `1`; but for `n ≡ 1 (mod 3)` the three counts, which add
up to `n`, cannot be equal.
-/

@[expose] public noncomputable section

namespace Camus

namespace NMSC

open Finset Filter Topology MeasureTheory ProbabilityTheory Coalescent Algorithm1

variable {L : Finset ℕ}

/-! ### The quartet tree that a gene tree induces on four taxa -/

/-- The gene trees in the support of the NMSC are good forests: nested or disjoint clusters. -/
theorem isGood_of_geneTreeDist {N : Brooqs.Net L} (hN : N.leaves.Nodup) {T : Finset (Finset L)}
    (hT : N.geneTreeDist id T ≠ 0) : Brooqs.IsGood T := by
  unfold Brooqs.Net.geneTreeDist at hT
  simp only [Matrix.vecMul, dotProduct] at hT
  obtain ⟨F, -, hF⟩ := exists_ne_zero_of_sum_ne_zero hT
  have hF' := left_ne_zero_of_mul hF
  rw [Brooqs.Net.forestDist_eq] at hF'
  obtain ⟨hFg, -, -⟩ := Brooqs.Net.forestDistOf_single_support N hN (Brooqs.sampledAt id)
    (fun _ _ => Brooqs.isGood_singletons _)
    (fun _ _ _ _ hab => Brooqs.disjoint_lineages_sampledAt id hab) hF'
  exact (Brooqs.kingmanAbsorption_support hFg (right_ne_zero_of_mul hF)).1

private theorem bd_side_pattern : ∀ u v : Fin 3, u ≠ v → ∀ X Y : Finset (Fin 4),
    (X = side u ∨ X = (side u)ᶜ) → (Y = side v ∨ Y = (side v)ᶜ) →
    ¬(X ⊆ Y ∨ Y ⊆ X ∨ Disjoint X Y) := by
  decide

/-- **A gene tree induces at most one quartet tree on four taxa.** A good forest (nested or
disjoint clusters) does not induce two different quartet trees on the four taxa `k`. -/
theorem induces_unique {k : QuartetKey} (hk : keyTaxa k ⊆ L) {T : Finset (Finset L)}
    (hT : Brooqs.IsGood T) {u v : Fin 3} (hu : Induces T (k.quartet u))
    (hv : Induces T (k.quartet v)) : u = v := by
  by_contra huv
  obtain ⟨-, A, hA, hAu⟩ := hu
  obtain ⟨-, B, hB, hBv⟩ := hv
  rw [cutBy_iff k hk] at hAu hBv
  refine bd_side_pattern u v huv _ _ hAu hBv ?_
  rcases hT.1.2 A hA B hB with h | h | h
  · exact Or.inl fun i hi => by
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact h hi
  · exact Or.inr (Or.inl fun i hi => by
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact h hi)
  · refine Or.inr (Or.inr (disjoint_left.2 fun i hiA hiB => ?_))
    simp only [mem_filter, mem_univ, true_and] at hiA hiB
    exact disjoint_left.1 h hiA hiB

/-- The label of the quartet tree that the gene tree `T` induces on the four taxa `k`: `0`, `1` or
`2` for `k.quartet 0`, `k.quartet 1`, `k.quartet 2`, and `2` if it induces none. -/
def blockLabel (k : QuartetKey) (T : Finset (Finset L)) : Fin 3 :=
  if Induces T (k.quartet 0) then 0 else if Induces T (k.quartet 1) then 1 else 2

/-- If the three quartet trees on `k` have probability `1/3`, every gene tree in the support of the
NMSC induces exactly one of them, the one of label `blockLabel k T`. -/
theorem induces_iff_blockLabel {N : Brooqs.Net L} (hN : N.WellFormed) {k : QuartetKey}
    (hk : keyTaxa k ⊆ L) (hthird : ∀ u, quartetProb N (k.quartet u) = 1 / 3)
    {T : Finset (Finset L)} (hT : N.geneTreeDist id T ≠ 0) (u : Fin 3) :
    Induces T (k.quartet u) ↔ blockLabel k T = u := by
  have hgood := isGood_of_geneTreeDist hN.2 hT
  -- the number of quartet trees on `k` that a gene tree induces
  set m : Finset (Finset L) → ℝ := fun T' =>
    ∑ v : Fin 3, if Induces T' (k.quartet v) then 1 else 0 with hm
  have hm1 : ∀ T', N.geneTreeDist id T' ≠ 0 → m T' ≤ 1 := by
    intro T' hT'
    have hg := isGood_of_geneTreeDist hN.2 hT'
    by_cases h : ∃ v, Induces T' (k.quartet v)
    · obtain ⟨v, hv⟩ := h
      have : ∀ w, (if Induces T' (k.quartet w) then (1 : ℝ) else 0) =
          if w = v then 1 else 0 := fun w => by
        by_cases hw : Induces T' (k.quartet w)
        · rw [ite_eq_left hw, ite_eq_left (induces_unique hk hg hw hv)]
        · rw [ite_eq_right hw, ite_eq_right (fun h : w = v => hw (h ▸ hv))]
      simp only [hm, this, sum_ite_eq', mem_univ, ite_true, le_refl]
    · simp only [not_exists] at h
      simp only [hm, h, ite_false, sum_const_zero]
      norm_num
  -- in expectation, a gene tree induces exactly one
  have hsum : ∑ T', N.geneTreeDist id T' * m T' = ∑ T', N.geneTreeDist id T' := by
    rw [Brooqs.Net.geneTreeDist_sum hN.2]
    have h3 : ∑ v : Fin 3, quartetProb N (k.quartet v) = 1 := by
      simp only [hthird, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
    rw [← h3]
    simp only [hm, mul_sum, quartetProb, mul_ite, mul_one, mul_zero]
    rw [sum_comm]
  have hzero : ∀ T', N.geneTreeDist id T' * (1 - m T') = 0 := by
    have hnn : ∀ T', 0 ≤ N.geneTreeDist id T' * (1 - m T') := fun T' => by
      by_cases h : N.geneTreeDist id T' = 0
      · rw [h, zero_mul]
      · exact mul_nonneg (Brooqs.Net.geneTreeDist_nonneg hN id T') (by linarith [hm1 T' h])
    have htot : ∑ T', N.geneTreeDist id T' * (1 - m T') = 0 := by
      simp only [mul_sub, mul_one, sum_sub_distrib, hsum, sub_self]
    exact fun T' => (sum_eq_zero_iff_of_nonneg fun T' _ => hnn T').1 htot T' (mem_univ _)
  have hm' : m T = 1 := by
    have := hzero T
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hT
    · linarith
  -- so `T` induces one quartet tree, and only one
  have hex : ∃ v, Induces T (k.quartet v) := by
    by_contra h
    simp only [not_exists] at h
    simp only [hm, h, ite_false, sum_const_zero] at hm'
    norm_num at hm'
  obtain ⟨v, hv⟩ := hex
  have hlab : blockLabel k T = v := by
    unfold blockLabel
    by_cases h0 : Induces T (k.quartet 0)
    · rw [ite_eq_left h0]
      exact induces_unique hk hgood h0 hv
    · rw [ite_eq_right h0]
      by_cases h1 : Induces T (k.quartet 1)
      · rw [ite_eq_left h1]
        exact induces_unique hk hgood h1 hv
      · rw [ite_eq_right h1]
        have hv2 : v = 2 := by
          have : v ≠ 0 := fun h => h0 (h ▸ hv)
          have : v ≠ 1 := fun h => h1 (h ▸ hv)
          omega
        exact hv2.symm
  rw [hlab]
  constructor
  · intro hu
    exact induces_unique hk hgood hv hu
  · rintro rfl
    exact hv

/-! ### Most frequent labels -/

/-- The number of the `n` labels `y` equal to `u`. -/
def labelCount {n : ℕ} (y : Fin n → Fin 3) (u : Fin 3) : ℕ := #{i | y i = u}

/-- The sequences of `n` labels in which `u` is a most frequent label. -/
def maxLabels (n : ℕ) (u : Fin 3) : Finset (Fin n → Fin 3) :=
  univ.filter fun y => ∀ u', labelCount y u' ≤ labelCount y u

/-- Exchanging two labels shows that every label is a most frequent one in the same number of
sequences. -/
theorem card_maxLabels (n : ℕ) (u v : Fin 3) : #(maxLabels n u) = #(maxLabels n v) := by
  set σ := Equiv.swap u v
  have hcnt : ∀ (y : Fin n → Fin 3) w, labelCount (σ ∘ y) w = labelCount y (σ w) := by
    intro y w
    unfold labelCount
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply]
    constructor
    · intro h
      rw [← h, Equiv.swap_apply_self]
    · intro h
      rw [h, Equiv.swap_apply_self]
  have hσσ : ∀ x, σ (σ x) = x := fun x => Equiv.swap_apply_self u v x
  have hmem : ∀ (y : Fin n → Fin 3) (a b : Fin 3), σ a = b →
      (y ∈ maxLabels n a ↔ σ ∘ y ∈ maxLabels n b) := by
    intro y a b hab
    simp only [maxLabels, mem_filter, mem_univ, true_and, hcnt, ← hab, hσσ]
    constructor
    · intro h w
      exact h (σ w)
    · intro h w
      have := h (σ w)
      rwa [hσσ] at this
  refine card_nbij' (fun y => σ ∘ y) (fun y => σ ∘ y) (fun y hy => ?_) (fun y hy => ?_)
    (fun y _ => ?_) (fun y _ => ?_)
  · exact (hmem y u v (Equiv.swap_apply_left u v)).1 hy
  · have h := (hmem (σ ∘ y) u v (Equiv.swap_apply_left u v)).2
    have hy' : σ ∘ (σ ∘ y) = y := by
      funext i
      simp [σ, Equiv.swap_apply_self]
    rw [hy'] at h
    exact h hy
  · funext i
    simp [σ, Equiv.swap_apply_self]
  · funext i
    simp [σ, Equiv.swap_apply_self]

/-- The `n` labels add up to `n`, so for `n ≡ 1 (mod 3)` no sequence has the three labels most
frequent at once. -/
theorem maxLabels_inter_empty {n : ℕ} (hn : n % 3 = 1) (y : Fin n → Fin 3) :
    ¬ (y ∈ maxLabels n 0 ∧ y ∈ maxLabels n 1 ∧ y ∈ maxLabels n 2) := by
  rintro ⟨h0, h1, h2⟩
  simp only [maxLabels, mem_filter, mem_univ, true_and] at h0 h1 h2
  have hsum : n = labelCount y 0 + labelCount y 1 + labelCount y 2 := by
    have := card_eq_sum_card_fiberwise (f := y) (s := (univ : Finset (Fin n)))
      (t := (univ : Finset (Fin 3))) (fun i _ => mem_univ _)
    rw [card_univ, Fintype.card_fin, Fin.sum_univ_three] at this
    exact this
  have e01 := le_antisymm (h0 1) (h1 0)
  have e12 := le_antisymm (h1 2) (h2 1)
  omega

theorem card_maxLabels_le {n : ℕ} (hn : n % 3 = 1) : 3 * #(maxLabels n 0) ≤ 2 * 3 ^ n := by
  have hu : ∀ u, #(maxLabels n u) = #(maxLabels n 0) := fun u => card_maxLabels n u 0
  have huniv : #(univ : Finset (Fin n → Fin 3)) = 3 ^ n := by simp
  set A := maxLabels n 0
  set B := maxLabels n 1
  set C := maxLabels n 2
  have h1 : #A + #B ≤ 3 ^ n + #(A ∩ B) := by
    rw [← card_union_add_card_inter, ← huniv]
    exact Nat.add_le_add_right (card_le_univ _) _
  have h2 : #(A ∩ B) + #C ≤ 3 ^ n := by
    rw [← card_union_of_disjoint, ← huniv]
    · exact card_le_univ _
    · rw [disjoint_left]
      intro y hy hC
      rw [mem_inter] at hy
      exact maxLabels_inter_empty hn y ⟨hy.1, hy.2, hC⟩
  have hB : #B = #A := hu 1
  have hC : #C = #A := hu 2
  omega

section Genes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]

/-- The labels of the quartet trees that the first `n` gene trees induce on the four taxa `k`. -/
def labels (k : QuartetKey) (G : ℕ → Ω → Finset (Finset L)) (n : ℕ) (ω : Ω) : Fin n → Fin 3 :=
  fun i => blockLabel k (G i ω)

private theorem bd_measureReal (N : Brooqs.Net L) (G0 : Ω → Finset (Finset L))
    (hG0 : AEMeasurable G0 P) (hlaw : ∀ T, P.real (G0 ⁻¹' {T}) = N.geneTreeDist id T)
    (S : Finset (Finset (Finset L))) :
    P.real (G0 ⁻¹' ↑S) = ∑ T ∈ S, N.geneTreeDist id T := by
  have hmap : ∀ S : Set (Finset (Finset L)), P.real (G0 ⁻¹' S) = (P.map G0).real S := fun S => by
    rw [measureReal_def, measureReal_def,
      Measure.map_apply_of_aemeasurable hG0 MeasurableSet.of_discrete]
  rw [hmap, ← sum_measureReal_singleton]
  refine sum_congr rfl fun T _ => ?_
  rw [← hmap, hlaw]

/-- Almost surely, every gene tree is in the support of the NMSC. -/
theorem ae_geneTreeDist_ne_zero {N : Brooqs.Net L} (G : ℕ → Ω → Finset (Finset L))
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) :
    ∀ᵐ ω ∂P, ∀ i, N.geneTreeDist id (G i ω) ≠ 0 := by
  rw [ae_all_iff]
  intro i
  set Z : Finset (Finset (Finset L)) := univ.filter fun T => N.geneTreeDist id T = 0
  have h0 : P (G 0 ⁻¹' ↑Z) = 0 := by
    have h := bd_measureReal N (G 0) (hid 0).aemeasurable_fst hlaw Z
    rw [sum_eq_zero fun T hT => (mem_filter.1 hT).2, measureReal_eq_zero_iff] at h
    exact h
  have hi : P (G i ⁻¹' ↑Z) = 0 := by
    rw [(hid i).measure_mem_eq MeasurableSet.of_discrete]
    exact h0
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hi
  simp only [Set.mem_ofPred_eq, not_not] at hω
  simp [Z, hω]

/-- **The label sequences are uniform.** If the three quartet trees on `k` have probability `1/3`,
each sequence of `n` labels is that of the first `n` gene trees with probability `3^{-n}`: the gene
trees are independent. -/
theorem prob_labels_eq {N : Brooqs.Net L} (hN : N.WellFormed) {k : QuartetKey}
    (hk : keyTaxa k ⊆ L) (hthird : ∀ u, quartetProb N (k.quartet u) = 1 / 3)
    (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) (n : ℕ) (y : Fin n → Fin 3) :
    P (labels k G n ⁻¹' {y}) = (1 / 3 : ENNReal) ^ n := by
  set y' : ℕ → Fin 3 := fun i => if h : i < n then y ⟨i, h⟩ else 0
  have hset : labels k G n ⁻¹' {y} =
      ⋂ i ∈ range n, G i ⁻¹' {T | blockLabel k T = y' i} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, mem_range,
      Set.mem_ofPred_eq, y']
    constructor
    · rintro h i hi
      rw [dite_eq_left hi, ← h]
      rfl
    · intro h
      funext i
      have := h i i.2
      rw [dite_eq_left i.2] at this
      exact this
  -- each label has probability `1/3`
  have hone : ∀ i u, P (G i ⁻¹' {T | blockLabel k T = u}) = 1 / 3 := by
    intro i u
    rw [(hid i).measure_mem_eq MeasurableSet.of_discrete]
    have hae : (G 0 ⁻¹' {T | blockLabel k T = u} : Set Ω) =ᵐ[P]
        {ω | Induces (G 0 ω) (k.quartet u)} := by
      filter_upwards [ae_geneTreeDist_ne_zero G hid hlaw] with ω hω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, eq_iff_iff]
      exact (induces_iff_blockLabel hN hk hthird (hω 0) u).symm
    rw [measure_congr hae]
    have hreal := measureReal_induces N (G 0) (hid 0).aemeasurable_fst hlaw (k.quartet u)
    rw [hthird] at hreal
    rw [← ofReal_measureReal, hreal]
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rw [hset, hind.measure_inter_preimage_eq_mul (range n) (fun i _ => MeasurableSet.of_discrete)]
  simp only [hone, prod_const, card_range]

/-- **Every label is most frequent with the same probability.** If the three quartet trees on `k`
have probability `1/3`, the probability that the quartet tree `u` is a most frequent one among the
quartet trees that the first `n` gene trees induce on `k` is `#(maxLabels n u) / 3^n`, the same for
the three. -/
theorem prob_counts_eq {N : Brooqs.Net L} (hN : N.WellFormed) {k : QuartetKey}
    (hk : keyTaxa k ⊆ L) (hthird : ∀ u, quartetProb N (k.quartet u) = 1 / 3)
    (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) (n : ℕ) (u : Fin 3) :
    P (labels k G n ⁻¹' ↑(maxLabels n u)) = #(maxLabels n u) * (1 / 3 : ENNReal) ^ n := by
  have hmeas : AEMeasurable (labels k G n) P := by
    refine AEMeasurable.of_eval fun i => ?_
    exact (Measurable.of_discrete (f := blockLabel k)).comp_aemeasurable
      (hid i).aemeasurable_fst
  rw [← Measure.map_apply_of_aemeasurable hmeas (Set.toFinite _).measurableSet,
    ← sum_measure_singleton]
  simp only [Measure.map_apply_of_aemeasurable hmeas (measurableSet_singleton _),
    prob_labels_eq hN hk hthird G hind hid hlaw n, sum_const, nsmul_eq_mul]

/-- Algorithm 1 keeps all the copies of a most frequent quartet tree: if it returns on the four taxa
`k` exactly the copies of `k.quartet d`, then `d` is a most frequent quartet tree on `k`. -/
private theorem bd_max_of_exact {t : ℝ} {Q : Multiset Quartet} {k : QuartetKey} {d : Fin 3}
    (h : ∀ u, (filterQuartets t Q).count (k.quartet u) =
      if u = d then Q.count (k.quartet u) else 0) (u : Fin 3) :
    Q.count (k.quartet u) ≤ Q.count (k.quartet d) := by
  set f := frequencies (Q.map quartetEquiv) k with hfdef
  have hf : ∀ u, f u = Q.count (k.quartet u) := fun u => frequencies_map Q k u
  have hmax : ∀ u, f u ≤ f (rank f).1 := fun u => by
    obtain ⟨h12, h23⟩ := rank_ordered f
    rcases rank_covers f u with h' | h' | h' <;> rw [h'] <;> omega
  have htop : (filterQuartets t Q).count (k.quartet (rank f).1) = f (rank f).1 := by
    rw [count_filterQuartets]
    exact filterBlock_top_count t (Q.map quartetEquiv) k
  rw [← hf, ← hf]
  by_cases hq : (rank f).1 = d
  · rw [← hq]
    exact hmax u
  · rw [h, ite_eq_right hq] at htop
    have := hmax u
    omega

private theorem bd_card_range {n : ℕ} (p : ℕ → Prop) [DecidablePred p] :
    #((range n).filter p) = #(univ.filter fun i : Fin n => p i) := by
  rw [← card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply]
  constructor
  · rintro ⟨hi, hp⟩
    exact ⟨⟨i, hi⟩, hp, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.2, hj⟩

/-- **Quartet Filtering does not converge to Q(N_r) when the three quartet trees are equally
probable.** Let the gene trees be independent, each with the law of the NMSC on the metric network
`N` with distinct leaf labels on the taxa `L`; let `N` display exactly one quartet tree on the four
taxa `k`, `k.quartet d`, and let the three quartet trees on `k` have probability `1/3`. For every
threshold `t`, it is not almost sure that, for all large numbers `n` of genes, Algorithm 1 applied
to the quartet trees of the first `n` gene trees returns on `k` exactly the copies of the quartet
tree of Q(N_r): the probability of that event is less than `1`. -/
theorem not_ae_filterQuartets_of_equal {N : Brooqs.Net L} (hN : N.WellFormed) {k : QuartetKey}
    (hk : keyTaxa k ⊆ L) {d : Fin 3} (hdisp : ∀ u, DisplaysQuartet N (k.quartet u) ↔ u = d)
    (hthird : ∀ u, quartetProb N (k.quartet u) = 1 / 3)
    (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) (t : ℝ) :
    ¬ ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ u,
      (filterQuartets t (geneQuartets (fun i => G i ω) n)).count (k.quartet u) =
        if DisplaysQuartet N (k.quartet u) then
          (geneQuartets (fun i => G i ω) n).count (k.quartet u) else 0 := by
  intro H
  -- almost surely, the counts of the quartet trees are the counts of the labels
  have hcount : ∀ᵐ ω ∂P, ∀ n u, (geneQuartets (fun i => G i ω) n).count (k.quartet u) =
      labelCount (labels k G n ω) u := by
    filter_upwards [ae_geneTreeDist_ne_zero G hid hlaw] with ω hω
    intro n u
    rw [count_geneQuartets, bd_card_range]
    unfold labelCount labels
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    exact induces_iff_blockLabel hN hk hthird (hω i) u
  -- if Algorithm 1 eventually keeps exactly the copies of `d`, `d` is eventually most frequent
  set A : ℕ → Set Ω := fun n => labels k G n ⁻¹' ↑(maxLabels n d) with hA
  have H2 : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ A n := by
    filter_upwards [H, hcount] with ω hω hc
    filter_upwards [hω] with n hn
    simp only [hA, Set.mem_preimage, coe_filter, maxLabels, Set.mem_ofPred_eq, mem_univ,
      true_and]
    intro u
    rw [← hc, ← hc]
    refine bd_max_of_exact (t := t) (fun u' => ?_) u
    rw [hn u']
    simp only [hdisp]
  -- so the probability that `d` is most frequent tends to `1`
  set B : ℕ → Set Ω := fun m => {ω | ∀ n, m ≤ n → ω ∈ A n} with hB
  have hBmono : Monotone B := fun m m' hmm' ω hω n hn => hω n (hmm'.trans hn)
  have hnull : P (⋃ m, B m)ᶜ = 0 := by
    have h : ∀ᵐ ω ∂P, ω ∈ ⋃ m, B m := by
      filter_upwards [H2] with ω hω
      obtain ⟨m, hm⟩ := eventually_atTop.1 hω
      exact Set.mem_iUnion.2 ⟨m, hm⟩
    exact ae_iff.1 h
  have hBU : P (⋃ m, B m) = 1 := by
    refine le_antisymm prob_le_one ?_
    calc (1 : ENNReal) = P Set.univ := measure_univ.symm
      _ = P ((⋃ m, B m) ∪ (⋃ m, B m)ᶜ) := by rw [Set.union_compl_self]
      _ ≤ P (⋃ m, B m) + P (⋃ m, B m)ᶜ := measure_union_le _ _
      _ = P (⋃ m, B m) := by rw [hnull, add_zero]
  have hlimB : Tendsto (fun m => P (B m)) atTop (𝓝 1) := by
    have := tendsto_measure_iUnion_atTop (μ := P) hBmono
    rwa [hBU] at this
  have hlimA : Tendsto (fun n => P (A n)) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlimB tendsto_const_nhds
      (fun m => measure_mono fun ω hω => hω m le_rfl) (fun n => prob_le_one)
  -- but for `n ≡ 1 (mod 3)` its probability is at most `2/3`
  have hvalue : ∀ n, (P (A n)).toReal = #(maxLabels n d) * (1 / 3 : ℝ) ^ n := fun n => by
    rw [hA]
    simp only
    rw [prob_counts_eq hN hk hthird G hind hid hlaw n d, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_natCast, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  have hle : ∀ m, (P (A (3 * m + 1))).toReal ≤ 2 / 3 := fun m => by
    rw [hvalue]
    have hcard := card_maxLabels_le (n := 3 * m + 1) (by omega)
    rw [card_maxLabels (3 * m + 1) 0 d] at hcard
    have hpos : (0 : ℝ) < 3 ^ (3 * m + 1) := by positivity
    have hcard' : (3 : ℝ) * #(maxLabels (3 * m + 1) d) ≤ 2 * 3 ^ (3 * m + 1) := by
      exact_mod_cast hcard
    rw [div_pow, one_pow, ← div_eq_mul_one_div, div_le_iff₀ hpos]
    linarith
  have hlimR : Tendsto (fun n => (P (A n)).toReal) atTop (𝓝 1) := by
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hlimA
    rw [ENNReal.toReal_one] at this
    exact this
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hlimR.eventually_const_lt (show (5 / 6 : ℝ) < 1 by
    norm_num))
  have h1 := hn₀ (3 * n₀ + 1) (by omega)
  have h2 := hle n₀
  linarith

/-- **Section 3.3: Quartet Filtering on the boundary of the anomaly zone.** Under the assumptions of
`NMSC.anomalous_filterQuartets`, if `p D = 1 - p`, then for every threshold `t`, it is not almost
sure that, for all large numbers `n` of genes, Algorithm 1 returns on the four taxa `k` exactly the
copies of the quartet tree of Q(N_r) (`NMSC.not_ae_filterQuartets_of_equal`). -/
theorem anomalous_not_ae_filterQuartets_boundary {N : Brooqs.Net L} (hN : N.WellFormed)
    (htaxa : ∀ x : L, x ∈ N.taxa) {k : QuartetKey} (hk : keyTaxa k ⊆ L) (C : N.Cycle)
    {i j a b : Fin 4} (hinj : Function.Injective ![i, j, a, b])
    (hbelow : C.below.lin (keyTaxon k hk) = {i, j}) (h3 : 3 ≤ #(C.top.lin (keyTaxon k hk)))
    (h1 : ∀ n ∈ C.side₁.nodes ++ C.side₂.nodes, #(n.2.2.lin (keyTaxon k hk)) ≤ 1)
    (G : ℕ → Ω → Finset (Finset L)) (hind : iIndepFun G P)
    (hid : ∀ n, IdentDistrib (G n) (G 0) P P)
    (hlaw : ∀ T, P.real (G 0 ⁻¹' {T}) = N.geneTreeDist id T) :
    ∃ h₁ h₂ L₀ : ℝ, 0 < h₁ ∧ 0 < h₂ ∧ 0 < L₀ ∧
      (C.apartProb ![keyTaxon k hk i, keyTaxon k hk j, keyTaxon k hk a, keyTaxon k hk b] *
          (C.γ * (1 - C.γ) * (1 - Real.exp (-L₀)) - C.γ ^ 2 * (1 - Real.exp (-h₁)) -
            (1 - C.γ) ^ 2 * (1 - Real.exp (-h₂))) =
        1 - C.apartProb ![keyTaxon k hk i, keyTaxon k hk j, keyTaxon k hk a, keyTaxon k hk b] →
        ∀ t, ¬ ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ u,
          (filterQuartets t (geneQuartets (fun i => G i ω) n)).count (k.quartet u) =
            if DisplaysQuartet N (k.quartet u) then
              (geneQuartets (fun i => G i ω) n).count (k.quartet u) else 0) := by
  obtain ⟨hdisp, -⟩ := anomalous_quartetProb hN htaxa hk C hinj hbelow h3 h1
  obtain ⟨h₁, h₂, L₀, p1, p2, p3, hb⟩ :=
    anomalous_filterQuartets_boundary hN htaxa hk C hinj hbelow h3 h1 G hind hid hlaw
  exact ⟨h₁, h₂, L₀, p1, p2, p3, fun hzone t =>
    not_ae_filterQuartets_of_equal hN hk hdisp (hb hzone).1 G hind hid hlaw t⟩

end Genes

end NMSC

end Camus
