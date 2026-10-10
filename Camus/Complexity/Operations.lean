module

public import Camus.Network.Reticulations
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace Camus

namespace PhyloTree

theorem nodes_card_fork (l r : PhyloTree) :
    (PhyloTree.fork l r).nodes.card = l.nodes.card + r.nodes.card + 1 := by
  classical
  have hdis : Disjoint (l.nodes.image (false :: ·)) (r.nodes.image (true :: ·)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨x,hx,hxp⟩ := Finset.mem_image.mp hp
    obtain ⟨y,hy,hyp⟩ := Finset.mem_image.mp hq
    exact Bool.false_ne_true (List.cons.inj (hxp.trans hyp.symm)).1
  have hn : [] ∉ l.nodes.image (false :: ·) ∪ r.nodes.image (true :: ·) := by simp
  simp only [nodes,Finset.card_insert_of_notMem hn,Finset.card_union_of_disjoint hdis]
  rw [Finset.card_image_of_injective _ (fun p q h => (List.cons.inj h).2),
    Finset.card_image_of_injective _ (fun p q h => (List.cons.inj h).2)]

theorem nodes_count (t : PhyloTree) : t.nodes.card + 1 = 2 * t.labels.length := by
  induction t with
  | leaf a => simp [nodes,labels]
  | fork l r ihl ihr =>
    rw [nodes_card_fork]
    simp only [labels,List.length_append]
    omega

end PhyloTree

namespace Complexity

open DynamicProgramming

/-- The quartet test is an abstract unit-cost oracle. Its required output is the
paper's novel-quartet predicate; this specifies no runtime for Lean's semantic,
noncomputable `edgeWeight`. Preprocessing supplies LCA and clade lookups. -/
structure DeltaOracle (t : PhyloTree) (Q : Multiset Quartet) where
  test : Pair → Quartet → Bool
  correct : ∀ e ∈ EdgeAbove.candidates t, ∀ q ∈ Q.toFinset,
    test e q = true ↔ q ∈ novel t Q (Realization.graph t {e})

/-- One cached weight is computed by scanning the distinct weighted observations.
Input multiplicities are available as stored integers; reading and compressing a
raw list of observations is outside this distinct-topology input convention. -/
noncomputable def oracleWeight {t : PhyloTree} {Q : Multiset Quartet}
    (D : DeltaOracle t Q) (e : Pair) : ℕ :=
  ∑ q ∈ Q.toFinset, if D.test e q = true then Q.count q else 0

theorem oracleWeight_eq {t : PhyloTree} {Q : Multiset Quartet}
    (D : DeltaOracle t Q) {e : Pair} (he : e ∈ EdgeAbove.candidates t) :
    oracleWeight D e = edgeWeight t Q e := by
  unfold oracleWeight edgeWeight
  apply Finset.sum_congr rfl
  intro q hq
  simp only [D.correct e he q hq]

/-- The finite table construction scans all ordered node pairs once. Each pair
belongs to precisely one target's subproblem, rather than being rescanned at
all targets. -/
theorem candidate_visits (t : PhyloTree) :
    ∑ v ∈ t.nodes, (pairsAt t v).card = (EdgeAbove.candidates t).card := by
  classical
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro e he
  exact EdgeAbove.target_mem_nodes (Finset.mem_filter.mp he).2

theorem candidates_bound (t : PhyloTree) :
    (EdgeAbove.candidates t).card ≤ t.nodes.card ^ 2 := by
  unfold EdgeAbove.candidates
  calc
    _ ≤ (t.nodes ×ˢ t.nodes).card := Finset.card_filter_le _ _
    _ = _ := by simp [pow_two]

theorem hanging_bound (t : PhyloTree) (e : Pair) :
    (hanging t e).card ≤ t.nodes.card := Finset.card_filter_le _ _

/-- The scalar hanging-forest summation reads one cell for each actual hanging
subtree. Equations (4) and (5) equal this sum by `hanging_score`. -/
noncomputable def hangingReads (t : PhyloTree) : ℕ :=
  ∑ e ∈ EdgeAbove.candidates t, (hanging t e).card

theorem hangingReads_bound (t : PhyloTree) :
    hangingReads t ≤ (EdgeAbove.candidates t).card * t.nodes.card := by
  unfold hangingReads
  calc
    _ ≤ ∑ _e ∈ EdgeAbove.candidates t, t.nodes.card :=
      Finset.sum_le_sum (fun e _ => hanging_bound t e)
    _ = _ := by simp

/-- Unit operations in an abstract tabulation: all-pairs LCA construction,
node-by-leaf membership table, depth and score arrays, one delta query per
candidate/distinct quartet, hanging-cell reads, and candidate comparisons.
Constant work per listed operation is absorbed by the final constant. -/
noncomputable def scalarOperations (t : PhyloTree) (Q : Multiset Quartet) : ℕ :=
  (t.nodes ×ˢ t.nodes).card + (t.nodes ×ˢ t.taxa).card + 2 * t.nodes.card +
    (EdgeAbove.candidates t ×ˢ Q.toFinset).card + hangingReads t +
    (EdgeAbove.candidates t).card

/-- Budget tabulation reuses the quartet weights. For each budget column and
hanging subtree it enumerates two partial-budget indices, and performs one
constant-time lookup/comparison per pair. This upper count allows infeasible
index pairs too, so it covers the recurrence's restricted allocations. -/
noncomputable def budgetOperations (t : PhyloTree) (Q : Multiset Quartet) (m : ℕ) : ℕ :=
  (t.nodes ×ˢ t.nodes).card + (t.nodes ×ˢ t.taxa).card + 2 * t.nodes.card +
    (EdgeAbove.candidates t ×ˢ Q.toFinset).card +
    hangingReads t * (Finset.range m ×ˢ (Finset.range (m+1) ×ˢ Finset.range (m+1))).card +
    (t.nodes ×ˢ (Finset.range m ×ˢ (Finset.range (m+1) ×ˢ Finset.range (m+1)))).card +
    (EdgeAbove.candidates t ×ˢ Finset.range m).card

/-- Scalar operation bound of §2.3. The constant is explicit; Q is counted
with duplicates removed, while their multiplicities remain stored weights. -/
theorem scalarOperations_bound {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet) :
    scalarOperations t Q ≤ 32 * t.taxa.card ^ 2 * (Q.toFinset.card + t.taxa.card) := by
  have hn := t.labels_nonempty
  have hnodes := t.nodes_count
  have htaxa : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  have hc := candidates_bound t
  have hh := hangingReads_bound t
  simp only [scalarOperations,Finset.card_product]
  rw [htaxa] at *
  have hcN : (EdgeAbove.candidates t).card ≤ 4*t.labels.length^2 := by nlinarith
  have hreads : hangingReads t ≤ 8*t.labels.length^3 := by
    nlinarith only [hh,hnodes,Nat.mul_le_mul_right t.nodes.card hcN]
  have hn2 : t.labels.length ≤ t.labels.length^2 := by nlinarith
  have hn3 : t.labels.length^2 ≤ t.labels.length^3 := by
    nlinarith [Nat.mul_le_mul_right t.labels.length hn2]
  nlinarith [Nat.mul_le_mul_right Q.toFinset.card hcN]

/-- §2.4's additional m³ n term, under the explicit unit-cost lookup model.
The algorithm needs only 1≤m≤n−1 columns; the upper restriction is supplied
by `anchored_reticulation_bound` and is unnecessary for this inequality. -/
theorem budgetOperations_bound {t : PhyloTree} (ht : t.WellLabelled)
    (Q : Multiset Quartet) {m : ℕ} (hm : 1 ≤ m) :
    budgetOperations t Q m ≤
      100 * t.taxa.card ^ 2 * (Q.toFinset.card + m ^ 3 * t.taxa.card) := by
  have hn := t.labels_nonempty
  have hnodes := t.nodes_count
  have htaxa : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  have hc := candidates_bound t
  have hh := hangingReads_bound t
  unfold budgetOperations
  simp only [Finset.card_product,Finset.card_range]
  rw [htaxa] at *
  have hcN : (EdgeAbove.candidates t).card ≤ 4*t.labels.length^2 := by nlinarith
  have hindex : m * ((m+1)*(m+1)) ≤ 4*m^3 := by
    have hb : m+1 ≤ 2*m := by omega
    have hs := Nat.mul_le_mul hb hb
    nlinarith only [Nat.mul_le_mul_left m hs]
  have hreads : hangingReads t ≤ 8*t.labels.length^3 := by
    nlinarith only [hh,hnodes,Nat.mul_le_mul_right t.nodes.card hcN]
  have hm2 : m ≤ m^2 := by nlinarith
  have hm3 : m ≤ m^3 := by nlinarith [Nat.mul_le_mul_right m hm2]
  have hmone : 1 ≤ m^3 := by omega
  have hn2 : t.labels.length ≤ t.labels.length^2 := by nlinarith
  have hn3 : t.labels.length^2 ≤ t.labels.length^3 := by
    nlinarith [Nat.mul_le_mul_right t.labels.length hn2]
  have hn13 : t.labels.length ≤ t.labels.length^3 := hn2.trans hn3
  have hpre : t.nodes.card*t.nodes.card + t.nodes.card*t.labels.length + 2*t.nodes.card ≤
      10*t.labels.length^3*m^3 := by
    nlinarith only [hnodes,hn2,hn3,Nat.mul_le_mul_right (t.labels.length^3) hmone]
  have hbranch : t.nodes.card*(m*((m+1)*(m+1))) ≤ 8*t.labels.length^3*m^3 := by
    nlinarith only [Nat.mul_le_mul (show t.nodes.card ≤ 2*t.labels.length by omega) hindex,
      Nat.mul_le_mul_right (m^3) hn13]
  have hcBudget : (EdgeAbove.candidates t).card*m ≤ 4*t.labels.length^3*m^3 := by
    nlinarith only [Nat.mul_le_mul hcN hm3,Nat.mul_le_mul_right (m^3) hn3]
  nlinarith only [hpre,hbranch,hcBudget,Nat.mul_le_mul hreads hindex,
    Nat.mul_le_mul_right Q.toFinset.card hcN]

def quartetKey (q : Quartet) : ℕ × (ℕ × (ℕ × (ℕ × Fin 3))) :=
  (q.a,q.b,q.c,q.d,q.split)

theorem quartetKey_injective : Function.Injective quartetKey := by
  intro q r h
  cases q
  cases r
  simp only [quartetKey,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl,rfl,rfl⟩
  rfl

/-- Storage of distinct observed quartets has the required fourth-degree bound
only when every observed quartet uses the constraint tree's taxon set. -/
theorem observedQuartets_bound (t : PhyloTree) (Q : Multiset Quartet)
    (hQ : ∀ q ∈ Q.toFinset, q.taxa ⊆ t.taxa) :
    Q.toFinset.card ≤ 3*t.taxa.card^4 := by
  classical
  let slots := t.taxa ×ˢ (t.taxa ×ˢ (t.taxa ×ˢ (t.taxa ×ˢ (Finset.univ : Finset (Fin 3)))))
  have hs : Q.toFinset.image quartetKey ⊆ slots := by
    intro k hk
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hk
    have h := hQ q hq
    have ha := h (show q.a ∈ q.taxa by simp [Quartet.taxa])
    have hb := h (show q.b ∈ q.taxa by simp [Quartet.taxa])
    have hc := h (show q.c ∈ q.taxa by simp [Quartet.taxa])
    have hd := h (show q.d ∈ q.taxa by simp [Quartet.taxa])
    simp [slots,quartetKey,ha,hb,hc,hd]
  have hcard := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ quartetKey_injective] at hcard
  have hslots : slots.card = 3*t.taxa.card^4 := by
    simp only [slots,Finset.card_product,Finset.card_univ,Fintype.card_fin]
    ring
  rw [hslots] at hcard
  exact hcard

/-- Number of unit-size stored integers: compressed observations, cached pair
weights, all-pairs LCA, clade membership, depth and scalar DP cells. Multiplicity
is one integer per distinct quartet, beside its four taxon labels and split.
This is the paper's unit-space convention. -/
noncomputable def scalarSpace (t : PhyloTree) (Q : Multiset Quartet) : ℕ :=
  6*Q.toFinset.card + (EdgeAbove.candidates t).card + (t.nodes ×ˢ t.nodes).card +
    (t.nodes ×ˢ t.taxa).card + 2*t.nodes.card

theorem scalarSpace_bound {t : PhyloTree} (ht : t.WellLabelled) (Q : Multiset Quartet)
    (hQ : ∀ q ∈ Q.toFinset, q.taxa ⊆ t.taxa) : scalarSpace t Q ≤ 32*t.taxa.card^4 := by
  have hn := t.labels_nonempty
  have hnodes := t.nodes_count
  have htaxa : t.taxa.card = t.labels.length := List.toFinset_card_of_nodup ht
  have hc := candidates_bound t
  have hq := observedQuartets_bound t Q hQ
  unfold scalarSpace
  simp only [Finset.card_product]
  rw [htaxa] at *
  have hn2 : t.labels.length ≤ t.labels.length^2 := by nlinarith
  have hn4 : t.labels.length^2 ≤ t.labels.length^4 := by nlinarith
  nlinarith

end Complexity
end Camus
