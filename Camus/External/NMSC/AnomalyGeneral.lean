module

public import Camus.External.NMSC.AnomalyShapes
public import Camus.External.NMSC.Swap

/-!
# The anomalous configuration in an arbitrary network

Section 3.3 of CAMUS designs Quartet Filtering (Algorithm 1) on the presumption that, on four taxa
where a level-1 network displays one quartet, that quartet is the most probable. The presumption
can fail only in the anomalous configuration (`Brooqs.Net.Anomalous`): a cycle `Ω` with two of the
four taxa below its hybrid node and the two others in two other components, a 3₂-cycle in the
terms of Ané, Fogg, Allman, Baños and Rhodes (2024). This file computes the quartet CFs of four
taxa in this configuration, in an arbitrary metric network with distinct leaf labels: they are the
CFs of the 3-cycle above two taxa `N₃₂` (`Brooqs.net32_quartetCF`) with effective parameters
(`Brooqs.Net.Cycle.quartetCF_of_anomalous`):

* `γ`, the inheritance probability of the cycle;
* `p`, the probability that the lineages of the two taxa below the hybrid node reach it apart
  (`Brooqs.Net.Cycle.apartProb`), in place of `e^{-ℓ}`; `0 ≤ p ≤ 1`, and `p = e^{-ℓ}` when the two
  taxa form a cherry with an edge of length `ℓ` above it (`Brooqs.Net.Cycle.apartProb_cherry`);
* lengths `h₁`, `h₂` and `L` added up along the sides of the cycle: the lengths between the hybrid
  node, the nodes from which the networks holding the two other taxa hang, and the top node
  (`Brooqs.Side.lenBelow`, `Brooqs.Side.lenAbove`, `Brooqs.Side.length`). With one of the two
  other taxa, `z`, hanging from the side `S₁` and the other outside the cycle, `h₁` is the length of
  `S₁` below the node of `z`, `L` the length above it, and `h₂` the length of `S₂`. With `z` on `S₁`
  and `w` on `S₂`, `L` is the length of the path between their nodes through the top node. With
  `z` above `w` on `S₁`, `h₁` is the length of `S₁` below the node of `w`, `L` the length between
  the two nodes, and `h₂` the length of `S₂` plus the length of `S₁` above the node of `z`. The
  cases with the sides exchanged follow by the symmetry of the model (`Brooqs.Net.SideSwap`).

The anomaly criterion follows (`Brooqs.Net.Cycle.anomalous_iff_of_anomalous`): the displayed
quartet is strictly less probable than the two others iff
`1 - p < p (γ(1 - γ)(1 - e^{-L}) - γ²(1 - e^{-h₁}) - (1 - γ)²(1 - e^{-h₂}))`, the criterion of
`Brooqs.net32_anomalous_iff_u` with `p` in place of `e^{-ℓ}`.

## Main results

* `Brooqs.Side.length`, `Brooqs.Side.lenAbove`, `Brooqs.Side.lenBelow`: lengths along a side.
* `Brooqs.Side.forestDist_of_lin_empty`, `Brooqs.Side.forestDist_of_lin_single`,
  `Brooqs.Side.forestDist_of_lin_pair`: the lineages that a side brings to the top node of its
  cycle, when its pendant networks hold no sampled taxon, one, or two.
* `Brooqs.Net.Cycle.apartProb`, `Brooqs.Net.Cycle.apartProb_nonneg`,
  `Brooqs.Net.Cycle.apartProb_le_one`, `Brooqs.Net.Cycle.apartProb_cherry`,
  `Brooqs.Net.Cycle.below_forestDist`: the probability that the two lineages below the hybrid
  node reach it apart.
* `Brooqs.Net.Cycle.quartetCF_of_anomalous`, `Brooqs.Net.Cycle.splitCF_of_anomalous`: the three
  quartet CFs, with the two taxa below the hybrid node labelled `0` and `1`, or with any labels.
* `Brooqs.Net.Cycle.anomalous_iff_of_anomalous`: the anomaly criterion.

## Proof

A quartet CF is the expected score of the forest at the top node of the cycle
(`Brooqs.quartetCF_eq_sum_top`). The forest arriving at the hybrid node is a good forest on the two
lineages below it, so they have coalesced or not (`Brooqs.Net.Cycle.below_forestDist`). A pendant
network holding at most one sampled taxon brings that lineage, or none, deterministically
(`Brooqs.Net.forestDist_of_card_le_one`), and the Kingman transitions along consecutive edges
compose (`Brooqs.kingmanTransition_add_vecMul`), so each side acts as the side of a 3₂-cycle with
the lengths added up (`Brooqs.Side.forestDist_of_lin_single` and the two other lemmas). The
expected score at the top node of such a cycle is computed in `AnomalyShapes.lean`
(`Brooqs.expectedScore_top_outside`, `Brooqs.expectedScore_top_sides`,
`Brooqs.expectedScore_top_oneSide`). The two undisplayed quartets have equal CFs
(`Brooqs.Net.splitCF_swap`) and the three CFs add up to `1` (`Brooqs.Net.splitCF_sum`).
-/

@[expose] public noncomputable section

namespace Brooqs

open Finset Matrix

universe u

variable {X : Type u}

/-! ### Lengths along a side -/

/-- The length of a side: the lengths of its edges added up, from the top node of the cycle to its
hybrid node. -/
def Side.length : Side X → ℝ
  | .hyb ℓ => ℓ
  | .node ℓ _ _ S => ℓ + S.length

theorem Side.length_pos : ∀ {S : Side X}, S.IsMetric → 0 < S.length
  | .hyb _, h => h
  | .node _ _ _ S, h => by
      have := Side.length_pos (S := S) h.2.2.2
      simp only [Side.length]
      linarith [h.1]

variable [DecidableEq X]

/-- The length of the path along the side `S` from the top node of the cycle to the node from which
hangs the network holding the taxon `t`. -/
def Side.lenAbove (t : X) : Side X → ℝ
  | .hyb _ => 0
  | .node ℓ _ M S => if t ∈ M.taxa then ℓ else ℓ + S.lenAbove t

/-- The length of the path along the side `S` from the node from which hangs the network holding the
taxon `t` to the hybrid node of the cycle. -/
def Side.lenBelow (t : X) : Side X → ℝ
  | .hyb ℓ => ℓ
  | .node _ _ M S => if t ∈ M.taxa then S.length else S.lenBelow t

theorem Side.lenBelow_pos (t : X) : ∀ {S : Side X}, S.IsMetric → 0 < S.lenBelow t
  | .hyb _, h => h
  | .node _ _ M S, h => by
      simp only [Side.lenBelow]
      split_ifs
      · exact Side.length_pos h.2.2.2
      · exact Side.lenBelow_pos t h.2.2.2

theorem Side.lenAbove_pos {t : X} : ∀ {S : Side X}, S.IsMetric → t ∈ S.taxa → 0 < S.lenAbove t
  | .hyb _, _, ht => by simp [Side.taxa, Side.leaves] at ht
  | .node _ _ M S, h, ht => by
      simp only [Side.lenAbove]
      split_ifs with hM
      · exact h.1
      · have hS : t ∈ S.taxa := by
          rw [Side.taxa_node] at ht
          exact (mem_union.1 ht).resolve_left hM
        linarith [h.1, Side.lenAbove_pos h.2.2.2 hS]

/-! ### The lineages that a side brings to the top node of its cycle -/

theorem Side.lin_node (s : Fin 4 → X) (ℓ b : ℝ) (M : Net X) (S : Side X) :
    (Side.node ℓ b M S).lin s = M.lin s ∪ S.lin s := by
  ext l
  simp [Side.lin, Net.lin, Side.taxa_node]

theorem Side.lin_hyb (s : Fin 4 → X) (ℓ : ℝ) : (Side.hyb ℓ : Side X).lin s = ∅ := by
  ext l
  simp [Side.lin, Side.taxa, Side.leaves]

private theorem ag_disjoint {ℓ b : ℝ} {M : Net X} {S : Side X}
    (h : (Side.node ℓ b M S).leaves.Nodup) {x : X} (hM : x ∈ M.taxa) : x ∉ S.taxa := by
  have hd := List.disjoint_of_nodup_append (show (M.leaves ++ S.leaves).Nodup from h)
  simp only [Net.taxa, Side.taxa, List.mem_toFinset] at hM ⊢
  exact fun hS => hd hM hS

omit [DecidableEq X] in
private theorem ag_nodup_tail {ℓ b : ℝ} {M : Net X} {S : Side X}
    (h : (Side.node ℓ b M S).leaves.Nodup) : S.leaves.Nodup :=
  (List.sublist_append_right M.leaves S.leaves).nodup h

private theorem ag_mem_lin {s : Fin 4 → X} {M : Net X} {l : Fin 4} :
    l ∈ M.lin s ↔ s l ∈ M.taxa := by
  simp [Net.lin]

private theorem ag_mem_lin_side {s : Fin 4 → X} {S : Side X} {l : Fin 4} :
    l ∈ S.lin s ↔ s l ∈ S.taxa := by
  simp [Side.lin]

/-- A network from which no lineage is sampled brings none. -/
theorem Net.forestDist_kT_of_lin_empty {M : Net X} {s : Fin 4 → X} (h : M.lin s = ∅) (b : ℝ) :
    M.forestDist s ᵥ* kingmanTransition b = Pi.single ∅ 1 := by
  have hc : #(univ.filter fun l => s l ∈ M.taxa) ≤ 1 := by
    change #(M.lin s) ≤ 1
    rw [h]
    simp
  rw [Net.forestDist_of_card_le_one M s hc]
  have hsf : M.sampledForest s = ∅ := by
    change (M.lin s).image (fun l => ({l} : Finset (Fin 4))) = ∅
    rw [h, image_empty]
  rw [hsf]
  exact single_vecMul_kingmanTransition ADR11.isForest_empty
    ((card_le_card (ADR11.roots_subset (∅ : Finset (Finset (Fin 4))))).trans (by simp)) b

/-- A network from which only the lineage `k` is sampled brings it, alone. -/
theorem Net.forestDist_kT_of_lin_single {M : Net X} {s : Fin 4 → X} {k : Fin 4}
    (h : M.lin s = {k}) (b : ℝ) :
    M.forestDist s ᵥ* kingmanTransition b = Pi.single {{k}} 1 := by
  have hc : #(univ.filter fun l => s l ∈ M.taxa) ≤ 1 := by
    change #(M.lin s) ≤ 1
    rw [h]
    simp
  rw [Net.forestDist_of_card_le_one M s hc]
  have hsf : M.sampledForest s = {{k}} := by
    change (M.lin s).image (fun l => ({l} : Finset (Fin 4))) = {{k}}
    rw [h, image_singleton]
  rw [hsf]
  have hF : ADR11.IsForest ({{k}} : Finset (Finset (Fin 4))) := by
    simpa using (isGood_singletons ({k} : Finset (Fin 4))).1
  exact single_vecMul_kingmanTransition hF
    ((card_le_card (ADR11.roots_subset _)).trans (by simp)) b

/-- **A side without sampled taxa.** If no lineage is sampled from the networks hanging from the
side `S`, a forest `E` that takes its hybrid edge travels along the whole side: Kingman's
coalescent for the time `S.length`. -/
theorem Side.forestDist_of_lin_empty {s : Fin 4 → X} :
    ∀ {S : Side X}, S.lin s = ∅ → ∀ E,
      S.forestDist s E = Pi.single E 1 ᵥ* kingmanTransition S.length
  | .hyb ℓ, _, E => by
      show kingmanTransition ℓ E = _
      funext G
      rw [single_one_vecMul]
      rfl
  | .node ℓ b M S, h, E => by
      rw [Side.lin_node, union_eq_empty] at h
      show forestUnion (S.forestDist s E) (M.forestDist s ᵥ* kingmanTransition b) ᵥ*
        kingmanTransition ℓ = _
      rw [Net.forestDist_kT_of_lin_empty h.1, forestUnion_single_empty,
        Side.forestDist_of_lin_empty h.2 E, kingmanTransition_add_vecMul]
      simp only [Side.length]
      rw [add_comm]

/-- **A side with one sampled taxon.** If only the lineage `k` is sampled from the networks
hanging from the side `S` (with distinct leaf labels), a forest `E` that takes its hybrid edge
travels for the time `S.lenBelow (s k)`, is joined by `k`, and travels for the time
`S.lenAbove (s k)` to the top node. -/
theorem Side.forestDist_of_lin_single {s : Fin 4 → X} {k : Fin 4} :
    ∀ {S : Side X}, S.leaves.Nodup → S.lin s = {k} → ∀ E,
      S.forestDist s E = forestUnion (Pi.single E 1 ᵥ* kingmanTransition (S.lenBelow (s k)))
        (Pi.single {{k}} 1) ᵥ* kingmanTransition (S.lenAbove (s k))
  | .hyb ℓ, _, h, _ => by
      rw [Side.lin_hyb] at h
      exact absurd h.symm (singleton_ne_empty k)
  | .node ℓ b M S, hn, h, E => by
      rw [Side.lin_node] at h
      have hmem : ∀ l, l ∈ M.lin s ∨ l ∈ S.lin s ↔ l = k := fun l => by
        rw [← mem_union, h, mem_singleton]
      show forestUnion (S.forestDist s E) (M.forestDist s ᵥ* kingmanTransition b) ᵥ*
        kingmanTransition ℓ = _
      by_cases hk : s k ∈ M.taxa
      · -- `k` hangs from the first node: the rest of the side brings nothing
        have hM : M.lin s = {k} := by
          ext l
          rw [mem_singleton]
          exact ⟨fun hl => (hmem l).1 (Or.inl hl), fun hl => hl ▸ ag_mem_lin.2 hk⟩
        have hS : S.lin s = ∅ := by
          ext l
          simp only [notMem_empty, iff_false]
          intro hl
          obtain rfl := (hmem l).1 (Or.inr hl)
          exact ag_disjoint hn hk (ag_mem_lin_side.1 hl)
        rw [Net.forestDist_kT_of_lin_single hM, Side.forestDist_of_lin_empty hS E]
        simp only [Side.lenBelow, Side.lenAbove, hk, ↓reduceIte]
      · -- `k` hangs further down
        have hM : M.lin s = ∅ := by
          ext l
          simp only [notMem_empty, iff_false]
          intro hl
          obtain rfl := (hmem l).1 (Or.inl hl)
          exact hk (ag_mem_lin.1 hl)
        have hS : S.lin s = {k} := by
          ext l
          rw [mem_singleton]
          refine ⟨fun hl => (hmem l).1 (Or.inr hl), fun hl => ?_⟩
          rcases (hmem l).2 hl with h' | h'
          · rw [hM] at h'
            exact absurd h' (notMem_empty l)
          · exact h'
        rw [Net.forestDist_kT_of_lin_empty hM, forestUnion_single_empty,
          Side.forestDist_of_lin_single (ag_nodup_tail hn) hS E, kingmanTransition_add_vecMul]
        simp only [Side.lenBelow, Side.lenAbove, hk, ↓reduceIte]
        rw [add_comm (S.lenAbove (s k))]

/-- **A side with two sampled taxa.** If exactly the lineages `k ≠ m` are sampled from the
networks hanging from the metric side `S` (with distinct leaf labels), from two different nodes,
then for the one, `u`, hanging higher and the other, `v`: a forest `E` that takes the hybrid edge
travels for the time `S.lenBelow (s v)`, is joined by `v`, travels for the positive time
`S.lenAbove (s v) - S.lenAbove (s u)`, is joined by `u`, and travels for the time
`S.lenAbove (s u)` to the top node. -/
theorem Side.forestDist_of_lin_pair {s : Fin 4 → X} {k m : Fin 4} (hkm : k ≠ m) :
    ∀ {S : Side X}, S.IsMetric → S.leaves.Nodup → S.lin s = {k, m} →
      (∀ n ∈ S.nodes, #(n.2.2.lin s) ≤ 1) →
      ∃ u v : Fin 4, ((u = k ∧ v = m) ∨ (u = m ∧ v = k)) ∧
        0 < S.lenAbove (s v) - S.lenAbove (s u) ∧ ∀ E,
          S.forestDist s E = forestUnion (forestUnion
            (Pi.single E 1 ᵥ* kingmanTransition (S.lenBelow (s v))) (Pi.single {{v}} 1) ᵥ*
              kingmanTransition (S.lenAbove (s v) - S.lenAbove (s u)))
            (Pi.single {{u}} 1) ᵥ* kingmanTransition (S.lenAbove (s u))
  | .hyb ℓ, _, _, h, _ => by
      rw [Side.lin_hyb] at h
      exact absurd h.symm (insert_ne_empty k {m})
  | .node ℓ b M S, hm, hn, h, hp => by
      rw [Side.lin_node] at h
      have hmem : ∀ l, l ∈ M.lin s ∨ l ∈ S.lin s ↔ l = k ∨ l = m := fun l => by
        rw [← mem_union, h, mem_insert, mem_singleton]
      have hM1 : #(M.lin s) ≤ 1 := hp (ℓ, b, M) (by simp [Side.nodes])
      have hpS : ∀ n ∈ S.nodes, #(n.2.2.lin s) ≤ 1 := fun n hn' =>
        hp n (by simp [Side.nodes, hn'])
      have hSm : S.IsMetric := hm.2.2.2
      have hSn : S.leaves.Nodup := ag_nodup_tail hn
      -- the lineage hanging from the first node, if any, is the higher one
      have key : ∀ {u v : Fin 4}, u ≠ v → (∀ l, l = k ∨ l = m ↔ l = u ∨ l = v) →
          s u ∈ M.taxa →
          ∃ u' v' : Fin 4, ((u' = k ∧ v' = m) ∨ (u' = m ∧ v' = k)) ∧
            0 < (Side.node ℓ b M S).lenAbove (s v') - (Side.node ℓ b M S).lenAbove (s u') ∧ ∀ E,
              forestUnion (S.forestDist s E) (M.forestDist s ᵥ* kingmanTransition b) ᵥ*
                kingmanTransition ℓ = forestUnion (forestUnion
                (Pi.single E 1 ᵥ* kingmanTransition ((Side.node ℓ b M S).lenBelow (s v')))
                  (Pi.single {{v'}} 1) ᵥ* kingmanTransition
                    ((Side.node ℓ b M S).lenAbove (s v') - (Side.node ℓ b M S).lenAbove (s u')))
                (Pi.single {{u'}} 1) ᵥ*
                  kingmanTransition ((Side.node ℓ b M S).lenAbove (s u')) := by
        intro u v huv hset hu
        have hmem' : ∀ l, l ∈ M.lin s ∨ l ∈ S.lin s ↔ l = u ∨ l = v := fun l =>
          (hmem l).trans (hset l)
        have hvM : s v ∉ M.taxa := by
          intro hv
          have h2 : ({u, v} : Finset (Fin 4)) ⊆ M.lin s := by
            intro l hl
            rw [mem_insert, mem_singleton] at hl
            rcases hl with rfl | rfl
            · exact ag_mem_lin.2 hu
            · exact ag_mem_lin.2 hv
          have := card_le_card h2
          rw [card_pair huv] at this
          omega
        have hM : M.lin s = {u} := by
          ext l
          rw [mem_singleton]
          constructor
          · intro hl
            rcases (hmem' l).1 (Or.inl hl) with rfl | rfl
            · rfl
            · exact absurd (ag_mem_lin.1 hl) hvM
          · rintro rfl
            exact ag_mem_lin.2 hu
        have hS : S.lin s = {v} := by
          ext l
          rw [mem_singleton]
          constructor
          · intro hl
            rcases (hmem' l).1 (Or.inr hl) with rfl | rfl
            · exact absurd (ag_mem_lin_side.1 hl) (ag_disjoint hn hu)
            · rfl
          · intro hl
            rw [hl]
            rcases (hmem' v).2 (Or.inr rfl) with h' | h'
            · exact absurd (ag_mem_lin.1 h') hvM
            · exact h'
        have hvS : s v ∈ S.taxa := ag_mem_lin_side.1 (by rw [hS]; exact mem_singleton_self v)
        have ha : (Side.node ℓ b M S).lenAbove (s u) = ℓ := by
          simp only [Side.lenAbove, hu, ↓reduceIte]
        have hb : (Side.node ℓ b M S).lenAbove (s v) = ℓ + S.lenAbove (s v) := by
          simp only [Side.lenAbove, hvM, ↓reduceIte]
        have hc : (Side.node ℓ b M S).lenBelow (s v) = S.lenBelow (s v) := by
          simp only [Side.lenBelow, hvM, ↓reduceIte]
        have hk' : (u = k ∧ v = m) ∨ (u = m ∧ v = k) := by
          rcases (hset u).2 (Or.inl rfl) with rfl | rfl
          · rcases (hset v).2 (Or.inr rfl) with h' | h'
            · exact absurd h'.symm huv
            · exact Or.inl ⟨rfl, h'⟩
          · rcases (hset v).2 (Or.inr rfl) with h' | h'
            · exact Or.inr ⟨rfl, h'⟩
            · exact absurd h'.symm huv
        refine ⟨u, v, hk', ?_, fun E => ?_⟩
        · rw [ha, hb]
          linarith [Side.lenAbove_pos hSm hvS]
        · rw [Net.forestDist_kT_of_lin_single hM, Side.forestDist_of_lin_single hSn hS E, ha, hb,
            hc, add_sub_cancel_left]
      by_cases hk : s k ∈ M.taxa
      · exact key hkm (fun l => Iff.rfl) hk
      by_cases hm' : s m ∈ M.taxa
      · exact key (Ne.symm hkm) (fun l => or_comm) hm'
      -- neither hangs from the first node: both hang further down
      have hM : M.lin s = ∅ := by
        ext l
        simp only [notMem_empty, iff_false]
        intro hl
        rcases (hmem l).1 (Or.inl hl) with rfl | rfl
        · exact hk (ag_mem_lin.1 hl)
        · exact hm' (ag_mem_lin.1 hl)
      have hS : S.lin s = {k, m} := by
        ext l
        rw [mem_insert, mem_singleton]
        refine ⟨fun hl => (hmem l).1 (Or.inr hl), fun hl => ?_⟩
        rcases (hmem l).2 hl with h' | h'
        · rw [hM] at h'
          exact absurd h' (notMem_empty l)
        · exact h'
      obtain ⟨u, v, huv, hpos, hE⟩ := Side.forestDist_of_lin_pair hkm hSm hSn hS hpS
      have huM : s u ∉ M.taxa := by rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
      have hvM : s v ∉ M.taxa := by rcases huv with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
      have ha : (Side.node ℓ b M S).lenAbove (s u) = ℓ + S.lenAbove (s u) := by
        simp only [Side.lenAbove, huM, ↓reduceIte]
      have hb : (Side.node ℓ b M S).lenAbove (s v) = ℓ + S.lenAbove (s v) := by
        simp only [Side.lenAbove, hvM, ↓reduceIte]
      have hc : (Side.node ℓ b M S).lenBelow (s v) = S.lenBelow (s v) := by
        simp only [Side.lenBelow, hvM, ↓reduceIte]
      have hd : ℓ + S.lenAbove (s v) - (ℓ + S.lenAbove (s u)) =
          S.lenAbove (s v) - S.lenAbove (s u) := by ring
      refine ⟨u, v, huv, by rw [ha, hb, hd]; exact hpos, fun E => ?_⟩
      show forestUnion (S.forestDist s E) (M.forestDist s ᵥ* kingmanTransition b) ᵥ*
        kingmanTransition ℓ = _
      rw [Net.forestDist_kT_of_lin_empty hM, forestUnion_single_empty, hE E,
        kingmanTransition_add_vecMul, ha, hb, hc, hd, add_comm (S.lenAbove (s u))]

/-! ### The two lineages below the hybrid node -/

/-- A good forest whose lineages are `0` and `1`: they have coalesced or not. -/
theorem pair_forest_cases {F : Finset (Finset (Fin 4))} (hF : IsGood F)
    (hl : ADR11.lineages F = {0, 1}) :
    F = {{0}, {1}} ∨ F = insert ({0} ∪ {1}) {{0}, {1}} := by
  have hsub : F ⊆ {{0}, {1}, {0, 1}} := by
    intro A hA
    have h1 : A ⊆ {0, 1} := hl ▸ ADR11.subset_lineages hA
    have key : ∀ A ∈ ({0, 1} : Finset (Fin 4)).powerset, A.Nonempty →
        A ∈ ({{0}, {1}, {0, 1}} : Finset (Finset (Fin 4))) := by decide
    exact key A (mem_powerset.2 h1) (hF.1.1 A hA)
  have key : ∀ G ∈ ({{0}, {1}, {0, 1}} : Finset (Finset (Fin 4))).powerset,
      (∀ A ∈ G, 2 ≤ #A → ∃ B ∈ G, ∃ C ∈ G, Disjoint B C ∧ B ∪ C = A) →
      ADR11.lineages G = {0, 1} → G = {{0}, {1}} ∨ G = insert ({0} ∪ {1}) {{0}, {1}} := by
    decide
  exact key F (mem_powerset.2 hsub) hF.2 hl

/-- The probability that the lineages `0` and `1` sampled by `s` below the hybrid node of the cycle
`Ω` reach the hybrid node apart: the probability that the forest arriving there along the edge
below the hybrid node is `{{0}, {1}}`. -/
def Net.Cycle.apartProb {N : Net X} (Ω : N.Cycle) (s : Fin 4 → X) : ℝ :=
  (Ω.below.forestDist s ᵥ* kingmanTransition Ω.ℓ) {{0}, {1}}

omit [DecidableEq X] in
/-- The cycle of a metric network with distinct leaf labels is metric, and its sides and the
network below its hybrid node have distinct leaf labels, in all. -/
theorem Net.Cycle.facts {N : Net X} (hN : N.WellFormed) (Ω : N.Cycle) :
    (0 < Ω.γ ∧ Ω.γ < 1 ∧ 0 < Ω.ℓ ∧ Ω.side₁.IsMetric ∧ Ω.side₂.IsMetric ∧ Ω.below.IsMetric) ∧
      (Ω.side₁.leaves ++ Ω.side₂.leaves ++ Ω.below.leaves).Nodup := by
  have hm : Ω.top.IsMetric := Net.isMetric_of_mem_subnets Ω.mem hN.1
  have hn : Ω.top.leaves.Nodup := (Net.leaves_sublist_of_mem_subnets Ω.mem).nodup hN.2
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hm
  exact ⟨⟨h1, h2, h3, h4, h5, h6⟩, hn⟩

/-- The forest arriving at the hybrid node of the cycle `Ω` is a probability distribution on good
forests on the lineages sampled below it. -/
theorem Net.Cycle.below_isForestDist {N : Net X} (hN : N.WellFormed) (Ω : N.Cycle)
    (s : Fin 4 → X) :
    IsForestDist (Ω.below.forestDist s ᵥ* kingmanTransition Ω.ℓ) (Ω.below.lin s) := by
  obtain ⟨⟨-, -, hℓ, -, -, hB⟩, hn⟩ := Ω.facts hN
  exact (Net.isForestDist hB ((List.sublist_append_right _ _).nodup hn) s).kT hℓ.le

theorem Net.Cycle.apartProb_nonneg {N : Net X} (hN : N.WellFormed) (Ω : N.Cycle)
    (s : Fin 4 → X) : 0 ≤ Ω.apartProb s :=
  (Ω.below_isForestDist hN s).nonneg _

theorem Net.Cycle.apartProb_le_one {N : Net X} (hN : N.WellFormed) (Ω : N.Cycle)
    (s : Fin 4 → X) : Ω.apartProb s ≤ 1 := by
  have h := Ω.below_isForestDist hN s
  rw [← h.sum_eq_one]
  exact single_le_sum (f := fun F => (Ω.below.forestDist s ᵥ* kingmanTransition Ω.ℓ) F)
    (fun F _ => h.nonneg F) (mem_univ _)

/-- **The two lineages below the hybrid node.** If exactly the lineages `0` and `1` are sampled
below the hybrid node of the cycle `Ω`, they arrive at the hybrid node apart with probability
`p = Ω.apartProb s`, and coalesced otherwise. -/
theorem Net.Cycle.below_forestDist {N : Net X} (hN : N.WellFormed) (Ω : N.Cycle)
    {s : Fin 4 → X} (hbelow : Ω.below.lin s = {0, 1}) :
    Ω.below.forestDist s ᵥ* kingmanTransition Ω.ℓ =
      Ω.apartProb s • Pi.single ({{0}, {1}} : Finset (Finset (Fin 4))) 1 +
        (1 - Ω.apartProb s) • Pi.single (insert ({0} ∪ {1}) {{0}, {1}}) 1 := by
  have h := Ω.below_isForestDist hN s
  rw [hbelow] at h
  have hsupp : ∀ F, (Ω.below.forestDist s ᵥ* kingmanTransition Ω.ℓ) F ≠ 0 →
      F = {{0}, {1}} ∨ F = insert ({0} ∪ {1}) {{0}, {1}} := fun F hF =>
    pair_forest_cases (h.support F hF).1 (h.support F hF).2
  have hne : ({{0}, {1}} : Finset (Finset (Fin 4))) ≠ insert ({0} ∪ {1}) {{0}, {1}} := by
    decide
  have hsum : Ω.apartProb s +
      (Ω.below.forestDist s ᵥ* kingmanTransition Ω.ℓ) (insert ({0} ∪ {1}) {{0}, {1}}) = 1 := by
    rw [← h.sum_eq_one, Net.Cycle.apartProb, ← sum_pair hne]
    refine sum_subset (subset_univ _) fun F _ hF => ?_
    by_contra h'
    rcases hsupp F h' with rfl | rfl <;> simp at hF
  funext F
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases h1 : F = {{0}, {1}}
  · subst h1
    simp only [ite_eq_right hne, ite_true, mul_one, mul_zero, add_zero]
    rfl
  · by_cases h2 : F = insert ({0} ∪ {1}) {{0}, {1}}
    · subst h2
      simp only [ite_eq_right (Ne.symm hne), ite_true, mul_one, mul_zero, zero_add]
      linarith
    · simp only [ite_eq_right h1, ite_eq_right h2, mul_zero, add_zero]
      by_contra h'
      rcases hsupp F h' with h'' | h''
      · exact h1 h''
      · exact h2 h''

private theorem ag_kT_two {i j : Fin 4} (hij : i ≠ j) (t : ℝ) :
    Pi.single ({{i}, {j}} : Finset (Finset (Fin 4))) 1 ᵥ* kingmanTransition t =
      Real.exp (-t) • Pi.single ({{i}, {j}} : Finset (Finset (Fin 4))) 1 +
        (1 - Real.exp (-t)) • Pi.single (insert ({i} ∪ {j}) {{i}, {j}}) 1 := by
  have hroots : roots ({{i}, {j}} : Finset (Finset (Fin 4))) = {{i}, {j}} := by
    revert i j
    decide
  have hF : ADR11.IsForest ({{i}, {j}} : Finset (Finset (Fin 4))) := by
    have := (isGood_singletons ({i, j} : Finset (Fin 4))).1
    simpa [image_insert] using this
  exact single_vecMul_kingmanTransition_two hF (by simpa using hij) hroots t

/-- **A cherry below the hybrid node.** If the network below the hybrid node of `Ω` is the cherry of
the taxa `s 0` and `s 1`, the lineages reach the hybrid node apart with probability `e^{-ℓ}`, where
`ℓ` is the length of the edge below the hybrid node. -/
theorem Net.Cycle.apartProb_cherry {N : Net X} (Ω : N.Cycle) {s : Fin 4 → X}
    (hs : Function.Injective s) {a b : ℝ}
    (hcherry : Ω.below = .tree a (.leaf (s 0)) b (.leaf (s 1))) :
    Ω.apartProb s = Real.exp (-Ω.ℓ) := by
  have hleaf : ∀ i : Fin 4, (Net.leaf (s i)).lin s = {i} := fun i => by
    ext l
    simp [Net.lin, Net.taxa_leaf, hs.eq_iff]
  unfold Net.Cycle.apartProb
  rw [hcherry]
  show (forestUnion ((Net.leaf (s 0)).forestDist s ᵥ* kingmanTransition a)
    ((Net.leaf (s 1)).forestDist s ᵥ* kingmanTransition b) ᵥ* kingmanTransition Ω.ℓ)
      {{0}, {1}} = _
  rw [Net.forestDist_kT_of_lin_single (hleaf 0), Net.forestDist_kT_of_lin_single (hleaf 1),
    forestUnion_single_single,
    show ({{0}} ∪ {{1}} : Finset (Finset (Fin 4))) = {{0}, {1}} from rfl,
    ag_kT_two (by decide)]
  have hne : ({{0}, {1}} : Finset (Finset (Fin 4))) ≠ {{0, 1}, {0}, {1}} := by decide
  simp [hne]

/-! ### The quartet CFs -/

/-- The expected score at the top node of a cycle whose side `S₁` brings at least one of the
lineages `2`, `3`, the side `S₂` the other or none, and below whose hybrid node the lineages `0`
and `1` arrive apart with probability `p`: the CF of `N₃₂` with `p` in place of `e^{-ℓ}`, for
positive lengths `h₁`, `h₂`, `L` added up along the sides. -/
private theorem ag_core {s : Fin 4 → X} (hs : Function.Injective s) (γ ℓ p : ℝ)
    (S₁ S₂ : Side X) (H : Net X)
    (hH : H.forestDist s ᵥ* kingmanTransition ℓ =
      p • Pi.single ({{0}, {1}} : Finset (Finset (Fin 4))) 1 +
        (1 - p) • Pi.single (insert ({0} ∪ {1}) {{0}, {1}}) 1)
    (hS₁m : S₁.IsMetric) (hS₂m : S₂.IsMetric) (hS₁n : S₁.leaves.Nodup) (hS₂n : S₂.leaves.Nodup)
    (hp : ∀ n ∈ S₁.nodes ++ S₂.nodes, #(n.2.2.lin s) ≤ 1)
    (hsub : S₁.lin s ∪ S₂.lin s ⊆ {2, 3}) (hdisj : Disjoint (S₁.lin s) (S₂.lin s))
    (hne : (S₁.lin s).Nonempty) :
    ∃ h₁ h₂ L : ℝ, 0 < h₁ ∧ 0 < h₂ ∧ 0 < L ∧
      ∑ F, (Net.cycle γ S₁ S₂ ℓ H).forestDist s F * quartetScore F =
        1 - p + p * (γ ^ 2 * (1 - 2 / 3 * Real.exp (-h₁)) +
          (1 - γ) ^ 2 * (1 - 2 / 3 * Real.exp (-h₂)) + 2 * γ * (1 - γ) * (Real.exp (-L) / 3)) := by
  have hA : ∀ A ∈ ({2, 3} : Finset (Fin 4)).powerset,
      A = ∅ ∨ A = {2} ∨ A = {3} ∨ A = {2, 3} := by decide
  have h1sub : S₁.lin s ⊆ {2, 3} := subset_union_left.trans hsub
  have h2sub : S₂.lin s ⊆ {2, 3} := subset_union_right.trans hsub
  have hp₁ : ∀ n ∈ S₁.nodes, #(n.2.2.lin s) ≤ 1 := fun n hn => hp n (List.mem_append_left _ hn)
  have hmem₁ : ∀ {k : Fin 4}, k ∈ S₁.lin s → s k ∈ S₁.taxa := fun hk => ag_mem_lin_side.1 hk
  have hmem₂ : ∀ {k : Fin 4}, k ∈ S₂.lin s → s k ∈ S₂.taxa := fun hk => ag_mem_lin_side.1 hk
  -- the side `S₁` brings one lineage `k`, the side `S₂` none or the other one `m`
  have one : ∀ {k m : Fin 4}, k ≠ 0 → k ≠ 1 → m ≠ 0 → m ≠ 1 → k ≠ m → S₁.lin s = {k} →
      (S₂.lin s = ∅ ∨ S₂.lin s = {m}) → ∃ h₁ h₂ L : ℝ, 0 < h₁ ∧ 0 < h₂ ∧ 0 < L ∧
        ∑ F, (Net.cycle γ S₁ S₂ ℓ H).forestDist s F * quartetScore F =
          1 - p + p * (γ ^ 2 * (1 - 2 / 3 * Real.exp (-h₁)) +
            (1 - γ) ^ 2 * (1 - 2 / 3 * Real.exp (-h₂)) +
              2 * γ * (1 - γ) * (Real.exp (-L) / 3)) := by
    intro k m hk0 hk1 hm0 hm1 hkm h1 h2
    have hk : s k ∈ S₁.taxa := hmem₁ (by rw [h1]; exact mem_singleton_self k)
    have hS₁ := Side.forestDist_of_lin_single hS₁n h1
    rcases h2 with h2 | h2
    · exact ⟨_, _, _, Side.lenBelow_pos _ hS₁m, Side.length_pos hS₂m, Side.lenAbove_pos hS₁m hk,
        expectedScore_top_outside hs hk0 hk1 γ ℓ _ _ _ p S₁ S₂ H hH hS₁
          (Side.forestDist_of_lin_empty h2)⟩
    · have hm : s m ∈ S₂.taxa := hmem₂ (by rw [h2]; exact mem_singleton_self m)
      exact ⟨_, _, _, Side.lenBelow_pos _ hS₁m, Side.lenBelow_pos _ hS₂m,
        add_pos (Side.lenAbove_pos hS₁m hk) (Side.lenAbove_pos hS₂m hm),
        expectedScore_top_sides hs hk0 hk1 hm0 hm1 hkm γ ℓ _ _ _ _ p S₁ S₂ H hH hS₁
          (Side.forestDist_of_lin_single hS₂n h2)⟩
  rcases hA _ (mem_powerset.2 h1sub) with h1 | h1 | h1 | h1
  · rw [h1] at hne
    exact absurd hne (by simp)
  · rcases hA _ (mem_powerset.2 h2sub) with h2 | h2 | h2 | h2
    · exact one (k := 2) (m := 3) (by decide) (by decide) (by decide) (by decide) (by decide) h1
        (Or.inl h2)
    · rw [h1, h2] at hdisj
      exact absurd hdisj (by decide)
    · exact one (k := 2) (m := 3) (by decide) (by decide) (by decide) (by decide) (by decide) h1
        (Or.inr h2)
    · rw [h1, h2] at hdisj
      exact absurd hdisj (by decide)
  · rcases hA _ (mem_powerset.2 h2sub) with h2 | h2 | h2 | h2
    · exact one (k := 3) (m := 2) (by decide) (by decide) (by decide) (by decide) (by decide) h1
        (Or.inl h2)
    · exact one (k := 3) (m := 2) (by decide) (by decide) (by decide) (by decide) (by decide) h1
        (Or.inr h2)
    · rw [h1, h2] at hdisj
      exact absurd hdisj (by decide)
    · rw [h1, h2] at hdisj
      exact absurd hdisj (by decide)
  · -- the side `S₁` brings both lineages, the side `S₂` none
    have h2 : S₂.lin s = ∅ := by
      rcases hA _ (mem_powerset.2 h2sub) with h2 | h2 | h2 | h2
      · exact h2
      all_goals
        rw [h1, h2] at hdisj
        exact absurd hdisj (by decide)
    obtain ⟨u, v, huv, hpos, hE⟩ :=
      Side.forestDist_of_lin_pair (k := 2) (m := 3) (by decide) hS₁m hS₁n h1 hp₁
    have hu : s u ∈ S₁.taxa := hmem₁ (by
      rw [h1]
      rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide)
    have hcases : (u ≠ 0 ∧ u ≠ 1 ∧ v ≠ 0 ∧ v ≠ 1 ∧ u ≠ v) := by
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    obtain ⟨hu0, hu1, hv0, hv1, huv'⟩ := hcases
    exact ⟨_, _, _, Side.lenBelow_pos _ hS₁m,
      add_pos (Side.lenAbove_pos hS₁m hu) (Side.length_pos hS₂m), hpos,
      expectedScore_top_oneSide hs hu0 hu1 hv0 hv1 huv' γ ℓ _ _ _ _ p S₁ S₂ H hH hE
        (Side.forestDist_of_lin_empty h2)⟩

/-- **The quartet CFs of four taxa in the anomalous configuration.** Let `N` be a metric network
with distinct leaf labels, `s` four distinct taxa of `N`, and `Ω` a cycle of `N` with exactly `s 0`
and `s 1` below its hybrid node, at least three of the four taxa below its top node, and at most
one in each network hanging from its sides (`Brooqs.Net.Anomalous`, with the two taxa below the
hybrid node labelled `0` and `1`). Let `γ` be the inheritance probability of `Ω` and `p` the
probability that the lineages of `s 0` and `s 1` reach the hybrid node apart
(`Brooqs.Net.Cycle.apartProb`). There are positive lengths `h₁`, `h₂`, `L`, added up along the
sides of `Ω` as in the module docstring, such that the three quartet CFs are those of `N₃₂`
(`Brooqs.net32_quartetCF`) with `p` in place of `e^{-ℓ}`:
* `CF(s₀s₁|s₂s₃) = 1 - p + p (γ²(1 - 2/3 e^{-h₁}) + (1 - γ)²(1 - 2/3 e^{-h₂}) + 2γ(1 - γ)e^{-L}/3)`;
* `CF(s₀s₂|s₁s₃) = CF(s₀s₃|s₁s₂) = p (γ² e^{-h₁}/3 + (1 - γ)² e^{-h₂}/3 + γ(1 - γ)(1 - e^{-L}/3))`.
-/
theorem Net.Cycle.quartetCF_of_anomalous {N : Net X} (hN : N.WellFormed) (Ω : N.Cycle)
    {s : Fin 4 → X} (hs : Function.Injective s) (hsN : ∀ l, s l ∈ N.taxa)
    (hbelow : Ω.below.lin s = {0, 1}) (h3 : 3 ≤ #(Ω.top.lin s))
    (h1 : ∀ n ∈ Ω.side₁.nodes ++ Ω.side₂.nodes, #(n.2.2.lin s) ≤ 1) :
    ∃ h₁ h₂ L : ℝ, 0 < h₁ ∧ 0 < h₂ ∧ 0 < L ∧
      N.quartetCF (s 0) (s 1) (s 2) (s 3) = 1 - Ω.apartProb s + Ω.apartProb s *
        (Ω.γ ^ 2 * (1 - 2 / 3 * Real.exp (-h₁)) + (1 - Ω.γ) ^ 2 * (1 - 2 / 3 * Real.exp (-h₂)) +
          2 * Ω.γ * (1 - Ω.γ) * (Real.exp (-L) / 3)) ∧
      N.quartetCF (s 0) (s 2) (s 1) (s 3) = Ω.apartProb s *
        (Ω.γ ^ 2 * (Real.exp (-h₁) / 3) + (1 - Ω.γ) ^ 2 * (Real.exp (-h₂) / 3) +
          Ω.γ * (1 - Ω.γ) * (1 - Real.exp (-L) / 3)) ∧
      N.quartetCF (s 0) (s 3) (s 1) (s 2) = Ω.apartProb s *
        (Ω.γ ^ 2 * (Real.exp (-h₁) / 3) + (1 - Ω.γ) ^ 2 * (Real.exp (-h₂) / 3) +
          Ω.γ * (1 - Ω.γ) * (1 - Real.exp (-L) / 3)) := by
  obtain ⟨⟨-, -, -, hS₁m, hS₂m, -⟩, hn⟩ := Ω.facts hN
  have hS₁n : Ω.side₁.leaves.Nodup :=
    ((List.sublist_append_left _ _).trans (List.sublist_append_left _ _)).nodup hn
  have hS₂n : Ω.side₂.leaves.Nodup :=
    ((List.sublist_append_right Ω.side₁.leaves _).trans (List.sublist_append_left _ _)).nodup hn
  -- the lineages sampled from the sides are `2` and `3`, from different sides
  have hd12 : ∀ x, x ∈ Ω.side₁.taxa → x ∉ Ω.side₂.taxa := by
    intro x h1x h2x
    have hd := List.disjoint_of_nodup_append
      (List.sublist_append_left (Ω.side₁.leaves ++ Ω.side₂.leaves) Ω.below.leaves |>.nodup hn)
    simp only [Side.taxa, List.mem_toFinset] at h1x h2x
    exact hd h1x h2x
  have hdB : ∀ x, x ∈ Ω.side₁.taxa ∪ Ω.side₂.taxa → x ∉ Ω.below.taxa := by
    intro x hx hB
    have hd := List.disjoint_of_nodup_append hn
    simp only [Side.taxa, Net.taxa, mem_union, List.mem_toFinset] at hx hB
    exact hd (List.mem_append.2 hx) hB
  have hinB : ∀ l, s l ∈ Ω.below.taxa ↔ l = 0 ∨ l = 1 := fun l => by
    rw [← ag_mem_lin, hbelow, mem_insert, mem_singleton]
  have hsub : Ω.side₁.lin s ∪ Ω.side₂.lin s ⊆ {2, 3} := by
    intro l hl
    have hl' : s l ∈ Ω.side₁.taxa ∪ Ω.side₂.taxa := by
      rcases mem_union.1 hl with h | h
      · exact mem_union_left _ (ag_mem_lin_side.1 h)
      · exact mem_union_right _ (ag_mem_lin_side.1 h)
    have h01 : ¬(l = 0 ∨ l = 1) := fun h => hdB _ hl' ((hinB l).2 h)
    have key : ∀ l : Fin 4, ¬(l = 0 ∨ l = 1) → l ∈ ({2, 3} : Finset (Fin 4)) := by decide
    exact key l h01
  have hdisj : Disjoint (Ω.side₁.lin s) (Ω.side₂.lin s) := by
    rw [disjoint_left]
    intro l h1l h2l
    exact hd12 _ (ag_mem_lin_side.1 h1l) (ag_mem_lin_side.1 h2l)
  have htop : Ω.top.lin s = Ω.side₁.lin s ∪ Ω.side₂.lin s ∪ Ω.below.lin s := by
    ext l
    simp [Net.lin, Side.lin, Net.Cycle.top, Net.taxa_cycle]
  have hne : (Ω.side₁.lin s).Nonempty ∨ (Ω.side₂.lin s).Nonempty := by
    by_contra h
    simp only [not_or, not_nonempty_iff_eq_empty] at h
    rw [htop, h.1, h.2, hbelow] at h3
    simp at h3
  have hp₂ : ∀ n ∈ Ω.side₂.nodes ++ Ω.side₁.nodes, #(n.2.2.lin s) ≤ 1 := fun n hn' =>
    h1 n (List.mem_append.2 ((List.mem_append.1 hn').symm))
  have hH := Ω.below_forestDist hN hbelow
  -- the expected score at the top node
  have hES : ∃ h₁ h₂ L : ℝ, 0 < h₁ ∧ 0 < h₂ ∧ 0 < L ∧
      ∑ F, Ω.top.forestDist s F * quartetScore F = 1 - Ω.apartProb s + Ω.apartProb s *
        (Ω.γ ^ 2 * (1 - 2 / 3 * Real.exp (-h₁)) + (1 - Ω.γ) ^ 2 * (1 - 2 / 3 * Real.exp (-h₂)) +
          2 * Ω.γ * (1 - Ω.γ) * (Real.exp (-L) / 3)) := by
    rcases hne with hne | hne
    · exact ag_core hs Ω.γ Ω.ℓ (Ω.apartProb s) Ω.side₁ Ω.side₂ Ω.below hH hS₁m hS₂m hS₁n hS₂n h1
        hsub hdisj hne
    · -- exchange the two sides
      obtain ⟨h₁, h₂, L, p1, p2, p3, hE⟩ := ag_core hs (1 - Ω.γ) Ω.ℓ (Ω.apartProb s) Ω.side₂
        Ω.side₁ Ω.below hH hS₂m hS₁m hS₂n hS₁n hp₂ (by rwa [union_comm]) hdisj.symm hne
      refine ⟨h₂, h₁, L, p2, p1, p3, ?_⟩
      have hsw : Ω.top.forestDist s =
          (Net.cycle (1 - Ω.γ) Ω.side₂ Ω.side₁ Ω.ℓ Ω.below).forestDist s :=
        (Net.SideSwap.swap_top Ω.γ Ω.side₁ Ω.side₂ Ω.ℓ Ω.below).forestDist_eq s
      rw [hsw, hE]
      ring
  obtain ⟨h₁, h₂, L, p1, p2, p3, hE⟩ := hES
  have h3' : 3 ≤ #(univ.filter fun l => s l ∈ Ω.top.taxa) := h3
  have hCF : N.quartetCF (s 0) (s 1) (s 2) (s 3) = 1 - Ω.apartProb s + Ω.apartProb s *
      (Ω.γ ^ 2 * (1 - 2 / 3 * Real.exp (-h₁)) + (1 - Ω.γ) ^ 2 * (1 - 2 / 3 * Real.exp (-h₂)) +
        2 * Ω.γ * (1 - Ω.γ) * (Real.exp (-L) / 3)) := by
    rw [quartetCF_eq_sum_top N hN.2 Ω s hsN h3', hE]
  -- the two other quartets have equal CFs, and the three add up to `1`
  have hB : Ω.below ∈ N.subnets := Net.mem_subnets_trans Ω.mem (by
    simp [Net.subnets, Net.self_mem_subnets])
  have hsw := Net.splitCF_swap hN.2 hB hsN (i := 0) (j := 1) hinB {0, 2}
  have hmap : ({0, 2} : Finset (Fin 4)).map (Equiv.swap (0 : Fin 4) 1).toEmbedding =
      ({0, 3} : Finset (Fin 4))ᶜ := by decide
  rw [hmap, Net.splitCF_compl] at hsw
  have hsum := Net.splitCF_sum hN.2 hsN
  have e0 : N.quartetCF (s 0) (s 1) (s 2) (s 3) = N.splitCF s {0, 1} :=
    N.quartetCF_eq_splitCF_of s (i := 0) (j := 1) (k := 2) (l := 3) (by decide)
  have e1 : N.quartetCF (s 0) (s 2) (s 1) (s 3) = N.splitCF s {0, 2} :=
    N.quartetCF_eq_splitCF_of s (i := 0) (j := 2) (k := 1) (l := 3) (by decide)
  have e2 : N.quartetCF (s 0) (s 3) (s 1) (s 2) = N.splitCF s {0, 3} :=
    N.quartetCF_eq_splitCF_of s (i := 0) (j := 3) (k := 1) (l := 2) (by decide)
  refine ⟨h₁, h₂, L, p1, p2, p3, hCF, ?_, ?_⟩
  · rw [e1]
    rw [e0] at hCF
    linarith
  · rw [e2]
    rw [e0] at hCF
    linarith

/-- **The anomaly criterion in an arbitrary network.** Under the assumptions of
`Brooqs.Net.Cycle.quartetCF_of_anomalous`, there are positive lengths `h₁`, `h₂`, `L` added up
along the sides of the cycle such that, with `p = Ω.apartProb s`, `γ = Ω.γ` and
`D = γ(1 - γ)(1 - e^{-L}) - γ²(1 - e^{-h₁}) - (1 - γ)²(1 - e^{-h₂})`:
* the quartet `s₀s₁|s₂s₃`, the only one of the three that `N` displays, has a strictly smaller CF
  than the two others iff `1 - p < p D`;
* it has a strictly larger CF iff `p D < 1 - p`;
* the three CFs are equal (to `1/3`) iff `p D = 1 - p`.
This is `Brooqs.net32_anomalous_iff_u` with `p` in place of `e^{-ℓ}`. -/
theorem Net.Cycle.anomalous_iff_of_anomalous {N : Net X} (hN : N.WellFormed) (Ω : N.Cycle)
    {s : Fin 4 → X} (hs : Function.Injective s) (hsN : ∀ l, s l ∈ N.taxa)
    (hbelow : Ω.below.lin s = {0, 1}) (h3 : 3 ≤ #(Ω.top.lin s))
    (h1 : ∀ n ∈ Ω.side₁.nodes ++ Ω.side₂.nodes, #(n.2.2.lin s) ≤ 1) :
    ∃ h₁ h₂ L : ℝ, 0 < h₁ ∧ 0 < h₂ ∧ 0 < L ∧
      (N.quartetCF (s 0) (s 1) (s 2) (s 3) < N.quartetCF (s 0) (s 2) (s 1) (s 3) ↔
        1 - Ω.apartProb s < Ω.apartProb s * (Ω.γ * (1 - Ω.γ) * (1 - Real.exp (-L)) -
          Ω.γ ^ 2 * (1 - Real.exp (-h₁)) - (1 - Ω.γ) ^ 2 * (1 - Real.exp (-h₂)))) ∧
      (N.quartetCF (s 0) (s 2) (s 1) (s 3) < N.quartetCF (s 0) (s 1) (s 2) (s 3) ↔
        Ω.apartProb s * (Ω.γ * (1 - Ω.γ) * (1 - Real.exp (-L)) -
          Ω.γ ^ 2 * (1 - Real.exp (-h₁)) - (1 - Ω.γ) ^ 2 * (1 - Real.exp (-h₂))) <
            1 - Ω.apartProb s) ∧
      (N.quartetCF (s 0) (s 1) (s 2) (s 3) = N.quartetCF (s 0) (s 2) (s 1) (s 3) ↔
        Ω.apartProb s * (Ω.γ * (1 - Ω.γ) * (1 - Real.exp (-L)) -
          Ω.γ ^ 2 * (1 - Real.exp (-h₁)) - (1 - Ω.γ) ^ 2 * (1 - Real.exp (-h₂))) =
            1 - Ω.apartProb s) := by
  obtain ⟨h₁, h₂, L, p1, p2, p3, e0, e1, -⟩ := Ω.quartetCF_of_anomalous hN hs hsN hbelow h3 h1
  refine ⟨h₁, h₂, L, p1, p2, p3, ?_, ?_, ?_⟩ <;> rw [e0, e1] <;> constructor <;> intro h <;>
    linarith

/-! ### Any labels -/

private theorem ag_lin_comp {M : Net X} {s : Fin 4 → X} {i j k m : Fin 4}
    (hinj : Function.Injective ![i, j, k, m]) :
    M.lin s = (M.lin ![s i, s j, s k, s m]).map ⟨![i, j, k, m], hinj⟩ := by
  have hsurj : Function.Surjective ![i, j, k, m] := Finite.surjective_of_injective hinj
  ext x
  simp only [mem_map, Function.Embedding.coeFn_mk, ag_mem_lin]
  constructor
  · intro hx
    obtain ⟨l, rfl⟩ := hsurj x
    refine ⟨l, ?_, rfl⟩
    fin_cases l <;> exact hx
  · rintro ⟨l, hl, rfl⟩
    fin_cases l <;> exact hl

/-- **The quartet CFs in the anomalous configuration, with any labels.** Let `N` be a metric
network with distinct leaf labels, `s` four distinct taxa of `N`, and `Ω` a cycle of `N` with
exactly `s i` and `s j` below its hybrid node, at least three of the four taxa below its top node,
and at most one in each network hanging from its sides (`Brooqs.Net.Anomalous`); `k` and `m` are
the two other labels. With `p` the probability that the lineages of `s i` and `s j` reach the hybrid
node apart (`Brooqs.Net.Cycle.apartProb` for the taxa listed as `s i, s j, s k, s m`) and `γ` the
inheritance probability of `Ω`, there are positive lengths `h₁`, `h₂`, `L` such that the CF of the
split `{i, j}`, the only one that `N` displays, is
`1 - p + p (γ²(1 - 2/3 e^{-h₁}) + (1 - γ)²(1 - 2/3 e^{-h₂}) + 2γ(1 - γ) e^{-L}/3)`, and the CFs of
the splits `{i, k}` and `{i, m}` are both
`p (γ² e^{-h₁}/3 + (1 - γ)² e^{-h₂}/3 + γ(1 - γ)(1 - e^{-L}/3))`. -/
theorem Net.Cycle.splitCF_of_anomalous {N : Net X} (hN : N.WellFormed) (Ω : N.Cycle)
    {s : Fin 4 → X} (hs : Function.Injective s) (hsN : ∀ l, s l ∈ N.taxa) {i j k m : Fin 4}
    (hinj : Function.Injective ![i, j, k, m]) (hbelow : Ω.below.lin s = {i, j})
    (h3 : 3 ≤ #(Ω.top.lin s)) (h1 : ∀ n ∈ Ω.side₁.nodes ++ Ω.side₂.nodes, #(n.2.2.lin s) ≤ 1) :
    ∃ h₁ h₂ L : ℝ, 0 < h₁ ∧ 0 < h₂ ∧ 0 < L ∧
      N.splitCF s {i, j} = 1 - Ω.apartProb ![s i, s j, s k, s m] +
        Ω.apartProb ![s i, s j, s k, s m] *
          (Ω.γ ^ 2 * (1 - 2 / 3 * Real.exp (-h₁)) + (1 - Ω.γ) ^ 2 * (1 - 2 / 3 * Real.exp (-h₂)) +
            2 * Ω.γ * (1 - Ω.γ) * (Real.exp (-L) / 3)) ∧
      N.splitCF s {i, k} = Ω.apartProb ![s i, s j, s k, s m] *
        (Ω.γ ^ 2 * (Real.exp (-h₁) / 3) + (1 - Ω.γ) ^ 2 * (Real.exp (-h₂) / 3) +
          Ω.γ * (1 - Ω.γ) * (1 - Real.exp (-L) / 3)) ∧
      N.splitCF s {i, m} = Ω.apartProb ![s i, s j, s k, s m] *
        (Ω.γ ^ 2 * (Real.exp (-h₁) / 3) + (1 - Ω.γ) ^ 2 * (Real.exp (-h₂) / 3) +
          Ω.γ * (1 - Ω.γ) * (1 - Real.exp (-L) / 3)) := by
  have hij : i ≠ j := fun h => absurd (hinj (a₁ := 0) (a₂ := 1) h) (by decide)
  have hik : i ≠ k := fun h => absurd (hinj (a₁ := 0) (a₂ := 2) h) (by decide)
  have him : i ≠ m := fun h => absurd (hinj (a₁ := 0) (a₂ := 3) h) (by decide)
  have hjk : j ≠ k := fun h => absurd (hinj (a₁ := 1) (a₂ := 2) h) (by decide)
  have hjm : j ≠ m := fun h => absurd (hinj (a₁ := 1) (a₂ := 3) h) (by decide)
  have hkm : k ≠ m := fun h => absurd (hinj (a₁ := 2) (a₂ := 3) h) (by decide)
  have hs'inj : Function.Injective ![s i, s j, s k, s m] := by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      first
      | rfl
      | exact absurd (hs h) (by assumption)
      | exact absurd (hs h).symm (by assumption)
  have hsN' : ∀ l, ![s i, s j, s k, s m] l ∈ N.taxa := fun l => by
    fin_cases l <;> exact hsN _
  have hcard : ∀ M : Net X, #(M.lin ![s i, s j, s k, s m]) = #(M.lin s) := fun M => by
    rw [ag_lin_comp (M := M) (s := s) hinj, card_map]
  have hbelow' : Ω.below.lin ![s i, s j, s k, s m] = {0, 1} := by
    have h := ag_lin_comp (M := Ω.below) (s := s) hinj
    rw [hbelow] at h
    ext l
    have hl : l ∈ Ω.below.lin ![s i, s j, s k, s m] ↔
        ![i, j, k, m] l ∈ ({i, j} : Finset (Fin 4)) := by
      rw [h, mem_map]
      constructor
      · intro hl
        exact ⟨l, hl, rfl⟩
      · rintro ⟨l', hl', hll'⟩
        rwa [← hinj hll']
    rw [hl, mem_insert, mem_singleton, mem_insert, mem_singleton]
    fin_cases l <;> simp [hij, hik.symm, him.symm, hjk.symm, hjm.symm, Ne.symm hij]
  have h3' : 3 ≤ #(Ω.top.lin ![s i, s j, s k, s m]) := by rw [hcard]; exact h3
  have h1' : ∀ n ∈ Ω.side₁.nodes ++ Ω.side₂.nodes, #(n.2.2.lin ![s i, s j, s k, s m]) ≤ 1 :=
    fun n hn => by rw [hcard]; exact h1 n hn
  obtain ⟨h₁, h₂, L, p1, p2, p3, e0, e1, e2⟩ :=
    Ω.quartetCF_of_anomalous hN hs'inj hsN' hbelow' h3' h1'
  refine ⟨h₁, h₂, L, p1, p2, p3, ?_, ?_, ?_⟩
  · rw [← N.quartetCF_eq_splitCF_of s hinj]
    exact e0
  · have hinj' : Function.Injective ![i, k, j, m] := by
      intro a b h
      fin_cases a <;> fin_cases b <;> simp_all
    rw [← N.quartetCF_eq_splitCF_of s hinj']
    exact e1
  · have hinj' : Function.Injective ![i, m, j, k] := by
      intro a b h
      fin_cases a <;> fin_cases b <;> simp_all
    rw [← N.quartetCF_eq_splitCF_of s hinj']
    exact e2

end Brooqs
