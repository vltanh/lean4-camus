module

public import Camus.Defs

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.Finset.Max

/-!
# Scores of quartet multisets

The score of a network is the number of quartets of the multiset `Q`, counted with
multiplicity, that it displays (Section 2.2); `score Q D` counts the elements of `Q` in a finite
set `D` of quartets. This file proves Equation (1) in its weighted form, the additivity of the
score over disjoint sets (used with Lemma 1), the relation between the number of quartets
displayed and the number satisfied, and the statements on optimal networks used in
Sections 2.4 and 3.2. The statements are generic in the type `α` of quartets.

## Main results

* `delta`: δ_T(q, (u, w)) of Definition 4.
* `equation1`: Equation (1), summing δ over the distinct quartets of `Q`.
* `score_offset`: the score of a network built on `T` is the score of `T` plus the number of
  quartets of `Q` that the network satisfies.
* `score_disjoint_union`: the score of a disjoint union is the sum of the scores.
* `Optimal`, `FewestReticulations`: an optimal member of a finite family, and one with fewest
  reticulations among the optimal members (Section 3.2).
* `atMostScore_mono`: the best score with at most `k` reticulations is nondecreasing in `k`
  (Section 2.4).
-/

@[expose] public section

namespace Camus

variable {α : Type*} [DecidableEq α]

/-- **Definition 4** (`mthst7`). δ_T(q, (u, w)): the number of times `q` appears in `Q` if `q` is
satisfied by the edge added above `(u, w)`, and 0 otherwise. Here `D` is the set of quartets
satisfied by that edge; in the dynamic program,
`D = DynamicProgramming.novel t Q (Realization.graph t {(u, w)})`. -/
def delta (Q : Multiset α) (D : Finset α) (q : α) : ℕ :=
  if q ∈ D then Q.count q else 0

/-- **Equation (1)** (`E1`), with `Q` counted as a weighted set of distinct quartets, as
Section 2.3 allows: s_e(u, w) = ∑ δ_T(q, (u, w)), summed over the distinct quartets `q` of `Q`,
is the number of quartets of `Q`, counted with multiplicity, in the set `D` of quartets satisfied
by the edge added above `(u, w)`. Summing δ over all `m` copies of a quartet of multiplicity `m`
would count it m² times (the report's E1). -/
theorem equation1 (Q : Multiset α) (D : Finset α) :
    score Q D = ∑ q ∈ Q.toFinset, delta Q D q := by
  have hm : score Q D = (Q.map (fun q => if q ∈ D then (1 : ℕ) else 0)).sum := by
    induction Q using Multiset.induction_on with
    | empty => simp [score]
    | @cons a Q ih =>
      by_cases ha : a ∈ D
      · simp [score, ha] at ih ⊢
        omega
      · simp [score, ha] at ih ⊢
        omega
  rw [hm, Finset.sum_multiset_map_count]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q ∈ D <;> simp [delta, hq]

/-- The score is at most the number of elements of `Q`, counted with multiplicity. -/
theorem score_le_card (Q : Multiset α) (D : Finset α) :
    score Q D ≤ Q.card := by
  exact Multiset.card_le_card (Multiset.filter_le _ Q)

/-- The score reaches the number of elements of `Q` if and only if every quartet of `Q` is
in `D`. -/
theorem score_eq_card_iff (Q : Multiset α) (D : Finset α) :
    score Q D = Q.card ↔ Q.toFinset ⊆ D := by
  constructor
  · intro h
    have hf := Multiset.eq_of_le_of_card_le (Multiset.filter_le (· ∈ D) Q) h.ge
    exact fun q hq => (Multiset.filter_eq_self.mp hf) q (Multiset.mem_toFinset.mp hq)
  · intro h
    unfold score
    rw [Multiset.filter_eq_self.mpr (fun q hq => h (Multiset.mem_toFinset.mpr hq))]

/-- If `T ⊆ D`, then `score Q D = score Q T + score Q (D \ T)`. Take for `D` the quartets of `Q`
displayed by a network built on a tree, and for `T` those displayed by the tree itself: the score
of the network is the score of the tree plus the number of quartets of `Q` that the network
satisfies. As the score of the tree is fixed, maximizing the score (Section 2.2) and maximizing
the number of satisfied quartets (Theorem 1) select the same networks. -/
theorem score_offset (Q : Multiset α) (T D : Finset α) (h : T ⊆ D) :
    score Q D = score Q T + score Q (D \ T) := by
  induction Q using Multiset.induction_on with
  | empty => simp [score]
  | @cons a Q ih =>
    by_cases ha : a ∈ T
    · have hd := h ha
      simp [score, ha, hd] at ih ⊢
      omega
    · by_cases hd : a ∈ D <;> simp [score, ha, hd] at ih ⊢ <;> omega

/-- The score in weighted-set form: the sum, over the quartets of `D`, of their multiplicities
in `Q`. -/
theorem score_eq_sum (Q : Multiset α) (D : Finset α) :
    score Q D = ∑ q ∈ D, Q.count q := by
  have h : ∀ q ∈ Q.filter (· ∈ D), q ∈ D := by
    intro q hq
    exact (Multiset.mem_filter.mp hq).2
  have hs := Multiset.sum_count_eq_card (s := D) (m := Q.filter (· ∈ D)) h
  unfold score
  rw [← hs]
  apply Finset.sum_congr rfl
  intro q hq
  simp [hq]

/-- The score of a union of pairwise disjoint sets `D e` is the sum of their scores. With
Lemma 1, which makes the quartets satisfied by a network the disjoint union of those satisfied by
its added edges, this gives the number of quartets of `Q` satisfied by the network as the sum of
the s_e(u, w) of its added edges. -/
theorem score_disjoint_union {E : Type*} [DecidableEq E]
    (Q : Multiset α) (edges : Finset E) (D : E → Finset α)
    (h : (edges : Set E).Pairwise (fun e f => Disjoint (D e) (D f))) :
    score Q (edges.biUnion D) = ∑ e ∈ edges, score Q (D e) := by
  simp only [score_eq_sum]
  exact Finset.sum_biUnion h

/-- `n` is optimal in the finite family `C`: `n ∈ C`, and no member `m` of `C` has a larger
score `score Q (displayed m)`, where `displayed m` is the set of quartets displayed by `m`. -/
def Optimal {N : Type*} (C : Finset N) (displayed : N → Finset α)
    (Q : Multiset α) (n : N) : Prop :=
  n ∈ C ∧ ∀ m ∈ C, score Q (displayed m) ≤ score Q (displayed n)

/-- `n` has at most as many reticulations as every optimal member of `C`. Together with
`Optimal C displayed Q n`, this says that `n` is an optimal member of `C` with the fewest
reticulations, the tie-break used for Section 3.2's recovery. -/
def FewestReticulations {N : Type*} (C : Finset N) (displayed : N → Finset α)
    (reticulations : N → ℕ) (Q : Multiset α) (n : N) : Prop :=
  ∀ m ∈ C, Optimal C displayed Q m → reticulations n ≤ reticulations m

/-- A nonempty finite family has an optimal member with the fewest reticulations among the
optimal members. -/
theorem exists_optimal_fewest {N : Type*} [DecidableEq N]
    (C : Finset N) (hC : C.Nonempty) (displayed : N → Finset α)
    (reticulations : N → ℕ) (Q : Multiset α) :
    ∃ n, Optimal C displayed Q n ∧
      FewestReticulations C displayed reticulations Q n := by
  classical
  obtain ⟨m, hm, hmax⟩ := C.exists_max_image (fun n => score Q (displayed n)) hC
  let winners := C.filter (fun n => score Q (displayed n) = score Q (displayed m))
  have hw : winners.Nonempty := ⟨m, by simp [winners, hm]⟩
  obtain ⟨n, hn, hmin⟩ := winners.exists_min_image reticulations hw
  have hnc : n ∈ C := (Finset.mem_filter.mp hn).1
  have hnscore : score Q (displayed n) = score Q (displayed m) :=
    (Finset.mem_filter.mp hn).2
  refine ⟨n, ⟨hnc, ?_⟩, ?_⟩
  · intro x hx
    rw [hnscore]
    exact hmax x hx
  · intro x hx hopt
    apply hmin x
    simp only [winners, Finset.mem_filter]
    exact ⟨hx, le_antisymm (hmax x hx) (hopt.2 m hm)⟩

/-- The best score among the members of `C` with at most `k` reticulations, and 0 if there is
none. -/
def atMostScore {N : Type*} [DecidableEq N] (C : Finset N)
    (displayed : N → Finset α) (reticulations : N → ℕ)
    (Q : Multiset α) (k : ℕ) : ℕ :=
  (C.filter (fun n => reticulations n ≤ k)).sup (fun n => score Q (displayed n))

/-- Section 2.4: the best score with at most `k` reticulations never decreases as `k`
increases, since the family of candidate networks grows with `k`. Section 2.4 states that the
score never decreases as the number of reticulations increases; for exactly `k` reticulations,
the networks it computes, this is false (the report's E3). -/
theorem atMostScore_mono {N : Type*} [DecidableEq N] (C : Finset N)
    (displayed : N → Finset α) (reticulations : N → ℕ) (Q : Multiset α)
    {j k : ℕ} (hjk : j ≤ k) :
    atMostScore C displayed reticulations Q j ≤
      atMostScore C displayed reticulations Q k := by
  apply Finset.sup_mono
  intro n hn
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,
    (Finset.mem_filter.mp hn).2.trans hjk⟩

end Camus
