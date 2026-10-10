module

public import Camus.Defs

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace Camus

variable {α : Type*} [DecidableEq α]

/-- Definition 4 (`mthst7`): an edge receives the multiplicity of each quartet it
satisfies and zero otherwise. -/
def delta (Q : Multiset α) (D : Finset α) (q : α) : ℕ :=
  if q ∈ D then Q.count q else 0

/-- Equation (1) (`E1`), using the distinct-topology convention of §2.3.
This is the representation bridge between a multiset and its weighted support. -/
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

theorem score_le_card (Q : Multiset α) (D : Finset α) :
    score Q D ≤ Q.card := by
  exact Multiset.card_le_card (Multiset.filter_le _ Q)

theorem score_eq_card_iff (Q : Multiset α) (D : Finset α) :
    score Q D = Q.card ↔ Q.toFinset ⊆ D := by
  constructor
  · intro h
    have hf := Multiset.eq_of_le_of_card_le (Multiset.filter_le (· ∈ D) Q) h.ge
    exact fun q hq => (Multiset.filter_eq_self.mp hf) q (Multiset.mem_toFinset.mp hq)
  · intro h
    unfold score
    rw [Multiset.filter_eq_self.mpr (fun q hq => h (Multiset.mem_toFinset.mpr hq))]

/-- Novel satisfaction and total support differ by the constraint tree's fixed
score. This justifies the paper's switch between the two objectives. -/
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

/-- The weighted-set form of support on an arbitrary finite repertoire. -/
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

/-- Lemma 1's numerical consequence: disjoint novel-quartet repertoires have
additive scores; each occurrence is counted exactly once. -/
theorem score_disjoint_union {E : Type*} [DecidableEq E]
    (Q : Multiset α) (edges : Finset E) (D : E → Finset α)
    (h : (edges : Set E).Pairwise (fun e f => Disjoint (D e) (D f))) :
    score Q (edges.biUnion D) = ∑ e ∈ edges, score Q (D e) := by
  simp only [score_eq_sum]
  exact Finset.sum_biUnion h

/-- An optimal repertoire in a finite feasible family; this is a property of the
selected object, rather than an assumption hidden in network data. -/
def Optimal {N : Type*} (C : Finset N) (displayed : N → Finset α)
    (Q : Multiset α) (n : N) : Prop :=
  n ∈ C ∧ ∀ m ∈ C, score Q (displayed m) ≤ score Q (displayed n)

/-- Tie-breaking chooses the smallest reticulation count among all optimizers. -/
def FewestReticulations {N : Type*} (C : Finset N) (displayed : N → Finset α)
    (reticulations : N → ℕ) (Q : Multiset α) (n : N) : Prop :=
  ∀ m ∈ C, Optimal C displayed Q m → reticulations n ≤ reticulations m

/-- Finite optimization with this tie-break always has a witness. -/
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

/-- Corrected §2.4: maximum support with AT MOST k reticulations. Using sup
with the empty-family value 0 is harmless for this nonnegative objective. -/
def atMostScore {N : Type*} [DecidableEq N] (C : Finset N)
    (displayed : N → Finset α) (reticulations : N → ℕ)
    (Q : Multiset α) (k : ℕ) : ℕ :=
  (C.filter (fun n => reticulations n ≤ k)).sup (fun n => score Q (displayed n))

/-- Corrected §2.4 monotonicity, explicitly authorized by the user. This is a
replacement for the false exact-budget monotonicity claim, not a weakening of a
numbered paper theorem. -/
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
