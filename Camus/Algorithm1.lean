module

public import Camus.Phylogeny
public import Camus.Filtering
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Camus

/-- Four increasing labels index one iteration of Algorithm 1. -/
structure QuartetKey where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  ab : a < b
  bc : b < c
  cd : c < d
  deriving DecidableEq

def Quartet.key (q : Quartet) : QuartetKey :=
  ⟨q.a, q.b, q.c, q.d, q.ab, q.bc, q.cd⟩

def QuartetKey.quartet (k : QuartetKey) (s : Fin 3) : Quartet :=
  ⟨k.a, k.b, k.c, k.d, k.ab, k.bc, k.cd, s⟩

/-- Sorting labels gives a bijection with a four-taxon key and one of exactly
three topologies; no repeated permutation of the same quartet is counted. -/
def quartetEquiv : Quartet ≃ QuartetKey × Fin 3 where
  toFun q := (q.key, q.split)
  invFun p := p.1.quartet p.2
  left_inv q := by cases q; rfl
  right_inv p := by rcases p with ⟨⟨a,b,c,d,ab,bc,cd⟩,s⟩; rfl

namespace Algorithm1

open scoped Classical

/-- Stable ordering of the three topology counts. Ties use the displayed index
order; the paper permits any ordering satisfying f₁≥f₂≥f₃. -/
def rank (f : Fin 3 → ℕ) : Fin 3 × Fin 3 × Fin 3 :=
  if f 1 ≤ f 0 then
    if f 2 ≤ f 1 then (0, 1, 2)
    else if f 2 ≤ f 0 then (0, 2, 1) else (2, 0, 1)
  else
    if f 2 ≤ f 0 then (1, 0, 2)
    else if f 2 ≤ f 1 then (1, 2, 0) else (2, 1, 0)

theorem rank_ordered (f : Fin 3 → ℕ) :
    f (rank f).2.1 ≤ f (rank f).1 ∧
    f (rank f).2.2 ≤ f (rank f).2.1 := by
  unfold rank
  split_ifs <;> dsimp only <;> omega

theorem rank_distinct (f : Fin 3 → ℕ) :
    (rank f).1 ≠ (rank f).2.1 ∧ (rank f).1 ≠ (rank f).2.2 ∧
      (rank f).2.1 ≠ (rank f).2.2 := by
  unfold rank
  split_ifs <;> decide

theorem rank_covers (f : Fin 3 → ℕ) (s : Fin 3) :
    s = (rank f).1 ∨ s = (rank f).2.1 ∨ s = (rank f).2.2 := by
  unfold rank
  split_ifs <;> fin_cases s <;> decide

variable {K : Type*} [DecidableEq K]

def frequencies (Q : Multiset (K × Fin 3)) (k : K) : Fin 3 → ℕ :=
  fun s => Q.count (k, s)

/-- One iteration of Algorithm 1, including the original multiplicities.
The least frequent topology is omitted and the most frequent always retained.
Only the runner-up uses the strict threshold test. -/
noncomputable def filterBlock (t : ℝ) (Q : Multiset (K × Fin 3)) (k : K) :
    Multiset (K × Fin 3) :=
  let f := frequencies Q k
  let r := rank f
  Multiset.replicate (f r.1) (k, r.1) +
    if retainSecond t (f r.2.1) (f r.2.2) then
      Multiset.replicate (f r.2.1) (k, r.2.1) else 0

theorem filterBlock_top_count (t : ℝ) (Q : Multiset (K × Fin 3)) (k : K) :
    (filterBlock t Q k).count (k, (rank (frequencies Q k)).1) =
      Q.count (k, (rank (frequencies Q k)).1) := by
  have h := (rank_distinct (frequencies Q k)).1
  simp only [filterBlock, Multiset.count_add]
  split_ifs <;> simp [Multiset.count_replicate, Ne.symm h, frequencies]

theorem filterBlock_second_count (t : ℝ) (Q : Multiset (K × Fin 3)) (k : K) :
    (filterBlock t Q k).count (k, (rank (frequencies Q k)).2.1) =
      if retainSecond t ((frequencies Q k) (rank (frequencies Q k)).2.1)
          ((frequencies Q k) (rank (frequencies Q k)).2.2) then
        Q.count (k, (rank (frequencies Q k)).2.1) else 0 := by
  have h := (rank_distinct (frequencies Q k)).1
  simp only [filterBlock, Multiset.count_add]
  split_ifs <;> simp [Multiset.count_replicate, h, frequencies]

theorem filterBlock_third_count (t : ℝ) (Q : Multiset (K × Fin 3)) (k : K) :
    (filterBlock t Q k).count (k, (rank (frequencies Q k)).2.2) = 0 := by
  have h := rank_distinct (frequencies Q k)
  simp only [filterBlock, Multiset.count_add]
  split_ifs <;> simp [Multiset.count_replicate, h.2.1, h.2.2]

theorem filterBlock_mono (Q : Multiset (K × Fin 3)) (k : K)
    {s t : ℝ} (hst : s ≤ t) : filterBlock t Q k ≤ filterBlock s Q k := by
  have hfreq : 0 ≤ ((frequencies Q k) (rank (frequencies Q k)).2.1 : ℝ) +
      ((frequencies Q k) (rank (frequencies Q k)).2.2 : ℝ) :=
    add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  dsimp only [filterBlock]
  split_ifs with ht hs hs
  · rfl
  · exact False.elim (hs (retainSecond_mono hfreq hst ht))
  · simpa only [add_zero] using Multiset.le_add_right
      (Multiset.replicate ((frequencies Q k) (rank (frequencies Q k)).1)
        (k, (rank (frequencies Q k)).1))
      (Multiset.replicate ((frequencies Q k) (rank (frequencies Q k)).2.1)
        (k, (rank (frequencies Q k)).2.1))
  · rfl

/-- Algorithm 1 over all four-taxon keys present in the observations.
Keys absent from the input would contribute the empty multiset. -/
noncomputable def filterEncoded (t : ℝ) (Q : Multiset (K × Fin 3)) :
    Multiset (K × Fin 3) :=
  ∑ k ∈ Q.toFinset.image Prod.fst, filterBlock t Q k

theorem filterEncoded_mono (Q : Multiset (K × Fin 3)) {s t : ℝ} (hst : s ≤ t) :
    filterEncoded t Q ≤ filterEncoded s Q := by
  exact Finset.sum_le_sum (fun k _ => filterBlock_mono Q k hst)

/-- Algorithm 1 applied to resolved quartets in the project's representation. -/
noncomputable def filterQuartets (t : ℝ) (Q : Multiset Quartet) : Multiset Quartet :=
  (filterEncoded t (Q.map quartetEquiv)).map quartetEquiv.symm

/-- The encoded frequency is exactly the quartet multiplicity in the paper. -/
theorem encoded_frequency (Q : Multiset Quartet) (q : Quartet) :
    frequencies (Q.map quartetEquiv) q.key q.split = Q.count q := by
  exact Multiset.count_map_eq_count' quartetEquiv Q quartetEquiv.injective q

theorem filterQuartets_mono (Q : Multiset Quartet) {s t : ℝ} (hst : s ≤ t) :
    filterQuartets t Q ≤ filterQuartets s Q := by
  exact Multiset.map_le_map (filterEncoded_mono (Q.map quartetEquiv) hst)

end Algorithm1
end Camus
