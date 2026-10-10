module

public import Camus.Galled.Basic
public import Camus.Pipelines.Filtering
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FinCases

/-!
# Section 3.4: Algorithm 1, quartet filtering

Algorithm 1 takes the quartets observed on one set of four taxa, whose three topologies have
frequencies `f₁ ≥ f₂ ≥ f₃`, and returns the copies of the most frequent topology `q₁`, together
with the copies of the second `q₂` iff `f₂ − f₃ > t · (f₂ + f₃)`. It is applied to every set of four
taxa to give the input `Q` of CAMUS. This file defines it on multisets of quartets and proves what
it returns.

A quartet is a set of four taxa (`QuartetKey`) with one of three topologies (`quartetEquiv`). For
one set of four taxa, `Algorithm1.filterBlock` orders the three topologies by their number of
copies in the input (`Algorithm1.rank`) and returns

* every copy of `q₁` (`filterBlock_top_count`),
* every copy of `q₂` if `f₂ − f₃ > t · (f₂ + f₃)`, and none otherwise (`filterBlock_second_count`),
* no copy of `q₃` (`filterBlock_third_count`).

The test uses numbers of copies instead of the paper's relative frequencies; it is homogeneous in
`(f₂, f₃)`, so dividing by the number of genes does not change it. Ties are broken by the index of
the topology, where the paper allows any order with `f₁ ≥ f₂ ≥ f₃`. For `t ≥ 0`, a tie `f₂ = f₃`
never keeps `q₂` (`not_retainSecond_equal`), so the order matters only when `f₁ = f₂` and `q₂` is
not kept. `Algorithm1.filterQuartets` applies the algorithm to every set of four taxa, and a larger
threshold keeps a smaller multiset (`filterQuartets_mono`).

## Main results

* `Algorithm1.filterBlock`: Algorithm 1 on one set of four taxa.
* `Algorithm1.filterBlock_top_count`, `Algorithm1.filterBlock_second_count`,
  `Algorithm1.filterBlock_third_count`: its output.
* `Algorithm1.filterQuartets`: Algorithm 1 on every set of four taxa.
* `Algorithm1.filterBlock_mono`, `Algorithm1.filterQuartets_mono`: monotonicity in `t`.
-/

@[expose] public section

namespace Camus

/-- A set of four taxa, as four increasing labels. -/
structure QuartetKey where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  ab : a < b
  bc : b < c
  cd : c < d
  deriving DecidableEq

/-- The set of four taxa of a quartet. -/
def Quartet.key (q : Quartet) : QuartetKey :=
  ⟨q.a, q.b, q.c, q.d, q.ab, q.bc, q.cd⟩

/-- The quartet on the four taxa `k` with topology `s`. -/
def QuartetKey.quartet (k : QuartetKey) (s : Fin 3) : Quartet :=
  ⟨k.a, k.b, k.c, k.d, k.ab, k.bc, k.cd, s⟩

/-- A quartet is a set of four taxa together with one of its three topologies. -/
def quartetEquiv : Quartet ≃ QuartetKey × Fin 3 where
  toFun q := (q.key, q.split)
  invFun p := p.1.quartet p.2
  left_inv q := by cases q; rfl
  right_inv p := by rcases p with ⟨⟨a,b,c,d,ab,bc,cd⟩,s⟩; rfl

namespace Algorithm1

open scoped Classical

/-- The three topologies `(q₁, q₂, q₃)` in order of decreasing count `f` (`rank_ordered`), ties
broken by the index of the topology. The paper allows any order with `f₁ ≥ f₂ ≥ f₃`. -/
def rank (f : Fin 3 → ℕ) : Fin 3 × Fin 3 × Fin 3 :=
  if f 1 ≤ f 0 then
    if f 2 ≤ f 1 then (0, 1, 2)
    else if f 2 ≤ f 0 then (0, 2, 1) else (2, 0, 1)
  else
    if f 2 ≤ f 0 then (1, 0, 2)
    else if f 2 ≤ f 1 then (1, 2, 0) else (2, 1, 0)

/-- `f₁ ≥ f₂ ≥ f₃` for the order `rank f`. -/
theorem rank_ordered (f : Fin 3 → ℕ) :
    f (rank f).2.1 ≤ f (rank f).1 ∧
    f (rank f).2.2 ≤ f (rank f).2.1 := by
  unfold rank
  split_ifs <;> dsimp only <;> omega

/-- `q₁`, `q₂`, `q₃` are distinct. -/
theorem rank_distinct (f : Fin 3 → ℕ) :
    (rank f).1 ≠ (rank f).2.1 ∧ (rank f).1 ≠ (rank f).2.2 ∧
      (rank f).2.1 ≠ (rank f).2.2 := by
  unfold rank
  split_ifs <;> decide

/-- Every topology is one of `q₁`, `q₂`, `q₃`. -/
theorem rank_covers (f : Fin 3 → ℕ) (s : Fin 3) :
    s = (rank f).1 ∨ s = (rank f).2.1 ∨ s = (rank f).2.2 := by
  unfold rank
  split_ifs <;> fin_cases s <;> decide

variable {K : Type*} [DecidableEq K]

/-- The number of copies in `Q` of each topology on the set of four taxa `k`. The paper's relative
frequencies `fᵢ` are these numbers divided by the number of genes. -/
def frequencies (Q : Multiset (K × Fin 3)) (k : K) : Fin 3 → ℕ :=
  fun s => Q.count (k, s)

/-- **Algorithm 1** (`btag245-BOX1`), on the set of four taxa `k`: every copy in `Q` of the most
frequent topology `q₁`, and every copy of the second `q₂` iff `f₂ − f₃ > t · (f₂ + f₃)`
(`retainSecond`), where `f₁ ≥ f₂ ≥ f₃` are the numbers of copies of `q₁`, `q₂`, `q₃` (`rank`). -/
noncomputable def filterBlock (t : ℝ) (Q : Multiset (K × Fin 3)) (k : K) :
    Multiset (K × Fin 3) :=
  let f := frequencies Q k
  let r := rank f
  Multiset.replicate (f r.1) (k, r.1) +
    if retainSecond t (f r.2.1) (f r.2.2) then
      Multiset.replicate (f r.2.1) (k, r.2.1) else 0

/-- Algorithm 1 keeps every copy of the most frequent topology `q₁`. -/
theorem filterBlock_top_count (t : ℝ) (Q : Multiset (K × Fin 3)) (k : K) :
    (filterBlock t Q k).count (k, (rank (frequencies Q k)).1) =
      Q.count (k, (rank (frequencies Q k)).1) := by
  have h := (rank_distinct (frequencies Q k)).1
  simp only [filterBlock, Multiset.count_add]
  split_ifs <;> simp [Multiset.count_replicate, Ne.symm h, frequencies]

/-- Algorithm 1 keeps every copy of the second topology `q₂` if `f₂ − f₃ > t · (f₂ + f₃)`, and none
otherwise. -/
theorem filterBlock_second_count (t : ℝ) (Q : Multiset (K × Fin 3)) (k : K) :
    (filterBlock t Q k).count (k, (rank (frequencies Q k)).2.1) =
      if retainSecond t ((frequencies Q k) (rank (frequencies Q k)).2.1)
          ((frequencies Q k) (rank (frequencies Q k)).2.2) then
        Q.count (k, (rank (frequencies Q k)).2.1) else 0 := by
  have h := (rank_distinct (frequencies Q k)).1
  simp only [filterBlock, Multiset.count_add]
  split_ifs <;> simp [Multiset.count_replicate, h, frequencies]

/-- Algorithm 1 keeps no copy of the least frequent topology `q₃`. -/
theorem filterBlock_third_count (t : ℝ) (Q : Multiset (K × Fin 3)) (k : K) :
    (filterBlock t Q k).count (k, (rank (frequencies Q k)).2.2) = 0 := by
  have h := rank_distinct (frequencies Q k)
  simp only [filterBlock, Multiset.count_add]
  split_ifs <;> simp [Multiset.count_replicate, h.2.1, h.2.2]

/-- A larger threshold keeps less: for `s ≤ t`, the output at `t` is contained in the output at
`s`. -/
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

/-- Algorithm 1 on every set of four taxa that occurs in `Q`, the outputs added up. -/
noncomputable def filterEncoded (t : ℝ) (Q : Multiset (K × Fin 3)) :
    Multiset (K × Fin 3) :=
  ∑ k ∈ Q.toFinset.image Prod.fst, filterBlock t Q k

/-- A larger threshold keeps less: for `s ≤ t`, `filterEncoded t Q ≤ filterEncoded s Q`. -/
theorem filterEncoded_mono (Q : Multiset (K × Fin 3)) {s t : ℝ} (hst : s ≤ t) :
    filterEncoded t Q ≤ filterEncoded s Q := by
  exact Finset.sum_le_sum (fun k _ => filterBlock_mono Q k hst)

/-- Section 3.4: Algorithm 1 applied to every set of four taxa of a multiset `Q` of quartets; the
result is the multiset given as input to CAMUS. -/
noncomputable def filterQuartets (t : ℝ) (Q : Multiset Quartet) : Multiset Quartet :=
  (filterEncoded t (Q.map quartetEquiv)).map quartetEquiv.symm

/-- The number of copies of a topology on a set of four taxa is the multiplicity in `Q` of the
corresponding quartet. -/
theorem encoded_frequency (Q : Multiset Quartet) (q : Quartet) :
    frequencies (Q.map quartetEquiv) q.key q.split = Q.count q := by
  exact Multiset.count_map_eq_count' quartetEquiv Q quartetEquiv.injective q

/-- A larger threshold keeps fewer quartets: for `s ≤ t`,
`filterQuartets t Q ≤ filterQuartets s Q`. -/
theorem filterQuartets_mono (Q : Multiset Quartet) {s t : ℝ} (hst : s ≤ t) :
    filterQuartets t Q ≤ filterQuartets s Q := by
  exact Multiset.map_le_map (filterEncoded_mono (Q.map quartetEquiv) hst)

end Algorithm1
end Camus
