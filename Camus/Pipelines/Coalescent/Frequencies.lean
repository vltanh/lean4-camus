module

public import Camus.Pipelines.Algorithm1
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Section 3.4: Algorithm 1 on converging frequencies

Section 3.4 explains Algorithm 1 by the limit of many genes. Under the multispecies coalescent the
relative frequencies `f₁, f₂, f₃` of the three topologies on four taxa approach probabilities
`p₁ > p₂ = p₃`, so "the gap between f2 and f3 will approach 0" and the test
`f₂ − f₃ > t · (f₂ + f₃)` eventually fails; and when `p₂ > p₃` and `t < (p₂ − p₃)/(p₂ + p₃)`, the
test eventually holds. This file proves both facts for any counts whose relative frequencies
converge, and what Algorithm 1 then returns. The probabilities and the almost sure convergence are
in `Camus/Pipelines/Coalescent.lean`.

The counts are `f n : Fin 3 → ℕ`, the numbers of copies of the three topologies among the quartet
trees of `n` genes; their relative frequencies are `f n s / n`.

## Main results

* `Algorithm1.eventually_msc_pattern`: if the limits satisfy `p s₁ > p s = p s' > 0` for the two
  topologies `s, s'` other than `s₁`, and `t > 0`, eventually `s₁` has strictly the largest count
  and the test fails for the two other topologies.
* `Algorithm1.eventually_retain_pattern`: if `p s₃` is strictly the smallest limit and the test
  holds for the limits, eventually `s₃` has strictly the smallest count and the test holds.
* `Algorithm1.filterBlock_eq_replicate`, `Algorithm1.filterBlock_count_of_retain`: the output of
  Algorithm 1 in these two situations.
* `Algorithm1.count_filterQuartets`: the multiplicity of a quartet tree in the output of
  Algorithm 1 is its multiplicity in the output on its own four taxa.
* `Algorithm1.count_filterBlock_le`: the output of Algorithm 1 on four taxa is part of its input.

## Proof (the paper's)

Under the multispecies coalescent the limits are `p₁ > p₂ = p₃ > 0`. The relative frequency of
the topology of `p₁` eventually exceeds the two others, so it is `q₁` (`rank_fst_eq_of_lt`). The
gap between the two others tends to `0` while `t` times their sum tends to `2 t p₂ > 0`, so the
test fails, whichever of them is `q₂` (`eventually_msc_pattern`), and Algorithm 1 keeps the copies
of `q₁` only (`filterBlock_eq_replicate`). For the converse, the topology of `p₃` eventually has
the smallest count, so it is `q₃` (`rank_snd_snd_eq_of_lt`), and the test, which holds for the
limits, holds for the counts (`eventually_retain_pattern`, `filterBlock_count_of_retain`).
-/

@[expose] public section

namespace Camus

open Filter Topology

namespace Algorithm1

variable {K : Type*} [DecidableEq K]

/-- A topology whose count is strictly the largest is the most frequent topology `q₁`. -/
theorem rank_fst_eq_of_lt {f : Fin 3 → ℕ} {s₁ : Fin 3} (h : ∀ s, s ≠ s₁ → f s < f s₁) :
    (rank f).1 = s₁ := by
  obtain ⟨h12, h23⟩ := rank_ordered f
  by_contra hne
  have hlt := h _ hne
  rcases rank_covers f s₁ with h' | h' | h'
  · exact hne h'.symm
  · rw [← h'] at h12
    omega
  · rw [← h'] at h23
    omega

/-- A topology whose count is strictly the smallest is the least frequent topology `q₃`. -/
theorem rank_snd_snd_eq_of_lt {f : Fin 3 → ℕ} {s₃ : Fin 3} (h : ∀ s, s ≠ s₃ → f s₃ < f s) :
    (rank f).2.2 = s₃ := by
  obtain ⟨h12, h23⟩ := rank_ordered f
  by_contra hne
  have hlt := h _ hne
  rcases rank_covers f s₃ with h' | h' | h'
  · rw [← h'] at h12
    omega
  · rw [← h'] at h23
    omega
  · exact hne h'.symm

/-- Every element of the output of Algorithm 1 on the set of four taxa `k` has key `k`. -/
theorem fst_of_mem_filterBlock {t : ℝ} {Q : Multiset (K × Fin 3)} {k : K} {p : K × Fin 3}
    (hp : p ∈ filterBlock t Q k) : p.1 = k := by
  simp only [filterBlock, Multiset.mem_add] at hp
  rcases hp with hp | hp
  · rw [Multiset.eq_of_mem_replicate hp]
  · split_ifs at hp with h
    · rw [Multiset.eq_of_mem_replicate hp]
    · exact absurd hp (Multiset.notMem_zero p)

/-- The output of Algorithm 1 on the set of four taxa `k` is part of its input: every topology is
kept with all its copies or not at all. -/
theorem count_filterBlock_le (t : ℝ) (Q : Multiset (K × Fin 3)) (k : K) (x : K × Fin 3) :
    (filterBlock t Q k).count x ≤ Q.count x := by
  by_cases hx : x.1 = k
  · obtain ⟨y, s⟩ := x
    obtain rfl : y = k := hx
    rcases rank_covers (frequencies Q y) s with rfl | rfl | rfl
    · rw [filterBlock_top_count]
    · rw [filterBlock_second_count]
      split_ifs <;> simp
    · rw [filterBlock_third_count]
      exact Nat.zero_le _
  · rw [Multiset.count_eq_zero.2 fun h => hx (fst_of_mem_filterBlock h)]
    exact Nat.zero_le _

/-- The multiplicity of a quartet `q` in the output of Algorithm 1 on every set of four taxa
(`filterQuartets`) is its multiplicity in the output on the four taxa of `q`. -/
theorem count_filterQuartets (t : ℝ) (Q : Multiset Quartet) (q : Quartet) :
    (filterQuartets t Q).count q =
      (filterBlock t (Q.map quartetEquiv) q.key).count (q.key, q.split) := by
  unfold filterQuartets filterEncoded
  conv_lhs => rw [← quartetEquiv.symm_apply_apply q]
  rw [Multiset.count_map_eq_count' _ _ quartetEquiv.symm.injective, Multiset.count_sum']
  have hq : quartetEquiv q = (q.key, q.split) := rfl
  rw [hq]
  refine Finset.sum_eq_single q.key (fun k _ hk => ?_) (fun hk => ?_)
  · -- the output on another set of four taxa contains no quartet on the taxa of `q`
    exact Multiset.count_eq_zero.2 fun h => hk (fst_of_mem_filterBlock h).symm
  · -- no quartet of `Q` is on the taxa of `q`, so the output on them is empty
    have h0 : ∀ s, frequencies (Q.map quartetEquiv) q.key s = 0 := fun s =>
      Multiset.count_eq_zero.2 fun h =>
        hk (Finset.mem_image.2 ⟨(q.key, s), Multiset.mem_toFinset.2 h, rfl⟩)
    refine Multiset.count_eq_zero.2 fun h => ?_
    simp only [filterBlock, h0, Multiset.replicate_zero, zero_add] at h
    split_ifs at h <;> exact absurd h (Multiset.notMem_zero _)

/-- If the topology `s₁` has strictly the largest count on the set of four taxa `k` and the test
fails for the two other topologies, in either order, Algorithm 1 keeps exactly the copies of
`s₁`. -/
theorem filterBlock_eq_replicate {t : ℝ} {Q : Multiset (K × Fin 3)} {k : K} {s₁ : Fin 3}
    (hmax : ∀ s, s ≠ s₁ → frequencies Q k s < frequencies Q k s₁)
    (hdrop : ∀ s s', s ≠ s₁ → s' ≠ s₁ →
      ¬ retainSecond t (frequencies Q k s) (frequencies Q k s')) :
    filterBlock t Q k = Multiset.replicate (Q.count (k, s₁)) (k, s₁) := by
  have h1 := rank_fst_eq_of_lt hmax
  obtain ⟨h12, h13, -⟩ := rank_distinct (frequencies Q k)
  rw [h1] at h12 h13
  simp only [filterBlock]
  rw [ite_eq_right (hdrop _ _ (Ne.symm h12) (Ne.symm h13)), add_zero, h1]
  rfl

/-- If the topology `s₃` has strictly the smallest count on the set of four taxa `k` and the test
holds for each other topology against `s₃`, Algorithm 1 keeps every copy of the two other
topologies and no copy of `s₃`. -/
theorem filterBlock_count_of_retain {t : ℝ} {Q : Multiset (K × Fin 3)} {k : K} {s₃ : Fin 3}
    (hmin : ∀ s, s ≠ s₃ → frequencies Q k s₃ < frequencies Q k s)
    (hkeep : ∀ s, s ≠ s₃ → retainSecond t (frequencies Q k s) (frequencies Q k s₃))
    (s : Fin 3) :
    (filterBlock t Q k).count (k, s) = if s = s₃ then 0 else Q.count (k, s) := by
  have h3 := rank_snd_snd_eq_of_lt hmin
  obtain ⟨-, h13, h23⟩ := rank_distinct (frequencies Q k)
  rw [h3] at h13 h23
  rcases rank_covers (frequencies Q k) s with rfl | rfl | rfl
  · rw [ite_eq_right h13, filterBlock_top_count]
  · rw [ite_eq_right h23, filterBlock_second_count, h3, ite_eq_left (hkeep _ h23)]
  · rw [ite_eq_left h3, filterBlock_third_count]

/-- If `0 ≤ p₃ < p₂ ≤ p₁` and the test of Algorithm 1 holds for `p₂` against `p₃`, it holds for
`p₁` against `p₃`. -/
theorem retainSecond_of_le {t p₁ p₂ p₃ : ℝ} (h₃ : 0 ≤ p₃) (h₂₃ : p₃ < p₂) (h₁₂ : p₂ ≤ p₁)
    (h : retainSecond t p₂ p₃) : retainSecond t p₁ p₃ := by
  unfold retainSecond at *
  -- the test forces `t < 1`
  have ht : t < 1 := by
    by_contra ht
    have ht' : 1 ≤ t := le_of_not_gt ht
    nlinarith
  nlinarith

/-- Of three distinct topologies, every topology other than the third is one of the first two. -/
theorem fin_three_cases {s₁ s₂ s₃ s : Fin 3} (h₁₂ : s₁ ≠ s₂) (h₁₃ : s₁ ≠ s₃) (h₂₃ : s₂ ≠ s₃)
    (hs : s ≠ s₃) : s = s₁ ∨ s = s₂ := by
  revert s₁ s₂ s₃ s
  decide

/-- Section 3.4: the pattern of the multispecies coalescent in the limit. Let `f n s` be the count
of the topology `s` on four taxa among `n` genes, with relative frequencies `f n s / n → p s`. If
`s₁` is strictly the most probable topology and the two others have the same positive probability
(the pattern of the multispecies coalescent), then for every threshold `t > 0`, eventually `s₁` has
strictly the largest count and the test `f₂ − f₃ > t · (f₂ + f₃)` fails for the two other
topologies, in either order: "the gap between f2 and f3 will approach 0", while `f₂ + f₃` stays
proportional to `n`. -/
theorem eventually_msc_pattern {f : ℕ → Fin 3 → ℕ} {p : Fin 3 → ℝ} {s₁ : Fin 3} {t : ℝ}
    (hf : ∀ s, Tendsto (fun n : ℕ => (f n s : ℝ) / n) atTop (𝓝 (p s)))
    (hmax : ∀ s, s ≠ s₁ → p s < p s₁) (heq : ∀ s s', s ≠ s₁ → s' ≠ s₁ → p s = p s')
    (hpos : ∀ s, s ≠ s₁ → 0 < p s) (ht : 0 < t) :
    ∀ᶠ n in atTop, (∀ s, s ≠ s₁ → f n s < f n s₁) ∧
      ∀ s s', s ≠ s₁ → s' ≠ s₁ → ¬ retainSecond t (f n s) (f n s') := by
  -- the relative frequency of `s₁` eventually exceeds the two others
  have h1 : ∀ s, ∀ᶠ n in atTop, s ≠ s₁ → (f n s : ℝ) / n < (f n s₁ : ℝ) / n := by
    intro s
    by_cases hs : s = s₁
    · exact Eventually.of_forall fun _ h => absurd hs h
    · filter_upwards [((hf s₁).sub (hf s)).eventually_const_lt (sub_pos.2 (hmax s hs))]
        with n hn _
      linarith
  -- the gap between the two other relative frequencies tends to `0`, their sum to `2 p₂ > 0`
  have h2 : ∀ s s', ∀ᶠ n in atTop, s ≠ s₁ → s' ≠ s₁ →
      |(f n s : ℝ) / n - (f n s' : ℝ) / n| < t * ((f n s : ℝ) / n + (f n s' : ℝ) / n) := by
    intro s s'
    by_cases hs : s = s₁
    · exact Eventually.of_forall fun _ h => absurd hs h
    by_cases hs' : s' = s₁
    · exact Eventually.of_forall fun _ _ h => absurd hs' h
    have hlim : Tendsto (fun n : ℕ => t * ((f n s : ℝ) / n + (f n s' : ℝ) / n) -
        |(f n s : ℝ) / n - (f n s' : ℝ) / n|) atTop
        (𝓝 (t * (p s + p s') - |p s - p s'|)) :=
      (((hf s).add (hf s')).const_mul t).sub ((hf s).sub (hf s')).abs
    have hlim_pos : 0 < t * (p s + p s') - |p s - p s'| := by
      rw [heq s s' hs hs', sub_self, abs_zero, sub_zero]
      have := hpos s' hs'
      positivity
    filter_upwards [hlim.eventually_const_lt hlim_pos] with n hn _ _
    linarith
  filter_upwards [eventually_all.2 h1, eventually_all.2 fun s => eventually_all.2 (h2 s),
    eventually_gt_atTop 0] with n hn1 hn2 hn0
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  refine ⟨fun s hs => ?_, fun s s' hs hs' hret => ?_⟩
  · exact_mod_cast (div_lt_div_iff_of_pos_right hn).1 (hn1 s hs)
  · -- the test, divided by `n`, contradicts the bound on the gap
    have hgap := hn2 s s' hs hs'
    unfold retainSecond at hret
    have hdiv : t * ((f n s : ℝ) / n + (f n s' : ℝ) / n) < (f n s : ℝ) / n - (f n s' : ℝ) / n := by
      rw [← add_div, ← sub_div, ← mul_div_assoc]
      exact (div_lt_div_iff_of_pos_right hn).2 hret
    linarith [le_abs_self ((f n s : ℝ) / n - (f n s' : ℝ) / n)]

/-- Section 3.4: the converse signal in the limit. Let `f n s` be the count of the topology `s` on
four taxa among `n` genes, with relative frequencies `f n s / n → p s`. If `s₃` is strictly the
least probable topology and the test of Algorithm 1 holds for the probabilities of each other
topology against `s₃`, then eventually `s₃` has strictly the smallest count and the test holds for
the counts. -/
theorem eventually_retain_pattern {f : ℕ → Fin 3 → ℕ} {p : Fin 3 → ℝ} {s₃ : Fin 3} {t : ℝ}
    (hf : ∀ s, Tendsto (fun n : ℕ => (f n s : ℝ) / n) atTop (𝓝 (p s)))
    (hmin : ∀ s, s ≠ s₃ → p s₃ < p s) (hret : ∀ s, s ≠ s₃ → retainSecond t (p s) (p s₃)) :
    ∀ᶠ n in atTop, (∀ s, s ≠ s₃ → f n s₃ < f n s) ∧
      ∀ s, s ≠ s₃ → retainSecond t (f n s) (f n s₃) := by
  -- the relative frequency of `s₃` is eventually below the two others
  have h1 : ∀ s, ∀ᶠ n in atTop, s ≠ s₃ → (f n s₃ : ℝ) / n < (f n s : ℝ) / n := by
    intro s
    by_cases hs : s = s₃
    · exact Eventually.of_forall fun _ h => absurd hs h
    · filter_upwards [((hf s).sub (hf s₃)).eventually_const_lt (sub_pos.2 (hmin s hs))]
        with n hn _
      linarith
  -- the test holds in the limit, hence eventually
  have h2 : ∀ s, ∀ᶠ n in atTop, s ≠ s₃ →
      t * ((f n s : ℝ) / n + (f n s₃ : ℝ) / n) < (f n s : ℝ) / n - (f n s₃ : ℝ) / n := by
    intro s
    by_cases hs : s = s₃
    · exact Eventually.of_forall fun _ h => absurd hs h
    have hlim : Tendsto (fun n : ℕ => ((f n s : ℝ) / n - (f n s₃ : ℝ) / n) -
        t * ((f n s : ℝ) / n + (f n s₃ : ℝ) / n)) atTop
        (𝓝 ((p s - p s₃) - t * (p s + p s₃))) :=
      ((hf s).sub (hf s₃)).sub (((hf s).add (hf s₃)).const_mul t)
    have hlim_pos : 0 < (p s - p s₃) - t * (p s + p s₃) := by
      have := hret s hs
      unfold retainSecond at this
      linarith
    filter_upwards [hlim.eventually_const_lt hlim_pos] with n hn _
    linarith
  filter_upwards [eventually_all.2 h1, eventually_all.2 h2, eventually_gt_atTop 0]
    with n hn1 hn2 hn0
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · exact_mod_cast (div_lt_div_iff_of_pos_right hn).1 (hn1 s hs)
  · -- multiply the test on relative frequencies by `n`
    have h := hn2 s hs
    rw [← add_div, ← sub_div, ← mul_div_assoc] at h
    exact (div_lt_div_iff_of_pos_right hn).1 h

end Algorithm1

end Camus
