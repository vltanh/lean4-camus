module

public import Camus.Network.Realization.SupportClades
public import Camus.Pipelines.Astral
public import Camus.Pipelines.SNP

/-!
# Section 3.2: the hypotheses of the consistency argument can be met

The consistency argument of Section 3.2 assumes that the sites evolve under the model of Warnow,
Tabatabaee and Evans ("WTE"; `External.SiteModel`) on the true network `N`, and that some tree `t`
displayed by `N` induces the most probable quartet on every four taxa
(`MostProbableQuartets`). This file shows that these hypotheses can be met by every canonical
network `Realization.graph t E` built on `t` (every network built on `t` is isomorphic to one,
`SupportSubdivision.canonical_iso`): with two states, uniform substitutions on the tree edges,
and small transmission probabilities on the added edges (`Realization.lowTransfer`), the quartet
that `t` induces on four taxa is strictly the most probable quartet on them
(`Realization.exists_mostProbable`). A site that evolves down the support switching, the subdivided
tree `t`, only contributes quartets induced by `t`, since the clades of that switching are those
of `t` (`Realization.cladeBelow_support_code`, `Realization.induced_of_mem_quartets_support`), and
it evolves down that switching with probability close to 1.

In particular the deeper-donor example meets every hypothesis of the paper's argument: the true
network `Counterexamples.shallowNet` is built on `Counterexamples.donorTree`, the tree displayed
by it, and under some site model the quartets of `donorTree` are the most probable; yet, with
probability tending to 1, the network `Counterexamples.deepNet`, not isomorphic to the true
network, is optimal for `Q_m` with the fewest reticulations among the optimal networks
(`Counterexamples.deeperDonor_meets_hypotheses`).

## Main results

* `Realization.induced_of_mem_quartets_support`: the quartets of a site that evolves down the
  support switching are induced by `t`.
* `Realization.lowTransfer`: a site model on `Realization.graph t E`.
* `Realization.exists_mostProbable`: under it, `t` induces the most probable quartets.
* `Counterexamples.deeperDonor_meets_hypotheses`: E7 under every hypothesis of the paper's
  argument.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Camus

namespace Realization

open DynamicProgramming

variable {t : PhyloTree} {E : Finset Pair}

/-- A site that evolves down the support switching of `Realization.graph t E` contributes only
quartets induced by `t`: the clade below every vertex of the support switching is a clade of
`t`. -/
theorem induced_of_mem_quartets_support (ht : t.WellLabelled)
    (hE : EdgeAbove.CycleSeparated t E) {σ : Type*} [DecidableEq σ]
    {h : External.SiteHistory (graph t E) σ} (hS : h.switching = supportEdges t E)
    {q : Quartet} (hq : q ∈ h.quartets) : q.induced t = true := by
  classical
  have hN := levelOne t ht E hE
  unfold External.SiteHistory.quartets at hq
  split_ifs at hq with hsnp
  · obtain ⟨e, he, hqe⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hqt, hcut⟩ := Finset.mem_filter.mp hqe
    have heS : e ∈ supportEdges t E := hS ▸ (Finset.mem_filter.mp he).1
    rw [hS] at hcut
    have hqt' : q.taxa ⊆ t.taxa := Quartet.mem_onTaxa.mp hqt
    -- the head of `e` is a vertex of `T` or a fresh vertex inside a wire
    obtain ⟨hr, hv⟩ := Finset.mem_erase.mp
      (External.Switchings.head_mem_slot hN (Finset.mem_union_left _ heS))
    have hclade : ∃ r ∈ t.nodes, (graph t E).cladeBelow (supportEdges t E) e.2 = t.taxaAt r := by
      rw [vertices_covered t E hE.1] at hv
      rcases Finset.mem_union.mp hv with horiginal | hinterior
      · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp horiginal
        exact ⟨p, hp, by rw [← hpe, cladeBelow_support_code ht hE hp]⟩
      · obtain ⟨r, hr, hvr⟩ := Finset.mem_biUnion.mp hinterior
        obtain ⟨hr0, hrn⟩ := Finset.mem_erase.mp hr
        exact ⟨r, hrn, cladeBelow_support_interior ht hE hrn hr0 hvr⟩
    obtain ⟨r, hrn, hrc⟩ := hclade
    rw [hrc] at hcut
    simp only [Quartet.induced, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    exact ⟨hqt', t.taxaAt r, taxaAt_mem_clades hrn, hcut⟩
  · exact absurd hq (Finset.notMem_empty q)

/-- A site model on `Realization.graph t E` with two states: the transmission probability `ε` on
each added edge and `1 - ε` on the other edge into its reticulation, the uniform distribution at
the root, the uniform row on the tree edges, and no change on the reticulation edges
(`External.SiteModel.uniform` otherwise). -/
noncomputable def lowTransfer (t : PhyloTree) (E : Finset Pair)
    (hE : E ⊆ EdgeAbove.candidates t) (ε : ℝ≥0) (hε0 : 0 < ε) (hε1 : ε < 1) :
    External.SiteModel (graph t E) Bool :=
  { External.SiteModel.uniform (graph t E) Bool with
    transmission := fun e =>
      if e ∈ E.image (fun f => (donor t f, recipient t f)) then ε else 1 - ε
    transmission_pos := fun e _ _ => by
      split_ifs
      · exact hε0
      · exact tsub_pos_of_lt hε1
    transmission_sum := fun v hv h2 => by
      classical
      -- the reticulation `v` is the recipient end `w'` of an added edge
      have hret : v ∈ (graph t E).vertices.filter (fun v => (graph t E).indegree v = 2) :=
        Finset.mem_filter.mpr ⟨hv, h2⟩
      rw [reticulation_vertices t E hE] at hret
      obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp hret
      have hroot : recipient t e₀ ≠ (graph t E).root := by
        intro h
        have := graph_root_indegree t E
        rw [← h, h2] at this
        exact absurd this (by decide)
      -- its two incoming edges: one support edge and the added edge
      obtain ⟨s, hs⟩ := Finset.card_eq_one.mp
        ((support_switching t E hE).2 _ hv hroot)
      have hsS : s ∈ supportEdges t E := (Finset.mem_filter.mp (hs ▸ Finset.mem_singleton_self s)).1
      have hsadd : s ∉ E.image (fun f => (donor t f, recipient t f)) := by
        intro hmem
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hmem
        exact added_edge_not_support hE hf hsS
      have hfilter : (graph t E).edges.filter (fun e => e.2 = recipient t e₀) =
          insert (donor t e₀, recipient t e₀) {s} := by
        change (supportEdges t E ∪ E.image (fun f => (donor t f, recipient t f))).filter
          (fun e => e.2 = recipient t e₀) = _
        rw [Finset.filter_union, hs, added_incoming_recipient_singleton t E hE he₀]
        ext x
        simp [or_comm]
      have hne : (donor t e₀, recipient t e₀) ∉ ({s} : Finset (ℕ × ℕ)) := by
        intro h
        rw [Finset.mem_singleton] at h
        exact hsadd (h ▸ Finset.mem_image.mpr ⟨e₀, he₀, rfl⟩)
      rw [hfilter, Finset.sum_insert hne, Finset.sum_singleton,
        ite_eq_left (Finset.mem_image.mpr ⟨e₀, he₀, rfl⟩), ite_eq_right hsadd]
      exact add_tsub_cancel_of_le hε1.le }

/-- The probability that a site under `lowTransfer` evolves down the support switching is at
least `(1 - ε)^K`, for `K` the number of support edges: the support edges into reticulations are
not added edges. -/
theorem support_switching_prob (hE : EdgeAbove.CycleSeparated t E) (ε : ℝ≥0) (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    (1 - ε) ^ (supportEdges t E).card ≤
      ∏ e ∈ (supportEdges t E).filter (fun e => (graph t E).indegree e.2 = 2),
        (lowTransfer t E hE.1 ε hε0 hε1).transmission e := by
  classical
  have hfactor : ∀ e ∈ (supportEdges t E).filter (fun e => (graph t E).indegree e.2 = 2),
      (lowTransfer t E hE.1 ε hε0 hε1).transmission e = 1 - ε := by
    intro e he
    have heS := (Finset.mem_filter.mp he).1
    change (if e ∈ E.image (fun f => (donor t f, recipient t f)) then ε else 1 - ε) = 1 - ε
    rw [ite_eq_right]
    intro hmem
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hmem
    exact added_edge_not_support hE.1 hf heS
  rw [Finset.prod_congr rfl hfactor, Finset.prod_const]
  exact pow_le_pow_of_le_one zero_le tsub_le_self (Finset.card_filter_le _ _)

/-- Under `lowTransfer` with `ε` small enough, the tree `t` induces the most probable quartet on
every four of its taxa. A quartet on four taxa of `t` that `t` does not induce is contributed
only by sites that do not evolve down the support switching
(`induced_of_mem_quartets_support`), which have probability at most `1 - (1 - ε)^K ≤ K ε`, for
`K` the number of support edges. The quartet that `t` induces is contributed by the site that
evolves down the support switching and changes only on the edge above a vertex whose clade cuts
it, with probability at least `(1 - ε)^K / 2^(K + 1)`. -/
theorem exists_mostProbable (t : PhyloTree) (ht : t.WellLabelled) (E : Finset Pair)
    (hE : EdgeAbove.CycleSeparated t E) :
    ∃ M : External.SiteModel (graph t E) Bool, MostProbableQuartets M t := by
  classical
  have hN := levelOne t ht E hE
  set K := (supportEdges t E).card
  set c : ℝ≥0 := (2⁻¹ : ℝ≥0) ^ (K + 3)
  set ε : ℝ≥0 := c / (K + 1)
  have hc0 : 0 < c := by positivity
  have hε0 : 0 < ε := by positivity
  have hc8 : c ≤ 8⁻¹ := by
    have : (2⁻¹ : ℝ≥0) ^ (K + 3) ≤ (2⁻¹ : ℝ≥0) ^ 3 :=
      pow_le_pow_of_le_one (by norm_num : (0 : ℝ≥0) ≤ 2⁻¹) (by norm_num : (2⁻¹ : ℝ≥0) ≤ 1)
        (by omega : 3 ≤ K + 3)
    calc c ≤ (2⁻¹ : ℝ≥0) ^ 3 := this
      _ = 8⁻¹ := by norm_num
  have hKε : (K : ℝ≥0) * ε ≤ c := by
    simp only [ε]
    rw [mul_div_assoc', div_le_iff₀ (by positivity), mul_comm c]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (zero_le : (0 : ℝ≥0) ≤ c)
  have hε1 : ε < 1 := by
    have : ε ≤ c := div_le_self (zero_le : (0 : ℝ≥0) ≤ c)
      (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ K))
    exact lt_of_le_of_lt (this.trans hc8) (by norm_num)
  set M := lowTransfer t E hE.1 ε hε0 hε1
  set Psupp := ∏ e ∈ (supportEdges t E).filter (fun e => (graph t E).indegree e.2 = 2),
    M.transmission e
  have hPsupp : (1 - ε) ^ K ≤ Psupp := support_switching_prob hE ε hε0 hε1
  -- Bernoulli: `(1 - ε)^K ≥ 1 - K ε ≥ 1 - c`, in the reals
  have hbern : (1 : ℝ) - c ≤ (Psupp : ℝ) := by
    have hε1' : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1.le
    have h1 : (1 : ℝ) + K * (-(ε : ℝ)) ≤ (1 + (-(ε : ℝ))) ^ K :=
      one_add_mul_le_pow (by linarith) K
    rw [← sub_eq_add_neg] at h1
    have h2 : ((1 - ε : ℝ≥0) : ℝ) = 1 - ε := NNReal.coe_sub hε1.le
    have h3 : ((1 - ε) ^ K : ℝ≥0) ≤ Psupp := hPsupp
    have h4 : ((K : ℝ≥0) * ε : ℝ≥0) ≤ c := hKε
    have h3' : ((1 - ε : ℝ≥0) : ℝ) ^ K ≤ (Psupp : ℝ) := by exact_mod_cast h3
    have h4' : (K : ℝ) * (ε : ℝ) ≤ (c : ℝ) := by exact_mod_cast h4
    rw [h2] at h3'
    nlinarith
  refine ⟨M, fun q hq s hs => ?_⟩
  -- the other quartet on the four taxa is not induced by `t`
  have hk : ({q.key.a, q.key.b, q.key.c, q.key.d} : Finset ℕ) ⊆ t.taxa := by
    simp only [Quartet.induced, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.1
  have hsplit : q.split = t.splitOf q.key := by
    have := t.key_quartet_splitOf ht hq
    rw [← congrArg Quartet.split this]
    rfl
  have hnot : (q.key.quartet s).induced t = false := by
    by_contra hind
    rw [Bool.not_eq_false] at hind
    exact hs (((t.induced_iff_splitOf ht q.key hk s).mp hind).trans hsplit.symm)
  -- upper bound: only sites off the support switching contribute it
  have hupper : M.quartetProb (q.key.quartet s) + Psupp ≤ 1 := by
    have hsub : Finset.univ.filter (fun h : External.SiteHistory (graph t E) Bool =>
        q.key.quartet s ∈ h.quartets) ⊆
        Finset.univ.filter (fun h => ¬ h.switching = supportEdges t E) := by
      intro h hh
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ h, fun hS => ?_⟩
      have := induced_of_mem_quartets_support ht hE hS (Finset.mem_filter.mp hh).2
      rw [hnot] at this
      exact Bool.false_ne_true this
    have hsplit_sum := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun h : External.SiteHistory (graph t E) Bool => h.switching = supportEdges t E)
      M.weight
    rw [M.weight_sum hN, M.sum_weight_switching hN (support_switching t E hE.1)] at hsplit_sum
    calc M.quartetProb (q.key.quartet s) + Psupp
        ≤ (∑ h ∈ Finset.univ.filter (fun h => ¬ h.switching = supportEdges t E), M.weight h) +
            Psupp := add_le_add_left (Finset.sum_le_sum_of_subset hsub) _
      _ = 1 := by rw [add_comm]; exact hsplit_sum
  -- lower bound: the site that changes only above a vertex of `t` whose clade cuts `q`
  obtain ⟨C, hC, hcut⟩ : ∃ C ∈ t.clades, q.cutBy C = true := by
    simp only [Quartet.induced, Bool.and_eq_true, List.any_eq_true] at hq
    exact hq.2
  obtain ⟨p, sub, hsub, hsubC⟩ := (PhyloTree.clades_mem_iff t C).mp hC
  have hp : p ∈ t.nodes := (t.mem_nodes_iff p).mpr ⟨sub, hsub⟩
  have hqt : q.taxa ⊆ t.taxa := hk
  have hp0 : p ≠ [] := by
    rintro rfl
    simp only [PhyloTree.nodeAt, Option.some.injEq] at hsub
    subst hsub
    exact Quartet.cutBy_not_whole q C (hsubC ▸ hqt) hcut
  have hcode : Address.code p ∈ (graph t E).vertices :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have hcode0 : Address.code p ≠ (graph t E).root := fun h => hp0 (Address.code_injective h)
  obtain ⟨⟨x, y⟩, hxy⟩ := Finset.card_eq_one.mp
    ((support_switching t E hE.1).2 _ hcode hcode0)
  have hxymem : (x, y) ∈ (supportEdges t E).filter (fun e => e.2 = Address.code p) :=
    hxy ▸ Finset.mem_singleton_self (x, y)
  have hxyS : (x, y) ∈ supportEdges t E := (Finset.mem_filter.mp hxymem).1
  have hy : y = Address.code p := (Finset.mem_filter.mp hxymem).2
  subst hy
  have hy1 : (graph t E).indegree (Address.code p) = 1 := graph_indegree_code t E hE.1 hp hp0
  let hist := External.SiteHistory.snp hN (support_switching t E hE.1) hxyS false true
  have hhist : q ∈ hist.quartets := by
    rw [External.SiteHistory.snp_quartets hN _ hxyS (by decide)]
    refine Finset.mem_filter.mpr ⟨Quartet.mem_onTaxa.mpr hqt, ?_⟩
    rw [cladeBelow_support_code ht hE hp]
    simp only [PhyloTree.taxaAt, hsub, hsubC]
    exact hcut
  have hsubst : ∀ e ∈ supportEdges t E, (2⁻¹ : ℝ≥0) ≤
      M.substitution e (hist.state e.1) (hist.state e.2) := by
    intro e he
    change (2⁻¹ : ℝ≥0) ≤ (if (graph t E).indegree e.2 = 2 then
      (if hist.state e.1 = hist.state e.2 then 1 else 0)
      else ((Fintype.card Bool : ℝ≥0))⁻¹)
    by_cases hexy : e = (x, Address.code p)
    · subst hexy
      simp [hy1]
    · have hst : hist.state e.1 = hist.state e.2 :=
        External.SiteHistory.snp_state_eq hN _ hxyS false true he hexy
      rw [hst]
      by_cases h2 : (graph t E).indegree e.2 = 2 <;> simp [h2]
  have hlower : Psupp * 2⁻¹ * (2⁻¹ : ℝ≥0) ^ K ≤ M.quartetProb q := by
    calc Psupp * 2⁻¹ * (2⁻¹ : ℝ≥0) ^ K
        ≤ M.weight hist := by
          change _ ≤ Psupp * M.root (hist.state (graph t E).root) *
            ∏ e ∈ supportEdges t E, M.substitution e (hist.state e.1) (hist.state e.2)
          gcongr
          · change (2⁻¹ : ℝ≥0) ≤ ((Fintype.card Bool : ℝ≥0))⁻¹
            simp
          · rw [← Finset.prod_const (s := supportEdges t E) (b := (2⁻¹ : ℝ≥0))]
            exact Finset.prod_le_prod hsubst
      _ ≤ M.quartetProb q := Finset.single_le_sum (fun _ _ => zero_le)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ hist, hhist⟩)
  -- compare, in the reals
  have hup' : (M.quartetProb (q.key.quartet s) : ℝ) + Psupp ≤ 1 := by exact_mod_cast hupper
  have hlow' : (Psupp : ℝ) * 2⁻¹ * (2⁻¹ : ℝ) ^ K ≤ M.quartetProb q := by
    exact_mod_cast hlower
  have hc' : (c : ℝ) = (2⁻¹ : ℝ) ^ K * 8⁻¹ := by
    simp only [c, pow_add]
    norm_num
  have hc8' : (c : ℝ) ≤ 8⁻¹ := by exact_mod_cast hc8
  have hpow : (0 : ℝ) < (2⁻¹ : ℝ) ^ K := by positivity
  have hP78 : (7 / 8 : ℝ) ≤ Psupp := by linarith
  have hprod := mul_le_mul_of_nonneg_right hP78 hpow.le
  rw [← NNReal.coe_lt_coe]
  nlinarith

end Realization

namespace Counterexamples

/-- Section 3.2, E7 under every hypothesis of the paper's consistency argument. Take for the true
network `shallowNet`, built on the tree `donorTree`, and a site model on it with two states under
which `donorTree` induces the most probable quartet on every four taxa (it exists by
`Realization.exists_mostProbable`). Then, for independent sites with the law of this model
(`External.SiteModel.sites`), the probability that `deepNet`, which is built on `donorTree` and
not isomorphic to `shallowNet`, displays as many quartets of `Q_m` as any network built on
`donorTree`, with the fewest reticulations among those, tends to 1. -/
theorem deeperDonor_meets_hypotheses :
    ∃ M : External.SiteModel shallowNet Bool,
      shallowNet.AnchoredExtension donorTree ∧ MostProbableQuartets M donorTree ∧
      Tendsto (fun m => M.sites shallowNet_anchored.1 {ω |
        (∀ R : RootedNetwork, R.AnchoredExtension donorTree →
          score (External.sampleQuartets (fun n ω => ω n) m ω)
              (DynamicProgramming.repertoire (External.sampleQuartets (fun n ω => ω n) m ω) R) ≤
            score (External.sampleQuartets (fun n ω => ω n) m ω)
              (DynamicProgramming.repertoire (External.sampleQuartets (fun n ω => ω n) m ω)
                deepNet)) ∧
        (∀ R : RootedNetwork, R.AnchoredExtension donorTree →
          (∀ R' : RootedNetwork, R'.AnchoredExtension donorTree →
            score (External.sampleQuartets (fun n ω => ω n) m ω)
                (DynamicProgramming.repertoire (External.sampleQuartets (fun n ω => ω n) m ω)
                  R') ≤
              score (External.sampleQuartets (fun n ω => ω n) m ω)
                (DynamicProgramming.repertoire (External.sampleQuartets (fun n ω => ω n) m ω)
                  R)) →
          deepNet.reticulationCount ≤ R.reticulationCount) ∧
        IsEmpty (deepNet.Iso shallowNet)}) atTop (𝓝 1) := by
  obtain ⟨M, hM⟩ : ∃ M : External.SiteModel shallowNet Bool, MostProbableQuartets M donorTree :=
    Realization.exists_mostProbable donorTree donorTree_wellLabelled {shallowPair}
      shallowPair_separated
  have h := snp_deeperDonor_tendsto M
    (fun n (ω : ℕ → External.SiteHistory shallowNet Bool) => ω n)
    (M.sites_iIndepFun shallowNet_anchored.1) (M.sites_identDistrib shallowNet_anchored.1)
    (M.sites_law shallowNet_anchored.1)
  exact ⟨M, shallowNet_anchored, hM, h⟩

end Counterexamples

end Camus
