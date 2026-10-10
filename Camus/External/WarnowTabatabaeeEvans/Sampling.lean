module

public import Camus.External.WarnowTabatabaeeEvans.SiteModel
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw

/-!
# Sites drawn independently from the single site model

Section 3.2 of the paper builds the multiset `Q` from an alignment of SNPs: every SNP adds one
copy of each quartet `ab|cd` with `a`, `b` in one state and `c`, `d` in the other. It then claims,
"according to the theory given in Warnow et al. (2025)", that as the number of sites grows the
support of `Q` equals `Q(N_r)` with probability tending to 1. This file proves that claim inside
the single site model of Warnow, Tabatabaee and Evans (WTE; `External.SiteModel`), for sites
`X 0, X 1, ...` that are independent with the law of the model: with `Q_m` the multiset
sum of the quartets of the SNPs among the first `m` sites (`External.sampleQuartets`), the
probability that the quartets of `Q_m` are exactly those displayed by `N` tends to 1
(`External.support_tendsto`). WTE prove the corresponding statement for clades (Theorem 6, with
the bound of Theorem 7); the adaptation to quartets is the paper's. The file also gives the law of
large numbers for the frequency of a quartet (`External.frequency_tendsto`), which the ASTRAL step
of the pipeline uses, and shows that independent sites with the law of the model exist
(`External.SiteModel.sites`).

## Main results

* `External.sampleQuartets`: the multiset `Q_m`.
* `External.displays_of_mem_sampleQuartets`: every quartet of `Q_m` is displayed by `N`.
* `External.support_tendsto`: the probability that the support of `Q_m` is the set of quartets
  displayed by `N` tends to 1.
* `External.frequency_tendsto`: the frequency of a quartet in `Q_m` converges almost surely to
  the probability that a site contributes it.
* `External.eventually_count_lt`: a quartet that a site contributes with smaller probability is
  eventually less frequent, almost surely.
* `External.tendsto_measure_of_ae_eventually`: events that hold eventually, almost surely, have
  probability tending to 1.
* `External.SiteModel.sites`, `External.SiteModel.sites_iIndepFun`,
  `External.SiteModel.sites_identDistrib`, `External.SiteModel.sites_law`: independent sites with
  the law of the model, on the infinite product space.

## Proof (WTE's, Theorems 6 and 7)

WTE (Theorem 6): "every clade in N has strictly positive probability of appearing as a clade for
an SNP. Hence, as the number of sites increases, with probability converging to 1, the set of
clades for the SNPs converges to Clades(N)." For quartets: every quartet of an SNP is displayed by
`N` (`External.SiteHistory.displays_of_mem_quartets`), and every quartet `q` displayed by `N` is
contributed by a site with a probability `p_q > 0` (`External.SiteModel.quartetProb_pos`). By
independence, `q` is missing from `Q_m` with probability `(1 - p_q)^m`; WTE (Theorem 7) bound the
probability that some clade is missing by Boole's inequality, here
`∑_q (1 - p_q)^m`, a finite sum over the quartets on the taxa of `N`, which tends to 0.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Camus.External

variable {N : RootedNetwork} {σ : Type*} [DecidableEq σ] {Ω : Type*}

/-- Section 3.2: the multiset `Q_m` built from the first `m` sites: one copy of each quartet of
each SNP among them (`External.SiteHistory.quartets`; a quartet "will be added only once for a
given SNP, but more than one SNP can produce the same quartet tree"). -/
noncomputable def sampleQuartets (X : ℕ → Ω → SiteHistory N σ) (m : ℕ) (ω : Ω) :
    Multiset Quartet :=
  ∑ n ∈ Finset.range m, ((X n ω).quartets).val

theorem mem_sampleQuartets {X : ℕ → Ω → SiteHistory N σ} {m : ℕ} {ω : Ω} {q : Quartet} :
    q ∈ sampleQuartets X m ω ↔ ∃ n < m, q ∈ (X n ω).quartets := by
  simp [sampleQuartets, Multiset.mem_sum]

/-- The multiplicity of `q` in `Q_m` is the number of sites among the first `m` that contribute
`q`. -/
theorem count_sampleQuartets (X : ℕ → Ω → SiteHistory N σ) (m : ℕ) (ω : Ω) (q : Quartet) :
    (sampleQuartets X m ω).count q =
      ∑ n ∈ Finset.range m, if q ∈ (X n ω).quartets then 1 else 0 := by
  rw [sampleQuartets, Multiset.count_sum']
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Multiset.count_eq_of_nodup (X n ω).quartets.nodup]
  simp only [Finset.mem_val]

/-- Every quartet of `Q_m` is displayed by `N`. -/
theorem displays_of_mem_sampleQuartets (hN : N.RootedBinaryLevelOne)
    {X : ℕ → Ω → SiteHistory N σ} {m : ℕ} {ω : Ω} {q : Quartet}
    (hq : q ∈ sampleQuartets X m ω) : N.DisplaysQuartet q := by
  obtain ⟨n, -, hn⟩ := mem_sampleQuartets.mp hq
  exact SiteHistory.displays_of_mem_quartets hN hn

variable [Fintype σ] [MeasurableSpace Ω]

/-- Section 3.2, "according to the theory given in Warnow et al. (2025)", inside WTE's model: for
sites `X 0, X 1, ...` that are independent and have the law of a site under the model `M` on a
rooted binary level-1 network `N`, with at least two states, the probability that the quartets of
`Q_m` are exactly the quartets displayed by `N` tends to 1. -/
theorem support_tendsto (M : SiteModel N σ) (hN : N.RootedBinaryLevelOne) [Nontrivial σ]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ℕ → Ω → SiteHistory N σ)
    (hind : iIndepFun X P) (hid : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hlaw : P.map (X 0) = M.law hN) :
    Tendsto (fun m => P {ω | ∀ q, q ∈ sampleQuartets X m ω ↔ N.DisplaysQuartet q}) atTop
      (𝓝 1) := by
  classical
  let D := (Quartet.onTaxa N.taxa).filter N.DisplaysQuartet
  let p : Quartet → ℝ≥0∞ := fun q => (M.quartetProb q : ℝ≥0∞)
  have hlawn : ∀ n (A : Set (SiteHistory N σ)), P (X n ⁻¹' A) = M.law hN A := by
    intro n A
    rw [← Measure.map_apply_of_aemeasurable (hid n).aemeasurable_fst MeasurableSet.of_discrete,
      (hid n).map_eq, hlaw]
  -- by independence, no site among the first `m` contributes `q` with probability `(1 - p_q)^m`
  have hmiss : ∀ q m, P (⋂ n ∈ Finset.range m, X n ⁻¹' {h | q ∈ h.quartets}ᶜ) =
      (1 - p q) ^ m := by
    intro q m
    rw [hind.measure_inter_preimage_eq_mul (Finset.range m)
      (fun _ _ => MeasurableSet.of_discrete)]
    simp only [hlawn, prob_compl_eq_one_sub MeasurableSet.of_discrete, SiteModel.law_quartets,
      Finset.prod_const, Finset.card_range, p]
  -- if `Q_m` misses a quartet displayed by `N`, some quartet on the taxa of `N` is missed by
  -- every site; the union bound
  have hbound : ∀ m, 1 - ∑ q ∈ D, (1 - p q) ^ m ≤
      P {ω | ∀ q, q ∈ sampleQuartets X m ω ↔ N.DisplaysQuartet q} := by
    intro m
    rw [tsub_le_iff_right]
    have hcover : Set.univ ⊆ {ω | ∀ q, q ∈ sampleQuartets X m ω ↔ N.DisplaysQuartet q} ∪
        ⋃ q ∈ D, ⋂ n ∈ Finset.range m, X n ⁻¹' {h | q ∈ h.quartets}ᶜ := by
      intro ω _
      by_cases hgood : ∀ q, q ∈ sampleQuartets X m ω ↔ N.DisplaysQuartet q
      · exact Or.inl hgood
      · right
        push Not at hgood
        obtain ⟨q, hq⟩ := hgood
        rcases hq with ⟨hin, hnot⟩ | ⟨hnot, hdisp⟩
        · exact absurd (displays_of_mem_sampleQuartets hN hin) hnot
        · simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff,
            Set.mem_ofPred_eq]
          refine ⟨q, Finset.mem_filter.mpr ⟨Quartet.mem_onTaxa.mpr hdisp.1, hdisp⟩,
            fun n hn hqn => hnot (mem_sampleQuartets.mpr ⟨n, Finset.mem_range.mp hn, hqn⟩)⟩
    calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
      _ ≤ P ({ω | ∀ q, q ∈ sampleQuartets X m ω ↔ N.DisplaysQuartet q} ∪
          ⋃ q ∈ D, ⋂ n ∈ Finset.range m, X n ⁻¹' {h | q ∈ h.quartets}ᶜ) := measure_mono hcover
      _ ≤ P {ω | ∀ q, q ∈ sampleQuartets X m ω ↔ N.DisplaysQuartet q} +
          P (⋃ q ∈ D, ⋂ n ∈ Finset.range m, X n ⁻¹' {h | q ∈ h.quartets}ᶜ) :=
        measure_union_le _ _
      _ ≤ P {ω | ∀ q, q ∈ sampleQuartets X m ω ↔ N.DisplaysQuartet q} +
          ∑ q ∈ D, (1 - p q) ^ m := by
        gcongr
        refine (measure_biUnion_finset_le D _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun q _ => hmiss q m
  -- each displayed quartet has positive probability, so the bound tends to 0
  have hzero : Tendsto (fun m => ∑ q ∈ D, (1 - p q) ^ m) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (f := fun q m => (1 - p q) ^ m) (a := fun _ => (0 : ℝ≥0∞))
      (x := atTop) D fun q hq => by
        refine ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
          (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero ?_)
        exact ENNReal.coe_ne_zero.mpr
          (M.quartetProb_pos hN (Finset.mem_filter.mp hq).2).ne'
    simpa using h
  have hone : Tendsto (fun m => 1 - ∑ q ∈ D, (1 - p q) ^ m) atTop (𝓝 1) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds hzero (Or.inl ENNReal.one_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hone tendsto_const_nhds hbound
    fun _ => prob_le_one

/-- The law of large numbers for a quartet: for independent sites with the law of the model `M`,
the frequency `(number of copies of q in Q_m) / m` converges almost surely to the probability
`quartetProb q` that a site contributes `q`. -/
theorem frequency_tendsto (M : SiteModel N σ) (hN : N.RootedBinaryLevelOne)
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ℕ → Ω → SiteHistory N σ)
    (hind : iIndepFun X P) (hid : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hlaw : P.map (X 0) = M.law hN) (q : Quartet) :
    ∀ᵐ ω ∂P, Tendsto (fun m => ((sampleQuartets X m ω).count q : ℝ) / m) atTop
      (𝓝 (M.quartetProb q : ℝ)) := by
  classical
  let A : Set (SiteHistory N σ) := {h | q ∈ h.quartets}
  let φ : SiteHistory N σ → ℝ := A.indicator 1
  have hφ : Measurable φ := Measurable.of_discrete
  -- the indicators that the sites contribute `q` are independent, identically distributed and
  -- integrable, with mean `quartetProb q`
  have hint : Integrable (φ ∘ X 0) P :=
    Integrable.comp_aemeasurable Integrable.of_finite (hid 0).aemeasurable_fst
  have hmean : ∫ ω, (φ ∘ X 0) ω ∂P = M.quartetProb q := by
    have hnull : NullMeasurableSet (X 0 ⁻¹' A) P :=
      (hid 0).aemeasurable_fst.nullMeasurableSet_preimage MeasurableSet.of_discrete
    have heq : φ ∘ X 0 = (X 0 ⁻¹' A).indicator 1 := by
      ext ω
      simp [φ, Set.indicator_apply]
    rw [heq, integral_indicator₀ hnull]
    simp only [Pi.one_apply]
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      ← Measure.map_apply_of_aemeasurable (hid 0).aemeasurable_fst MeasurableSet.of_discrete,
      hlaw, SiteModel.law_quartets, ENNReal.coe_toReal]
  have h := strong_law_ae_real (fun n => φ ∘ X n) hint
    (fun i j hij => (hind.indepFun hij).comp hφ hφ) (fun i => (hid i).comp hφ)
  filter_upwards [h] with ω hω
  rw [hmean] at hω
  refine hω.congr fun m => ?_
  rw [count_sampleQuartets]
  push_cast
  refine congrArg (· / (m : ℝ)) (Finset.sum_congr rfl fun n _ => ?_)
  by_cases hn : q ∈ (X n ω).quartets <;> simp [φ, A, hn]

/-- If a site contributes `q'` with smaller probability than `q`, then almost surely `q'` has
fewer copies than `q` in `Q_m` for all large `m`. -/
theorem eventually_count_lt (M : SiteModel N σ) (hN : N.RootedBinaryLevelOne)
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ℕ → Ω → SiteHistory N σ)
    (hind : iIndepFun X P) (hid : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hlaw : P.map (X 0) = M.law hN) {q q' : Quartet}
    (hlt : M.quartetProb q' < M.quartetProb q) :
    ∀ᵐ ω ∂P, ∀ᶠ m in atTop, (sampleQuartets X m ω).count q' < (sampleQuartets X m ω).count q := by
  filter_upwards [frequency_tendsto M hN X hind hid hlaw q,
    frequency_tendsto M hN X hind hid hlaw q'] with ω hq hq'
  filter_upwards [hq'.eventually_lt hq (by exact_mod_cast hlt)] with m hm
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp at hm
  · have hm' := (div_lt_div_iff_of_pos_right (by exact_mod_cast hpos : (0 : ℝ) < m)).mp hm
    exact_mod_cast hm'

/-- Events that hold, almost surely, for all large `m` have probability tending to 1. -/
theorem tendsto_measure_of_ae_eventually {P : Measure Ω} [IsProbabilityMeasure P]
    {A : ℕ → Set Ω} (h : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ω ∈ A m) :
    Tendsto (fun m => P (A m)) atTop (𝓝 1) := by
  -- the events "`A k` for all `k ≥ m`" increase to an event of probability 1
  let B : ℕ → Set Ω := fun m => {ω | ∀ k ≥ m, ω ∈ A k}
  have hmono : Monotone B := fun m m' hmm' ω hω k hk => hω k (hmm'.trans hk)
  have hunion : P (⋃ m, B m) = 1 := by
    refine le_antisymm prob_le_one ?_
    have hnull : P {ω | ¬ ∀ᶠ m in atTop, ω ∈ A m} = 0 := ae_iff.mp h
    calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
      _ ≤ P ((⋃ m, B m) ∪ {ω | ¬ ∀ᶠ m in atTop, ω ∈ A m}) := by
        refine measure_mono fun ω _ => ?_
        by_cases hω : ∀ᶠ m in atTop, ω ∈ A m
        · obtain ⟨m, hm⟩ := eventually_atTop.mp hω
          exact Or.inl (Set.mem_iUnion.mpr ⟨m, hm⟩)
        · exact Or.inr hω
      _ ≤ P (⋃ m, B m) + P {ω | ¬ ∀ᶠ m in atTop, ω ∈ A m} := measure_union_le _ _
      _ = P (⋃ m, B m) := by rw [hnull, add_zero]
  have hB : Tendsto (fun m => P (B m)) atTop (𝓝 1) := by
    rw [← hunion]
    exact tendsto_measure_iUnion_atTop hmono
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hB tendsto_const_nhds
    (fun m => measure_mono fun ω hω => hω m le_rfl) fun _ => prob_le_one

namespace SiteModel

omit [DecidableEq σ]

/-- Independent sites with the law of the model `M`: the product law on sequences of histories
(`Measure.infinitePi`), under which the coordinates are the sites. -/
noncomputable def sites (M : SiteModel N σ) (hN : N.RootedBinaryLevelOne) :
    Measure (ℕ → SiteHistory N σ) :=
  Measure.infinitePi fun _ => M.law hN

instance (M : SiteModel N σ) (hN : N.RootedBinaryLevelOne) :
    IsProbabilityMeasure (M.sites hN) := by
  unfold sites
  infer_instance

/-- Under `sites`, the coordinates are independent. -/
theorem sites_iIndepFun (M : SiteModel N σ) (hN : N.RootedBinaryLevelOne) :
    iIndepFun (fun n (ω : ℕ → SiteHistory N σ) => ω n) (M.sites hN) :=
  iIndepFun_infinitePi (P := fun _ => M.law hN) (X := fun _ => id) fun _ => measurable_id

/-- Under `sites`, each coordinate has the law of a site. -/
theorem sites_map (M : SiteModel N σ) (hN : N.RootedBinaryLevelOne) (n : ℕ) :
    (M.sites hN).map (fun ω => ω n) = M.law hN :=
  Measure.infinitePi_map_eval _ n

/-- Under `sites`, the coordinates are identically distributed. -/
theorem sites_identDistrib (M : SiteModel N σ) (hN : N.RootedBinaryLevelOne) (n : ℕ) :
    IdentDistrib (fun ω : ℕ → SiteHistory N σ => ω n) (fun ω => ω 0) (M.sites hN)
      (M.sites hN) where
  aemeasurable_fst := (measurable_pi_apply n).aemeasurable
  aemeasurable_snd := (measurable_pi_apply 0).aemeasurable
  map_eq := by rw [sites_map, sites_map]

/-- Under `sites`, the first coordinate has the law of a site. -/
theorem sites_law (M : SiteModel N σ) (hN : N.RootedBinaryLevelOne) :
    (M.sites hN).map (fun ω => ω 0) = M.law hN :=
  sites_map M hN 0

end SiteModel

end Camus.External
