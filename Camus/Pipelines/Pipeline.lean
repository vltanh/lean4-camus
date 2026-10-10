module

public import Camus.Pipelines.AstralTree
public import Camus.Pipelines.SNPCondition

/-!
# Section 3.2: the SNP pipeline as one statement

Section 3.2 of the paper runs a pipeline on an alignment of SNPs: the multiset `Q` of the quartets
of the SNPs is given to ASTRAL, which returns a tree `T` maximizing the quartet support score; `T`
"will be rooted using the outgroup and then passed to CAMUS", which returns a network built on `T`
optimal for `Q`. The section argues that, in the model of Warnow, Tabatabaee and Evans
(`External.SiteModel`), this pipeline returns the true network `N` with probability tending to 1
when some tree `t` displayed by `N` induces the most probable quartet on every four taxa. The
library proves the steps separately: ASTRAL's step (`astral_maximizer_tendsto`), the support of
`Q` (`External.support_tendsto`), and CAMUS's step, corrected (`snp_recovery_tendsto`). This file
composes them into one statement about the pipeline (`pipeline_tendsto`).

Let `N` be built on `t`, with the leaf of an outgroup `o` a child of the root of `t`, and assume
the paper's condition on `t` (`MostProbableQuartets`) and, as the correction of the report's E7
requires, that `N` is identifiable under inclusion and that CAMUS breaks ties toward the fewest
reticulations. Then, with probability tending to 1, the pipeline has an output (ASTRAL may return
`t`, and CAMUS may return `N` on it), and every output is isomorphic to `N`: every tree of maximum
quartet support score rooted at `o` (`AstralOutput`, `PhyloTree.RootedAt`) gives, through every
network that CAMUS may return on it (`CamusOutput`), a network isomorphic to `N`. Without
identifiability under inclusion the pipeline may fail, also with an outgroup and under every other
hypothesis of the paper's argument: in the deeper-donor example of
`Camus/Pipelines/InclusionOutgroup.lean`, with probability tending to 1, every tree of maximum
score rooted at the outgroup gives a network that CAMUS may return and that is not isomorphic to
the true network (`pipeline_outgroup_tendsto`, `pipeline_outgroup_meets_hypotheses`).

## Main results

* `AstralOutput`, `CamusOutput`: the trees that ASTRAL may return, and the networks that CAMUS may
  return with the tie-break toward the fewest reticulations.
* `pipeline_recovery`: the pipeline for one multiset `Q` whose support is `Q(N_r)` and in which the
  quartets of `t` are the most frequent.
* `pipeline_tendsto`: Section 3.2's pipeline in WTE's model, corrected.
* `pipeline_outgroup_tendsto`, `pipeline_outgroup_meets_hypotheses`: the pipeline fails in the
  deeper-donor example with an outgroup, which is not identifiable under inclusion.

## Proof (the paper's)

1. "ASTRAL will return t": for every four taxa, the quartet of `t` is the most frequent quartet on
   them, almost surely for all large numbers of sites (`ae_eventually_mostFrequent`), and then `t`
   has the largest quartet support score, and every tree with the largest score induces the
   quartets of `t` (`astralOutput_self`, `induced_eq_of_astralOutput`).
2. "This tree will be rooted using the outgroup and then passed to CAMUS": a tree rooted at the
   outgroup with the quartets of `t` is `t` up to the order of the children
   (`PhyloTree.rootedIso_of_induced_eq`), so the networks built on it are those built on `t`
   (`PhyloTree.RootedIso.camusOutput_iff`).
3. "According to the theory given in Warnow et al. (2025)", the support of `Q` is `Q(N_r)`, almost
   surely for all large numbers of sites (`ae_eventually_support`).
4. "CAMUS will add the correct reticulations and return N": false as stated (E7); with
   identifiability under inclusion and the tie-break, `recovery`.

Steps 1 and 3 hold together, almost surely for all large numbers of sites, so their probability
tends to 1 (`External.tendsto_measure_of_ae_eventually`); no measurability of the events is needed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace Camus

open DynamicProgramming

/-- Section 3.1: `T` is a tree that ASTRAL may return on the multiset `Q` of quartet trees and the
taxa `X`, since "it solves its optimization problem exactly": a well-labelled tree on `X` whose
quartet support score is the largest among the well-labelled trees on `X`. A `PhyloTree` stands
for its unrooted form here: the score depends only on the quartets it induces. -/
def AstralOutput (Q : Multiset Quartet) (X : Finset ℕ) (T : PhyloTree) : Prop :=
  T.WellLabelled ∧ T.taxa = X ∧ ∀ T' : PhyloTree, T'.WellLabelled → T'.taxa = X →
    quartetSupport Q T' ≤ quartetSupport Q T

/-- Sections 2.2 and 2.4: `P` is a network that CAMUS may return on the constraint tree `T` and
the multiset `Q`, with the tie-break toward the fewest reticulations: `P` is built on `T`, displays
as many quartets of `Q` (with multiplicity) as any network built on `T`, and has the fewest
reticulations among the networks built on `T` that do. For a fixed `T`, the number of quartets of
`Q` displayed and the number satisfied (Theorem 1) differ by the number of quartets of `Q` that `T`
induces, so both objectives have the same optimal networks. -/
def CamusOutput (Q : Multiset Quartet) (T : PhyloTree) (P : RootedNetwork) : Prop :=
  P.AnchoredExtension T ∧
    (∀ R : RootedNetwork, R.AnchoredExtension T →
      score Q (repertoire Q R) ≤ score Q (repertoire Q P)) ∧
    ∀ R : RootedNetwork, R.AnchoredExtension T →
      (∀ R' : RootedNetwork, R'.AnchoredExtension T →
        score Q (repertoire Q R') ≤ score Q (repertoire Q R)) →
      P.reticulationCount ≤ R.reticulationCount

/-- CAMUS's problem is the same on two trees with the same clades, up to the order of the
children: the same networks are built on them (`RootedIso.anchoredExtension_iff`). -/
theorem PhyloTree.RootedIso.camusOutput_iff {T T' : PhyloTree} (h : T.RootedIso T')
    (Q : Multiset Quartet) (P : RootedNetwork) : CamusOutput Q T P ↔ CamusOutput Q T' P := by
  simp only [CamusOutput, h.anchoredExtension_iff]

/-- The quartet support score of a tree depends only on the quartets it induces. -/
theorem quartetSupport_congr (Q : Multiset Quartet) {T T' : PhyloTree}
    (h : ∀ q : Quartet, q.induced T = q.induced T') : quartetSupport Q T = quartetSupport Q T' := by
  unfold quartetSupport
  simp only [h]

/-- Section 3.2: if, for every four taxa of `t`, the quartet that `t` induces has more copies in
`Q` than the two other quartets on them, then every tree that ASTRAL may return on the taxa of `t`
induces the quartets of `t` (`quartetSupport_lt`). -/
theorem induced_eq_of_astralOutput {Q : Multiset Quartet} {t T : PhyloTree} (ht : t.WellLabelled)
    (hfreq : ∀ q : Quartet, q.induced t = true → ∀ s : Fin 3, s ≠ q.split →
      Q.count (q.key.quartet s) < Q.count q)
    (hT : AstralOutput Q t.taxa T) (q : Quartet) : q.induced T = q.induced t := by
  obtain ⟨hTw, htaxa, hmax⟩ := hT
  by_contra hq
  exact absurd (hmax t ht rfl) (not_le.mpr (quartetSupport_lt Q t T ht hTw htaxa hfreq ⟨q, hq⟩))

/-- Section 3.2: under the same condition, ASTRAL may return `t`: every tree on its taxa has at
most its score, with equality exactly for the trees that induce its quartets. -/
theorem astralOutput_self {Q : Multiset Quartet} {t : PhyloTree} (ht : t.WellLabelled)
    (hfreq : ∀ q : Quartet, q.induced t = true → ∀ s : Fin 3, s ≠ q.split →
      Q.count (q.key.quartet s) < Q.count q) :
    AstralOutput Q t.taxa t := by
  refine ⟨ht, rfl, fun T hT htaxa => ?_⟩
  by_cases hdiff : ∃ q : Quartet, q.induced T ≠ q.induced t
  · exact (quartetSupport_lt Q t T ht hT htaxa hfreq hdiff).le
  · push Not at hdiff
    rw [quartetSupport_congr Q hdiff]

/-- If the quartets of `Q` are exactly those displayed by `N`, every network that displays as
many quartets of `Q` as `N` displays every quartet that `N` displays. -/
theorem displays_of_optimal {N : RootedNetwork} {Q : Multiset Quartet}
    (hQ : ∀ q, q ∈ Q ↔ N.DisplaysQuartet q) {R : RootedNetwork}
    (hR : score Q (repertoire Q N) ≤ score Q (repertoire Q R)) :
    ∀ q, N.DisplaysQuartet q → R.DisplaysQuartet q := by
  classical
  have hNscore : score Q (repertoire Q N) = Q.card := by
    apply (score_eq_card_iff Q _).mpr
    intro q hq
    simp only [repertoire, Finset.mem_filter]
    exact ⟨hq, (hQ q).mp (Multiset.mem_toFinset.mp hq)⟩
  have hRscore : score Q (repertoire Q R) = Q.card :=
    le_antisymm (score_le_card _ _) (hNscore ▸ hR)
  intro q hq
  have hmem := (score_eq_card_iff Q _).mp hRscore (Multiset.mem_toFinset.mpr ((hQ q).mpr hq))
  simp only [repertoire, Finset.mem_filter] at hmem
  exact hmem.2

/-- Section 3.2, the pipeline for one multiset `Q`. Let `N` be built on `t`, rooted at the
outgroup `o`, and identifiable under inclusion (as in `recovery`). Let the quartets of `Q` be
exactly those displayed by `N`, and let the quartet that `t` induces on every four of its taxa
have more copies in `Q` than the two other quartets on them. Then the pipeline has an output:
ASTRAL may return `t`, and CAMUS may return `N` on `t`. And every output is isomorphic to `N`:
for every tree `T` that ASTRAL may return, rooted at `o`, every network that CAMUS may return
on `T` is isomorphic to `N`.

Departure from the paper: the paper concludes that CAMUS returns `N` because `N` "is the unique
network that can satisfy all the quartets in Q(Nr)", which is false (the report's E7);
identifiability under inclusion and the tie-break toward the fewest reticulations replace that
step, as in `recovery`. -/
theorem pipeline_recovery (t : PhyloTree) (ht : t.WellLabelled) {o : ℕ} (hto : t.RootedAt o)
    (N : RootedNetwork) (hN : N.AnchoredExtension t)
    (identifiable : ∀ P : RootedNetwork, P.AnchoredExtension t →
      (∀ q, N.DisplaysQuartet q → P.DisplaysQuartet q) →
      P.reticulationCount ≤ N.reticulationCount → Nonempty (P.Iso N))
    (Q : Multiset Quartet)
    (hfreq : ∀ q : Quartet, q.induced t = true → ∀ s : Fin 3, s ≠ q.split →
      Q.count (q.key.quartet s) < Q.count q)
    (hQ : ∀ q, q ∈ Q ↔ N.DisplaysQuartet q) :
    (AstralOutput Q N.taxa t ∧ CamusOutput Q t N) ∧
      ∀ T : PhyloTree, AstralOutput Q N.taxa T → T.RootedAt o →
        ∀ P : RootedNetwork, CamusOutput Q T P → Nonempty (P.Iso N) := by
  classical
  have hNt : N.taxa = t.taxa := by
    obtain ⟨S, ⟨H⟩⟩ := hN.2
    exact H.taxa_preserved
  rw [hNt]
  -- `N` displays every quartet of `Q`, so it is optimal
  have hNopt : ∀ R : RootedNetwork, R.AnchoredExtension t →
      score Q (repertoire Q R) ≤ score Q (repertoire Q N) := by
    intro R _
    have hNscore : score Q (repertoire Q N) = Q.card := by
      apply (score_eq_card_iff Q _).mpr
      intro q hq
      simp only [repertoire, Finset.mem_filter]
      exact ⟨hq, (hQ q).mp (Multiset.mem_toFinset.mp hq)⟩
    exact hNscore ▸ score_le_card _ _
  -- and has the fewest reticulations among the optimal networks: an optimal network with fewer
  -- would display every quartet that `N` displays, and so be isomorphic to `N`
  have hNcamus : CamusOutput Q t N := by
    refine ⟨hN, hNopt, fun R hR hRopt => ?_⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨i⟩ := identifiable R hR (displays_of_optimal hQ (hRopt N hN)) hlt.le
    have := i.reticulationCount_eq hR.1 hN.1
    omega
  refine ⟨⟨astralOutput_self ht hfreq, hNcamus⟩, fun T hT hTo P hP => ?_⟩
  -- step 1: the tree returned by ASTRAL induces the quartets of `t`
  have hq := induced_eq_of_astralOutput ht hfreq hT
  -- step 2: rooted at the outgroup, it is `t` up to the order of the children, so `P` is a
  -- network that CAMUS may return on `t`
  have hiso : T.RootedIso t := PhyloTree.rootedIso_of_induced_eq hT.1 ht hT.2.1 hq hTo hto
  obtain ⟨hPt, hPopt, hPfew⟩ := (hiso.camusOutput_iff Q P).mp hP
  -- step 3, corrected: `recovery`
  exact recovery t N hN Q hQ identifiable P hPt hPopt hPfew

variable {N : RootedNetwork} {σ : Type*} [Fintype σ] [DecidableEq σ] {Ω : Type*}
  [MeasurableSpace Ω]

/-- Section 3.2: "for every four species, the most frequently observed quartet tree will be the
most probable quartet tree". Under `MostProbableQuartets`, almost surely, for all large numbers
`m` of sites, the quartet that `t` induces on every four of its taxa has more copies in `Q_m` than
the two other quartets on them. -/
theorem ae_eventually_mostFrequent (M : External.SiteModel N σ) (hN : N.RootedBinaryLevelOne)
    (t : PhyloTree) (hcond : MostProbableQuartets M t) {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → External.SiteHistory N σ) (hind : iIndepFun X P)
    (hid : ∀ n, IdentDistrib (X n) (X 0) P P) (hlaw : P.map (X 0) = M.law hN) :
    ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ∀ q : Quartet, q.induced t = true → ∀ s : Fin 3, s ≠ q.split →
      (External.sampleQuartets X m ω).count (q.key.quartet s) <
        (External.sampleQuartets X m ω).count q := by
  classical
  let K := (Quartet.onTaxa t.taxa).filter fun q => q.induced t = true
  let S : Quartet → Finset (Fin 3) := fun q => Finset.univ.filter (· ≠ q.split)
  have hK : ∀ q : Quartet, q.induced t = true → q ∈ K := by
    intro q hq
    refine Finset.mem_filter.mpr ⟨Quartet.mem_onTaxa.mpr ?_, hq⟩
    simp only [Quartet.induced, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.1
  -- each of the finitely many comparisons holds eventually, almost surely, by the strong law
  have hae : ∀ᵐ ω ∂P, ∀ q ∈ K, ∀ s ∈ S q, ∀ᶠ m in atTop,
      (External.sampleQuartets X m ω).count (q.key.quartet s) <
        (External.sampleQuartets X m ω).count q := by
    rw [Filter.eventually_all_finset]
    intro q hq
    rw [Filter.eventually_all_finset]
    intro s hs
    exact External.eventually_count_lt M hN X hind hid hlaw
      (hcond q (Finset.mem_filter.mp hq).2 s (Finset.mem_filter.mp hs).2)
  filter_upwards [hae] with ω hω
  have hev : ∀ᶠ m in atTop, ∀ q ∈ K, ∀ s ∈ S q,
      (External.sampleQuartets X m ω).count (q.key.quartet s) <
        (External.sampleQuartets X m ω).count q := by
    rw [Filter.eventually_all_finset]
    intro q hq
    rw [Filter.eventually_all_finset]
    exact hω q hq
  filter_upwards [hev] with m hm q hq s hs
  exact hm q (hK q hq) s (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩)

/-- Section 3.2, "according to the theory given in Warnow et al. (2025)": almost surely, for all
large numbers `m` of sites, the quartets of `Q_m` are exactly those displayed by `N`. Every
quartet displayed by `N` is contributed by a site with positive probability
(`External.SiteModel.quartetProb_pos`), so its frequency in `Q_m` converges almost surely to a
positive limit (`External.frequency_tendsto`). -/
theorem ae_eventually_support (M : External.SiteModel N σ) (hN : N.RootedBinaryLevelOne)
    [Nontrivial σ] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → External.SiteHistory N σ) (hind : iIndepFun X P)
    (hid : ∀ n, IdentDistrib (X n) (X 0) P P) (hlaw : P.map (X 0) = M.law hN) :
    ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ∀ q, q ∈ External.sampleQuartets X m ω ↔ N.DisplaysQuartet q := by
  classical
  let D := (Quartet.onTaxa N.taxa).filter N.DisplaysQuartet
  -- each of the finitely many quartets displayed by `N` is eventually in `Q_m`
  have hae : ∀ᵐ ω ∂P, ∀ q ∈ D, ∀ᶠ m in atTop, q ∈ External.sampleQuartets X m ω := by
    rw [Filter.eventually_all_finset]
    intro q hq
    have hpos : (0 : ℝ) < M.quartetProb q := by
      exact_mod_cast M.quartetProb_pos hN (Finset.mem_filter.mp hq).2
    filter_upwards [External.frequency_tendsto M hN X hind hid hlaw q] with ω hω
    filter_upwards [hω.eventually (lt_mem_nhds hpos)] with m hm
    by_contra hnot
    rw [Multiset.count_eq_zero.mpr hnot] at hm
    simp at hm
  filter_upwards [hae] with ω hω
  filter_upwards [(Filter.eventually_all_finset D).mpr hω] with m hm q
  -- every quartet of `Q_m` is displayed by `N`
  refine ⟨External.displays_of_mem_sampleQuartets hN, fun hq => ?_⟩
  exact hm q (Finset.mem_filter.mpr ⟨Quartet.mem_onTaxa.mpr hq.1, hq⟩)

/-- Section 3.2, the SNP pipeline in WTE's model, corrected. Let the true network `N` be built on
the tree `t`, with the leaf of the outgroup `o` a child of the root of `t`; let `t` induce the
most probable quartet on every four taxa (`MostProbableQuartets`), and let `N` be identifiable
under inclusion (as in `recovery`). Let the sites `X 0, X 1, ...` be independent with the law of a
site under a model `M` on `N` with at least two states, and `Q_m` the multiset of the quartets of
the SNPs among the first `m` sites. Then the probability of the following event tends to 1: the
pipeline has an output (ASTRAL may return `t` on `Q_m` and the taxa of `N`, and CAMUS may return
`N` on `t`), and for every tree `T` that ASTRAL may return, rooted at `o`, every network that
CAMUS may return on `T` is isomorphic to `N`.

Departure from the paper: the paper concludes that CAMUS returns `N` because `N` "is the unique
network that can satisfy all the quartets in Q(Nr)", which is false (the report's E7,
`pipeline_outgroup_tendsto`); identifiability under inclusion and the tie-break toward the fewest
reticulations replace that step, as in `recovery`. "ASTRAL will return t" is read for every tree
of maximum score: such a tree, rooted at the outgroup, is `t` up to the order of the children,
which gives the same networks. -/
theorem pipeline_tendsto [Nontrivial σ] (t : PhyloTree) (ht : t.WellLabelled) {o : ℕ}
    (hto : t.RootedAt o) (N : RootedNetwork) (hN : N.AnchoredExtension t)
    (identifiable : ∀ P : RootedNetwork, P.AnchoredExtension t →
      (∀ q, N.DisplaysQuartet q → P.DisplaysQuartet q) →
      P.reticulationCount ≤ N.reticulationCount → Nonempty (P.Iso N))
    (M : External.SiteModel N σ) (hcond : MostProbableQuartets M t)
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → External.SiteHistory N σ)
    (hind : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (hlaw : μ.map (X 0) = M.law hN.1) :
    Tendsto (fun m => μ {ω |
      (AstralOutput (External.sampleQuartets X m ω) N.taxa t ∧
        CamusOutput (External.sampleQuartets X m ω) t N) ∧
      ∀ T : PhyloTree, AstralOutput (External.sampleQuartets X m ω) N.taxa T → T.RootedAt o →
        ∀ P : RootedNetwork, CamusOutput (External.sampleQuartets X m ω) T P →
          Nonempty (P.Iso N)}) atTop (𝓝 1) := by
  refine External.tendsto_measure_of_ae_eventually ?_
  -- steps 1 and 3 hold together, almost surely for all large `m`
  filter_upwards [ae_eventually_mostFrequent M hN.1 t hcond X hind hid hlaw,
    ae_eventually_support M hN.1 X hind hid hlaw] with ω hfreq hsupp
  filter_upwards [hfreq, hsupp] with m hm hm'
  -- on that event, the pipeline for one multiset
  exact pipeline_recovery t ht hto N hN identifiable _ hm hm'

namespace Counterexamples

/-- The tree `(O,((A,B),(C,(F,(D,E)))))` is rooted at the outgroup `O = 6`. -/
theorem outgroupTree_rootedAt : outgroupTree.RootedAt 6 := ⟨false, outgroupTree_child⟩

/-- The taxa of `outgroupShallowNet` are those of its tree. -/
theorem outgroupShallowNet_taxa : outgroupShallowNet.taxa = outgroupTree.taxa := rfl

/-- The deeper-donor example with an outgroup is not identifiable under inclusion (the hypothesis
`identifiable` of `pipeline_tendsto`): `outgroupDeepNet` is built on the tree, displays every
quartet that `outgroupShallowNet` displays, has one reticulation as it does, and is not isomorphic
to it. -/
theorem outgroup_not_identifiable :
    ¬ ∀ P : RootedNetwork, P.AnchoredExtension outgroupTree →
      (∀ q, outgroupShallowNet.DisplaysQuartet q → P.DisplaysQuartet q) →
      P.reticulationCount ≤ outgroupShallowNet.reticulationCount →
      Nonempty (P.Iso outgroupShallowNet) := by
  intro h
  obtain ⟨i⟩ := h outgroupDeepNet outgroupDeepNet_anchored outgroup_subset_deep (by
    rw [Realization.single_reticulationCount outgroupDeepPair_mem,
      Realization.single_reticulationCount outgroupShallowPair_mem])
  exact outgroupDeep_not_iso.false i

/-- The pipeline on the deeper-donor example, for one multiset `Q`: if the quartets of `Q` are
exactly those displayed by `outgroupShallowNet`, and the quartet that the tree induces on every
four taxa has more copies in `Q` than the two other quartets on them, then ASTRAL may return the
tree, and for every tree `T` that ASTRAL may return, rooted at the outgroup, CAMUS may return
`outgroupDeepNet` on `T`, which is not isomorphic to `outgroupShallowNet`. -/
theorem outgroup_pipeline (Q : Multiset Quartet)
    (hfreq : ∀ q : Quartet, q.induced outgroupTree = true → ∀ s : Fin 3, s ≠ q.split →
      Q.count (q.key.quartet s) < Q.count q)
    (hQ : ∀ q, q ∈ Q ↔ outgroupShallowNet.DisplaysQuartet q) :
    AstralOutput Q outgroupShallowNet.taxa outgroupTree ∧
      ∀ T : PhyloTree, AstralOutput Q outgroupShallowNet.taxa T → T.RootedAt 6 →
        CamusOutput Q T outgroupDeepNet ∧ IsEmpty (outgroupDeepNet.Iso outgroupShallowNet) := by
  rw [outgroupShallowNet_taxa]
  refine ⟨astralOutput_self outgroupTree_wellLabelled hfreq, fun T hT hTo => ⟨?_,
    outgroupDeep_not_iso⟩⟩
  -- the tree returned by ASTRAL, rooted at the outgroup, is the tree up to the order of the
  -- children, on which CAMUS may return the deeper donor
  have hiso : T.RootedIso outgroupTree := PhyloTree.rootedIso_of_induced_eq hT.1
    outgroupTree_wellLabelled hT.2.1
    (induced_eq_of_astralOutput outgroupTree_wellLabelled hfreq hT) hTo outgroupTree_rootedAt
  obtain ⟨hopt, hfew⟩ := outgroupDeep_optimal_fewest Q hQ
  exact (hiso.camusOutput_iff Q _).mpr ⟨outgroupDeepNet_anchored, hopt, hfew⟩

end Counterexamples

/-- Section 3.2, the report's E7 for the whole pipeline in WTE's model, with an outgroup. Take for
the true network `Counterexamples.outgroupShallowNet`, built on the tree
`(O,((A,B),(C,(F,(D,E)))))` rooted at the outgroup `O = 6`, any site model on it with at least two
states under which the tree induces the most probable quartet on every four taxa, and independent
sites with its law. Then the probability of the following event tends to 1: ASTRAL may return the
tree, and for every tree `T` that ASTRAL may return, rooted at the outgroup, CAMUS may return
`Counterexamples.outgroupDeepNet` on `T`, which is not isomorphic to the true network. The only
hypothesis of `pipeline_tendsto` that fails is identifiability under inclusion
(`Counterexamples.outgroup_not_identifiable`). -/
theorem pipeline_outgroup_tendsto [Nontrivial σ]
    (M : External.SiteModel Counterexamples.outgroupShallowNet σ)
    (hcond : MostProbableQuartets M Counterexamples.outgroupTree) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → External.SiteHistory Counterexamples.outgroupShallowNet σ)
    (hind : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (hlaw : μ.map (X 0) = M.law Counterexamples.outgroupShallowNet_anchored.1) :
    Tendsto (fun m => μ {ω |
      AstralOutput (External.sampleQuartets X m ω) Counterexamples.outgroupShallowNet.taxa
          Counterexamples.outgroupTree ∧
        ∀ T : PhyloTree, AstralOutput (External.sampleQuartets X m ω)
            Counterexamples.outgroupShallowNet.taxa T → T.RootedAt 6 →
          CamusOutput (External.sampleQuartets X m ω) T Counterexamples.outgroupDeepNet ∧
            IsEmpty (Counterexamples.outgroupDeepNet.Iso Counterexamples.outgroupShallowNet)})
      atTop (𝓝 1) := by
  refine External.tendsto_measure_of_ae_eventually ?_
  filter_upwards [ae_eventually_mostFrequent M Counterexamples.outgroupShallowNet_anchored.1
      Counterexamples.outgroupTree hcond X hind hid hlaw,
    ae_eventually_support M Counterexamples.outgroupShallowNet_anchored.1 X hind hid hlaw]
    with ω hfreq hsupp
  filter_upwards [hfreq, hsupp] with m hm hm'
  exact Counterexamples.outgroup_pipeline _ hm hm'

/-- Section 3.2, the report's E7 for the whole pipeline, under every hypothesis of the paper's
argument but identifiability under inclusion: for some site model with two states on
`Counterexamples.outgroupShallowNet`, the tree `(O,((A,B),(C,(F,(D,E)))))`, rooted at the outgroup
`O = 6`, induces the most probable quartet on every four taxa, and, for independent sites with the
law of this model (`External.SiteModel.sites`), with probability tending to 1, ASTRAL may return
the tree, and on every tree that ASTRAL may return, rooted at the outgroup, CAMUS may return
`Counterexamples.outgroupDeepNet`, which is not isomorphic to the true network. -/
theorem pipeline_outgroup_meets_hypotheses :
    ∃ M : External.SiteModel Counterexamples.outgroupShallowNet Bool,
      MostProbableQuartets M Counterexamples.outgroupTree ∧
      Tendsto (fun m => M.sites Counterexamples.outgroupShallowNet_anchored.1 {ω |
        AstralOutput (External.sampleQuartets (fun n ω => ω n) m ω)
            Counterexamples.outgroupShallowNet.taxa Counterexamples.outgroupTree ∧
          ∀ T : PhyloTree, AstralOutput (External.sampleQuartets (fun n ω => ω n) m ω)
              Counterexamples.outgroupShallowNet.taxa T → T.RootedAt 6 →
            CamusOutput (External.sampleQuartets (fun n ω => ω n) m ω) T
                Counterexamples.outgroupDeepNet ∧
              IsEmpty (Counterexamples.outgroupDeepNet.Iso Counterexamples.outgroupShallowNet)})
        atTop (𝓝 1) := by
  obtain ⟨M, hM⟩ : ∃ M : External.SiteModel Counterexamples.outgroupShallowNet Bool,
      MostProbableQuartets M Counterexamples.outgroupTree :=
    Realization.exists_mostProbable Counterexamples.outgroupTree
      Counterexamples.outgroupTree_wellLabelled {Counterexamples.outgroupShallowPair}
      (Realization.single_separated Counterexamples.outgroupShallowPair_mem)
  exact ⟨M, hM, pipeline_outgroup_tendsto M hM
    (fun n (ω : ℕ → External.SiteHistory Counterexamples.outgroupShallowNet Bool) => ω n)
    (M.sites_iIndepFun Counterexamples.outgroupShallowNet_anchored.1)
    (M.sites_identDistrib Counterexamples.outgroupShallowNet_anchored.1)
    (M.sites_law Counterexamples.outgroupShallowNet_anchored.1)⟩

end Camus
