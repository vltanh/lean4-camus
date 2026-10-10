module

public import Camus.External.WarnowTabatabaeeEvans.Sampling
public import Camus.Pipelines.Algorithm1

/-!
# Section 3.1 and the first step of Section 3.2: ASTRAL

Section 3.1 of the paper describes ASTRAL: given a multiset `Q` of quartet trees (in the SNP
pipeline of Section 3.2, the quartets of the SNPs, each treated as a gene tree), ASTRAL returns a
tree `T` on the taxa that maximizes the quartet support score score(T) = ∑_{q ∈ Q(T)} w(q),
where w(q) is the number of copies of `q` in `Q` (`quartetSupport`). The first step of the
consistency argument of Section 3.2 reads: "as the number of sites increases, for every four
species, the most frequently observed quartet tree will be the most probable quartet tree with
probability converging to 1, and so the quartet support score of t will be larger than the score
of any other tree. When the quartet support score for t is larger than any other tree's quartet
support, ASTRAL will return t since it solves its optimization problem exactly."

This file proves that step inside the single site model of Warnow, Tabatabaee and Evans
(`External.SiteModel`). A well-labelled tree induces exactly one quartet on each set of four of
its taxa (`PhyloTree.induced_existsUnique`). Under the paper's condition that, for every four taxa
of `t`, the quartet that `t` induces is strictly the most probable quartet on them, per site
(`MostProbableQuartets`), the probability that the score of `t` is larger than the score of every
well-labelled tree on the same taxa that induces a different set of quartets tends to 1
(`astral_tendsto`); so every tree of maximum score induces the quartets of `t`
(`astral_maximizer_tendsto`). That such a tree, rooted at the outgroup, is `t` itself is the
classical fact that the quartets of a binary tree determine it; it is not formalized here.

Trees are rooted (`PhyloTree`) and stand for their unrooted forms: `Quartet.induced` computes
`Q(T)` of the unrooted tree, and every unrooted binary tree is the unrooted form of a rooted one,
so maximizing over well-labelled `PhyloTree`s on the taxa is ASTRAL's problem.

## Main results

* `quartetSupport`: the quartet support score of Section 3.1.
* `PhyloTree.induced_existsUnique`: a well-labelled tree induces exactly one quartet on each set
  of four of its taxa.
* `quartetSupport_lt`: if, for every four taxa of `t`, the quartet that `t` induces has more
  copies in `Q` than the two other quartets on them, then `t` has a larger score than every
  well-labelled tree on the same taxa with a different set of quartets.
* `MostProbableQuartets`: the paper's condition on `t`.
* `astral_tendsto`, `astral_maximizer_tendsto`: the first step of Section 3.2, in probability.

## Proof (the paper's)

1. For every four taxa, the quartet that `t` induces is the most frequent quartet on them, with
   probability tending to 1: by the strong law of large numbers each frequency converges to the
   per-site probability (`External.eventually_count_lt`), and there are finitely many sets of four
   taxa (`External.tendsto_measure_of_ae_eventually`).
2. Then the score of `t` is larger than the score of any other tree: the score of a tree is the
   sum, over the sets of four taxa, of the number of copies of the one quartet it induces on them
   (`quartetSupport_eq_sum_keys`), and the terms of `t` are at least those of any tree, and larger
   where the two trees differ (`quartetSupport_lt`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Camus

/-- **Section 3.1**: the quartet support score of the tree `T` for the multiset `Q`,
score(T) = ∑_{q ∈ Q(T)} w(q), where w(q) is the number of copies of `q` in `Q`: the number of
quartets of `Q`, counted with multiplicity, induced by `T` (`quartetSupport_eq_card`). -/
noncomputable def quartetSupport (Q : Multiset Quartet) (T : PhyloTree) : ℕ :=
  ∑ q ∈ Q.toFinset.filter (fun q => q.induced T = true), Q.count q

/-- The quartet support score counts the quartets of `Q` induced by `T`, with multiplicity. -/
theorem quartetSupport_eq_card (Q : Multiset Quartet) (T : PhyloTree) :
    quartetSupport Q T = (Q.filter (fun q => q.induced T = true)).card := by
  classical
  have h := score_eq_sum Q (Q.toFinset.filter (fun q => q.induced T = true))
  rw [quartetSupport, ← h, score]
  congr 1
  refine Multiset.filter_congr fun q hq => ?_
  simp [Finset.mem_filter, Multiset.mem_toFinset.mpr hq]

namespace PhyloTree

/-- The clades of `t` are sets of taxa of `t`. -/
theorem clade_subset_taxa (t : PhyloTree) : ∀ C ∈ t.clades, C ⊆ t.taxa := by
  induction t with
  | leaf a =>
    intro C hC
    simp only [clades, List.mem_singleton] at hC
    subst hC
    simp [taxa, labels]
  | fork l r ihl ihr =>
    intro C hC
    have hlt : l.taxa ⊆ (fork l r).taxa := by
      simp [taxa, labels, List.toFinset_append, Finset.subset_union_left]
    have hrt : r.taxa ⊆ (fork l r).taxa := by
      simp [taxa, labels, List.toFinset_append, Finset.subset_union_right]
    simp only [clades, List.mem_cons, List.mem_append] at hC
    rcases hC with rfl | hC | hC
    · simp [taxa, labels, List.toFinset_append]
    · exact (ihl C hC).trans hlt
    · exact (ihr C hC).trans hrt

/-- The set of all taxa of `t` is a clade of `t`, the clade of the root. -/
theorem taxa_mem_clades (t : PhyloTree) : t.taxa ∈ t.clades := by
  cases t with
  | leaf a => simp [taxa, labels, clades]
  | fork l r => simp [taxa, labels, clades, List.toFinset_append]

/-- Every set `F` of at least two taxa of `t` meets some clade of `t` in exactly two taxa: the
lowest clade containing two of them. -/
theorem exists_clade_two (t : PhyloTree) :
    ∀ F ⊆ t.taxa, 2 ≤ F.card → ∃ C ∈ t.clades, (F.filter (· ∈ C)).card = 2 := by
  classical
  induction t with
  | leaf a =>
    intro F hF h2
    have := Finset.card_le_card hF
    simp [taxa, labels] at this
    omega
  | fork l r ihl ihr =>
    intro F hF h2
    by_cases hl : 2 ≤ (F.filter (· ∈ l.taxa)).card
    · obtain ⟨C, hC, hcard⟩ := ihl _ (fun x hx => (Finset.mem_filter.mp hx).2) hl
      refine ⟨C, List.mem_cons_of_mem _ (List.mem_append_left _ hC), ?_⟩
      rw [Finset.filter_filter] at hcard
      rw [← hcard]
      congr 1
      exact Finset.filter_congr fun x _ =>
        ⟨fun h => ⟨l.clade_subset_taxa C hC h, h⟩, fun h => h.2⟩
    by_cases hr : 2 ≤ (F.filter (· ∈ r.taxa)).card
    · obtain ⟨C, hC, hcard⟩ := ihr _ (fun x hx => (Finset.mem_filter.mp hx).2) hr
      refine ⟨C, List.mem_cons_of_mem _ (List.mem_append_right _ hC), ?_⟩
      rw [Finset.filter_filter] at hcard
      rw [← hcard]
      congr 1
      exact Finset.filter_congr fun x _ =>
        ⟨fun h => ⟨r.clade_subset_taxa C hC h, h⟩, fun h => h.2⟩
    -- neither child contains two taxa of `F`, so `F` has two taxa and the root's clade works
    refine ⟨(fork l r).taxa, taxa_mem_clades _, ?_⟩
    have hsplit : F = F.filter (· ∈ l.taxa) ∪ F.filter (· ∈ r.taxa) := by
      rw [← Finset.filter_or]
      refine (Finset.filter_true_of_mem fun x hx => ?_).symm
      have := hF hx
      simpa [taxa, labels, List.toFinset_append] using this
    have hle := Finset.card_union_le (F.filter (· ∈ l.taxa)) (F.filter (· ∈ r.taxa))
    rw [← hsplit] at hle
    rw [Finset.filter_true_of_mem fun x hx => hF hx]
    omega

/-- The clades of a well-labelled tree are laminar: two clades are nested or disjoint. -/
theorem clades_laminar (t : PhyloTree) (ht : t.WellLabelled) :
    ∀ A ∈ t.clades, ∀ B ∈ t.clades, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  induction t with
  | leaf a =>
    intro A hA B hB
    simp only [clades, List.mem_singleton] at hA hB
    subst hA hB
    exact Or.inl (Finset.Subset.refl _)
  | fork l r ihl ihr =>
    have hnd : (l.labels ++ r.labels).Nodup := ht
    obtain ⟨hl, hr, hlr⟩ := List.nodup_append.mp hnd
    have hdisj : Disjoint l.taxa r.taxa := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact hlr a (List.mem_toFinset.mp ha) a (List.mem_toFinset.mp hb) rfl
    have hroot : (l.taxa ∪ r.taxa) = (fork l r).taxa := by
      simp [taxa, labels, List.toFinset_append]
    intro A hA B hB
    simp only [clades, List.mem_cons, List.mem_append] at hA hB
    rcases hA with rfl | hA | hA
    · refine Or.inr (Or.inl ?_)
      rw [hroot]
      exact (fork l r).clade_subset_taxa B (by
        rcases hB with rfl | hB | hB
        · simp [clades]
        · simp [clades, hB]
        · simp [clades, hB])
    · rcases hB with rfl | hB | hB
      · refine Or.inl ((l.clade_subset_taxa A hA).trans ?_)
        exact Finset.subset_union_left
      · exact ihl hl A hA B hB
      · exact Or.inr (Or.inr (hdisj.mono (l.clade_subset_taxa A hA)
          (r.clade_subset_taxa B hB)))
    · rcases hB with rfl | hB | hB
      · refine Or.inl ((r.clade_subset_taxa A hA).trans ?_)
        exact Finset.subset_union_right
      · exact Or.inr (Or.inr (hdisj.symm.mono (r.clade_subset_taxa A hA)
          (l.clade_subset_taxa B hB)))
      · exact ihr hr A hA B hB

end PhyloTree

namespace Quartet

/-- Which of the four taxa `x, y, z, w` of a quartet (in increasing order) a set must contain to
cut the quartet with topology `s`: `x, y` and not `z, w` or the reverse for ab|cd (`s = 0`), and
similarly for ac|bd (`s = 1`) and ad|bc (`s = 2`). -/
def splitPattern (s : Fin 3) (x y z w : Bool) : Bool :=
  if s = 0 then (x && y && !z && !w) || (!x && !y && z && w)
  else if s = 1 then (x && !y && z && !w) || (!x && y && !z && w)
  else (x && !y && !z && w) || (!x && y && z && !w)

/-- A set cuts a quartet if and only if it contains the four taxa in the pattern of the quartet's
topology. -/
theorem cutBy_eq_splitPattern (q : Quartet) (C : Finset ℕ) :
    q.cutBy C = splitPattern q.split (decide (q.a ∈ C)) (decide (q.b ∈ C))
      (decide (q.c ∈ C)) (decide (q.d ∈ C)) := by
  unfold cutBy sides splitPattern
  by_cases h0 : q.split = 0
  · simp only [h0, ite_true]
    by_cases ha : q.a ∈ C <;> by_cases hb : q.b ∈ C <;> by_cases hc : q.c ∈ C <;>
      by_cases hd : q.d ∈ C <;>
      simp [ha, hb, hc, hd, Finset.insert_subset_iff, Finset.disjoint_left]
  by_cases h1 : q.split = 1
  · simp only [h1, ite_true, show (1 : Fin 3) ≠ 0 by decide, ite_false]
    by_cases ha : q.a ∈ C <;> by_cases hb : q.b ∈ C <;> by_cases hc : q.c ∈ C <;>
      by_cases hd : q.d ∈ C <;>
      simp [ha, hb, hc, hd, Finset.insert_subset_iff, Finset.disjoint_left]
  · simp only [h0, h1, ite_false]
    by_cases ha : q.a ∈ C <;> by_cases hb : q.b ∈ C <;> by_cases hc : q.c ∈ C <;>
      by_cases hd : q.d ∈ C <;>
      simp [ha, hb, hc, hd, Finset.insert_subset_iff, Finset.disjoint_left]

/-- The memberships `x, y, z, w` and `x', y', z', w'` of four taxa in two sets are those of
nested or disjoint sets. -/
def laminarPattern (x y z w x' y' z' w' : Bool) : Bool :=
  ((!x || x') && (!y || y') && (!z || z') && (!w || w')) ||
  ((!x' || x) && (!y' || y) && (!z' || z) && (!w' || w)) ||
  (!(x && x') && !(y && y') && !(z && z') && !(w && w'))

/-- Two sets that cut quartets of different topologies on the same four taxa are neither nested
nor disjoint. -/
theorem splitPattern_laminar : ∀ (s s' : Fin 3) (x y z w x' y' z' w' : Bool),
    splitPattern s x y z w = true → splitPattern s' x' y' z' w' = true →
    laminarPattern x y z w x' y' z' w' = true → s = s' := by
  decide

/-- Nested or disjoint sets give a laminar membership pattern on any four taxa. -/
theorem laminarPattern_of_laminar {A B : Finset ℕ} (h : A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (a b c d : ℕ) :
    laminarPattern (decide (a ∈ A)) (decide (b ∈ A)) (decide (c ∈ A)) (decide (d ∈ A))
      (decide (a ∈ B)) (decide (b ∈ B)) (decide (c ∈ B)) (decide (d ∈ B)) = true := by
  unfold laminarPattern
  rcases h with h | h | h
  · have hx : ∀ x, (!decide (x ∈ A) || decide (x ∈ B)) = true := fun x => by
      by_cases hx : x ∈ A <;> simp [hx, h _]
    rw [hx a, hx b, hx c, hx d]
    rfl
  · have hx : ∀ x, (!decide (x ∈ B) || decide (x ∈ A)) = true := fun x => by
      by_cases hx : x ∈ B <;> simp [hx, h _]
    rw [hx a, hx b, hx c, hx d]
    simp
  · have hx : ∀ x, (!(decide (x ∈ A) && decide (x ∈ B))) = true := fun x => by
      by_cases hx : x ∈ A <;> simp [hx, Finset.disjoint_left.mp h]
    rw [hx a, hx b, hx c, hx d]
    simp

/-- A set that contains exactly two of the four taxa cuts the quartet of some topology. -/
theorem splitPattern_of_two : ∀ x y z w : Bool,
    x.toNat + y.toNat + z.toNat + w.toNat = 2 → ∃ s, splitPattern s x y z w = true := by
  decide

end Quartet

/-- The quartet on the four taxa of `k` with topology `s` has the four taxa of `k`. -/
theorem QuartetKey.quartet_taxa (k : QuartetKey) (s : Fin 3) :
    (k.quartet s).taxa = {k.a, k.b, k.c, k.d} := rfl

theorem QuartetKey.quartet_key (k : QuartetKey) (s : Fin 3) : (k.quartet s).key = k := rfl

@[simp] theorem QuartetKey.quartet_a (k : QuartetKey) (s : Fin 3) : (k.quartet s).a = k.a := rfl

@[simp] theorem QuartetKey.quartet_b (k : QuartetKey) (s : Fin 3) : (k.quartet s).b = k.b := rfl

@[simp] theorem QuartetKey.quartet_c (k : QuartetKey) (s : Fin 3) : (k.quartet s).c = k.c := rfl

@[simp] theorem QuartetKey.quartet_d (k : QuartetKey) (s : Fin 3) : (k.quartet s).d = k.d := rfl

theorem QuartetKey.quartet_split (k : QuartetKey) (s : Fin 3) : (k.quartet s).split = s := rfl

theorem Quartet.key_quartet (q : Quartet) : q.key.quartet q.split = q := by
  cases q
  rfl

namespace PhyloTree

/-- **Section 3.1**: a well-labelled tree `t` induces exactly one quartet on each set `k` of four
of its taxa: some clade of `t` meets the four taxa in exactly two (`exists_clade_two`), and two
clades that cut different quartets on them would be neither nested nor disjoint
(`clades_laminar`). -/
theorem induced_existsUnique (t : PhyloTree) (ht : t.WellLabelled) (k : QuartetKey)
    (hk : ({k.a, k.b, k.c, k.d} : Finset ℕ) ⊆ t.taxa) :
    ∃! s : Fin 3, (k.quartet s).induced t = true := by
  classical
  have hab := k.ab
  have hbc := k.bc
  have hcd := k.cd
  -- existence: a clade meeting the four taxa in exactly two of them
  have hF : ({k.a, k.b, k.c, k.d} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
  obtain ⟨C, hC, hcard⟩ := t.exists_clade_two _ hk (by omega)
  have hsum : (decide (k.a ∈ C)).toNat + (decide (k.b ∈ C)).toNat + (decide (k.c ∈ C)).toNat +
      (decide (k.d ∈ C)).toNat = 2 := by
    rw [← hcard, Finset.card_filter, Finset.sum_insert (by simp; omega),
      Finset.sum_insert (by simp; omega), Finset.sum_pair (by omega)]
    by_cases ha : k.a ∈ C <;> by_cases hb : k.b ∈ C <;> by_cases hc : k.c ∈ C <;>
      by_cases hd : k.d ∈ C <;> simp [ha, hb, hc, hd]
  obtain ⟨s, hs⟩ := Quartet.splitPattern_of_two _ _ _ _ hsum
  refine ⟨s, ?_, ?_⟩
  · simp only [Quartet.induced, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    refine ⟨by rw [QuartetKey.quartet_taxa]; exact hk, C, hC, ?_⟩
    rw [Quartet.cutBy_eq_splitPattern]
    exact hs
  -- uniqueness: two clades cutting quartets of different topologies contradict laminarity
  intro s' hs'
  simp only [Quartet.induced, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hs'
  obtain ⟨-, B, hB, hcut⟩ := hs'
  rw [Quartet.cutBy_eq_splitPattern] at hcut
  simp only [QuartetKey.quartet_a, QuartetKey.quartet_b, QuartetKey.quartet_c,
    QuartetKey.quartet_d, QuartetKey.quartet_split] at hcut
  exact Quartet.splitPattern_laminar s' s _ _ _ _ _ _ _ _ hcut hs
    (Quartet.laminarPattern_of_laminar (t.clades_laminar ht B hB C hC) _ _ _ _)

/-- The topology of the quartet that `T` induces on the four taxa `k` (and `0` if it induces
none). -/
noncomputable def splitOf (T : PhyloTree) (k : QuartetKey) : Fin 3 := by
  classical
  exact if h : ∃ s : Fin 3, (k.quartet s).induced T = true then Classical.choose h else 0

/-- `T` induces the quartet of topology `splitOf T k` on the four taxa `k`, and no other. -/
theorem induced_iff_splitOf (T : PhyloTree) (hT : T.WellLabelled) (k : QuartetKey)
    (hk : ({k.a, k.b, k.c, k.d} : Finset ℕ) ⊆ T.taxa) (s : Fin 3) :
    (k.quartet s).induced T = true ↔ s = T.splitOf k := by
  classical
  obtain ⟨s₀, hs₀, huniq⟩ := T.induced_existsUnique hT k hk
  have hex : ∃ s : Fin 3, (k.quartet s).induced T = true := ⟨s₀, hs₀⟩
  have hspec : (k.quartet (T.splitOf k)).induced T = true := by
    unfold splitOf
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  constructor
  · intro hs
    rw [huniq s hs, huniq _ hspec]
  · rintro rfl
    exact hspec

/-- A quartet induced by `T` is the quartet of topology `splitOf T` on its four taxa. -/
theorem key_quartet_splitOf (T : PhyloTree) (hT : T.WellLabelled) {q : Quartet}
    (hq : q.induced T = true) : q.key.quartet (T.splitOf q.key) = q := by
  have hk : ({q.key.a, q.key.b, q.key.c, q.key.d} : Finset ℕ) ⊆ T.taxa := by
    simp only [Quartet.induced, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.1
  have h := (T.induced_iff_splitOf hT q.key hk q.split).mp (by rw [Quartet.key_quartet]; exact hq)
  rw [← h, Quartet.key_quartet]

end PhyloTree

/-- The sets of four taxa in `X`. -/
noncomputable def keysOn (X : Finset ℕ) : Finset QuartetKey :=
  (Quartet.onTaxa X).image Quartet.key

theorem mem_keysOn {X : Finset ℕ} {k : QuartetKey} :
    k ∈ keysOn X ↔ ({k.a, k.b, k.c, k.d} : Finset ℕ) ⊆ X := by
  constructor
  · intro hk
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
    exact Quartet.mem_onTaxa.mp hq
  · intro h
    exact Finset.mem_image.mpr ⟨k.quartet 0, Quartet.mem_onTaxa.mpr h, rfl⟩

/-- The quartet support score of a well-labelled tree `T` is the sum, over the sets of four taxa
of `T`, of the number of copies in `Q` of the quartet that `T` induces on them. -/
theorem quartetSupport_eq_sum_keys (Q : Multiset Quartet) (T : PhyloTree) (hT : T.WellLabelled) :
    quartetSupport Q T = ∑ k ∈ keysOn T.taxa, Q.count (k.quartet (T.splitOf k)) := by
  classical
  have hinduced : ∀ q : Quartet, q.induced T = true → q.taxa ⊆ T.taxa := by
    intro q hq
    simp only [Quartet.induced, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.1
  -- the quartets of `Q(T)` absent from `Q` have no copies
  have h1 : quartetSupport Q T =
      ∑ q ∈ (Quartet.onTaxa T.taxa).filter (fun q => q.induced T = true), Q.count q := by
    unfold quartetSupport
    apply Finset.sum_subset
    · intro q hq
      have hind := (Finset.mem_filter.mp hq).2
      exact Finset.mem_filter.mpr ⟨Quartet.mem_onTaxa.mpr (hinduced q hind), hind⟩
    · intro q hq hnot
      have hind := (Finset.mem_filter.mp hq).2
      have hQ : q ∉ Q.toFinset := fun hQ => hnot (Finset.mem_filter.mpr ⟨hQ, hind⟩)
      exact Multiset.count_eq_zero.mpr fun h => hQ (Multiset.mem_toFinset.mpr h)
  -- each set of four taxa carries exactly one quartet of `Q(T)`
  rw [h1]
  refine Finset.sum_nbij' Quartet.key (fun k => k.quartet (T.splitOf k)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    exact Finset.mem_image.mpr ⟨q, (Finset.mem_filter.mp hq).1, rfl⟩
  · intro k hk
    have hk' := mem_keysOn.mp hk
    exact Finset.mem_filter.mpr ⟨Quartet.mem_onTaxa.mpr hk',
      (T.induced_iff_splitOf hT k hk' _).mpr rfl⟩
  · intro q hq
    exact T.key_quartet_splitOf hT (Finset.mem_filter.mp hq).2
  · intro k _
    rfl
  · intro q hq
    rw [T.key_quartet_splitOf hT (Finset.mem_filter.mp hq).2]

/-- Section 3.2, the comparison of scores: if, for every four taxa of `t`, the quartet that `t`
induces on them has more copies in `Q` than the two other quartets on them, then every
well-labelled tree `T` on the taxa of `t` that induces a different set of quartets has a smaller
quartet support score than `t`. -/
theorem quartetSupport_lt (Q : Multiset Quartet) (t T : PhyloTree) (ht : t.WellLabelled)
    (hT : T.WellLabelled) (htaxa : T.taxa = t.taxa)
    (hdom : ∀ q : Quartet, q.induced t = true → ∀ s : Fin 3, s ≠ q.split →
      Q.count (q.key.quartet s) < Q.count q)
    (hdiff : ∃ q : Quartet, q.induced T ≠ q.induced t) :
    quartetSupport Q T < quartetSupport Q t := by
  rw [quartetSupport_eq_sum_keys Q T hT, quartetSupport_eq_sum_keys Q t ht, htaxa]
  apply Finset.sum_lt_sum
  · -- on every four taxa, the quartet of `t` has at least as many copies as that of `T`
    intro k hk
    have hk' := mem_keysOn.mp hk
    by_cases hs : T.splitOf k = t.splitOf k
    · rw [hs]
    · exact (hdom _ ((t.induced_iff_splitOf ht k hk' _).mpr rfl) (T.splitOf k) hs).le
  · -- and strictly more where the two trees induce different quartets
    obtain ⟨q, hq⟩ := hdiff
    have hqt : q.taxa ⊆ t.taxa := by
      cases h1 : q.induced T
      · cases h2 : q.induced t
        · rw [h1, h2] at hq
          exact absurd rfl hq
        · simp only [Quartet.induced, Bool.and_eq_true, decide_eq_true_eq] at h2
          exact h2.1
      · simp only [Quartet.induced, Bool.and_eq_true, decide_eq_true_eq] at h1
        exact htaxa ▸ h1.1
    refine ⟨q.key, mem_keysOn.mpr hqt, ?_⟩
    have hs : T.splitOf q.key ≠ t.splitOf q.key := by
      intro heq
      apply hq
      have h1 := T.induced_iff_splitOf hT q.key (htaxa ▸ hqt) q.split
      have h2 := t.induced_iff_splitOf ht q.key hqt q.split
      rw [Quartet.key_quartet] at h1 h2
      rw [heq] at h1
      exact Bool.eq_iff_iff.mpr (h1.trans h2.symm)
    exact hdom _ ((t.induced_iff_splitOf ht q.key hqt _).mpr rfl) _ hs

variable {N : RootedNetwork} {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Section 3.2's condition on the tree `t` ("the most probable quartet tree is induced by t"):
for every four taxa of `t`, the quartet that `t` induces on them is strictly the most probable
quartet on them, per site, under the model `M`: a site contributes it to `Q` with larger
probability than each of the two other quartets on those taxa. -/
def MostProbableQuartets (M : External.SiteModel N σ) (t : PhyloTree) : Prop :=
  ∀ q : Quartet, q.induced t = true → ∀ s : Fin 3, s ≠ q.split →
    M.quartetProb (q.key.quartet s) < M.quartetProb q

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Section 3.2: "as the number of sites increases, for every four species, the most frequently
observed quartet tree will be the most probable quartet tree with probability converging to 1".
Under `MostProbableQuartets`, the probability that, for every four taxa of `t`, the quartet that
`t` induces has more copies in `Q_m` than the two other quartets on them tends to 1. -/
theorem mostFrequent_tendsto (M : External.SiteModel N σ) (hN : N.RootedBinaryLevelOne)
    (t : PhyloTree) (hcond : MostProbableQuartets M t) {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → External.SiteHistory N σ) (hind : iIndepFun X P)
    (hid : ∀ n, IdentDistrib (X n) (X 0) P P) (hlaw : P.map (X 0) = M.law hN) :
    Tendsto (fun m => P {ω | ∀ q : Quartet, q.induced t = true → ∀ s : Fin 3, s ≠ q.split →
      (External.sampleQuartets X m ω).count (q.key.quartet s) <
        (External.sampleQuartets X m ω).count q}) atTop (𝓝 1) := by
  classical
  let K := (Quartet.onTaxa t.taxa).filter fun q => q.induced t = true
  let S : Quartet → Finset (Fin 3) := fun q => Finset.univ.filter (· ≠ q.split)
  have hK : ∀ q : Quartet, q.induced t = true → q ∈ K := by
    intro q hq
    refine Finset.mem_filter.mpr ⟨Quartet.mem_onTaxa.mpr ?_, hq⟩
    simp only [Quartet.induced, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.1
  -- each of the finitely many comparisons holds eventually, almost surely, by the strong law
  have hall : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ∀ q ∈ K, ∀ s ∈ S q,
      (External.sampleQuartets X m ω).count (q.key.quartet s) <
        (External.sampleQuartets X m ω).count q := by
    have hpair : ∀ q ∈ K, ∀ s ∈ S q, ∀ᵐ ω ∂P, ∀ᶠ m in atTop,
        (External.sampleQuartets X m ω).count (q.key.quartet s) <
          (External.sampleQuartets X m ω).count q := fun q hq s hs =>
      External.eventually_count_lt M hN X hind hid hlaw
        (hcond q (Finset.mem_filter.mp hq).2 s (Finset.mem_filter.mp hs).2)
    have hae : ∀ᵐ ω ∂P, ∀ q ∈ K, ∀ s ∈ S q, ∀ᶠ m in atTop,
        (External.sampleQuartets X m ω).count (q.key.quartet s) <
          (External.sampleQuartets X m ω).count q := by
      rw [Filter.eventually_all_finset]
      intro q hq
      rw [Filter.eventually_all_finset]
      exact hpair q hq
    filter_upwards [hae] with ω hω
    rw [Filter.eventually_all_finset]
    intro q hq
    rw [Filter.eventually_all_finset]
    exact hω q hq
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (External.tendsto_measure_of_ae_eventually hall) tendsto_const_nhds
    (fun m => measure_mono fun ω hω => ?_) fun _ => prob_le_one
  intro q hq s hs
  exact hω q (hK q hq) s (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩)

/-- Section 3.2, the ASTRAL step: "the quartet support score of t will be larger than the score
of any other tree". Under `MostProbableQuartets`, for independent sites with the law of the model
`M`, the probability that the quartet support score of `t` for `Q_m` is larger than the score of
every well-labelled tree on the taxa of `t` that induces a different set of quartets tends
to 1. -/
theorem astral_tendsto (M : External.SiteModel N σ) (hN : N.RootedBinaryLevelOne)
    (t : PhyloTree) (ht : t.WellLabelled) (hcond : MostProbableQuartets M t)
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ℕ → Ω → External.SiteHistory N σ)
    (hind : iIndepFun X P) (hid : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hlaw : P.map (X 0) = M.law hN) :
    Tendsto (fun m => P {ω | ∀ T : PhyloTree, T.WellLabelled → T.taxa = t.taxa →
      (∃ q : Quartet, q.induced T ≠ q.induced t) →
        quartetSupport (External.sampleQuartets X m ω) T <
          quartetSupport (External.sampleQuartets X m ω) t}) atTop (𝓝 1) := by
  -- the most frequent quartets are those of `t`, and then `t` has the largest score
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (mostFrequent_tendsto M hN t hcond X hind hid hlaw) tendsto_const_nhds
    (fun m => measure_mono fun ω hω => ?_) fun _ => prob_le_one
  intro T hT htaxa hdiff
  exact quartetSupport_lt _ t T ht hT htaxa hω hdiff

/-- Section 3.2: "ASTRAL will return t since it solves its optimization problem exactly", up to
the classical fact, not formalized here, that a binary tree is determined by its quartets. Under
`MostProbableQuartets`, the probability that every well-labelled tree on the taxa of `t` with the
largest quartet support score for `Q_m` induces the quartets of `t` tends to 1. -/
theorem astral_maximizer_tendsto (M : External.SiteModel N σ) (hN : N.RootedBinaryLevelOne)
    (t : PhyloTree) (ht : t.WellLabelled) (hcond : MostProbableQuartets M t)
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ℕ → Ω → External.SiteHistory N σ)
    (hind : iIndepFun X P) (hid : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hlaw : P.map (X 0) = M.law hN) :
    Tendsto (fun m => P {ω | ∀ T : PhyloTree, T.WellLabelled → T.taxa = t.taxa →
      (∀ T' : PhyloTree, T'.WellLabelled → T'.taxa = t.taxa →
        quartetSupport (External.sampleQuartets X m ω) T' ≤
          quartetSupport (External.sampleQuartets X m ω) T) →
      ∀ q : Quartet, q.induced T = q.induced t}) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (astral_tendsto M hN t ht hcond X hind hid hlaw) tendsto_const_nhds
    (fun m => measure_mono fun ω hω => ?_) fun _ => prob_le_one
  intro T hT htaxa hmax q
  by_contra hq
  exact absurd (hmax t ht rfl) (not_le.mpr (hω T hT htaxa ⟨q, hq⟩))

end Camus
