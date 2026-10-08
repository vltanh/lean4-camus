module

public import Camus.Phylogeny
public import Camus.Score
public import Camus.Triangles
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

@[expose] public section

namespace Camus.Counterexamples

open PhyloTree GalledNetwork

def q0123 (s : Fin 3) : Quartet := ⟨0, 1, 2, 3, by decide, by decide, by decide, s⟩
def q0124 (s : Fin 3) : Quartet := ⟨0, 1, 2, 4, by decide, by decide, by decide, s⟩
def q0134 (s : Fin 3) : Quartet := ⟨0, 1, 3, 4, by decide, by decide, by decide, s⟩
def q0234 (s : Fin 3) : Quartet := ⟨0, 2, 3, 4, by decide, by decide, by decide, s⟩
def q1234 (s : Fin 3) : Quartet := ⟨1, 2, 3, 4, by decide, by decide, by decide, s⟩

/-- A=0, B=1, C=2, D=3, and outgroup O=4. The child order is immaterial
biologically and is chosen here to match the recorded support switching exactly. -/
def constraint : PhyloTree :=
  .fork (.leaf 4) (.fork (.fork (.leaf 1) (.leaf 0)) (.fork (.leaf 3) (.leaf 2)))

def truth : GalledNetwork :=
  .fork (.leaf 4) (.fork (.fork (.leaf 1) (.leaf 0)) (.fork (.leaf 3) (.leaf 2)))

/-- Add the edge above A→C. The gall has three hanging path nodes plus its
source and reticulation, hence five cycle vertices. The outgroup remains outside. -/
def extra : GalledNetwork :=
  .fork (.leaf 4) (.gall [.leaf 1, .leaf 0] [.leaf 3] (.leaf 2))

/-- Exactly the five quartets induced on the five four-taxon subsets of T. -/
def data : Multiset Quartet :=
  {q0123 0, q0124 0, q0134 0, q0234 2, q1234 2}

def repertoire (Q : Multiset Quartet) (n : GalledNetwork) : Finset Quartet :=
  Q.toFinset.filter (fun q => n.containsQuartet q = true)

def novelRepertoire (Q : Multiset Quartet) (n : GalledNetwork)
    (t : PhyloTree) : Finset Quartet :=
  Q.toFinset.filter (fun q => n.satisfies t q = true)

/-- This input really contains every induced quartet of the truth, rather than
an arbitrarily selected subset. Four increasing labels from {0,1,2,3,4} have
exactly the five possibilities enumerated below. -/
theorem data_is_exact (q : Quartet) :
    q.induced constraint = true ↔ q ∈ data := by
  by_cases ht : q.taxa ⊆ constraint.taxa
  · have hd : q.d ≤ 4 := by
      have hm := ht (by simp [Quartet.taxa] : q.d ∈ q.taxa)
      simp [constraint, PhyloTree.taxa, PhyloTree.labels] at hm
      omega
    rcases q with ⟨a, b, c, d, hab, hbc, hcd, s⟩
    change d ≤ 4 at hd
    have hp :
        (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3) ∨
        (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 4) ∨
        (a = 0 ∧ b = 1 ∧ c = 3 ∧ d = 4) ∨
        (a = 0 ∧ b = 2 ∧ c = 3 ∧ d = 4) ∨
        (a = 1 ∧ b = 2 ∧ c = 3 ∧ d = 4) := by omega
    rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
      fin_cases s <;> decide +kernel +revert
  · have hq : q ∉ data := by
      intro hq
      simp [data] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> exact ht (by decide)
    simp [Quartet.induced, ht, hq]

/-- Checked witnesses for E4 (§3.2): distinct reticulation counts, valid,
well-labelled networks, the same displayed constraint tree, and equal maximum
input support. The finite-family formulation already contradicts unique
optimality in any larger feasible family because the score cannot exceed 5. -/
theorem uniqueness_counterexample :
    truth.Phylogenetic ∧ extra.Phylogenetic ∧
    truth.Extends constraint ∧ extra.Extends constraint ∧
    truth.reticulations = 0 ∧ extra.reticulations = 1 ∧
    score data (repertoire data truth) = data.card ∧
    score data (repertoire data extra) = data.card ∧
    score data (novelRepertoire data truth constraint) = 0 ∧
    score data (novelRepertoire data extra constraint) = 0 := by
  have ht : truth.Valid := by simp [truth, Valid]
  have he : extra.Valid := by simp [extra, Valid]
  have htl : truth.WellLabelled := by simp [truth, GalledNetwork.WellLabelled, GalledNetwork.labels]
  have hel : extra.WellLabelled := by simp [extra, GalledNetwork.WellLabelled, GalledNetwork.labels]
  simp only [Phylogenetic, ht, he, htl, hel, true_and]
  decide +kernel

/-- For the fixed exact input `data`, both witnesses attain the total number
of observations and are global maxima, not merely maxima in a selected finite
pair of candidates. -/
theorem witnesses_globally_optimal (n : GalledNetwork) :
    score data (repertoire data n) ≤ score data (repertoire data truth) ∧
    score data (repertoire data n) ≤ score data (repertoire data extra) := by
  have ht := uniqueness_counterexample.2.2.2.2.2.2.1
  have he := uniqueness_counterexample.2.2.2.2.2.2.2.1
  constructor <;> simpa only [ht, he] using score_le_card data (repertoire data n)

/-- E1: literal multiset summation of delta counts two copies twice. The
weighted-support sum in Equation1 gives 2, whereas the occurrence sum gives4. -/
theorem squared_multiplicity_counterexample :
    score ({(0 : ℕ), 0} : Multiset ℕ) {0} = 2 ∧
    (({(0 : ℕ), 0} : Multiset ℕ).map
      (delta ({(0 : ℕ), 0} : Multiset ℕ) {0})).sum = 4 := by
  decide

/-- E3 exact-budget witnesses. T=(A,(B,(D,C))). -/
def smallConstraint : PhyloTree := .fork (.leaf 0) (.fork (.leaf 1) (.fork (.leaf 3) (.leaf 2)))

def oneReticulation : GalledNetwork :=
  .fork (.leaf 0) (.gall [] [.leaf 1, .leaf 3] (.leaf 2))

def twoReticulations : GalledNetwork :=
  .gall [.leaf 0] [] (.gall [] [.leaf 1, .leaf 3] (.leaf 2))

def threeTriangles : GalledNetwork :=
  .gall [.leaf 0] [] (.gall [.leaf 1] [] (.gall [.leaf 3] [] (.leaf 2)))

def oneQuartet : Multiset Quartet := {q0123 1}

/-- Computed witness scores. The separate saturation theorem is needed to
exclude a different three-reticulation network with better score. -/
theorem exact_budget_witnesses :
    oneReticulation.Phylogenetic ∧ twoReticulations.Phylogenetic ∧
    threeTriangles.Phylogenetic ∧
    oneReticulation.Extends smallConstraint ∧
    twoReticulations.Extends smallConstraint ∧
    threeTriangles.Extends smallConstraint ∧
    oneReticulation.reticulations = 1 ∧ twoReticulations.reticulations = 2 ∧
    threeTriangles.reticulations = 3 ∧
    score oneQuartet (repertoire oneQuartet oneReticulation) = 1 ∧
    score oneQuartet (repertoire oneQuartet twoReticulations) = 1 ∧
    score oneQuartet (repertoire oneQuartet threeTriangles) = 0 := by
  have h1 : oneReticulation.Valid := by simp [oneReticulation, Valid]
  have h2 : twoReticulations.Valid := by simp [twoReticulations, Valid]
  have h3 : threeTriangles.Valid := by simp [threeTriangles, Valid]
  have hl1 : oneReticulation.WellLabelled := by simp [oneReticulation, GalledNetwork.WellLabelled, GalledNetwork.labels]
  have hl2 : twoReticulations.WellLabelled := by simp [twoReticulations, GalledNetwork.WellLabelled, GalledNetwork.labels]
  have hl3 : threeTriangles.WellLabelled := by simp [threeTriangles, GalledNetwork.WellLabelled, GalledNetwork.labels]
  simp only [Phylogenetic, h1, h2, h3, hl1, hl2, hl3, true_and]
  decide +kernel

/-- Every four-leaf valid block network at exact budget three is saturated,
so it has no quartet beyond the constraint switching. This is the universal
upper bound missing from a comparison of individual witnesses. -/
theorem exact_three_score_zero (n : GalledNetwork) (hn : n.Valid)
    (hleaves : n.labels.length = 4) (hr : n.reticulations = 3)
    (hext : n.Extends smallConstraint) :
    score oneQuartet (repertoire oneQuartet n) = 0 := by
  have hsat : n.reticulations + 1 = n.labels.length := by omega
  have hq := saturated_contains_eq n hn hsat smallConstraint hext (q0123 1)
  have ht : (q0123 1).induced smallConstraint = false := by decide
  rw [ht] at hq
  simp [score, repertoire, oneQuartet, hq]

/-- E3: the exact-budget optimum is one at budget two and zero at budget three
in the concrete valid four-leaf block model. In particular, exact-budget
monotonicity cannot be justified by inclusion of feasible families. -/
theorem exact_budget_nonmonotone :
    (∃ n : GalledNetwork, n.Phylogenetic ∧ n.labels.length = 4 ∧
      n.Extends smallConstraint ∧ n.reticulations = 2 ∧
      score oneQuartet (repertoire oneQuartet n) = 1) ∧
    (∀ n : GalledNetwork, n.Valid → n.labels.length = 4 →
      n.Extends smallConstraint → n.reticulations = 3 →
      score oneQuartet (repertoire oneQuartet n) = 0) := by
  constructor
  · refine ⟨twoReticulations, exact_budget_witnesses.2.1, ?_, ?_, ?_, ?_⟩
    · decide +kernel
    · exact exact_budget_witnesses.2.2.2.2.1
    · exact exact_budget_witnesses.2.2.2.2.2.2.2.1
    · exact exact_budget_witnesses.2.2.2.2.2.2.2.2.2.2.1
  · intro n hn hl he hr
    exact exact_three_score_zero n hn hl hr he

end Camus.Counterexamples
