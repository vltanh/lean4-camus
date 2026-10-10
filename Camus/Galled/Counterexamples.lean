module

public import Camus.Galled.Basic
public import Camus.Score
public import Camus.Galled.Triangles
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

/-!
# Checked examples in the block grammar: E1, E3 and E4

Three findings of the report, on concrete networks of the block grammar `GalledNetwork`, checked by
evaluation. Labels: `A = 0`, `B = 1`, `C = 2`, `D = 3`, and the outgroup `O = 4`.

* E1, Equation (1). The paper calls `Q` a multiset, while `δ_T(q, (u, w))` already counts the copies
  of `q` in `Q`. Summing `δ` over `Q` copy by copy counts a quartet with `c` copies `c · c` times
  (`squared_multiplicity_counterexample`, with `c = 2`). The formalization sums over the distinct
  quartets of `Q`, as the weighted-set representation of Section 2.3 suggests (`Camus.equation1`).
* E3, Section 2.4. For `T = (A,(B,(D,C)))` and `Q = {AC|BD}`, a valid network built on `T` with two
  reticulations displays `AC|BD`, and every valid four-leaf network built on `T` with three
  reticulations displays no quartet of `Q` (`exact_budget_nonmonotone`): the best score for an
  exact number of reticulations can decrease.
* E4, Section 3.2. The five-leaf tree `T = (O,((B,A),(D,C)))` (`truth`) and the network obtained by
  adding one edge above `(A, C)` (`extra`) are both built on `T` and both display the five quartets
  of `T`, with zero and one reticulations (`uniqueness_counterexample`): the true network is not the
  unique optimum.

The directed-graph versions of E3 and E4 are `Counterexamples.graph_exact_budget_nonmonotone` and
`Counterexamples.graph_uniqueness_counterexample`, which also use `smallConstraint`, `oneQuartet`,
`constraint` and `data` from this file.
-/

@[expose] public section

namespace Camus.Counterexamples

open PhyloTree GalledNetwork

/-- The quartet on the taxa `0, 1, 2, 3` with split `s`: `01|23` for `s = 0`, `02|13` for `s = 1`,
`03|12` for `s = 2`. The next four definitions are the same for the other sets of four taxa of
`{0, 1, 2, 3, 4}`. -/
def q0123 (s : Fin 3) : Quartet := ⟨0, 1, 2, 3, by decide, by decide, by decide, s⟩
def q0124 (s : Fin 3) : Quartet := ⟨0, 1, 2, 4, by decide, by decide, by decide, s⟩
def q0134 (s : Fin 3) : Quartet := ⟨0, 1, 3, 4, by decide, by decide, by decide, s⟩
def q0234 (s : Fin 3) : Quartet := ⟨0, 2, 3, 4, by decide, by decide, by decide, s⟩
def q1234 (s : Fin 3) : Quartet := ⟨1, 2, 3, 4, by decide, by decide, by decide, s⟩

/-- E4: the five-leaf tree `T = (O,((B,A),(D,C)))`. Its child order is that of a tree displayed by
`extra`, since `Extends` compares plane trees. -/
def constraint : PhyloTree :=
  .fork (.leaf 4) (.fork (.fork (.leaf 1) (.leaf 0)) (.fork (.leaf 3) (.leaf 2)))

/-- E4: the true network, the tree `T` itself, with no reticulation. -/
def truth : GalledNetwork :=
  .fork (.leaf 4) (.fork (.fork (.leaf 1) (.leaf 0)) (.fork (.leaf 3) (.leaf 2)))

/-- E4: `T` with one edge added above `(A, C)`. Its cycle has five vertices: `((B,A),(D,C))` at the
top, `(B,A)` and the subdivision vertex above `A` on one path, `(D,C)` on the other, and the
reticulation above `C`. The outgroup `O` is outside the cycle. -/
def extra : GalledNetwork :=
  .fork (.leaf 4) (.gall [.leaf 1, .leaf 0] [.leaf 3] (.leaf 2))

/-- E4: the five quartets of `T`, one for each set of four of its taxa: `AB|CD`, `AB|CO`, `AB|DO`,
`AO|CD` and `BO|CD`. -/
def data : Multiset Quartet :=
  {q0123 0, q0124 0, q0134 0, q0234 2, q1234 2}

/-- The distinct quartets of `Q` displayed by the block network `n`. -/
def repertoire (Q : Multiset Quartet) (n : GalledNetwork) : Finset Quartet :=
  Q.toFinset.filter (fun q => n.containsQuartet q = true)

/-- The distinct quartets of `Q` satisfied by the block network `n` relative to `t`. -/
def novelRepertoire (Q : Multiset Quartet) (n : GalledNetwork)
    (t : PhyloTree) : Finset Quartet :=
  Q.toFinset.filter (fun q => n.satisfies t q = true)

/-- E4: `data` is the set of quartets induced by `T`, so `Q = data` is a multiset version of
`Q(N_r)` for the true network `N = T`. -/
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

/-- E4 (Section 3.2): `truth` and `extra` are phylogenetic networks built on `T`, with zero and one
reticulations; both display all five quartets of `data`, and neither satisfies any (they are all
quartets of `T`). No network displays more than the five quartets, so both are optimal
(`witnesses_globally_optimal`) and the true network is not the unique optimum. -/
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

/-- E4: every block network displays at most as many quartets of `data` as `truth` and as `extra`,
which display all of them. -/
theorem witnesses_globally_optimal (n : GalledNetwork) :
    score data (repertoire data n) ≤ score data (repertoire data truth) ∧
    score data (repertoire data n) ≤ score data (repertoire data extra) := by
  have ht := uniqueness_counterexample.2.2.2.2.2.2.1
  have he := uniqueness_counterexample.2.2.2.2.2.2.2.1
  constructor <;> simpa only [ht, he] using score_le_card data (repertoire data n)

/-- E1 (Equation (1)): for `Q = {0, 0}` and `D = {0}`, two elements of `Q` lie in `D`, but summing
`δ = delta Q D` over `Q` copy by copy gives `2 + 2 = 4`. Equation (1) is therefore read as a sum
over the distinct elements of `Q` (`Camus.equation1`). -/
theorem squared_multiplicity_counterexample :
    score ({(0 : ℕ), 0} : Multiset ℕ) {0} = 2 ∧
    (({(0 : ℕ), 0} : Multiset ℕ).map
      (delta ({(0 : ℕ), 0} : Multiset ℕ) {0})).sum = 4 := by
  decide

/-- E3: the four-leaf tree `T = (A,(B,(D,C)))`. Its quartet is `AB|CD`. -/
def smallConstraint : PhyloTree := .fork (.leaf 0) (.fork (.leaf 1) (.fork (.leaf 3) (.leaf 2)))

/-- E3: `T` with the edge from above `(B,(D,C))` to above `C`. Its cycle passes through `(B,(D,C))`
and `(D,C)`; deleting the tree edge into the reticulation gives `(A,(C,(B,D)))`, which induces
`AC|BD`. -/
def oneReticulation : GalledNetwork :=
  .fork (.leaf 0) (.gall [] [.leaf 1, .leaf 3] (.leaf 2))

/-- E3: `oneReticulation` with a triangle at the root, from above `A` to above `(B,(D,C))`. -/
def twoReticulations : GalledNetwork :=
  .gall [.leaf 0] [] (.gall [] [.leaf 1, .leaf 3] (.leaf 2))

/-- E3: `T` with a triangle at each of its three internal vertices. -/
def threeTriangles : GalledNetwork :=
  .gall [.leaf 0] [] (.gall [.leaf 1] [] (.gall [.leaf 3] [] (.leaf 2)))

/-- E3: `Q = {AC|BD}`, a quartet that `T` does not induce. -/
def oneQuartet : Multiset Quartet := {q0123 1}

/-- E3: `oneReticulation`, `twoReticulations` and `threeTriangles` are phylogenetic networks built
on `T`, with one, two and three reticulations, displaying `1`, `1` and `0` quartets of `Q`. That no
other network with three reticulations does better is `exact_three_score_zero`. -/
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

/-- E3: every valid four-leaf network built on `T` with exactly three reticulations displays no
quartet of `Q`. With `n − 1 = 3` reticulations it consists of triangles, so it displays only the
quartet `AB|CD` of `T` (`GalledNetwork.saturated_contains_eq`). -/
theorem exact_three_score_zero (n : GalledNetwork) (hn : n.Valid)
    (hleaves : n.labels.length = 4) (hr : n.reticulations = 3)
    (hext : n.Extends smallConstraint) :
    score oneQuartet (repertoire oneQuartet n) = 0 := by
  have hsat : n.reticulations + 1 = n.labels.length := by omega
  have hq := saturated_contains_eq n hn hsat smallConstraint hext (q0123 1)
  have ht : (q0123 1).induced smallConstraint = false := by decide
  rw [ht] at hq
  simp [score, repertoire, oneQuartet, hq]

/-- E3 (Section 2.4), in the block grammar: some phylogenetic four-leaf network built on
`T = (A,(B,(D,C)))` with exactly two reticulations displays the quartet of `Q = {AC|BD}`, and every
valid four-leaf network built on `T` with exactly three reticulations displays none. The best score
for an exact number of reticulations decreases from `1` to `0`, against Section 2.4's "the score
... will never decrease as the number of reticulations increases". -/
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
