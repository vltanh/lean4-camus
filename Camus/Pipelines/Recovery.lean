module

public import Camus.Score
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Section 3.2, corrected: recovery of the true network

Section 3.2 of the paper argues that when `Q` is a multiset version of `Q(N_r)`, "CAMUS will add the
correct reticulations and return N, since this is the unique network that can satisfy all the
quartets in Q(N_r)". The uniqueness is false (the report's E7,
`Counterexamples.graph_uniqueness_counterexample`): a network that displays a superset of the true
network's quartets ties it. This file proves a corrected statement, for a finite family `C` of
candidate networks, each with a finite set of displayed quartets and a number of reticulations,
under two extra hypotheses: the true network is identifiable under inclusion
(`IdentifiableUnderInclusion`), and ties in the score are broken in favour of the fewest
reticulations (`FewestReticulations`). The statement in probability is
`correctedStatisticalConsistency` (`Camus/Pipelines/Statistical.lean`).

## Main results

* `IdentifiableUnderInclusion`: every candidate that displays all quartets of the true network and
  has no more reticulations is equivalent to it.
* `correctedConsistency`: if the support of `Q` is the set of quartets displayed by the true
  network, the true network is identifiable under inclusion, and the selected network has the best
  score with the fewest reticulations among the networks with the best score, then the selected
  network is equivalent to the true network.
* `correctedEventualConsistency`: the same along a sequence of inputs whose support is eventually
  the set of quartets displayed by the true network.

## Proof

The true network displays every quartet of `Q`, so its score is `|Q|`, the largest possible. The
selected network has the best score, so it also scores `|Q|`, hence displays every quartet of `Q`,
that is, every quartet that the true network displays. The true network has the best score, so the
tie-break gives the selected network at most as many reticulations. Identifiability under
inclusion concludes.
-/

@[expose] public section

namespace Camus

variable {α N : Type*} [DecidableEq α]

/-- Identifiability of `truth` under inclusion, in the family `C` and up to the relation
`equivalent`: every `n ∈ C` that displays every quartet displayed by `truth`, with no more
reticulations than `truth`, is equivalent to `truth`. Inclusion, rather than equality of the
displayed sets, is needed because the score counts the quartets of `Q` that a network displays and
does not penalize the others. If `truth` has no reticulation, the condition holds as soon as every
network of `C` without reticulation is equivalent to `truth`. -/
def IdentifiableUnderInclusion (C : Finset N) (displayed : N → Finset α)
    (reticulations : N → ℕ) (equivalent : N → N → Prop) (truth : N) : Prop :=
  ∀ n ∈ C, displayed truth ⊆ displayed n →
    reticulations n ≤ reticulations truth → equivalent n truth

/-- Section 3.2, corrected. Let `C` be a finite family of candidate networks containing `truth`,
with displayed quartet sets `displayed` and reticulation counts `reticulations`. Assume that the
support of `Q` is the set of quartets displayed by `truth` (`exact_support`: `Q` is a multiset
version of `Q(N_r)`), that `truth` is identifiable under inclusion in `C` (`identifiable`), and that
`selected` has the best score over `C` (`optimal`) with the fewest reticulations among the networks
of `C` with the best score (`tie_break`). Then `selected` is equivalent to `truth`.

The paper concludes this because the true network "is the unique network that can satisfy all the
quartets in Q(N_r)", which is false (the report's E7,
`Counterexamples.graph_uniqueness_counterexample`); `identifiable` and `tie_break` replace that
step. -/
theorem correctedConsistency (C : Finset N) (displayed : N → Finset α)
    (reticulations : N → ℕ) (equivalent : N → N → Prop) (truth selected : N)
    (truth_feasible : truth ∈ C) (Q : Multiset α)
    (exact_support : Q.toFinset = displayed truth)
    (identifiable : IdentifiableUnderInclusion C displayed reticulations equivalent truth)
    (optimal : Optimal C displayed Q selected)
    (tie_break : FewestReticulations C displayed reticulations Q selected) :
    equivalent selected truth := by
  -- `truth` displays every quartet of `Q`, so its score is `|Q|`, the largest possible
  have htruth : score Q (displayed truth) = Q.card :=
    (score_eq_card_iff Q (displayed truth)).mpr (by rw [exact_support])
  -- so the optimal `selected` scores `|Q|` too
  have hselected : score Q (displayed selected) = Q.card :=
    le_antisymm (score_le_card Q (displayed selected))
      (htruth ▸ optimal.2 truth truth_feasible)
  -- hence `selected` displays every quartet that `truth` displays
  have hcovers : displayed truth ⊆ displayed selected := by
    rw [← exact_support]
    exact (score_eq_card_iff Q (displayed selected)).mp hselected
  -- `truth` is optimal, so the tie-break gives `selected` at most as many reticulations
  have htruth_opt : Optimal C displayed Q truth :=
    ⟨truth_feasible, fun n _ => htruth ▸ score_le_card Q (displayed n)⟩
  exact identifiable selected optimal.1 hcovers
    (tie_break truth truth_feasible htruth_opt)

/-- Section 3.2, corrected, along a sequence of inputs. Assume that `truth ∈ C` is identifiable
under inclusion, that the support of `observations k` is, for all large `k`, the set of quartets
displayed by `truth`, and that each `selected k` has the best score for `observations k` with the
fewest reticulations among the networks with the best score. Then `selected k` is equivalent to
`truth` for all large `k`. This is the deterministic step of the paper's limit argument, and
applies to each sample path separately. -/
theorem correctedEventualConsistency (C : Finset N) (displayed : N → Finset α)
    (reticulations : N → ℕ) (equivalent : N → N → Prop) (truth : N)
    (truth_feasible : truth ∈ C)
    (identifiable : IdentifiableUnderInclusion C displayed reticulations equivalent truth)
    (observations : ℕ → Multiset α) (selected : ℕ → N)
    (exact_support : ∀ᶠ k in Filter.atTop, (observations k).toFinset = displayed truth)
    (optimal : ∀ k, Optimal C displayed (observations k) (selected k))
    (tie_break : ∀ k, FewestReticulations C displayed reticulations
      (observations k) (selected k)) :
    ∀ᶠ k in Filter.atTop, equivalent (selected k) truth := by
  filter_upwards [exact_support] with k hk
  exact correctedConsistency C displayed reticulations equivalent truth (selected k)
    truth_feasible (observations k) hk identifiable (optimal k) (tie_break k)

end Camus
