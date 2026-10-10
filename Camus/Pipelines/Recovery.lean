module

public import Camus.Score
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

namespace Camus

variable {α N : Type*} [DecidableEq α]

/-- Explicit identifiability up to a chosen topology equivalence: among feasible
networks containing every true displayed quartet and using no more reticulations
than the truth, only the true topology occurs. Inclusion, rather than equality,
is essential because the CAMUS objective does not penalize extra quartets.

This is an additional hypothesis of the corrected §3.2 theorem. It is not
claimed to follow from the cited identifiability theorem about exact repertoires. -/
def IdentifiableUnderInclusion (C : Finset N) (displayed : N → Finset α)
    (reticulations : N → ℕ) (equivalent : N → N → Prop) (truth : N) : Prop :=
  ∀ n ∈ C, displayed truth ⊆ displayed n →
    reticulations n ≤ reticulations truth → equivalent n truth

/-- Corrected §3.2 recovery theorem (user-authorized replacement of the false
uniqueness claim): exact empirical support, explicit identifiability under
inclusion, and minimum-reticulation tie-breaking imply recovery of the truth
up to the stated topology equivalence.

Departure from the paper: the printed uniqueness assertion is false (REPORT E4).
The additional hypotheses and tie-break describe a new corrected result; they
are never passed off as hypotheses of the original paper theorem. -/
theorem correctedConsistency (C : Finset N) (displayed : N → Finset α)
    (reticulations : N → ℕ) (equivalent : N → N → Prop) (truth selected : N)
    (truth_feasible : truth ∈ C) (Q : Multiset α)
    (exact_support : Q.toFinset = displayed truth)
    (identifiable : IdentifiableUnderInclusion C displayed reticulations equivalent truth)
    (optimal : Optimal C displayed Q selected)
    (tie_break : FewestReticulations C displayed reticulations Q selected) :
    equivalent selected truth := by
  have htruth : score Q (displayed truth) = Q.card :=
    (score_eq_card_iff Q (displayed truth)).mpr (by rw [exact_support])
  have hselected : score Q (displayed selected) = Q.card :=
    le_antisymm (score_le_card Q (displayed selected))
      (htruth ▸ optimal.2 truth truth_feasible)
  have hcovers : displayed truth ⊆ displayed selected := by
    rw [← exact_support]
    exact (score_eq_card_iff Q (displayed selected)).mp hselected
  have htruth_opt : Optimal C displayed Q truth :=
    ⟨truth_feasible, fun n _ => htruth ▸ score_le_card Q (displayed n)⟩
  exact identifiable selected optimal.1 hcovers
    (tie_break truth truth_feasible htruth_opt)

/-- Deterministic eventual recovery. It can be applied separately to every
sample path on which empirical support is eventually exact. It does not assert
an unproved law of large numbers or a property of the biological model. -/
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
