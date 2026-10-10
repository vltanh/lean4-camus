module

public import Camus.Galled.Basic

@[expose] public section

namespace Camus.GalledNetwork

/-- Slack in the n−1 reticulation bound: an ordinary fork costs one unit,
and a gall with h hanging subnetworks costs h−1 units. -/
def slack : GalledNetwork → ℕ
  | .leaf _ => 0
  | .fork l r => slack l + slack r + 1
  | .gall l r b => (l.map slack).sum + (r.map slack).sum + slack b +
      (l.length + r.length - 1)
termination_by n => sizeOf n

/-- Exact vertex-count identity underlying §2.4's bound. -/
theorem reticulations_add_slack (n : GalledNetwork) (hn : n.Valid) :
    n.reticulations + 1 + n.slack = n.labels.length := by
  let listProperty := fun xs : List GalledNetwork =>
    (∀ x ∈ xs, Valid x) →
      (xs.map reticulations).sum + xs.length + (xs.map slack).sum =
        (xs.flatMap labels).length
  have h : n.Valid → n.reticulations + 1 + n.slack = n.labels.length := by
    apply GalledNetwork.rec
      (motive_1 := fun n => n.Valid → n.reticulations + 1 + n.slack = n.labels.length)
      (motive_2 := listProperty)
    · intro a _
      simp [reticulations, slack, labels]
    · intro l r ihl ihr hvalid
      simp only [Valid] at hvalid
      have hl := ihl hvalid.1
      have hr := ihr hvalid.2
      simp only [reticulations, slack, labels, List.length_append]
      omega
    · intro l r b ihl ihr ihb hvalid
      simp only [Valid] at hvalid
      have hl := ihl hvalid.2.1
      have hr := ihr hvalid.2.2.1
      have hb := ihb hvalid.2.2.2
      have hlen : 1 ≤ l.length + r.length := by
        rcases hvalid.1 with hleft | hright
        · have := List.length_pos_iff.mpr hleft
          omega
        · have := List.length_pos_iff.mpr hright
          omega
      simp only [reticulations, slack, labels, List.length_append]
      omega
    · intro _
      simp
    · intro a xs iha ihxs hvalid
      have ha := iha (hvalid a (by simp))
      have hx := ihxs (fun x hx => hvalid x (by simp [hx]))
      dsimp [listProperty] at hx ⊢
      simp only [List.map_cons, List.sum_cons,
        List.flatMap_cons, List.length_append]
      omega
  exact h hn

/-- §2.4: a valid binary galled network with n leaves has at most n−1
reticulations. This counts labels with multiplicity; distinct leaf labels give
the paper's species count by the subsequent representation bridge. -/
theorem reticulation_bound (n : GalledNetwork) (hn : n.Valid) :
    n.reticulations ≤ n.labels.length - 1 := by
  have h := reticulations_add_slack n hn
  omega

/-- Distinct labels connect the storage list's length to the number of species. -/
theorem labels_card (n : GalledNetwork) (hn : n.WellLabelled) :
    n.labels.toFinset.card = n.labels.length := by
  exact List.toFinset_card_of_nodup hn

end Camus.GalledNetwork
