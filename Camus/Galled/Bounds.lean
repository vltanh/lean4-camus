module

public import Camus.Galled.Basic

/-!
# The bound of `n − 1` reticulations, in the block grammar

Section 2.4 of the paper uses that "a level-1 phylogenetic network on n leaves will not have more
than n−1 reticulations". In the block grammar this is a count: with `slack` charging one unit per
fork and `h − 1` units per gall with `h` hanging subnetworks, a valid network with `n` leaves has
`reticulations + 1 + slack = n`. A network attains the bound iff its slack is `0`, i.e. it has no
fork and every gall is a triangle (`Camus/Galled/Triangles.lean`). The bound for the directed-graph
networks is `RootedNetwork.anchored_reticulation_bound`.

## Main results

* `GalledNetwork.reticulations_add_slack`: `reticulations + 1 + slack = n`.
* `GalledNetwork.reticulation_bound`: at most `n − 1` reticulations.
-/

@[expose] public section

namespace Camus.GalledNetwork

/-- The slack in the bound of `n − 1` reticulations: one unit per fork and `h − 1` units per gall
with `h` hanging subnetworks. -/
def slack : GalledNetwork → ℕ
  | .leaf _ => 0
  | .fork l r => slack l + slack r + 1
  | .gall l r b => (l.map slack).sum + (r.map slack).sum + slack b +
      (l.length + r.length - 1)
termination_by n => sizeOf n

/-- A valid network with `n` leaves has `reticulations + 1 + slack = n`. -/
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

/-- Section 2.4: a valid network with `n` leaves has at most `n − 1` reticulations. Here `n` counts
the leaves, `n.labels.length`; with distinct labels it is the number of taxa (`labels_card`). -/
theorem reticulation_bound (n : GalledNetwork) (hn : n.Valid) :
    n.reticulations ≤ n.labels.length - 1 := by
  have h := reticulations_add_slack n hn
  omega

/-- With distinct labels, the number of leaves is the number of taxa. -/
theorem labels_card (n : GalledNetwork) (hn : n.WellLabelled) :
    n.labels.toFinset.card = n.labels.length := by
  exact List.toFinset_card_of_nodup hn

end Camus.GalledNetwork
