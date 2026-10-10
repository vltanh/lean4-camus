module

public import Camus.Pipelines.NMSC.Filtering
public import Camus.External.NMSC.Swap

/-!
# Sections 3.3 and 3.4 do not depend on the order of the sides of a cycle

`Brooqs.Net.SideSwap N N'` says that `N'` is the network `N` with the two sides of some of its
cycles exchanged: the same network, described with another order of the sides
(`Camus/External/NMSC/Swap.lean`). This file shows that what Sections 3.3 and 3.4 use of `N` does
not depend on this order: the probabilities of the quartet trees under the NMSC
(`NMSC.quartetProb`), the quartet trees in Q(N_r) (`NMSC.DisplaysQuartet`), the displayed trees
T(N) (`NMSC.DisplaysTree`), the CF pattern that Quartet Filtering presumes (`NMSC.RegularOn`), the
absence of the anomalous configuration (`NMSC.NoAnomaly`) and the bound `t₀(N)` on the threshold
(`NMSC.threshold`).

## Main results

* `NMSC.quartetProb_eq_of_sideSwap`: the probabilities of the quartet trees.
* `NMSC.displaysQuartet_iff_of_sideSwap`, `NMSC.displaysTree_iff_of_sideSwap`: Q(N_r) and T(N).
* `NMSC.regularOn_iff_of_sideSwap`, `NMSC.noAnomaly_iff_of_sideSwap`: the CF pattern and the
  anomalous configuration.
* `NMSC.threshold_eq_of_sideSwap`: the bound `t₀(N)`.
-/

@[expose] public noncomputable section

namespace Camus

namespace NMSC

open Finset

variable {L : Finset ℕ} {N N' : Brooqs.Net L}

/-- The probability that a gene tree induces a quartet tree is the same under the NMSC on `N` and
on `N'`. -/
theorem quartetProb_eq_of_sideSwap (h : N.SideSwap N') (q : Quartet) :
    quartetProb N q = quartetProb N' q := by
  simp only [quartetProb, h.geneTreeDist_eq]

/-- `N` and `N'` display the same quartet trees: Q(N_r) does not depend on the order of the sides
of a cycle. -/
theorem displaysQuartet_iff_of_sideSwap (h : N.SideSwap N') (q : Quartet) :
    DisplaysQuartet N q ↔ DisplaysQuartet N' q := by
  simp only [DisplaysQuartet, h.mem_displayed_iff]

/-- `N` and `N'` have the same displayed trees T(N), as unrooted trees of CAMUS. -/
theorem displaysTree_iff_of_sideSwap (h : N.SideSwap N') (T : PhyloTree) :
    DisplaysTree N T ↔ DisplaysTree N' T := by
  simp only [DisplaysTree, h.mem_displayed_iff]

/-- The four taxa of `k` have the CF pattern that Quartet Filtering presumes on `N` iff they have
it on `N'`. -/
theorem regularOn_iff_of_sideSwap (h : N.SideSwap N') (k : QuartetKey) :
    RegularOn N k ↔ RegularOn N' k := by
  simp only [RegularOn, displaysQuartet_iff_of_sideSwap h, quartetProb_eq_of_sideSwap h]

/-- `N` has no four taxa in the anomalous configuration iff `N'` has none. -/
theorem noAnomaly_iff_of_sideSwap (h : N.SideSwap N') : NoAnomaly N ↔ NoAnomaly N' := by
  simp only [NoAnomaly, h.anomalous_iff]

/-- The bound `t₀(N)` on the threshold of Quartet Filtering is the same for `N` and `N'`: the
ratios `(p₂ − p₃)/(p₂ + p₃)` are those of the same quartet trees, with the same probabilities. -/
theorem threshold_eq_of_sideSwap (h : N.SideSwap N') : threshold N = threshold N' := by
  have hr : ratios N = ratios N' := by
    simp only [ratios, displaysQuartet_iff_of_sideSwap h, quartetProb_eq_of_sideSwap h]
  simp only [threshold, hr]

end NMSC

end Camus
