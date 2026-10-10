# The network multispecies coalescent

**Why it is here.** Sections 3.3 and 3.4 of the paper assume that gene trees evolve down a level-1
network under the network multispecies coalescent (NMSC), and motivate Quartet Filtering
(Algorithm 1) by the distributions of quartet trees that it gives. This directory holds that model.

**Where it comes from.** The files are copied from the Lean formalization of BROOQS (Shayesteh
Arasti and Siavash Mirarab, *BROOQS: Spectral Methods Resolve Level-1 Hybridization Cycles without
Tests of Symmetry*, bioRxiv [10.64898/2026.08.31.748319](https://doi.org/10.64898/2026.08.31.748319)),
lean4-brooqs, library `Primitive`, commit `1c2eede`, by the maintainer of this project. The
namespace `Brooqs` is kept, so that the two copies stay comparable. BROOQS's F-matrix and the steps
of its algorithm are left out. The model:

- rooted metric level-1 networks, described recursively from the root (`Brooqs.Net`), with positive
  edge lengths, inheritance probabilities in `(0, 1)` and distinct leaf labels
  (`Brooqs.Net.WellFormed`);
- Kingman's coalescent on forests of gene lineages, from the formalization of Allman, Degnan and
  Rhodes (2011), lean4-adr11 (a dependency of this project);
- the NMSC (`Brooqs.Net.forestDist`, `Brooqs.Net.geneTreeDist`), and the quartet concordance factors
  (`Brooqs.Net.quartetCF`);
- the quartet concordance factors of four components of a cycle, which are those of the induced
  metric quarnet (H. Baños, *Identifying species network features from gene tree quartets under the
  coalescent model*, Bull. Math. Biol. 81 (2019) 494–534): `Brooqs.nmsc_quartetCF`;
- sampling consistency: the gene tree of a subset of the lineages has the distribution of the
  coalescent of that subset (`Brooqs.Net.geneTreeDist_restrict`), so a quartet CF is the
  probability that a gene tree on all the taxa displays the quartet (`Brooqs.quartetCF_eq_displays`).

**What was added for CAMUS.** The copied files are unchanged except for their docstrings, which
name BROOQS where they refer to its paper, and two public lemmas: `Brooqs.exists_context_kernel`
and `Brooqs.quartetCF_eq_sum_subnet` in `Context.lean` (the argument of
`Brooqs.quartetCF_eq_sum_top`, stated for any subnetwork; `quartetCF_eq_sum_top` is now its
corollary) and `Brooqs.quartetCF_eq_of_components` in `Cycle.lean` (the steps of
`Brooqs.nmsc_quartetCF` for four given taxa). The new files:

- `Displayed.lean`: the displayed trees of a network (CAMUS's Definition 1), by their clusters, and
  its displayed quartets (`Brooqs.Net.Displays`).
- `ThreeCycle.lean`: the quartet CFs of a 3-cycle above two taxa, `N₃₂`, and the anomaly: the only
  quartet that `N₃₂` displays on its four taxa can be strictly the least probable
  (`Brooqs.net32_anomaly`).
- `GeneLaw.lean`: the gene tree distribution is a probability distribution, and independent gene
  trees with that law (`Brooqs.Net.genes`).
- `Splits.lean`, `FourComponents.lean`, `Pairs.lean`, `Pattern.lean`: the CF pattern that Quartet
  Filtering presumes holds for every set of four taxa except in the anomalous configuration
  (`Brooqs.Net.regularOn_of_not_anomalous`), and its weaker part holds always
  (`Brooqs.Net.weakPattern`).

The consequences for Sections 3.3 and 3.4 of CAMUS are in `Camus/Pipelines/NMSC/`.
