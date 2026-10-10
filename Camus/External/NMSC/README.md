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
