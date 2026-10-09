# Conditional cited result

`Observation2.lean` defines the proposition `Camus.External.WarnowTabatabaeeEvansObservation2`. It is assumed explicitly by the main optimizer theorem and the quartet attribution lemma, with no project axiom.

Source: Tandy Warnow, Yasamin Tabatabaee and Steven N. Evans, *Advances in Estimating Level-1 Phylogenetic Networks from Unrooted SNPs*, Journal of Computational Biology 32(1), 3–27 (2025), [DOI 10.1089/cmb.2024.0710](https://journals.sagepub.com/doi/10.1089/cmb.2024.0710), Observation 2. First published online 2024-11-25.

The proposition characterizes displayed quartets of a rooted binary level-1 graph by a bridge cut or by two cuts on one cycle, with one cut incident to the bottom reticulation. Its Lean display definition uses actual switchings and labelled-leaf connectivity. It does not assume unique cycle attribution, graph completeness or the CAMUS recurrence; those are proved in the library.

Mathlib has general graph theory but no phylogenetic network quartet characterization. A proof from switching display would require an additional cycle/cut analysis. The user chose this explicit conditional boundary. Consequently the README, report and metadata describe the project as conditional.
