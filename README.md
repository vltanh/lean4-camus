# CAMUS in Lean 4

Conditional formalization of Willson and Warnow's [CAMUS paper](https://doi.org/10.1093/bioinformatics/btag245), using Lean 4 and Mathlib. The main theorem takes the cited **Warnow–Tabatabaee–Evans Observation 2** as an explicit named hypothesis. Its own graph decomposition, directed realization, quartet attribution and dynamic-programming argument are proved locally. See [REPORT.md](REPORT.md) for the source audit and precise scope.

The graph library treats arbitrary finite rooted binary level-1 networks with a root-preserving subdivision of the supplied constraint tree. It proves their canonical cycle representation and switching/cut invariance. The recurrence uses the paper's Equations 1–5 and proves feasibility, attainment and global optimality. The exact-budget variant uses a maximum-pruned knapsack recurrence, with infeasible counts represented explicitly. Abstract unit-cost operation and compressed-storage bounds match the source asymptotic forms.

The main proof follows the paper's argument. An additional canonical wire bridge formalizes deletion and suppression and reuses Lemma 2 for ghost-wire ownership; the report records this representation step.

Two false secondary claims receive the user-approved corrections: monotonicity holds for **at most** a reticulation budget; recovery needs explicit inclusion-identifiability and minimum-reticulation tie-breaking. The report records counterexamples, the weighted interpretation of Eq. 1 and every proof departure.

## Build and verification

The toolchain and Mathlib are pinned to `v4.35.0-rc4`.

```sh
lake exe cache get
lake build
lake env lean scripts/Audit.lean
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
python3 scripts/sync_challenge_defs.py --check
lake env lake comparator --config=comparator.json
```

[`Challenge.lean`](Challenge.lean) contains deliberate proof placeholders for the four immutable target statements; [`Solution.lean`](Solution.lean) proves the same statements. The library passes the standard-axiom audit, and Comparator accepts all four target statements under Lean and NanoDa. Local packaging is intended for Palomar; publication, external preflight and registration require separate authorization.

The dated literature search found no earlier CAMUS formalization or erratum. Related quarnet reconstruction methods and later NetCS work address different inputs or pipeline stages; [REPORT.md](REPORT.md#10-literature-context) gives the primary sources and scope of that search.

To refresh the audit's generated import list after adding a module, run `python3 scripts/update_audit_imports.py`. The shared Challenge definition copy is maintained by [`scripts/sync_challenge_defs.py`](scripts/sync_challenge_defs.py).

This development used Codex CLI 0.162.0-alpha.2 with `gpt-6.1-sol` and three collaborating agents, following [formalize-math-paper 2.2.0](https://github.com/vltanh/formalize-math-paper). Human authorship and automation accounting are recorded separately in [CREDITS.md](CREDITS.md). Independent review is documented in [docs/review.md](docs/review.md).
