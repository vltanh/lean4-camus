# Credits

## Who

- Human author and maintainer: The-Anh Vu-Le, from the workspace's Git identity and skill configuration. The user chose the target and approved the corrected recovery and budget statements, the cited conditional premise, and completion of the directed-network library.
- Formalization: Codex CLI 0.162.0-alpha.2 with model `gpt-6.1-sol`, as recorded by the local session transcripts. Work began from an empty project, with no imported Lean draft.
- Procedure: [formalize-math-paper](https://github.com/vltanh/formalize-math-paper), version 2.2.0. Statements were reviewed before proofs and recorded in commit `f51f064`.
- Review: independent collaborating agents checked the published JATS source, proof routes, graph bridges, budget recurrence, cost model, findings and literature. No human mathematical review or paper-author endorsement is claimed.

## First formalization, 8–9 October 2026 UTC

- The parent agent set up the pinned Lean/Mathlib project, archived the source, proved scalar DP geometry, literal equation/frontier bridges, baseline display and general subdivision invariance, assembled the main theorem, and integrated the checks and packaging.
- Three distinct subagents worked on graph completeness, directed realization and source/proof review. The reviewer was resumed for attribution, budget proofs and audit work. All used the inherited model; no model override was supplied.
- The graph completeness agent proved extraction, admissibility, cycle geometry, vertex decoding, canonical isomorphism and suppression transport.
- The realization agent proved degrees, DAG and cactus laws, support construction, canonical wire refinement, reticulation bounds, operation/storage counts and the directed budget counterexample.
- The source-review agent independently checked statements and proof routes, proved isomorphism transport and quartet attribution, developed the exact-budget knapsack recurrence and prepared the audit report. Review of each large proof group came from an agent other than its prover.
- Agents compiled against private artifact snapshots. The parent ran one integrating Lake build at a time.

Accounting runs from **2026-10-08 17:29:13 America/Chicago (22:29:13 UTC)** to the REPORT completion commit **a13d877**, at **2026-10-08 19:25:44 America/Chicago (2026-10-09 00:25:44 UTC)**. Figures come from local Codex JSONL transcripts, summarized in [docs/run-stats.json](docs/run-stats.json).

- Elapsed time to the audited report: **1 h 56 min 31 s**.
- Distinct subagents: 3; maximum active subagents: 3; maximum agents including the parent: 4.
- Combined subagent active time: **2 h 30 min 15 s**, excluding idle intervals; including the parent: **4 h 26 min 46 s**. Active time includes tool execution and waiting inside an active turn.
- Source reviewer: 9 own turns (8 resumptions); completeness agent: 3 (2 resumptions); realization agent: 2 (1 resumption). Their inherited fork histories are excluded.
- Top-level tool requests: **980**. Nested calls inside orchestration cells and shell commands are not counted as additional top-level requests.
- Model: `gpt-6.1-sol`; exact model-call counts are not exposed. The raw summary records distinct cumulative token-usage reports instead.
- Monetary spend: not tracked. Local Lean builds and a remote model service were used.
- Publishing, external preflight and registry submission were not performed.

Token accounting, with input split into uncached input and cache reads:

| Work | Uncached input | Cache reads | Total input | Output |
| --- | --- | --- | --- | --- |
| Parent | 1,039,125 | 40,162,432 | 41,201,557 | 227,852 |
| Subagents | 1,826,042 | 71,052,416 | 72,878,458 | 345,950 |
| Total | 2,865,167 | 111,214,848 | 114,080,015 | 573,802 |

Reported reasoning output: 205,527 tokens, included in output. Cache-write input: 0. Counts use the latest cumulative usage at the report commit, subtracting each child's inherited baseline before its first own turn. They exclude packaging work after that commit. No raw transcript text or session identifiers are published. [`scripts/codex_run_stats.py`](scripts/codex_run_stats.py) implements this accounting.
