# Credits

How this formalization was made, from the run logs and the session transcripts.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the formalization, chose its scope (the
  directed-graph model of networks, the corrected statements of Sections 2.4 and 3.2) and asked for
  the second round.
- **Formalization:** two AI systems, in two rounds. The first formalization was made by OpenAI's
  `gpt-6.1-sol` in Codex CLI 0.162.0-alpha.2, from an empty project, with three sub-agents. The
  second round, a restyle with a new audit, was made by Claude Opus 5.5 (`claude-opus-5-5`,
  Anthropic) in Claude Code 2.1.296 (VS Code extension), in one session with sub-agents.
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill,
  version 2.2.0 (commit `d82a98e1237e5b864bb76185b1ebb5548092a184`), in both rounds.
- **Review:** no person has reviewed the proofs. In each round, agents other than the provers
  reviewed the statements against the paper and compared the proofs with the paper's; in the second
  round, other agents also checked the report's findings and its account of the literature against
  their sources.

## The first formalization (8 October 2026)

How it was made, from the first round's own record:

- **The paper.** The main session set up the project on Lean and Mathlib `v4.35.0-rc4` and took the
  publisher's JATS XML as the source of record, since no TeX source is public.
- **The statements.** The main session wrote the definitions and the statements, with a
  directed-graph model of rooted level-1 networks; a review sub-agent checked them against the
  paper, and the baseline was committed. The author chose a conditional formalization, which
  assumed Observation 2 of Warnow, Tabatabaee and Evans, and the corrected statements of Sections
  2.4 and 3.2.
- **The proofs.** The main session proved the geometry of the dynamic program, the forms of the
  equations, the display of the tree and the invariance under subdivision, and assembled Theorem 1.
  Three sub-agents proved the rest: one the completeness of the canonical networks, one their
  realization (with the reticulation bounds, the operation counts and the counterexample of Section
  2.4), and the review sub-agent, resumed eight times, the invariance under isomorphism, Lemma 1,
  the exact-budget recurrence and the report. Each large group of proofs was reviewed by a
  sub-agent other than its prover.
- **The checks.** The main session ran the builds, the axiom audit, the route check and Comparator,
  and wrote the Palomar files.

Figures, from 8 October 2026, 17:29 CDT, to the commit that completed its report (`a13d877`,
19:25 CDT), as the first round computed them from the Codex session transcripts:

- **Elapsed time:** 1.94 hours (1 hour 56 minutes).
- **Sub-agents:** 3, at most 3 running at once, for 2.5 hours of working time in all (4.45 hours
  with the main session).
- **Tool calls and tokens:** 980 top-level tool calls in all. The sub-agents used 0.35 million
  output tokens, 1.83 million uncached input tokens and 71 million cache reads; the main session
  used 0.23 million output tokens, 1.04 million uncached input tokens and 40 million cache reads.
- **Model calls:** all to `gpt-6.1-sol`; the transcripts do not record their number.

## The restyle (10 October 2026)

The author asked to "restyle it in your usual way": to present the formalization as the procedure's
other formalizations are presented.

How it was made:

- **The library.** The main session moved the 87 modules into directories by the paper's sections
  and topics, removed six modules that only re-exported others, and later removed three duplicated
  lemmas. Six sub-agents, each on its own group of files, wrote a module docstring for every file,
  rewrote the declaration docstrings in the paper's terms with the paper's labels, and marked the
  paper's steps in the main proofs, changing no code; the main session checked that with comments
  removed every file was unchanged.
- **Observation 2.** The main session proved Observation 2 of Warnow, Tabatabaee and Evans, which
  the first round had assumed (and which its authors state without proof), from the library's
  lemmas on switchings and cycles, and removed the hypothesis from every result: the formalization
  became unconditional. It also proved the second sentence of Lemma 1 for every network built on
  the tree.
- **The statements.** The main session restated the Challenge in the procedure's form: Theorem 1,
  the claim of Section 2.4 for networks, the two refuted claims as negations, the corrected
  Section 3.2 for networks, and theorems that show the definitions and hypotheses meaningful. It
  replaced three statements of the first round that were generic lemmas about finite families.
- **Review.** A sub-agent reviewed every statement against the paper's JATS source and found them
  faithful; it also showed that CAMUS itself may return the wrong network on the counterexample of
  Section 3.2, which the main session added to the library. A sub-agent searched the literature and
  the paper's versions.
- **The audit.** The main session rewrote the audit script, the routes of the paper's proofs, CI,
  and wrote [`REPORT.md`](REPORT.md) and [`README.md`](README.md), renumbering the findings in the paper's order and adding
  three (E1, E2 and the typos, E9 since the third round). A sub-agent
  checked every finding of the report and every summary of another work against its source, and the
  main session applied its corrections.

Figures, from 10 October 2026, 08:21 CDT, to the commit that completes [`REPORT.md`](REPORT.md) (`d23396d`,
10:08 CDT), taken from the session's transcript with the skill's `session_stats.py`:

- **Elapsed time:** 1.78 hours (1 hour 47 minutes).
- **Sub-agents:** 9 (six for the documentation, one for the review of the statements, one for the
  literature, one for the verification of the report), at most 8 running at once, for 4.2 hours of
  working time in all.
- **Tool calls and tokens:** the sub-agents made 1,324 tool calls, with 3.71 million input tokens and
  187 million cache reads; the main session made 245 tool calls, with 0.40 million output tokens,
  0.86 million input tokens and 125 million cache reads. The sub-agents' transcripts record their
  output tokens only in part (most messages carry the count at the start of their stream), so their
  recorded 0.03 million output tokens is a lower bound.
- **Model calls:** 1,020, all to Claude Opus 5.5 (234 by the main session, 786 by the sub-agents).

The elapsed time includes the builds, which the transcript does not separate from the rest. The
figures leave out the work after the report: the credits, and the final checks of the packaging.
