# Credits

How this formalization was made, from the run logs and the session transcripts.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the formalization, chose its scope (the
  directed-graph model of networks, the corrected statements of Sections 2.4 and 3.2), asked for
  the second, third and fourth rounds, and approved copying the network multispecies coalescent
  from their formalization of BROOQS.
- **Formalization:** two AI systems, in four rounds. The first formalization was made by OpenAI's
  `gpt-6.1-sol` in Codex CLI 0.162.0-alpha.2, from an empty project, with three sub-agents. The
  second round, a restyle with a new audit, and the third and fourth, which formalized what the
  second had left out, were made by Claude Opus 5.5 (`claude-opus-5-5`, Anthropic) in Claude Code
  2.1.296 (VS Code extension), in one session with sub-agents.
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill,
  version 2.2.0 (commit `d82a98e1237e5b864bb76185b1ebb5548092a184`), in all four rounds.
- **Review:** no person has reviewed the proofs. In the first three rounds, agents other than the
  provers reviewed the statements against the paper and compared the proofs with the paper's; in
  the second and third rounds, other agents also checked the report's findings and its account of
  the literature against their sources. In the fourth round, an agent other than the prover
  reviewed only the files of the SNP pipeline.

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
  three (E1, E2 and the typos, E10 since the fourth round). A sub-agent
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

## The third round (10 October 2026)

The second round's report listed what it left out (its Section 9). Asked whether those items should
be formalized, Claude proposed four: backtracking in the modified dynamic program of Section 2.4,
Section 3.2 inside the site model of Warnow, Tabatabaee and Evans, Definition 1's networks whose root
lies above the root of `T`, and the motivation of Algorithm 1 from the multispecies coalescent. The
author answered: "I think there is a proof of running time complexity? Add counterexamples. Do 1-4."

How it was made:

- **The plan.** Before the round, the main session had found, in the block grammar, the deeper-donor
  counterexample to identifiability under inclusion. It added lean4-adr11 as a dependency, wrote the
  statements that the workstreams would share (Definition 1 by the clades of switchings, the
  quartets displayed by `T + e`, the deeper-donor counterexample) with temporary proofs, checked them
  by evaluation, and started six sub-agents at once, each in its own git worktree and branch.
- **The work.** The sub-agents proved:
  - the shared statements and the deeper-donor counterexample, with its general form for cross
    pairs and a backtracking trace that returns the wrong network;
  - backtracking for Section 2.4, and, after a computer search, the counterexample to the stopping
    rule (E6);
  - the cost semantics of Sections 2.3 and 2.4, with the constant-time quartet test;
  - Definition 1's class, Theorem 1 over it, and the false claim of Section 3.2 on bases (E8);
  - the site model of Warnow, Tabatabaee and Evans, with the gap in their Theorem 6, the ASTRAL
    step, the corrected recovery and E7 in the model;
  - Algorithm 1 under the multispecies coalescent, from lean4-adr11.
- **Integration.** The main session merged the six branches, moved the definitions that the new
  statements need into the shared block, restated the Challenge (15 theorems), retired the
  accounting of Section 2.3 that the cost semantics supersedes, renumbered the findings in the
  paper's order, updated the audit, and rewrote the report.
- **Review.** Two sub-agents checked the round's statements against the paper and against Warnow,
  Tabatabaee and Evans, and the report against its sources and the code. They found that the
  counterexample in the site model lacked the outgroup that the paper assumes, and that the site
  model was a special case of theirs; the sub-agent of the site model, resumed, fixed both, and the
  main session applied the corrections to the report.

Figures, from 10 October 2026, 10:28 CDT (the author's request), to the commit that completes the
report of this round (`f08c4ba`, 13:16 CDT), taken from the session's transcript with the skill's
`session_stats.py`:

- **Elapsed time:** 2.81 hours (2 hours 49 minutes).
- **Sub-agents:** 10: six workstreams, two reviewers, and two read-only helpers that a reviewer
  started; at most 6 running at once; one resumed once; 7.1 hours of working time in all.
- **Tool calls and tokens:** the sub-agents made 1,226 tool calls, with 6.21 million input tokens and
  425 million cache reads; the main session made 194 tool calls, with 0.41 million output tokens,
  0.71 million input tokens and 87 million cache reads. As in the second round, the sub-agents'
  recorded 0.03 million output tokens is a lower bound.
- **Model calls:** 1,380, all to Claude Opus 5.5 (193 by the main session, 1,187 by the sub-agents).

The figures leave out the work after the report: the wrapping of long lines, the credits, and the
final checks of the packaging.

## The fourth round (10 October 2026)

Asked whether the formalization went too far, and what of the paper it still left out, Claude
listed the items that remained in the third round's report. The author chose: "1-3 seem ok. the
first 2 points of 4 seems ok. for the NMSC model, would @../lean4-brooqs helps?", and on the
network multispecies coalescent of their formalization of BROOQS: "Maybe you can copy it to here.
This paper is published, so should be fine to make the public library." A library shared with the
author's other formalizations was put off.

How it was made:

- **The plan.** The main session wrote a brief for the round and started three sub-agents at once,
  each in its own git worktree: tree-basedness, with Figure 1 and the totality of the pipeline;
  trees determined by their quartets, with the SNP pipeline of Section 3.2 as one statement; and
  the time of backtracking in Section 2.4, with peak memory. After the author's answer, it copied
  the network multispecies coalescent of the formalization of BROOQS (commit `1c2eede`) into
  [`Camus/External/NMSC/`](Camus/External/NMSC) and started a fourth sub-agent on Sections 3.3 and 3.4 under that model.
- **The work.** The sub-agents proved:
  - that every level-1 network is built on one of its trees, with at most `n − 1` reticulations,
    and which quartet trees the network of Figure 1 displays;
  - that two trees with the same quartets are equal up to the order of their children (Steel's
    theorem, through lean4-adr11), and the SNP pipeline as one statement in the site model, with
    an outgroup;
  - the time of backtracking in Section 2.4, `O(n²(|Q| + m³n))`, and the peak memory of the
    programs of Sections 2.3 and 2.4, in a cost semantics with a space component;
  - Quartet Filtering under the network coalescent: the pattern of the quartet concordance factors
    outside the anomalous configuration, the consistency of the filter there, and the anomalous
    3-cycle of Ané et al. (2024), under which the filter keeps a quartet tree that the network does
    not display (E9).
- **Integration.** The main session merged the four branches, removed two modules that duplicated
  others, wrapped long lines, updated the audit, and rewrote the report with the new finding.
- **Review.** A read-only sub-agent, started by the sub-agent of the pipeline, reviewed its new
  files; that sub-agent, resumed, applied the findings. The author asked why the round took so long
  ("Why are we taking so long? Are we trying to prove new results?"); the main session explained
  that the network coalescent goes beyond the paper, and asked the fourth sub-agent to wrap up,
  after about three hours.

Figures, from 10 October 2026, 13:42 CDT (the author's request), to the commit that completes the
report of this round (`e96eedd`, 16:56 CDT), taken from the session's transcript with the skill's
`session_stats.py`:

- **Elapsed time:** 3.24 hours (3 hours 14 minutes).
- **Sub-agents:** 5: four workstreams and the reviewer that one of them started; at most 5 running
  at once; one resumed once; 5.5 hours of working time in all.
- **Tool calls and tokens:** the sub-agents made 832 tool calls, with 4.17 million input tokens and
  312 million cache reads; the main session made 74 tool calls, with 0.13 million output tokens,
  1.13 million input tokens and 59 million cache reads. As in the earlier rounds, the sub-agents'
  recorded 0.01 million output tokens is a lower bound.
- **Model calls:** 885, all to Claude Opus 5.5 (80 by the main session, 805 by the sub-agents).

The figures leave out the work after the report: the credits, and the final checks of the
packaging.
