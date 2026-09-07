# Project origins and retrospective Git history

According to the author, this project originated during a visit to the
University of Edinburgh in November 2025. No GitHub repository was created
or published at that time. The surviving directory does not establish exact
development dates or the sequence of individual implementation changes.

The surviving local Git records begin on August 28, 2026. This history was
reconstructed on 2026-09-07 from recovered Git snapshots, module dependencies,
documentation, filesystem metadata, and cached build artifacts. All new Git
author and committer dates record the reconstruction itself. No November 2025
day or time has been invented or used to backdate a commit.

## Evidence and limits

- The earliest recoverable commit, `28e4bd6de198f13f9ac117ba9d6d3338d26ba3c6`,
  already contains the full pipeline, Duper reconstruction, and the three
  current test modules. No earlier implementation snapshots were found.
- The original main history ended at
  `6a7f54f0a2f3d52e9bed0f3364db738f9d13bb54`, following the initial import
  `28d30d6b10fb4b6f081bad90b81238e23362a09f` and licensing commit
  `9ab135af9cbc55e25795c4035c1e6b46cc71b888`.
- Local reflogs record repository creation activity and pushes on August 28,
  2026. Remote state was not independently checked during reconstruction.
- Some root file creation timestamps are August 27, 2026. Most source file
  timestamps coincide with the August 28 translation cherry-pick. They do
  not establish original development dates.
- The pinned Duper, lean-auto, and batteries commits are dated May 26, 2026.
  The recovered Lean v4.30.0 environment is not a November 2025 snapshot.
- No independent source backups or November 2025 notes were found within
  the project directory. Third-party trees were inventoried, not audited
  line by line for their own development history.
- README and encoder comments describe dependent-sort and nonempty-sort
  issues. The recovered source already has safeguards; no pre-fix version
  was manufactured to create a separate historical fix event.

## Reconstructed stages

| Stage | Contents | Historical date and confidence |
| --- | --- | --- |
| 1 | Configuration, shared types, utilities, SMT syntax | Unknown; present by August 28, 2026. High confidence in logical foundation role; low confidence in historical date. |
| 2 | Premise features, collection, selection | Unknown; present by August 28, 2026. High confidence in dependency order; low confidence in historical date. |
| 3 | Encoding, problem assembly, monomorphization | Unknown; present by August 28, 2026. High confidence in dependency order; low confidence in historical date. |
| 4 | z3 and cvc5 backends | Unknown; present by August 28, 2026. Must logically precede integration; order relative to premise and encoder work is unknown. |
| 5 | Tactic frontend and optional reconstruction hook | Unknown; present by August 28, 2026. High confidence in dependency order; low confidence in historical date. |
| 6 | Duper adapter, public imports, integration tests | Unknown; present by August 28, 2026. High confidence in logical grouping; exact original order unknown. |
| 7 | Chinese README and package rename | August 28, 2026: README present by 22:49:45, rename recorded by 22:52:49 (UTC+08:00). High confidence in recorded order. |
| 8 | Apache-2.0 license | August 28, 2026, recorded author time 22:54:14 (UTC+08:00). High confidence in recorded order. |
| 9 | English documentation and messages | August 28, 2026, recorded author time 23:05:04 (UTC+08:00). High confidence in recorded order. |
| 10 | This provenance record | 2026-09-07. New documentation, not an inferred historical event. |

Stages 1–6 are logical subdivisions of one recovered complete snapshot,
not independently recovered historical versions. Their intermediate trees
are not claimed to be buildable historical releases. Configuration retains
the recovered dependency pins and options even before their consuming modules
are introduced. Public import roots arrive with their dependencies in stage 6.
Stage 7 combines recovered documentation and naming states. Stages 7, 8,
and 9 reproduce the corresponding original Git trees exactly. Stage 10 adds
only provenance documentation. Existing source authorship and coauthor/session
attribution are retained in the reconstructed import commit messages.

## Generated files and experiment evidence

The `.lake` directory was inventoried at 6,302 files, approximately 729 MB,
including dependencies, compiled Lean modules, generated C, shared libraries,
and build traces. It remains ignored and is not part of the reconstructed
source history. `lake-manifest.json` remains tracked as the dependency lockfile;
its old `LeanHammer` package name is preserved rather than silently repaired.

Cached traces inspected before reconstruction recorded 19 unsat results,
12 Duper proofs, and 7 trust-axiom closures in each of `HammerTest.Basic`
and `HammerTest.Reconstruct`. These were existing results, not fresh validation
at the time of the inspection. The soundness suite contains five negative
examples using `fail_if_success` and intentional `sorry`; its cached trace
reported no errors. These checks are not a general soundness proof.

Generated C/setup/hash remnants of `HammerTest.NoRecon`, dated August 28,
2026, survive without its source. They establish that a module with that name
was compiled, not its original test contents. No source was recreated from
that name. No standalone experiment dataset or source backup was found
outside the generated/dependency trees and recoverable Git objects.

## Preservation

The original `main` branch and remote configuration were retained. Before
reconstruction, all locally recoverable commits were anchored under
`refs/archive/pre-reconstruction/` and included in a verified local Git bundle
under `.git/history-preservation/`. The original reflog and HEAD identifier
were saved beside the bundle. These local preservation files are not tracked
project files and are not automatically included in a normal clone.

The reconstructed history is on `reconstructed-history`. No remote history
was rewritten or pushed as part of this reconstruction.
