# math

A monorepo for mathematics research. Each project pairs machine-checked proofs (Lean 4) with a
paper, experiments, and research notes. Projects are self-contained and independent of each other.

## Projects

| Project | Topic | Status |
|---|---|---|
| [`research/grh-pseudorandomness`](research/grh-pseudorandomness/) | Explicit, formally verified spectral bounds for prime Cayley graphs on (ℤ/qℤ)^×, built on the Lean proof of GRH for Dirichlet L-functions | Lean results complete (unconditional, standard axioms only); paper draft complete ([PDF](research/grh-pseudorandomness/paper/main.pdf)) |

## Structure

```
math/
├── README.md            this file
├── LICENSE              MIT (original work; see "Licensing")
├── .gitignore           shared ignores (build outputs, vendored checkouts, virtualenvs)
└── research/
    └── <project>/       one directory per project, fully self-contained
        ├── README.md        results, layout, how to reproduce
        ├── lean/            Lean 4 project with its own lakefile, lean-toolchain and Mathlib pin
        ├── paper/           LaTeX source and compiled PDF
        ├── experiments/     numerical experiments; scripts and the small result tables (out/) cited by the paper
        ├── verification/    dependency fetch script, axiom audits, kernel-replay logs
        ├── notes/           literature review, candidate results, proof obligations, research log
        ├── ATTRIBUTION.md   third-party code and results used, with licenses
        └── vendor/          (git-ignored) pinned external checkouts, created by verification/fetch_deps.sh
```

Not every project needs every directory. A project with no formal component has no `lean/`, for example.

## Conventions

- **Self-contained projects.** All paths inside a project are relative to that project's directory. Its README
  says how to reproduce everything from there. Projects may pin different Lean and Mathlib versions.
- **Pinned dependencies.** Every external dependency is pinned to a commit. Large checkouts and build outputs
  (`vendor/`, `.lake/`, `.venv/`, LaTeX auxiliary files) are not committed; each project's
  `verification/fetch_deps.sh` recreates them.
- **What counts as proved.** A result is called *formal* only if it builds without `sorry`, and its
  `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`. The audit logs are committed
  under `verification/`. Papers name the Lean declaration behind each formal claim and mark everything else
  as informal.
- **Honest novelty.** Each project keeps a literature review and novelty assessment in `notes/`, and its
  paper credits closely related prior work explicitly.
- **Attribution.** Vendored or adapted code is listed in the project's `ATTRIBUTION.md` and keeps a provenance
  header in each file.
- **Branches.** Work happens on per-project branches (e.g. `grh-pseudorandomness`) and is merged into `main`.

## Starting a new project

1. Create `research/<project-name>/` with a `README.md` stating the question and the planned deliverables.
2. Add only the subdirectories you need: `notes/` first, then `lean/` (`lake new`, pin the toolchain), `paper/`,
   and `experiments/`.
3. If it builds on external Lean projects, pin them in `verification/fetch_deps.sh` and depend on them via
   `vendor/` paths.
4. Add a row to the project table above.

## Licensing

Original work in this repository is under the MIT License (`LICENSE`). Third-party code vendored into a
project keeps its original license, typically Apache-2.0 for the Lean projects used so far. It is listed in
that project's `ATTRIBUTION.md`.
