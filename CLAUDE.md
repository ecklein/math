# CLAUDE.md — research process for this repository

This repository is a monorepo of mathematics research projects. Each one pairs machine-checked Lean 4
proofs with a paper. Projects live in `research/<project>/` and are self-contained (see `README.md`).
Each project has its own `CLAUDE.md` holding project-specific state; read it before working there.

Keeping these files current is part of the job:
- At the end of any session that changes results, status, commands or conventions, update the
  project's `CLAUDE.md` (state, open tasks, gotchas).
- Lessons that would help *any* project belong in this file.
- Keep both concise: state facts, not narrative. The research log lives in `notes/research_log.md`.

## Research workflow

Follow these phases. Later ones often send you back to earlier ones.

1. **Audit the foundations.** Clone the exact dependency commit and read its statement files (e.g.
   `Statements.lean`), the theorem interface you will use, and its build pins. Record facts in
   `notes/<dep>_audit.md`, marking which you checked yourself and which are only reported by others.
   Know precisely what the dependency does *not* prove. Example: the GRH proof locates zeros but
   gives no explicit prime-sum bound.
2. **Pinned environment first.** Match the dependency's Lean toolchain and Mathlib commit exactly. Use a
   path dependency on a git-ignored `vendor/` checkout, created by `verification/fetch_deps.sh`, so its
   build is reused. After `lake update`, check that every package revision in `lake-manifest.json`
   matches the dependency's manifest.
3. **Literature review** (`notes/literature_review.md`). Tag every item: **[O]** = opened and read,
   **[S]** = seen only in search snippets or secondary sources, **[M]** = from memory. Only [O] items may
   be cited in the paper.
4. **Candidates.** Write at least three precise candidate theorems (`notes/conjectures.md`). Rank them on
   novelty, significance, feasibility, dependence on the new input, usefulness and formalization cost.
   Reject candidates whose novelty is only that they "become unconditional". Record dead ends, with the
   reason, in `notes/failed_approaches.md`.
5. **Novelty assessment** (`notes/novelty_assessment.md`). For each candidate, name the closest results,
   compare hypotheses, conclusions and parameters, and say whether it follows trivially. Never claim
   uniqueness.
6. **Proof obligations** (`notes/proof_obligations.md`). Break the proof into lettered obligations, each
   with status `open` / `informal-done` / `lean-stated` / `lean-done`. Keep the list current.
7. **Informal and formal proofs in parallel.** Prove a result first under an explicit hypothesis (e.g.
   `hGRH : GRHHyp`), then discharge the hypothesis in a single, separate module.
8. **Numerical sanity checks of every bound.** Compute the true quantity exactly where possible and check
   that the bound dominates it. Do this *before* formalizing, and again after. These checks caught two of
   our own errors: a lower-order term of size `e^a` written as `2a`, and an optimal constant of `≈1.2236`
   stated as `2`.
9. **Paper.** Write it only once the results are formal. See "Papers" below.
10. **Re-check novelty before circulating.** Read the *full text* of the closest papers, not just the
    abstracts. Searches over abstracts and snippets missed Lamzouri–Li–Soundararajan §6 (Lemma 6.1), which
    turned out to be the asymptotic form of our main leading term.

## Honesty rules

- Say "formal" only for results that are machine-checked with `sorry`-free proofs and the standard axioms.
  Label everything else "informal" in the notes, READMEs and the paper.
- When an earlier claim turns out wrong, correct it everywhere it appears (notes, README, paper) and
  record the correction with its date. Never quietly rewrite history.
- Empirical statistics are evidence, not proof. Make no cryptographic claims without a reduction.
- Never invent bibliographic data, titles or authors. If a document has no title, say so (example:
  Alpöge's announcement PDF).
- Report modest novelty as modest.

## Lean conventions

- **Structure.** Split modules into `GRH/` (or `<Dep>/`): `Interface` holding the hypothesis, and
  `Discharge` holding the proof from the dependency. Then the analytic layer, the pseudorandomness layer,
  `Vendor/`, and `MainTheorems/Conditional` plus `Unconditional`. The default lake target should exclude
  modules that import the full dependency.
- **Forbidden:** `sorry`, `admit`, new `axiom`s, `native_decide`, `implemented_by`, `@[extern]`.
- **Reuse before rewriting.** Search Mathlib at the pinned commit, then the dependency, then other projects
  on the same pin (PrimeNumberTheoremAnd, rh-prime-error, schoenfeld-rh-lean, zeta-23-lean, grh-miller).
  Vendor what you need with a provenance header (source, commit, license, what changed). List it in
  `ATTRIBUTION.md`.
- **Porting across Mathlib versions.** Copy the import closure, build it, fix the root errors, rebuild, and
  repeat; hidden failures appear in later rounds. Record the full diff in
  `verification/<lib>-port.diff`. API drift we met between Mathlib `51e6992e` and `56a00585`:
  - removed file `Mathlib.Tactic.LinearCombinationPrime`: vendor it from the old commit;
  - `Finset.prod_le_prod` → `prod_le_prod₀`, and `prod_le_one` → `prod_le_one₀` (for nonnegative factors);
  - `logDeriv_mul` / `logDeriv_prod` on pointwise lambdas: fold first with
    `show (fun s => f s * g s) = f * g from rfl`;
  - `positivity` doesn't unfold `id`: use `simp only [id_eq]; positivity`;
  - `fun_prop` can't handle `Nat.floor` measurability: use `Nat.measurable_floor`;
  - `field_simp` normal forms changed;
  - upstream libraries may rely on `autoImplicit = true`: set it per `lean_lib`.
- **Proof-engineering pitfalls:**
  - `set x := … with hx` hides syntactic forms. Lemma results stay in the unfolded form, so `rw`
    and `linarith` see different atoms. Add `have : <unfolded> = x := rfl` and rewrite.
  - `linarith` treats `(A + B)/(2π)` and `A/(2π)` as unrelated atoms. Supply the `add_div` split.
  - Numeric certificates: use Mathlib's `Real.exp_one_gt_d9`/`lt_d9`, `Real.pi_gt_d6`/`lt_d6` and
    `Real.log_two_lt_d9`. Factor every bound into a small lemma: big `nlinarith` calls in large contexts
    hit heartbeat timeouts.
  - Floors and `Nat.log`: bound with `Nat.floor_lt` and `Nat.log_lt_of_lt_pow`. Rewrite `2 ^ 18` to a
    numeral before calling `omega`.
- **Build hygiene.** Use `lake build --no-build <targets>` to see whether anything is stale, for example
  after moving directories. `import Mathlib` files compile slowly while another big build runs.

## Verification checklist

Run this before claiming a result, and record each item in `verification/README.md`:
1. `lake build` of every target, with no errors.
2. `verification/Axioms.lean`: `#print axioms` for every headline theorem. Each must list only `propext`,
   `Classical.choice`, `Quot.sound`. Save the output to `axioms.log`.
3. `verification/EnvAxioms.lean`: list every axiom in the whole imported environment. Only Lean core
   (`Init.*`) entries are allowed.
4. `leanchecker` replay of every project module, recording each module's own exit code. Run the loop
   with `lake env leanchecker $m >/dev/null 2>&1; echo "$m: exit $?"`; piping into `tail` makes `$?`
   report `tail`'s exit code instead.
5. Source scan for the forbidden constructs. Matches inside comments or docstrings (e.g. a docstring
   example containing `axiom`) are not real declarations, but confirm that with check 3.
6. Not yet done in our projects, but planned: Comparator against a Mathlib-only statement file, and
   nanoda/lean4lean replay.

## Experiments

Use Python with the root `.venv` (numpy, sympy, scipy, pypdf; scipy's HiGHS `linprog` handles the extremal-kernel LPs). Prefer exact computation over sampling; for
prime `q`, one FFT over the discrete-log table gives the bias against all characters at once. Commit
scripts and the small result tables (`experiments/out/*.tsv`) that the paper cites.

## Papers

- The author of every paper is **Ethan Klein** (`\author{Ethan Klein}`). Add no other authors, affiliation or email
  unless asked; credit tools and libraries in the acknowledgements instead.
- Every paper ends with a **"Use of AI"** paragraph: it names the model and version, says what the model did and what
  the author did, says the author takes responsibility, and separates kernel-checked from human-reviewed claims.
  Model the wording on `research/grh-pseudorandomness/paper/sections/limitations.tex`.
- Use `paper/` with `main.tex` (amsart), `sections/*.tex` and `references.bib`. Commit the compiled
  `main.pdf`; ignore auxiliary files.
- Every formal claim names its Lean declaration. Statements must match the Lean definitions exactly:
  recheck after any Lean change.
- Verify the bibliography against Crossref (`api.crossref.org/works/<doi>`) or the arXiv API. Record
  any unconfirmed field in the bib `note`.
- Build with BasicTeX: `pdflatex main && bibtex main && pdflatex main && pdflatex main`. There is no
  `latexmk`, and the `enumitem` package isn't available.
  - Typeset Lean identifiers with `\lean` (= `\nolinkurl`, with `\UrlBreaks` at `. _ - /` and capitals).
  - `#` cannot appear inside a macro argument.
  - `amsart` needs the abstract after `\begin{document}`.
- A finished build has no errors, no undefined references or citations, and no overfull boxes. Check the
  PDF text for `??` and `[?]` (extract it with `pypdf`).

## Environment notes (this machine)

- elan in `~/.elan`; TeX in `/Library/TeX/texbin` (add to `PATH`); Python venv at the repository root.
- No `pdftoppm`: read PDFs by text extraction with `pypdf`, working on a copy in the scratchpad.
- Downloading and running prebuilt binaries is blocked by the permission check. Ask the user to install
  tools instead (as with BasicTeX). Homebrew may build dependencies from source on macOS 14, which is slow.
- Machine: 12 cores, 36 GB RAM. The GRH dependency build takes about 1 h 46 min. `leanchecker` takes
  about 1 minute per module.

## Git

- Work on a branch named after the project, never directly on `main`. Commit, push or merge only when the
  user asks. The repository is **public**: pushing publishes.
- End commit messages with the attribution line given in the session. Merge pull requests with a merge
  commit unless told otherwise.
