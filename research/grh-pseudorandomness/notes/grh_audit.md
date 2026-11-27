# Audit of the GRH formalization (dependency)

Status date: 2026-11-26. Everything below was checked directly in the cloned repository
(`vendor/grh-lean`, commit `72fead102f663d5c7a407964a13dc0cf9d977207`) unless marked
"reported", which means it is taken from the verification pages and not re-run here.

## Pinned environment (checked)

| Item | Value | Source |
|---|---|---|
| Repository | github.com/lsernau/grh-lean | cloned |
| Commit | `72fead10` (the only commit, "Lean proof of GRH") | `git log` |
| Edition used | `grh-compact/` (794 `.lean` files under `src/`) | `find` |
| Lean | v4.35.0, commit `eb6cafb7` | `lean-toolchain`, `lean --version` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` | `lakefile.toml`, `lake-manifest.json` |
| License | Apache 2.0, Copyright 2026 Anthropic, PBC | `LICENSE`, README |
| Lake options | `maxHeartbeats = 4000000`, `--tstack=400000`, `autoImplicit = false` | `lakefile.toml` |

## Theorem interface (checked, `src/Statements.lean`, imports only Mathlib)

```lean
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

`src/Main.lean` proves `riemannHypothesis : RiemannHypothesis` (Mathlib's definition),
`riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`,
`LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`.

The interface we use is `LFunction_ne_zero_of_half_lt_re`. It covers every modulus `N ≥ 1` and
every character, primitive or not, including imprimitive characters, whose `LFunction` in Mathlib
differs from the primitive one by finitely many Euler factors (those factors vanish only on
`Re s = 0`, so the statement is consistent).

## Scope (checked)

- The statements are about zero location only. The repository proves no explicit bound on
  `ψ(x, χ)`, on character sums over primes, on the least prime in a progression, or any
  Chebotarev statement.
- `src/Lib/Analytic` has five files: `PolyaVinogradov`, `Primes/AuxiliaryPrimes`,
  `Landau/PolarLandau`, `QuadraticTwist/ZeroFreeTwist`, `DirichletTheta/MellinTheta`.
  `polya_vinogradov` (unconditional, for `χ ≠ 1`) and `exists_norm_LFunction_le` are potentially
  reusable.
- The proof's own prime-sum statement `eventually_primeError_le_rpow` is an eventual (ineffective,
  modulus-dependent) one-sided bound used to *derive* GRH. It is not a uniform bound and is the
  wrong direction for our purposes.
- GRH is **not** established for Hecke L-functions of imaginary quadratic fields, so
  Jao–Miller–Venkatesan's isogeny/class-group expanders remain conditional. It does give GRH for
  Dedekind zeta functions of abelian number fields (they factor into Dirichlet L-functions), but
  that factorization is not formalized here.

## Verification reported by third parties (not re-run here)

- Sutherland (shortgrh page): sandboxed `lake build` of both editions; `#print axioms` gives
  `propext, Classical.choice, Quot.sound`; `leanchecker` replay 794/794; `lake comparator
  --paranoid` accepted on two machines; nanoda, lean4lean, con-leche, con-ron accept.
- Rubinstein: compact edition compiles, same axioms, leanchecker 794/794, comparator `--paranoid`
  accepted (run without Comparator's sandbox).
- The original (longer) proof uses Lean v4.33.1 and Mathlib `0df444a3`; the two Mathlib
  versions have not been formally checked equivalent. We depend only on the compact edition.
- Rubinstein notes that Alpöge's companion paper does not prove the main inequality; the Lean
  development is the claimed proof. Our results inherit exactly the trust base of that Lean proof.

## Local reproduction (this project)

- elan 4.4.0 installed; toolchain v4.35.0 (`eb6cafb7`) matches the pin.
- `lake exe cache get && lake build` of `grh-compact`: see `verification/` once complete.
