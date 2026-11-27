import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Bias of weighted integer distributions against Dirichlet characters

A *weighted sample space* is a finite set `S ⊆ ℕ` with nonnegative weights `w`. Its pushforward
to `ZMod q` defines a distribution on `(ZMod q)ˣ` when every element of `S` is coprime to `q`.
Its *bias* against a Dirichlet character `χ` is `‖Σ_{n∈S} w n χ n‖ / Σ_{n∈S} w n`.

`charSum_eq_eigenvalue` is the identity that makes bias the spectral quantity. The function `χ`
on `ZMod q` is an eigenfunction of the averaging operator `f ↦ (g ↦ Σ w n f(g n))` of the weighted
Cayley graph, with eigenvalue `Σ w n χ n`.
-/

namespace GRHPseudo

open Finset

variable {q : ℕ}

/-- The unnormalised character sum `Σ_{n∈S} w n χ n`. -/
noncomputable def charSum (S : Finset ℕ) (w : ℕ → ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ S, (w n : ℂ) * χ n

/-- Total mass. -/
noncomputable def mass (S : Finset ℕ) (w : ℕ → ℝ) : ℝ := ∑ n ∈ S, w n

/-- Bias of the weighted sample space against `χ`. -/
noncomputable def bias (S : Finset ℕ) (w : ℕ → ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ‖charSum S w χ‖ / mass S w

/-- Averaging operator of the weighted Cayley graph on `ZMod q`, acting on functions. -/
noncomputable def cayleyAvg (S : Finset ℕ) (w : ℕ → ℝ) (f : ZMod q → ℂ) : ZMod q → ℂ :=
  fun g ↦ ∑ n ∈ S, (w n : ℂ) * f (g * n)

/-- Characters are eigenfunctions of the Cayley averaging operator; the eigenvalue is the
character sum. -/
theorem charSum_eq_eigenvalue (S : Finset ℕ) (w : ℕ → ℝ) (χ : DirichletCharacter ℂ q)
    (g : ZMod q) : cayleyAvg S w (χ : ZMod q → ℂ) g = charSum S w χ * χ g := by
  simp only [cayleyAvg, charSum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  ring

/-- Normalised bias bound from an absolute bound and a mass lower bound. This is the step where
an analytic estimate turns into a pseudorandomness statement. -/
theorem bias_le_of_bounds (S : Finset ℕ) (w : ℕ → ℝ) (χ : DirichletCharacter ℂ q) {E M : ℝ}
    (hE : ‖charSum S w χ‖ ≤ E) (hM : 0 < M) (hmass : M ≤ mass S w) : bias S w χ ≤ E / M := by
  unfold bias
  have hm : 0 < mass S w := lt_of_lt_of_le hM hmass
  calc ‖charSum S w χ‖ / mass S w ≤ E / mass S w := by gcongr
    _ ≤ E / M := by
      have hE0 : 0 ≤ E := le_trans (norm_nonneg _) hE
      exact div_le_div_of_nonneg_left hE0 hM hmass

end GRHPseudo
