import GRHPseudo.AnalyticNumberTheory.Sharp.Certificate64
import GRHPseudo.KernelSeparation.Majorant4
import GRHPseudo.MainTheorems.Unconditional

/-! Lists every `axiom` declaration in the environment after importing the project, including
Mathlib, the GRH proof, and the ported explicit-formula library. Anything outside Lean core's own
axioms would be a newly introduced axiom. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if let .axiomInfo _ := ci then names := names.push n
  for n in names.qsort (·.toString < ·.toString) do
    IO.println s!"{n}  (module: {(env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)})"
