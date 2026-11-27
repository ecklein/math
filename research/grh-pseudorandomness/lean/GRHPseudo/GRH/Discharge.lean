import GRHPseudo.GRH.Interface
import Main

/-!
# Discharging the GRH hypothesis

`LFunction_ne_zero_of_half_lt_re` is the compact edition's theorem (its `src/Main.lean`), whose
type is the definition `DirichletLNonvanishingRightOfHalf` from `src/Statements.lean`. Lean checks
here that it has exactly the type `GRHHyp` used throughout this project.
-/

namespace GRHPseudo

/-- GRH for Dirichlet L-functions, from the Lean proof of Alpöge (with Claude), compact edition. -/
theorem grh : GRHHyp := LFunction_ne_zero_of_half_lt_re

end GRHPseudo
