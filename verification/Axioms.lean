import GRHPseudo.MainTheorems.Unconditional
import GRHPseudo.AnalyticNumberTheory.Sharp.Assembly
import GRHPseudo.Pseudorandomness.RankTwo

-- GRH dependency, as used here
#print axioms GRHPseudo.grh
-- analytic layer
#print axioms GRHPseudo.norm_LFunction_le_linear
#print axioms GRHPseudo.norm_logDeriv_LFunction_le
#print axioms GRHPseudo.integral_vertical_eq
#print axioms GRHPseudo.norm_sum_vonMangoldt_char_le
-- pseudorandomness layer
#print axioms GRHPseudo.charSum_eq_eigenvalue
#print axioms GRHPseudo.inner_mul_inner_le
#print axioms GRHPseudo.massLower_le_mass
#print axioms GRHPseudo.bias_primeMeasure_le
-- main theorems
#print axioms GRHPseudo.Main.primeCharSum_conditional
#print axioms GRHPseudo.Main.bias_conditional
#print axioms GRHPseudo.Main.primeCharSum
#print axioms GRHPseudo.Main.bias_primeMeasure
-- sharp route (explicit formula + positivity)
#print axioms Zeta23.ThmE.EF_lit_chi_L
#print axioms Zeta23.WeilEF.EF_lit_zetaZeroConfig
#print axioms GRHPseudo.Sharp.norm_primeSide_twist_le
#print axioms GRHPseudo.Sharp.primeSideZeta_twist_eq
#print axioms GRHPseudo.Sharp.norm_gammaSide_twist_le
#print axioms GRHPseudo.Sharp.bias_sharp
-- Layer 2: closed-form constants and the q ≤ 2^64 certificate
#print axioms GRHPseudo.Sharp.bias_closed
#print axioms GRHPseudo.Main.zerosOnLine
#print axioms GRHPseudo.Main.bias_sharp_closed
#print axioms GRHPseudo.Main.bias_le_half_of_le_two_pow_64
