import GRHPseudo.MainTheorems.Unconditional
import GRHPseudo.KernelSeparation.Majorant4
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
-- convolution-square kernel (majorant positivity, sharper gamma bound, certificate n ≤ 48400)
#print axioms GRHPseudo.Sharp.norm_primeSide_twist_le_maj
#print axioms GRHPseudo.Sharp.primeSideZeta_twist_eq_maj
#print axioms GRHPseudo.Sharp.Ilog_div_le_sharp
#print axioms GRHPseudo.Sharp.Conv.bias_sharp
#print axioms GRHPseudo.Sharp.Conv.bias_closed
#print axioms GRHPseudo.Main.bias_convSq_sharp
#print axioms GRHPseudo.Main.bias_convSq_closed
#print axioms GRHPseudo.Main.bias_le_half_of_le_two_pow_64_convSq
-- window-4 kernel separation (paper Lemma 16 part 2, Prop 17(1) with constant 9/8, Prop 18 instance)
#print axioms GRHPseudo.KernelSeparation.certOK_sound
#print axioms GRHPseudo.KernelSeparation.certOK_data
#print axioms GRHPseudo.KernelSeparation.paperFT_tri
#print axioms GRHPseudo.KernelSeparation.integral_paperFT_mul_cexp
#print axioms GRHPseudo.KernelSeparation.paperFT_pwl
#print axioms GRHPseudo.KernelSeparation.integral_pwl_mul_exp
#print axioms GRHPseudo.KernelSeparation.integral_norm_paperFT_pwl_le
#print axioms GRHPseudo.KernelSeparation.kernel4_separation
#print axioms GRHPseudo.KernelSeparation.nine_eighths_lt_convSq_window4
#print axioms GRHPseudo.KernelSeparation.window4_kernel_beats_convSq
#print axioms GRHPseudo.KernelSeparation.kernel4_majorant
