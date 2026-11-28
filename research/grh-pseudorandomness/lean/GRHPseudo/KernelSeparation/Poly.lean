import Mathlib

/-!
# Integer list polynomials and an exact sum-of-squares certificate

Polynomials with integer coefficients are lists `[a₀, a₁, …]`, evaluated at `w : ℂ` as
`evC a w = ∑ⱼ aⱼ wʲ`. On the unit circle, `‖evC a w‖² = c₀ + 2 ∑_{m ≥ 1} cₘ Re wᵐ` with
`cₘ = ∑ⱼ aⱼ aⱼ₊ₘ` the autocorrelation `acf a` (`normSq_evC`).

`certOK k r g D` is a Boolean check, cheap enough for the kernel (`decide +kernel`), of the identity
`|r(w)²|² − D²|k(w)|² − |g(w)|² = E(w)` with `E` coefficient-dominated (`E₀ ≥ 2 ∑_{m≥1} |Eₘ|`).
Its soundness theorem `certOK_sound` gives `D ‖k(w)‖ ≤ ‖r(w)‖²` on the unit circle.
-/

namespace GRHPseudo.KernelSeparation

open Complex

/-- Coefficientwise sum, padding the shorter list with zeros. -/
def ladd : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: ladd xs ys

/-- Scalar multiple. -/
def lsmul (c : ℤ) : List ℤ → List ℤ
  | [] => []
  | x :: xs => (c * x) :: lsmul c xs

/-- Polynomial product (Cauchy product of coefficient lists). -/
def conv : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, b => ladd (lsmul a b) (0 :: conv as b)

/-- Autocorrelation `cₘ = ∑ⱼ aⱼ aⱼ₊ₘ`, `m = 0, …, length − 1`. -/
def acf : List ℤ → List ℤ
  | [] => []
  | a :: as => ladd (lsmul a (a :: as)) (acf as)

/-- `∑ |xᵢ|`. -/
def absSum : List ℤ → ℤ
  | [] => 0
  | x :: xs => (x.natAbs : ℤ) + absSum xs

/-- Coefficient dominance `E₀ ≥ 2 ∑_{m ≥ 1} |Eₘ|`. -/
def dominated : List ℤ → Bool
  | [] => true
  | e :: es => decide (2 * absSum es ≤ e)

/-- The certificate check: `acf (r * r) − D² acf k − acf g` is coefficient-dominated. -/
def certOK (k r g : List ℤ) (D : ℤ) : Bool :=
  dominated (ladd (ladd (acf (conv r r)) (lsmul (-(D * D)) (acf k))) (lsmul (-1) (acf g)))

/-- Evaluation `∑ⱼ aⱼ wʲ` (Horner form). -/
def evC : List ℤ → ℂ → ℂ
  | [], _ => 0
  | a :: as, w => (a : ℂ) + w * evC as w

/-- Constant coefficient (`0` for the empty list). -/
def hd : List ℤ → ℤ
  | [] => 0
  | a :: _ => a

/-- The cosine form `c₀ + 2 ∑_{m≥1} cₘ Re wᵐ = 2 Re (∑ cₘ wᵐ) − c₀`. -/
noncomputable def cosForm (cs : List ℤ) (w : ℂ) : ℝ := 2 * (evC cs w).re - hd cs

@[simp] lemma evC_nil (w : ℂ) : evC [] w = 0 := rfl
@[simp] lemma evC_cons (a : ℤ) (as : List ℤ) (w : ℂ) : evC (a :: as) w = a + w * evC as w := rfl

lemma evC_ladd (xs ys : List ℤ) (w : ℂ) : evC (ladd xs ys) w = evC xs w + evC ys w := by
  induction xs generalizing ys with
  | nil => simp [ladd]
  | cons x xs ih =>
    cases ys with
    | nil => simp [ladd]
    | cons y ys => simp only [ladd, evC_cons, ih]; push_cast; ring

lemma hd_ladd (xs ys : List ℤ) : hd (ladd xs ys) = hd xs + hd ys := by
  cases xs <;> cases ys <;> simp [ladd, hd]

lemma evC_lsmul (c : ℤ) (xs : List ℤ) (w : ℂ) : evC (lsmul c xs) w = c * evC xs w := by
  induction xs with
  | nil => simp [lsmul]
  | cons x xs ih => simp only [lsmul, evC_cons, ih]; push_cast; ring

lemma hd_lsmul (c : ℤ) (xs : List ℤ) : hd (lsmul c xs) = c * hd xs := by
  cases xs <;> simp [lsmul, hd]

lemma evC_conv (a b : List ℤ) (w : ℂ) : evC (conv a b) w = evC a w * evC b w := by
  induction a with
  | nil => simp [conv]
  | cons x xs ih => simp only [conv, evC_ladd, evC_lsmul, evC_cons, ih]; push_cast; ring

lemma cosForm_ladd (xs ys : List ℤ) (w : ℂ) :
    cosForm (ladd xs ys) w = cosForm xs w + cosForm ys w := by
  simp only [cosForm, evC_ladd, hd_ladd, add_re]; push_cast; ring

lemma cosForm_lsmul (c : ℤ) (xs : List ℤ) (w : ℂ) :
    cosForm (lsmul c xs) w = c * cosForm xs w := by
  simp only [cosForm, evC_lsmul, hd_lsmul]
  rw [show ((c : ℂ) * evC xs w).re = c * (evC xs w).re by
    rw [show (c : ℂ) = ((c : ℝ) : ℂ) by push_cast; rfl, re_ofReal_mul]]
  push_cast; ring

/-- On the unit circle, `|a(w)|²` is the cosine form of the autocorrelation. -/
theorem normSq_evC (a : List ℤ) {w : ℂ} (hw : ‖w‖ = 1) :
    normSq (evC a w) = cosForm (acf a) w := by
  induction a with
  | nil => simp [acf, cosForm, hd]
  | cons x xs ih =>
    rw [acf, cosForm_ladd, cosForm_lsmul, ← ih]
    have hw2 : normSq w = 1 := by rw [normSq_eq_norm_sq, hw]; norm_num
    simp only [cosForm, evC_cons, hd]
    set X := evC xs w
    have hre : ((x : ℂ) + w * X).re = x + (w * X).re := by simp
    rw [hre, show ((x : ℂ) + w * X) = ((x : ℝ) : ℂ) + w * X by push_cast; rfl,
      normSq_add, normSq_mul, hw2, normSq_ofReal]
    simp only [mul_re, ofReal_re, ofReal_im, conj_re, conj_im, zero_mul, sub_zero, one_mul]
    ring

lemma norm_evC_le (es : List ℤ) {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖evC es w‖ ≤ absSum es := by
  induction es with
  | nil => simp [absSum]
  | cons e es ih =>
    simp only [evC_cons, absSum]
    calc ‖(e : ℂ) + w * evC es w‖ ≤ ‖(e : ℂ)‖ + ‖w‖ * ‖evC es w‖ := by
            rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ |(e : ℝ)| + 1 * absSum es := by
            gcongr
            rw [Complex.norm_intCast]
      _ = _ := by push_cast [Int.natCast_natAbs]; ring_nf

/-- A coefficient-dominated cosine form is nonnegative on the unit circle. -/
theorem cosForm_nonneg_of_dominated {es : List ℤ} (h : dominated es = true) {w : ℂ}
    (hw : ‖w‖ = 1) : 0 ≤ cosForm es w := by
  cases es with
  | nil => simp [cosForm, hd]
  | cons e es =>
    simp only [dominated, decide_eq_true_eq] at h
    have hb := norm_evC_le es hw.le
    have hre : -‖w * evC es w‖ ≤ (w * evC es w).re := by
      have := abs_re_le_norm (w * evC es w); rw [abs_le] at this; linarith [this.1]
    rw [norm_mul, hw, one_mul] at hre
    have hcast : (2 * absSum es : ℝ) ≤ e := by exact_mod_cast h
    simp only [cosForm, evC_cons, hd, add_re, intCast_re]
    linarith

/-- **Soundness of the certificate.** If `certOK k r g D`, then `D ‖k(w)‖ ≤ ‖r(w)‖²` on the unit
circle. -/
theorem certOK_sound {k r g : List ℤ} {D : ℤ} (hD : 0 ≤ D) (h : certOK k r g D = true) {w : ℂ}
    (hw : ‖w‖ = 1) : (D : ℝ) * ‖evC k w‖ ≤ ‖evC r w‖ ^ 2 := by
  have h0 := cosForm_nonneg_of_dominated h hw
  rw [cosForm_ladd, cosForm_ladd, cosForm_lsmul, cosForm_lsmul, ← normSq_evC _ hw,
    ← normSq_evC _ hw, ← normSq_evC _ hw, evC_conv] at h0
  have hG := normSq_nonneg (evC g w)
  simp only [normSq_eq_norm_sq, norm_mul] at h0 hG
  push_cast at h0
  have key : ((D : ℝ) * ‖evC k w‖) ^ 2 ≤ (‖evC r w‖ ^ 2) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 key

end GRHPseudo.KernelSeparation
