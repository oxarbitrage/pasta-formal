import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Pasta.Fields

namespace Pasta

/-! # The Vesta curve

Vesta is one half of the Pasta 2-cycle, an elliptic curve over `Fq` in short
Weierstrass form: **y² = x³ + 5**.

It has prime order equal to `Fp.p` (the Pallas base field modulus) and cofactor 1.
Together with Pallas it enables efficient recursive proof composition in the
[Halo 2](https://zcash.github.io/halo2/) proving system used by Zcash.

-/

noncomputable section

/-- The Vesta elliptic curve over `Fq`: **y² = x³ + 5**.

All Weierstrass coefficients except `a₆` are zero, giving a curve in
short Weierstrass form. Vesta shares the same equation as Pallas but is
defined over a different field. -/
def Vesta : WeierstrassCurve Fq where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 5

/-- The discriminant of Vesta equals -10800 in `Fq`. -/
theorem Vesta.delta_eq : Vesta.Δ = ((-10800 : ℤ) : Fq) := by
  simp only [Vesta, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
             WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast; ring

/-- The discriminant of Vesta is a unit in `Fq`.

Since `Fq.p > 10800`, the characteristic does not divide 10800,
so `-10800 ≠ 0` in `Fq`. -/
theorem Vesta.discriminant_isUnit : IsUnit Vesta.Δ := by
  rw [Vesta.delta_eq, isUnit_iff_ne_zero, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro h
  have : (Fq.p : ℤ) ≤ 10800 :=
    Int.le_of_dvd (by norm_num) (by rwa [Int.dvd_neg] at h)
  simp only [Fq.p] at this
  omega

/-- Vesta is an elliptic curve (its discriminant is a unit). -/
instance : Vesta.IsElliptic :=
  ⟨Vesta.discriminant_isUnit⟩

/-- The point `(-1, 2)` satisfies the Vesta curve equation `y² = x³ + 5`.

Verification: `2² = 4 = (-1)³ + 5`. -/
theorem Vesta.equation_neg1_2 : Vesta.toAffine.Equation (-1) 2 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [Vesta, WeierstrassCurve.toAffine]
  ring

/-- A generator of the Vesta curve: the point `(-1, 2)`.

This is a standard generator used in the
[pasta_curves](https://github.com/zcash/pasta_curves) implementation. -/
def Vesta.generator : Vesta.toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk Vesta.equation_neg1_2

end

end Pasta
