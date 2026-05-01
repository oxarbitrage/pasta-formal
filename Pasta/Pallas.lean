import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Pasta.Fields

namespace Pasta

/-! # The Pallas curve

Pallas is one half of the Pasta 2-cycle, an elliptic curve over `Fp` in short
Weierstrass form: **y² = x³ + 5**.

It has prime order equal to `Fq.p` (the Vesta base field modulus) and cofactor 1.
Together with Vesta it enables efficient recursive proof composition in the
[Halo 2](https://zcash.github.io/halo2/) proving system used by Zcash.

-/

noncomputable section

/-- The Pallas elliptic curve over `Fp`: **y² = x³ + 5**.

All Weierstrass coefficients except `a₆` are zero, giving a curve in
short Weierstrass form. -/
def Pallas : WeierstrassCurve Fp where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 5

/-- The discriminant of Pallas equals -10800 in `Fp`.

For `y² = x³ + b`, the discriminant formula gives `Δ = -16(4a³ + 27b²)`.
With `a = 0` and `b = 5`: `Δ = -16 × 675 = -10800`. -/
theorem Pallas.delta_eq : Pallas.Δ = ((-10800 : ℤ) : Fp) := by
  simp only [Pallas, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
             WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast; ring

/-- The discriminant of Pallas is a unit in `Fp`.

Since `Fp.p > 10800`, the characteristic does not divide 10800,
so `-10800 ≠ 0` in `Fp`. -/
theorem Pallas.discriminant_isUnit : IsUnit Pallas.Δ := by
  rw [Pallas.delta_eq, isUnit_iff_ne_zero, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro h
  have : (Fp.p : ℤ) ≤ 10800 :=
    Int.le_of_dvd (by norm_num) (by rwa [Int.dvd_neg] at h)
  simp only [Fp.p] at this
  omega

/-- Pallas is an elliptic curve (its discriminant is a unit). -/
instance : Pallas.IsElliptic :=
  ⟨Pallas.discriminant_isUnit⟩

/-- The point `(-1, 2)` satisfies the Pallas curve equation `y² = x³ + 5`.

Verification: `2² = 4 = (-1)³ + 5`. -/
theorem Pallas.equation_neg1_2 : Pallas.toAffine.Equation (-1) 2 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [Pallas, WeierstrassCurve.toAffine]
  ring

/-- A generator of the Pallas curve: the point `(-1, 2)`.

This is a standard generator used in the
[pasta_curves](https://github.com/zcash/pasta_curves) implementation. -/
def Pallas.generator : Pallas.toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk Pallas.equation_neg1_2

end

end Pasta
