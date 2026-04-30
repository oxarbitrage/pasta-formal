import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import ZcashFormal.Fields

namespace ZcashFormal

/-! # The Pallas curve

Pallas is an elliptic curve over `Fp` in short Weierstrass form:

    y² = x³ + 5

It has prime order equal to `Fq.p` (the Vesta base field modulus) and cofactor 1.
Together with Vesta it forms a 2-cycle enabling efficient recursive proof composition
in the Halo 2 proving system.
-/

noncomputable section

/-- The Pallas curve: y² = x³ + 5 over Fp. -/
def Pallas : WeierstrassCurve Fp where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 5

/-- The discriminant of Pallas is nonzero in Fp.
    For y² = x³ + 5 the discriminant is -16(4·0³ + 27·25) = -10800,
    which is nonzero since char(Fp) ∤ 10800. -/
theorem Pallas.discriminant_isUnit : IsUnit Pallas.Δ := by
  sorry

/-- Pallas is an elliptic curve (its discriminant is a unit). -/
instance : Pallas.IsElliptic :=
  ⟨Pallas.discriminant_isUnit⟩

/-- A generator of the Pallas group: (-1, 2). -/
def Pallas.generator : Pallas.toAffine.Point := by
  sorry

end

end ZcashFormal
