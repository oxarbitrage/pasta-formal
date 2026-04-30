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

theorem Pallas.delta_eq : Pallas.Δ = ((-10800 : ℤ) : Fp) := by
  simp only [Pallas, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
             WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast; ring

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

/-- A generator of the Pallas group: (-1, 2). -/
def Pallas.generator : Pallas.toAffine.Point := by
  sorry

end

end ZcashFormal
