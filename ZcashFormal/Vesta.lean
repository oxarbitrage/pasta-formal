import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import ZcashFormal.Fields

namespace ZcashFormal

/-! # The Vesta curve

Vesta is an elliptic curve over `Fq` in short Weierstrass form:

    y² = x³ + 5

It has prime order equal to `Fp.p` (the Pallas base field modulus) and cofactor 1.
Together with Pallas it forms a 2-cycle enabling efficient recursive proof composition
in the Halo 2 proving system.
-/

noncomputable section

/-- The Vesta curve: y² = x³ + 5 over Fq. -/
def Vesta : WeierstrassCurve Fq where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 5

theorem Vesta.delta_eq : Vesta.Δ = ((-10800 : ℤ) : Fq) := by
  simp only [Vesta, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
             WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast; ring

theorem Vesta.discriminant_isUnit : IsUnit Vesta.Δ := by
  rw [Vesta.delta_eq, isUnit_iff_ne_zero, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro h
  have : (Fq.p : ℤ) ≤ 10800 :=
    Int.le_of_dvd (by norm_num) (by rwa [Int.dvd_neg] at h)
  simp only [Fq.p] at this
  omega

instance : Vesta.IsElliptic :=
  ⟨Vesta.discriminant_isUnit⟩

theorem Vesta.equation_neg1_2 : Vesta.toAffine.Equation (-1) 2 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [Vesta, WeierstrassCurve.toAffine]
  ring

/-- A generator of the Vesta group: the point (-1, 2). -/
def Vesta.generator : Vesta.toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk Vesta.equation_neg1_2

end

end ZcashFormal
