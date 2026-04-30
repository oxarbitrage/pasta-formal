import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import ZcashFormal.Pallas
import ZcashFormal.Vesta

namespace ZcashFormal

/-! # The Pallas–Vesta 2-cycle

The defining property of the Pasta curves: each curve's group order equals the
other curve's base field characteristic. This is what enables recursive proof
composition in Halo 2 — a proof verified over one curve produces a statement
natively expressible in the other curve's arithmetic circuit.

    |Pallas(Fp)| = char(Fq) = Fq.p
    |Vesta(Fq)| = char(Fp) = Fp.p

Proving the group orders requires either:
  1. A verified point-counting algorithm (e.g., Schoof's algorithm), or
  2. An externally computed primality certificate + group order witness.

These are left as `sorry` for now and represent the main proof obligations.
-/

-- TODO: formalize once Mathlib exposes Fintype for curve points over finite fields
-- theorem cycle_pallas_to_vesta :
--     Fintype.card Pallas.toAffine.Point = Fq.p := by sorry
-- theorem cycle_vesta_to_pallas :
--     Fintype.card Vesta.toAffine.Point = Fp.p := by sorry

/-- Both curves share the same equation y² = x³ + 5, just over different fields. -/
theorem same_equation :
    Pallas.a₁ = 0 ∧ Pallas.a₂ = 0 ∧ Pallas.a₃ = 0 ∧ Pallas.a₄ = 0 ∧ Pallas.a₆ = 5 ∧
    Vesta.a₁ = 0 ∧ Vesta.a₂ = 0 ∧ Vesta.a₃ = 0 ∧ Vesta.a₄ = 0 ∧ Vesta.a₆ = 5 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ZcashFormal
