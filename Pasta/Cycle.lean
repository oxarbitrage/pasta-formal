import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Pasta.Pallas
import Pasta.Vesta

namespace Pasta

/-! # The Pallas–Vesta 2-cycle

The defining property of the Pasta curves is that they form a **2-cycle**:
each curve's group order equals the other curve's base field characteristic.

    |Pallas(𝔽_p)| = q
    |Vesta(𝔽_q)|  = p

This is what enables recursive proof composition in Halo 2: a proof verified
over one curve produces a statement natively expressible as arithmetic in the
other curve's scalar field, which *is* the first curve's base field. Proofs
can therefore recurse back and forth without an expensive field embedding.

### What's proven here

- Both curves share the equation `y² = x³ + 5` (just over different fields).

### What's not yet proven (future work)

The group order equalities above require a verified point-counting algorithm
(e.g., Schoof's algorithm) or an externally computed group order certificate.
These are not yet available in Mathlib for curves over large finite fields.
-/

/-- Pallas and Vesta share the same short Weierstrass equation `y² = x³ + 5`.

Both curves have `a₁ = a₂ = a₃ = a₄ = 0` and `a₆ = 5`; they differ only in
the base field (`𝔽_p` vs `𝔽_q`). This structural coincidence is by design —
the Pasta curve search selected a single equation that yields prime-order
curves over *both* fields simultaneously. -/
theorem same_equation :
    Pallas.a₁ = 0 ∧ Pallas.a₂ = 0 ∧ Pallas.a₃ = 0 ∧ Pallas.a₄ = 0 ∧ Pallas.a₆ = 5 ∧
    Vesta.a₁ = 0 ∧ Vesta.a₂ = 0 ∧ Vesta.a₃ = 0 ∧ Vesta.a₄ = 0 ∧ Vesta.a₆ = 5 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Pasta
