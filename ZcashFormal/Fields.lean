import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

namespace ZcashFormal

/-! # Pasta curve base fields

The Pallas and Vesta curves form a 2-cycle of elliptic curves. Their defining
feature is that each curve's scalar field is the other's base field.

  Pallas base field prime = Vesta scalar field prime = `Fp.p`
  Vesta base field prime = Pallas scalar field prime = `Fq.p`

Both primes are ≈ 2^254.
-/

namespace Fp

/-- The Pallas base field modulus. Equal to the Vesta group order.
    0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001 -/
def p : ℕ := 28948022309329048855892746252171976963363056481941560715954676764349967630337

instance : Fact (Nat.Prime p) := ⟨by sorry⟩

end Fp

namespace Fq

/-- The Vesta base field modulus. Equal to the Pallas group order.
    0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001 -/
def p : ℕ := 28948022309329048855892746252171976963363056481941647379679742748393362948097

instance : Fact (Nat.Prime p) := ⟨by sorry⟩

end Fq

/-- The Pallas base field (also the Vesta scalar field). -/
abbrev Fp := ZMod Fp.p

/-- The Vesta base field (also the Pallas scalar field). -/
abbrev Fq := ZMod Fq.p

end ZcashFormal
