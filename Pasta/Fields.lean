import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Pasta.PrattCertificates

namespace Pasta

/-! # Pasta curve base fields

The Pallas and Vesta curves form a 2-cycle of elliptic curves over prime fields.
Each curve's scalar field equals the other's base field:

  - Pallas is defined over `Fp` and has scalar field `Fq`
  - Vesta is defined over `Fq` and has scalar field `Fp`

Both primes are ≈ 2²⁵⁴ and were chosen to enable efficient recursive proof
composition in the Halo 2 proving system. See
[Zcash Protocol Specification §5.4.9.6](https://zips.z.cash/protocol/protocol.pdf#pallasandvesta).

Primality is proven via the Lucas test (Pratt certificates) with witness `a = 5`,
which is a primitive root for both fields.
-/

private theorem prime_dvd_prime_eq {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h : p ∣ q) : p = q :=
  (hq.eq_one_or_self_of_dvd p h).resolve_left hp.one_lt.ne'

set_option maxRecDepth 4096

namespace Fp

/-- The Pallas base field modulus (also the Vesta group order).

`Fp.p = 2²⁵⁴ + 45560315531506369815346746415080538113`

In hex: `0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001`. -/
def p : ℕ := 28948022309329048855892746252171976963363056481941560715954676764349967630337

private theorem factorization :
    p - 1 = 2 ^ 32 * 3 * 463 * 539204044132271846773 *
        8999194758858563409123804352480028797519453 := by native_decide

/-- `Fp.p` is prime, proven via a Pratt certificate with witness `a = 5`.

The factorization `p - 1 = 2³² × 3 × 463 × 539204044132271846773
× 8999194758858563409123804352480028797519453` is verified by `native_decide`,
and `5` is shown to be a primitive root by checking `5^((p-1)/q) ≢ 1`
for each prime factor `q`. -/
instance : Fact (Nat.Prime p) := ⟨by
  apply lucas_primality p (5 : ZMod p)
  · native_decide
  · intro q hq hqd
    rw [factorization] at hqd
    have : q = 2 ∨ q = 3 ∨ q = 463 ∨
        q = 539204044132271846773 ∨
        q = 8999194758858563409123804352480028797519453 := by
      have h2 : Nat.Prime 2 := by decide
      have h3 : Nat.Prime 3 := by decide
      have h463 : Nat.Prime 463 := by decide
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · rcases hq.dvd_mul.mp h with h | h
            · left; exact prime_dvd_prime_eq hq h2 (hq.dvd_of_dvd_pow h)
            · right; left; exact prime_dvd_prime_eq hq h3 h
          · right; right; left; exact prime_dvd_prime_eq hq h463 h
        · right; right; right; left
          exact prime_dvd_prime_eq hq PrattCertificates.prime_A h
      · right; right; right; right
        exact prime_dvd_prime_eq hq PrattCertificates.prime_B h
    rcases this with rfl | rfl | rfl | rfl | rfl <;> native_decide⟩

end Fp

namespace Fq

/-- The Vesta base field modulus (also the Pallas group order).

`Fq.p = 2²⁵⁴ + 45560315531506369815346746415080538113 + 86663886297413177741937042428387104`

In hex: `0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001`. -/
def p : ℕ := 28948022309329048855892746252171976963363056481941647379679742748393362948097

private theorem factorization :
    p - 1 = 2 ^ 32 * 3 ^ 2 * 1709 * 24859 * 1690502597179744445941507 *
        10427374428728808478656897599072717 := by native_decide

/-- `Fq.p` is prime, proven via a Pratt certificate with witness `a = 5`.

The factorization `p - 1 = 2³² × 3² × 1709 × 24859 × 1690502597179744445941507
× 10427374428728808478656897599072717` is verified by `native_decide`,
and `5` is shown to be a primitive root by checking `5^((p-1)/q) ≢ 1`
for each prime factor `q`. -/
instance : Fact (Nat.Prime p) := ⟨by
  apply lucas_primality p (5 : ZMod p)
  · native_decide
  · intro q hq hqd
    rw [factorization] at hqd
    have : q = 2 ∨ q = 3 ∨ q = 1709 ∨ q = 24859 ∨
        q = 1690502597179744445941507 ∨
        q = 10427374428728808478656897599072717 := by
      have h2 : Nat.Prime 2 := by decide
      have h3 : Nat.Prime 3 := by decide
      have h1709 : Nat.Prime 1709 := by norm_num
      have h24859 : Nat.Prime 24859 := by norm_num
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · rcases hq.dvd_mul.mp h with h | h
            · rcases hq.dvd_mul.mp h with h | h
              · left; exact prime_dvd_prime_eq hq h2 (hq.dvd_of_dvd_pow h)
              · right; left; exact prime_dvd_prime_eq hq h3 (hq.dvd_of_dvd_pow h)
            · right; right; left; exact prime_dvd_prime_eq hq h1709 h
          · right; right; right; left; exact prime_dvd_prime_eq hq h24859 h
        · right; right; right; right; left
          exact prime_dvd_prime_eq hq PrattCertificates.prime_C h
      · right; right; right; right; right
        exact prime_dvd_prime_eq hq PrattCertificates.prime_D h
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide⟩

end Fq

/-- The Pallas base field `𝔽_p`, defined as `ℤ/pℤ` where `p = Fp.p`.
This is also the Vesta scalar field. -/
abbrev Fp := ZMod Fp.p

/-- The Vesta base field `𝔽_q`, defined as `ℤ/qℤ` where `q = Fq.p`.
This is also the Pallas scalar field. -/
abbrev Fq := ZMod Fq.p

end Pasta
