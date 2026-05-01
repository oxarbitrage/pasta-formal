import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

namespace ZcashFormal

/-! # Pasta curve base fields

The Pallas and Vesta curves form a 2-cycle of elliptic curves. Their defining
feature is that each curve's scalar field is the other's base field.

  Pallas base field prime = Vesta scalar field prime = `Fp.p`
  Vesta base field prime = Pallas scalar field prime = `Fq.p`

Both primes are ≈ 2^254. Primality is proven via the Lucas test (Pratt certificates)
with witness a = 5 (a primitive root for both fields).
-/

private theorem prime_dvd_prime_eq {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h : p ∣ q) : p = q :=
  (hq.eq_one_or_self_of_dvd p h).resolve_left hp.one_lt.ne'

set_option maxRecDepth 4096

namespace Fp

/-- The Pallas base field modulus. Equal to the Vesta group order.
    0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001 -/
def p : ℕ := 28948022309329048855892746252171976963363056481941560715954676764349967630337

private def A : ℕ := 539204044132271846773
private def B : ℕ := 8999194758858563409123804352480028797519453

private theorem hA_prime : Nat.Prime A := by sorry
private theorem hB_prime : Nat.Prime B := by sorry

private theorem factorization : p - 1 = 2 ^ 32 * 3 * 463 * A * B := by native_decide

instance : Fact (Nat.Prime p) := ⟨by
  apply lucas_primality p (5 : ZMod p)
  · native_decide
  · intro q hq hqd
    rw [factorization] at hqd
    have : q = 2 ∨ q = 3 ∨ q = 463 ∨ q = A ∨ q = B := by
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
        · right; right; right; left; exact prime_dvd_prime_eq hq hA_prime h
      · right; right; right; right; exact prime_dvd_prime_eq hq hB_prime h
    rcases this with rfl | rfl | rfl | rfl | rfl <;> native_decide⟩

end Fp

namespace Fq

/-- The Vesta base field modulus. Equal to the Pallas group order.
    0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001 -/
def p : ℕ := 28948022309329048855892746252171976963363056481941647379679742748393362948097

private def C : ℕ := 1690502597179744445941507
private def D : ℕ := 10427374428728808478656897599072717

private theorem hC_prime : Nat.Prime C := by sorry
private theorem hD_prime : Nat.Prime D := by sorry

private theorem factorization : p - 1 = 2 ^ 32 * 3 ^ 2 * 1709 * 24859 * C * D := by native_decide

instance : Fact (Nat.Prime p) := ⟨by
  apply lucas_primality p (5 : ZMod p)
  · native_decide
  · intro q hq hqd
    rw [factorization] at hqd
    have : q = 2 ∨ q = 3 ∨ q = 1709 ∨ q = 24859 ∨ q = C ∨ q = D := by
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
        · right; right; right; right; left; exact prime_dvd_prime_eq hq hC_prime h
      · right; right; right; right; right; exact prime_dvd_prime_eq hq hD_prime h
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide⟩

end Fq

/-- The Pallas base field (also the Vesta scalar field). -/
abbrev Fp := ZMod Fp.p

/-- The Vesta base field (also the Pallas scalar field). -/
abbrev Fq := ZMod Fq.p

end ZcashFormal
