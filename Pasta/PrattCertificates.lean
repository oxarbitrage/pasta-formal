import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-! # Pratt primality certificates for intermediate factors

Recursive Pratt certificates proving primality of the large factors appearing
in the factorizations of (Fp.p - 1) and (Fq.p - 1). Each certificate provides
a primitive root and the prime factorization of (factor - 1), verified by
`native_decide` for modular exponentiations and `norm_num` for small primes.
-/

namespace Pasta.PrattCertificates

set_option maxRecDepth 4096

private theorem prime_dvd_prime_eq {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h : p ∣ q) : p = q :=
  (hq.eq_one_or_self_of_dvd p h).resolve_left hp.one_lt.ne'

/-! ## Level 3: smallest primes needing Pratt certificates

These are primes too large for `decide` but small enough that their p-1
factorizations contain only primes handleable by `norm_num`.
-/

theorem prime_125803 : Nat.Prime 125803 := by norm_num
theorem prime_149503 : Nat.Prime 149503 := by norm_num
theorem prime_897019 : Nat.Prime 897019 := by norm_num
theorem prime_958679 : Nat.Prime 958679 := by norm_num
theorem prime_294793 : Nat.Prime 294793 := by norm_num
theorem prime_115603 : Nat.Prime 115603 := by norm_num
theorem prime_413527 : Nat.Prime 413527 := by norm_num
theorem prime_772231 : Nat.Prime 772231 := by norm_num

/-! ## Level 2: primes whose p-1 factors include Level 3 primes -/

theorem prime_2012849 : Nat.Prime 2012849 := by
  apply lucas_primality 2012849 (3 : ZMod 2012849)
  · native_decide
  · intro q hq hqd
    have : (2012849 : ℕ) - 1 = 2 ^ 4 * 125803 := by norm_num
    rw [this] at hqd
    have : q = 2 ∨ q = 125803 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · left; exact prime_dvd_prime_eq hq (by decide) (hq.dvd_of_dvd_pow h)
      · right; exact prime_dvd_prime_eq hq prime_125803 h
    rcases this with rfl | rfl <;> native_decide

theorem prime_4025699 : Nat.Prime 4025699 := by
  apply lucas_primality 4025699 (2 : ZMod 4025699)
  · native_decide
  · intro q hq hqd
    have : (4025699 : ℕ) - 1 = 2 * 2012849 := by norm_num
    rw [this] at hqd
    have : q = 2 ∨ q = 2012849 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · left; exact prime_dvd_prime_eq hq (by decide) h
      · right; exact prime_dvd_prime_eq hq prime_2012849 h
    rcases this with rfl | rfl <;> native_decide

theorem prime_5701177 : Nat.Prime 5701177 := by
  apply lucas_primality 5701177 (7 : ZMod 5701177)
  · native_decide
  · intro q hq hqd
    have : (5701177 : ℕ) - 1 = 2 ^ 3 * 3 ^ 2 * 13 * 6091 := by norm_num
    rw [this] at hqd
    have : q = 2 ∨ q = 3 ∨ q = 13 ∨ q = 6091 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · left; exact prime_dvd_prime_eq hq (by decide) (hq.dvd_of_dvd_pow h)
          · right; left; exact prime_dvd_prime_eq hq (by decide) (hq.dvd_of_dvd_pow h)
        · right; right; left; exact prime_dvd_prime_eq hq (by decide) h
      · right; right; right; exact prime_dvd_prime_eq hq (by norm_num) h
    rcases this with rfl | rfl | rfl | rfl <;> native_decide

theorem prime_6942563 : Nat.Prime 6942563 := by
  apply lucas_primality 6942563 (2 : ZMod 6942563)
  · native_decide
  · intro q hq hqd
    have : (6942563 : ℕ) - 1 = 2 * 11 * 17 * 19 * 977 := by norm_num
    rw [this] at hqd
    have : q = 2 ∨ q = 11 ∨ q = 17 ∨ q = 19 ∨ q = 977 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · rcases hq.dvd_mul.mp h with h | h
            · left; exact prime_dvd_prime_eq hq (by decide) h
            · right; left; exact prime_dvd_prime_eq hq (by decide) h
          · right; right; left; exact prime_dvd_prime_eq hq (by decide) h
        · right; right; right; left; exact prime_dvd_prime_eq hq (by decide) h
      · right; right; right; right; exact prime_dvd_prime_eq hq (by norm_num) h
    rcases this with rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem prime_1197907 : Nat.Prime 1197907 := by
  apply lucas_primality 1197907 (3 : ZMod 1197907)
  · native_decide
  · intro q hq hqd
    have : (1197907 : ℕ) - 1 = 2 * 3 * 53 * 3767 := by norm_num
    rw [this] at hqd
    have : q = 2 ∨ q = 3 ∨ q = 53 ∨ q = 3767 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · left; exact prime_dvd_prime_eq hq (by decide) h
          · right; left; exact prime_dvd_prime_eq hq (by decide) h
        · right; right; left; exact prime_dvd_prime_eq hq (by decide) h
      · right; right; right; exact prime_dvd_prime_eq hq (by norm_num) h
    rcases this with rfl | rfl | rfl | rfl <;> native_decide

theorem prime_4229279 : Nat.Prime 4229279 := by
  apply lucas_primality 4229279 (13 : ZMod 4229279)
  · native_decide
  · intro q hq hqd
    have : (4229279 : ℕ) - 1 = 2 * 827 * 2557 := by norm_num
    rw [this] at hqd
    have : q = 2 ∨ q = 827 ∨ q = 2557 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · left; exact prime_dvd_prime_eq hq (by decide) h
        · right; left; exact prime_dvd_prime_eq hq (by norm_num) h
      · right; right; exact prime_dvd_prime_eq hq (by norm_num) h
    rcases this with rfl | rfl | rfl <;> native_decide

theorem prime_80513981 : Nat.Prime 80513981 := by
  apply lucas_primality 80513981 (2 : ZMod 80513981)
  · native_decide
  · intro q hq hqd
    have : (80513981 : ℕ) - 1 = 2 ^ 2 * 5 * 4025699 := by norm_num
    rw [this] at hqd
    have : q = 2 ∨ q = 5 ∨ q = 4025699 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · left; exact prime_dvd_prime_eq hq (by decide) (hq.dvd_of_dvd_pow h)
        · right; left; exact prime_dvd_prime_eq hq (by decide) h
      · right; right; exact prime_dvd_prime_eq hq prime_4025699 h
    rcases this with rfl | rfl | rfl <;> native_decide

theorem prime_41655379 : Nat.Prime 41655379 := by
  apply lucas_primality 41655379 (3 : ZMod 41655379)
  · native_decide
  · intro q hq hqd
    have : (41655379 : ℕ) - 1 = 2 * 3 * 6942563 := by norm_num
    rw [this] at hqd
    have : q = 2 ∨ q = 3 ∨ q = 6942563 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · left; exact prime_dvd_prime_eq hq (by decide) h
        · right; left; exact prime_dvd_prime_eq hq (by decide) h
      · right; right; exact prime_dvd_prime_eq hq prime_6942563 h
    rcases this with rfl | rfl | rfl <;> native_decide

theorem prime_399082391 : Nat.Prime 399082391 := by
  apply lucas_primality 399082391 (7 : ZMod 399082391)
  · native_decide
  · intro q hq hqd
    have : (399082391 : ℕ) - 1 = 2 * 5 * 7 * 5701177 := by norm_num
    rw [this] at hqd
    have : q = 2 ∨ q = 5 ∨ q = 7 ∨ q = 5701177 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · left; exact prime_dvd_prime_eq hq (by decide) h
          · right; left; exact prime_dvd_prime_eq hq (by decide) h
        · right; right; left; exact prime_dvd_prime_eq hq (by decide) h
      · right; right; right; exact prime_dvd_prime_eq hq prime_5701177 h
    rcases this with rfl | rfl | rfl | rfl <;> native_decide

/-! ## Level 1: primes whose p-1 factors include Level 2 primes -/

theorem prime_417677162933 : Nat.Prime 417677162933 := by
  apply lucas_primality 417677162933 (2 : ZMod 417677162933)
  · native_decide
  · intro q hq hqd
    have : (417677162933 : ℕ) - 1 = 2 ^ 2 * 59 * 1973 * 897019 := by native_decide
    rw [this] at hqd
    have : q = 2 ∨ q = 59 ∨ q = 1973 ∨ q = 897019 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · left; exact prime_dvd_prime_eq hq (by decide) (hq.dvd_of_dvd_pow h)
          · right; left; exact prime_dvd_prime_eq hq (by decide) h
        · right; right; left; exact prime_dvd_prime_eq hq (by norm_num) h
      · right; right; right; exact prime_dvd_prime_eq hq prime_897019 h
    rcases this with rfl | rfl | rfl | rfl <;> native_decide

theorem prime_22160661629 : Nat.Prime 22160661629 := by
  apply lucas_primality 22160661629 (3 : ZMod 22160661629)
  · native_decide
  · intro q hq hqd
    have : (22160661629 : ℕ) - 1 = 2 ^ 2 * 7 * 19 * 41655379 := by native_decide
    rw [this] at hqd
    have : q = 2 ∨ q = 7 ∨ q = 19 ∨ q = 41655379 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · left; exact prime_dvd_prime_eq hq (by decide) (hq.dvd_of_dvd_pow h)
          · right; left; exact prime_dvd_prime_eq hq (by decide) h
        · right; right; left; exact prime_dvd_prime_eq hq (by decide) h
      · right; right; right; exact prime_dvd_prime_eq hq prime_41655379 h
    rcases this with rfl | rfl | rfl | rfl <;> native_decide

theorem prime_325086459374267 : Nat.Prime 325086459374267 := by
  apply lucas_primality 325086459374267 (2 : ZMod 325086459374267)
  · native_decide
  · intro q hq hqd
    have : (325086459374267 : ℕ) - 1 = 2 * 509 * 413527 * 772231 := by native_decide
    rw [this] at hqd
    have : q = 2 ∨ q = 509 ∨ q = 413527 ∨ q = 772231 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · left; exact prime_dvd_prime_eq hq (by decide) h
          · right; left; exact prime_dvd_prime_eq hq (by norm_num) h
        · right; right; left; exact prime_dvd_prime_eq hq prime_413527 h
      · right; right; right; exact prime_dvd_prime_eq hq prime_772231 h
    rcases this with rfl | rfl | rfl | rfl <;> native_decide

theorem prime_4129989133 : Nat.Prime 4129989133 := by
  apply lucas_primality 4129989133 (5 : ZMod 4129989133)
  · native_decide
  · intro q hq hqd
    have : (4129989133 : ℕ) - 1 = 2 ^ 2 * 3 * 359 * 958679 := by native_decide
    rw [this] at hqd
    have : q = 2 ∨ q = 3 ∨ q = 359 ∨ q = 958679 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · left; exact prime_dvd_prime_eq hq (by decide) (hq.dvd_of_dvd_pow h)
          · right; left; exact prime_dvd_prime_eq hq (by decide) h
        · right; right; left; exact prime_dvd_prime_eq hq (by norm_num) h
      · right; right; right; exact prime_dvd_prime_eq hq prime_958679 h
    rcases this with rfl | rfl | rfl | rfl <;> native_decide

theorem prime_5247740253619 : Nat.Prime 5247740253619 := by
  apply lucas_primality 5247740253619 (2 : ZMod 5247740253619)
  · native_decide
  · intro q hq hqd
    have : (5247740253619 : ℕ) - 1 = 2 * 3 ^ 3 * 17 * 71 * 80513981 := by native_decide
    rw [this] at hqd
    have : q = 2 ∨ q = 3 ∨ q = 17 ∨ q = 71 ∨ q = 80513981 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · rcases hq.dvd_mul.mp h with h | h
            · left; exact prime_dvd_prime_eq hq (by decide) h
            · right; left; exact prime_dvd_prime_eq hq (by decide) (hq.dvd_of_dvd_pow h)
          · right; right; left; exact prime_dvd_prime_eq hq (by decide) h
        · right; right; right; left; exact prime_dvd_prime_eq hq (by decide) h
      · right; right; right; right; exact prime_dvd_prime_eq hq prime_80513981 h
    rcases this with rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem prime_5239247429827 : Nat.Prime 5239247429827 := by
  apply lucas_primality 5239247429827 (2 : ZMod 5239247429827)
  · native_decide
  · intro q hq hqd
    have : (5239247429827 : ℕ) - 1 = 2 * 3 ^ 2 * 757 * 12149 * 31649 := by native_decide
    rw [this] at hqd
    have : q = 2 ∨ q = 3 ∨ q = 757 ∨ q = 12149 ∨ q = 31649 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · rcases hq.dvd_mul.mp h with h | h
            · left; exact prime_dvd_prime_eq hq (by decide) h
            · right; left; exact prime_dvd_prime_eq hq (by decide) (hq.dvd_of_dvd_pow h)
          · right; right; left; exact prime_dvd_prime_eq hq (by norm_num) h
        · right; right; right; left; exact prime_dvd_prime_eq hq (by norm_num) h
      · right; right; right; right; exact prime_dvd_prime_eq hq (by norm_num) h
    rcases this with rfl | rfl | rfl | rfl | rfl <;> native_decide

/-! ## Level 0: the four target primes used in Fp.p and Fq.p factorizations -/

theorem prime_A : Nat.Prime 539204044132271846773 := by
  apply lucas_primality 539204044132271846773 (5 : ZMod 539204044132271846773)
  · native_decide
  · intro q hq hqd
    have : (539204044132271846773 : ℕ) - 1 = 2 ^ 2 * 3 ^ 5 * 89 * 14923 * 417677162933 := by
      native_decide
    rw [this] at hqd
    have : q = 2 ∨ q = 3 ∨ q = 89 ∨ q = 14923 ∨ q = 417677162933 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · rcases hq.dvd_mul.mp h with h | h
            · left; exact prime_dvd_prime_eq hq (by decide) (hq.dvd_of_dvd_pow h)
            · right; left; exact prime_dvd_prime_eq hq (by decide) (hq.dvd_of_dvd_pow h)
          · right; right; left; exact prime_dvd_prime_eq hq (by decide) h
        · right; right; right; left; exact prime_dvd_prime_eq hq (by norm_num) h
      · right; right; right; right; exact prime_dvd_prime_eq hq prime_417677162933 h
    rcases this with rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem prime_B : Nat.Prime 8999194758858563409123804352480028797519453 := by
  apply lucas_primality 8999194758858563409123804352480028797519453
      (2 : ZMod 8999194758858563409123804352480028797519453)
  · native_decide
  · intro q hq hqd
    have : (8999194758858563409123804352480028797519453 : ℕ) - 1 =
        2 ^ 2 * 3 ^ 4 * 11 * 2531 * 115603 * 1197907 * 22160661629 * 325086459374267 := by
      native_decide
    rw [this] at hqd
    have : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 2531 ∨ q = 115603 ∨ q = 1197907 ∨
        q = 22160661629 ∨ q = 325086459374267 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · rcases hq.dvd_mul.mp h with h | h
            · rcases hq.dvd_mul.mp h with h | h
              · rcases hq.dvd_mul.mp h with h | h
                · rcases hq.dvd_mul.mp h with h | h
                  · left; exact prime_dvd_prime_eq hq (by decide) (hq.dvd_of_dvd_pow h)
                  · right; left; exact prime_dvd_prime_eq hq (by decide) (hq.dvd_of_dvd_pow h)
                · right; right; left; exact prime_dvd_prime_eq hq (by decide) h
              · right; right; right; left; exact prime_dvd_prime_eq hq (by norm_num) h
            · right; right; right; right; left; exact prime_dvd_prime_eq hq prime_115603 h
          · right; right; right; right; right; left
            exact prime_dvd_prime_eq hq prime_1197907 h
        · right; right; right; right; right; right; left
          exact prime_dvd_prime_eq hq prime_22160661629 h
      · right; right; right; right; right; right; right
        exact prime_dvd_prime_eq hq prime_325086459374267 h
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem prime_C : Nat.Prime 1690502597179744445941507 := by
  apply lucas_primality 1690502597179744445941507
      (2 : ZMod 1690502597179744445941507)
  · native_decide
  · intro q hq hqd
    have : (1690502597179744445941507 : ℕ) - 1 = 2 * 3 * 13 * 4129989133 * 5247740253619 := by
      native_decide
    rw [this] at hqd
    have : q = 2 ∨ q = 3 ∨ q = 13 ∨ q = 4129989133 ∨ q = 5247740253619 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · rcases hq.dvd_mul.mp h with h | h
            · left; exact prime_dvd_prime_eq hq (by decide) h
            · right; left; exact prime_dvd_prime_eq hq (by decide) h
          · right; right; left; exact prime_dvd_prime_eq hq (by decide) h
        · right; right; right; left; exact prime_dvd_prime_eq hq prime_4129989133 h
      · right; right; right; right; exact prime_dvd_prime_eq hq prime_5247740253619 h
    rcases this with rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem prime_D : Nat.Prime 10427374428728808478656897599072717 := by
  apply lucas_primality 10427374428728808478656897599072717
      (2 : ZMod 10427374428728808478656897599072717)
  · native_decide
  · intro q hq hqd
    have : (10427374428728808478656897599072717 : ℕ) - 1 =
        2 ^ 2 * 294793 * 4229279 * 399082391 * 5239247429827 := by native_decide
    rw [this] at hqd
    have : q = 2 ∨ q = 294793 ∨ q = 4229279 ∨ q = 399082391 ∨ q = 5239247429827 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · rcases hq.dvd_mul.mp h with h | h
            · left; exact prime_dvd_prime_eq hq (by decide) (hq.dvd_of_dvd_pow h)
            · right; left; exact prime_dvd_prime_eq hq prime_294793 h
          · right; right; left; exact prime_dvd_prime_eq hq prime_4229279 h
        · right; right; right; left; exact prime_dvd_prime_eq hq prime_399082391 h
      · right; right; right; right; exact prime_dvd_prime_eq hq prime_5239247429827 h
    rcases this with rfl | rfl | rfl | rfl | rfl <;> native_decide

end Pasta.PrattCertificates
