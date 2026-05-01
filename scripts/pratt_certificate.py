"""Compute Pratt primality certificates for the Pasta curve primes."""

import math
import random

random.seed(42)

Fp_p = 28948022309329048855892746252171976963363056481941560715954676764349967630337
Fq_p = 28948022309329048855892746252171976963363056481941647379679742748393362948097


def is_probable_prime(n, k=20):
    """Miller-Rabin primality test."""
    if n < 2:
        return False
    if n == 2 or n == 3:
        return True
    if n % 2 == 0:
        return False
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for _ in range(k):
        a = random.randrange(2, n - 1)
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def pollard_rho(n):
    """Find a non-trivial factor of n using Pollard's rho algorithm."""
    if n % 2 == 0:
        return 2
    x = random.randint(2, n - 1)
    y = x
    c = random.randint(1, n - 1)
    d = 1
    while d == 1:
        x = (x * x + c) % n
        y = (y * y + c) % n
        y = (y * y + c) % n
        d = math.gcd(abs(x - y), n)
    return d if d != n else None


def factor(n):
    """Return the complete prime factorization of n as a dict {prime: exponent}."""
    if n <= 1:
        return {}
    if is_probable_prime(n):
        return {n: 1}
    # trial division for small factors
    factors = {}
    for p in range(2, 10000):
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
    if n == 1:
        return factors
    if is_probable_prime(n):
        factors[n] = factors.get(n, 0) + 1
        return factors
    # Pollard's rho for remaining factors
    stack = [n]
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if is_probable_prime(m):
            factors[m] = factors.get(m, 0) + 1
            continue
        d = None
        while d is None:
            d = pollard_rho(m)
        stack.append(d)
        stack.append(m // d)
    return factors


def find_primitive_root(p, factors_of_p_minus_1):
    """Find a primitive root mod p using the prime factors of p-1."""
    prime_factors = list(factors_of_p_minus_1.keys())
    for a in range(2, 1000):
        if pow(a, p - 1, p) != 1:
            continue
        is_root = True
        for q in prime_factors:
            if pow(a, (p - 1) // q, p) == 1:
                is_root = False
                break
        if is_root:
            return a
    return None


def verify_certificate(p, a, prime_factors):
    """Verify the Pratt certificate."""
    assert pow(a, p - 1, p) == 1, f"a^(p-1) != 1 mod p"
    for q in prime_factors:
        val = pow(a, (p - 1) // q, p)
        assert val != 1, f"a^((p-1)/{q}) == 1 mod p, a={a} is not a primitive root"
    print(f"  Certificate verified!")


def compute_certificate(name, p):
    print(f"\n{'='*60}")
    print(f"Pratt certificate for {name}")
    print(f"p = {p}")
    print(f"p (hex) = {hex(p)}")
    print(f"{'='*60}")

    pm1 = p - 1
    print(f"\nFactoring p - 1 = {pm1}...")
    factors = factor(pm1)
    print(f"\np - 1 = ", end="")
    parts = []
    for q in sorted(factors.keys()):
        e = factors[q]
        if e == 1:
            parts.append(str(q))
        else:
            parts.append(f"{q}^{e}")
    print(" × ".join(parts))

    # verify factorization
    product = 1
    for q, e in factors.items():
        product *= q ** e
    assert product == pm1, "Factorization is incorrect!"
    print("Factorization verified.")

    prime_factors = sorted(factors.keys())
    print(f"\nPrime factors of p-1: {prime_factors}")

    print(f"\nSearching for primitive root...")
    a = find_primitive_root(p, factors)
    print(f"Primitive root: a = {a}")

    print(f"\nVerifying certificate...")
    verify_certificate(p, a, prime_factors)

    # Print verification values for Lean
    print(f"\n--- Values for Lean proof ---")
    print(f"p = {p}")
    print(f"a = {a}")
    print(f"prime_factors = {prime_factors}")
    print(f"a^(p-1) mod p = {pow(a, p - 1, p)}")
    for q in prime_factors:
        val = pow(a, (p - 1) // q, p)
        print(f"a^((p-1)/{q}) mod p = {val}")

    return a, factors


if __name__ == "__main__":
    a_fp, factors_fp = compute_certificate("Fp (Pallas base field)", Fp_p)
    a_fq, factors_fq = compute_certificate("Fq (Vesta base field)", Fq_p)
