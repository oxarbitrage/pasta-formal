# pasta-formal

**Status:** Fully proven — zero `sorry` statements.

A Lean 4 formalization of the Pasta curves (Pallas and Vesta) — the 2-cycle of elliptic curves at the heart of Zcash's Halo 2 recursive proving system.

## Overview

This library provides machine-checked proofs of the foundational arithmetic properties of the Pasta curves. Both Pallas (`y² = x³ + 5` over `𝔽_p`) and Vesta (`y² = x³ + 5` over `𝔽_q`) are formalized as Mathlib `WeierstrassCurve` instances with proven `IsElliptic` instances, verified by computing that the discriminant `Δ = -10800` is a unit in each field.

The primality of both 255-bit field moduli — the central trust anchor for the entire curve construction — is proven from first principles using the Lucas primality test with explicit Pratt certificates. The certificates are hierarchical: 28 intermediate primes appearing in the factorizations of `p - 1` and `q - 1` are themselves proven prime recursively before the top-level Lucas tests can close.

The defining cycle property — `|Pallas(𝔽_p)| = q` and `|Vesta(𝔽_q)| = p` — is axiomatized in `Pasta/Cycle.lean`. Proving it formally requires a verified implementation of Schoof's point-counting algorithm (or an AGM-based certificate), which is not yet available in Mathlib. All other results are unconditionally proved. The cycle axioms are also used (as `order_pallas`) in the downstream `redpallas-formal` library.

## Mathematical Background

### The Pasta Curve Equations

Both curves are in **short Weierstrass form**:

```
y² = x³ + a₄·x + a₆
```

with `a₁ = a₂ = a₃ = a₄ = 0` and `a₆ = 5`, so the equation is simply `y² = x³ + 5`. The coefficient `5` was selected by the Zcash team's exhaustive search over the joint Weierstrass parameter space: it is the smallest positive integer such that `y² = x³ + b` simultaneously defines a prime-order curve over both `𝔽_p` (giving Pallas) and `𝔽_q` (giving Vesta).

The two 255-bit primes are:

| Field | Modulus | Hex |
|-------|---------|-----|
| `Fp.p` | `28948022309329048855892746252171976963363056481941560715954676764349967630337` | `0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001` |
| `Fq.p` | `28948022309329048855892746252171976963363056481941647379679742748393362948097` | `0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001` |

The discriminant for `y² = x³ + 5` is `Δ = -16(4·0³ + 27·5²) = -10800`. Since both primes exceed `10800`, neither divides `10800`, so `Δ` is a unit in both `𝔽_p` and `𝔽_q` and both curves are elliptic.

### The 2-Cycle Property

The Pasta curves are designed so that:

```
|Pallas(𝔽_p)| = Fq.p = q
|Vesta(𝔽_q)|  = Fp.p = p
```

Each curve's rational point group has order equal to the *other* curve's field characteristic. This means the scalar field of Pallas is `𝔽_q`, which is exactly the base field of Vesta, and vice versa.

This is the key property enabling **efficient Incrementally Verifiable Computation (IVC)** in Halo 2. When a SNARK proof over Pallas is verified inside a circuit, the verification arithmetic lives naturally in `𝔽_q` — exactly the scalar field of Vesta. A Vesta circuit can therefore natively express "I verified a Pallas proof" without any field extension, field embedding, or non-native arithmetic. The two curves alternate across recursive proof layers with no overhead from field mismatch.

### Why 2-Adicity Matters

Both `p - 1` and `q - 1` are divisible by `2³²`:

```
p - 1 = 2³² × 3 × 463 × 539204044132271846773 × 8999194758858563409123804352480028797519453
q - 1 = 2³² × 3² × 1709 × 24859 × 1690502597179744445941507 × 10427374428728808478656897599072717
```

The factor `2³²` means the multiplicative groups `𝔽_p*` and `𝔽_q*` each contain a subgroup of order `2³²`. This is the **2-adicity** required for the Number Theoretic Transform (NTT), the fast polynomial multiplication algorithm underlying Halo 2's PLONKish constraint system. NTTs over domains of size up to `2³²` can be evaluated over these fields without any further extension.

## Formalization

### `Pasta/Fields.lean`

Defines the two field moduli `Fp.p` and `Fq.p` and proves both are prime via the Lucas primality test (`lucas_primality` from Mathlib). The witness `a = 5` is a primitive root for both fields. Primality is reduced to showing `5^((p-1)/q) ≢ 1 (mod p)` for each prime factor `q` of `p - 1`. Also defines the field types `Fp := ZMod Fp.p` and `Fq := ZMod Fq.p`.

### `Pasta/PrattCertificates.lean`

Provides hierarchical Pratt primality certificates for the 28 large intermediate prime factors appearing in the factorizations of `Fp.p - 1` and `Fq.p - 1`. The certificates are organized in 4 levels, where each level's primality proofs depend on the level below. Modular exponentiations are discharged by `native_decide`; small primes use `norm_num`.

### `Pasta/Pallas.lean`

Defines the Pallas curve as a `WeierstrassCurve Fp` with `a₁ = a₂ = a₃ = a₄ = 0` and `a₆ = 5`. Proves that the discriminant `Δ = -10800` is a unit in `Fp`, establishes the `IsElliptic` instance, and verifies that `(-1, 2)` satisfies the curve equation.

### `Pasta/Vesta.lean`

Mirror structure over `Fq`: the Vesta curve definition, discriminant unit proof, `IsElliptic` instance, and the same example point `(-1, 2)`.

### `Pasta/Cycle.lean`

Proves `same_equation`: both Pallas and Vesta share `a₁ = a₂ = a₃ = a₄ = 0`, `a₆ = 5` (proof by `rfl`). Also contains the two cycle conjecture axioms for the group orders (see §Axioms below).

## Key Results

### Primality of the Field Moduli

Both `Fp.p` and `Fq.p` are proven prime via the Lucas primality test with hierarchical Pratt certificates and primitive root witness `a = 5`. The proofs are unconditional: every step reduces to verified `native_decide` computations over concrete natural number arithmetic.

The factorizations that make the Lucas test work:

```
p - 1 = 2³² × 3 × 463 × 539204044132271846773 × 8999194758858563409123804352480028797519453
q - 1 = 2³² × 3² × 1709 × 24859 × 1690502597179744445941507 × 10427374428728808478656897599072717
```

### Elliptic Curve Well-Formedness

The discriminant `Δ = -10800` is proven to be a unit in both `Fp` and `Fq`. Since both primes exceed `10800`, neither divides `10800`, so `¬(p ∣ 10800)` holds, making `10800 : ZMod p` invertible. The `IsElliptic` instances for Pallas and Vesta follow directly.

### The Curve Cycle Structure

The cycle conjecture asserts:

```
|Pallas(𝔽_p)| = Fq.p    (cycle_conjecture_pallas)
|Vesta(𝔽_q)|  = Fp.p    (cycle_conjecture_vesta)
```

These are stated as axioms in `Pasta/Cycle.lean`. Proving them formally requires Schoof's algorithm for counting points on elliptic curves over finite fields, or an equivalent AGM-based certificate — neither of which is currently available in Mathlib. The results are well-established numerically (verified by the Zcash team's `pasta-hadeshash` Sage scripts). The same result is used as the axiom `order_pallas` in `redpallas-formal`.

## Axioms

All theorems and instances in this library are fully proven except for the two cycle conjecture axioms in `Cycle.lean`, which assert the group orders of Pallas and Vesta:

| Axiom | File | Justification |
|-------|------|---------------|
| `cycle_conjecture_pallas` | `Cycle.lean` | Requires Schoof's algorithm — not in Mathlib |
| `cycle_conjecture_vesta` | `Cycle.lean` | Same |

All other results (primality, well-formedness, `IsElliptic` instances, `same_equation`) are unconditionally proved with zero `sorry` statements.

## Dependencies

- **Lean 4** (v4.30.0-rc2)
- **Mathlib4** — elliptic curve library (`WeierstrassCurve`, `Affine.Point`), `lucas_primality`, `ZMod`

## Building

```shell
lake update    # fetch Mathlib (downloads ~3 GB of cached oleans)
lake build     # builds in ~5 seconds after cache download
```

## Usage as a Dependency

Add to your `lakefile.lean`:

```lean
require pasta_formal from git
  "https://github.com/oxarbitrage/pasta-formal"
```

Then import with `import Pasta.Fields`, `import Pasta.Pallas`, etc.

## Downstream Projects

- **[sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal)** — Sinsemilla hash function
- **[poseidon-formal](https://github.com/oxarbitrage/poseidon-formal)** — Poseidon hash function
- **[redpallas-formal](https://github.com/oxarbitrage/redpallas-formal)** — RedPallas signature scheme
- **[orchard-formal](https://github.com/oxarbitrage/orchard-formal)** — Orchard protocol
- **[halo2-formal](https://github.com/oxarbitrage/halo2-formal)** — Halo 2 PLONKish constraint system

## References

- [Zcash Protocol Specification §5.4.9.7](https://zips.z.cash/protocol/protocol.pdf)
- [Halo 2 book](https://zcash.github.io/halo2/)
- [Pasta curves reference](https://github.com/zcash/pasta)
- [pasta-hadeshash (round constants reference)](https://github.com/zcash/pasta-hadeshash)

## License

MIT
