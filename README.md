# pasta-formal

Lean 4 formalization of the [Pasta curves](https://zips.z.cash/protocol/protocol.pdf#pallasandvesta) (Pallas and Vesta) used in Zcash's [Halo 2](https://zcash.github.io/halo2/) proving system.

**Status: fully proven — zero `sorry`.**

## What's formalized

All definitions and theorems live under the `Pasta` namespace.

| Property | File | Proof technique |
|----------|------|-----------------|
| Primality of `Fp.p` (Pallas base field, ~2²⁵⁴) | `Pasta/Fields.lean` | Lucas test / Pratt certificate, witness a=5 |
| Primality of `Fq.p` (Vesta base field, ~2²⁵⁴) | `Pasta/Fields.lean` | Lucas test / Pratt certificate, witness a=5 |
| Primality of 28 intermediate factors | `Pasta/PrattCertificates.lean` | Recursive Pratt certificates |
| Pallas curve definition (y² = x³ + 5 over `𝔽_p`) | `Pasta/Pallas.lean` | — |
| Vesta curve definition (y² = x³ + 5 over `𝔽_q`) | `Pasta/Vesta.lean` | — |
| Discriminant is a unit (both curves) | `Pasta/Pallas.lean`, `Pasta/Vesta.lean` | Δ = -10800, p ∤ 10800 since p > 10800 |
| `IsElliptic` instances (both curves) | `Pasta/Pallas.lean`, `Pasta/Vesta.lean` | From discriminant |
| Point (-1, 2) on both curves | `Pasta/Pallas.lean`, `Pasta/Vesta.lean` | Equation check via `ring` |
| Both curves share the equation y² = x³ + 5 | `Pasta/Cycle.lean` | `rfl` |

## Downstream projects

This library is the foundation for a stack of Zcash formalizations:

- **[sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal)** — Sinsemilla hash function
- **[poseidon-formal](https://github.com/oxarbitrage/poseidon-formal)** — Poseidon hash function
- **[redpallas-formal](https://github.com/oxarbitrage/redpallas-formal)** — RedPallas signature scheme
- **[orchard-formal](https://github.com/oxarbitrage/orchard-formal)** — Orchard protocol (value commitments, nullifiers, binding signatures)
- **[halo2-formal](https://github.com/oxarbitrage/halo2-formal)** — Halo 2 PLONKish constraint system

## Building

Requires [elan](https://github.com/leanprover/elan). The correct Lean toolchain is installed automatically.

```sh
lake update    # fetch Mathlib (downloads ~3 GB of cached oleans)
lake build     # builds in ~5 seconds after cache download
```

## Dependencies

- **Lean 4** (v4.30.0-rc2)
- **Mathlib4** — elliptic curve library (`WeierstrassCurve`, `Affine.Point`, group law) and `lucas_primality`

## Usage as a dependency

Add to your `lakefile.lean`:

```lean
require pasta_formal from git
  "https://github.com/oxarbitrage/pasta-formal"
```

Then import with `import Pasta.Fields`, `import Pasta.Pallas`, etc.

## Future work

- **Cycle property**: prove |Pallas(𝔽_p)| = q and |Vesta(𝔽_q)| = p (requires a verified point-counting algorithm or an external certificate)

## References

- [Zcash Protocol Specification §5.4.9.6](https://zips.z.cash/protocol/protocol.pdf#pallasandvesta) — Pallas and Vesta parameters
- [zcash/pasta_curves](https://github.com/zcash/pasta_curves) — Rust implementation
- [Angdinata & Xu, ITP 2023](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2023.6) — Mathlib's elliptic curve group law proof

## License

MIT
