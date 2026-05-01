# pasta-formal

Lean 4 formalization of the [Pasta curves](https://electriccoin.co/blog/the-pasta-curves-for-halo-2-and-beyond/) (Pallas and Vesta) used in Zcash's [Halo 2](https://zcash.github.io/halo2/) proving system.

**Status: fully proven — zero `sorry`.**

## What's formalized

All definitions and theorems live under the `Pasta` namespace.

| Property | File | Proof technique |
|----------|------|-----------------|
| Primality of `Fp.p` (Pallas base field, ~2²⁵⁴) | `Pasta/Fields.lean` | Lucas test / Pratt certificate, witness a=5 |
| Primality of `Fq.p` (Vesta base field, ~2²⁵⁴) | `Pasta/Fields.lean` | Lucas test / Pratt certificate, witness a=5 |
| Primality of 20+ intermediate factors | `Pasta/PrattCertificates.lean` | Recursive Pratt certificates |
| Pallas curve definition (y² = x³ + 5 over `𝔽_p`) | `Pasta/Pallas.lean` | — |
| Vesta curve definition (y² = x³ + 5 over `𝔽_q`) | `Pasta/Vesta.lean` | — |
| Discriminant is a unit (both curves) | `Pasta/Pallas.lean`, `Pasta/Vesta.lean` | Δ = -10800, p ∤ 10800 since p > 10800 |
| `IsElliptic` instances (both curves) | `Pasta/Pallas.lean`, `Pasta/Vesta.lean` | From discriminant |
| Generator point (-1, 2) on both curves | `Pasta/Pallas.lean`, `Pasta/Vesta.lean` | Equation check via `ring` |
| Both curves share the equation y² = x³ + 5 | `Pasta/Cycle.lean` | `rfl` |

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

This library is designed as a building block for downstream Zcash formalizations:

- **Cycle property**: prove |Pallas(𝔽_p)| = q and |Vesta(𝔽_q)| = p (requires a verified point-counting algorithm or an external certificate)
- **Sinsemilla**: hash function used in Orchard
- **RedPallas**: re-randomizable Schnorr signatures over Pallas
- **Orchard circuit components**: note commitment, nullifier derivation, Merkle path verification

## References

- [The Pasta Curves for Halo 2 and Beyond](https://electriccoin.co/blog/the-pasta-curves-for-halo-2-and-beyond/) — curve design rationale
- [zcash/pasta_curves](https://github.com/zcash/pasta_curves) — Rust implementation
- [Zcash Protocol Specification §5.4.9.6](https://zips.z.cash/protocol/protocol.pdf) — Pallas and Vesta parameters
- [Angdinata & Xu, ITP 2023](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2023.6) — Mathlib's elliptic curve group law proof

## License

MIT
