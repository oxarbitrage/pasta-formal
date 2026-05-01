# pasta-formal

Lean 4 formalization of the [Pasta curves](https://electriccoin.co/blog/the-pasta-curves-for-halo-2-and-beyond/) (Pallas and Vesta) used in Zcash's [Halo 2](https://zcash.github.io/halo2/) proving system.

**Status: fully proven — zero `sorry`.**

## What's formalized

| Property | File | Proof technique |
|----------|------|-----------------|
| Primality of Fp (Pallas base field, ~2^254) | `Fields.lean` | Lucas test / Pratt certificate, witness a=5 |
| Primality of Fq (Vesta base field, ~2^254) | `Fields.lean` | Lucas test / Pratt certificate, witness a=5 |
| Primality of 20+ intermediate factors | `PrattCertificates.lean` | Recursive Pratt certificates |
| Pallas curve definition (y² = x³ + 5 over Fp) | `Pallas.lean` | — |
| Vesta curve definition (y² = x³ + 5 over Fq) | `Vesta.lean` | — |
| Discriminant is a unit (both curves) | `Pallas.lean`, `Vesta.lean` | Δ = -10800, p ∤ 10800 since p > 10800 |
| `IsElliptic` instances (both curves) | `Pallas.lean`, `Vesta.lean` | From discriminant |
| Generator point (-1, 2) on both curves | `Pallas.lean`, `Vesta.lean` | Equation check via `ring` |
| Both curves share the equation y² = x³ + 5 | `Cycle.lean` | `rfl` |

## Building

Requires [elan](https://github.com/leanprover/elan). The correct Lean toolchain is installed automatically.

```sh
lake update    # fetch Mathlib (downloads ~3 GB of cached oleans)
lake build     # builds in ~5 seconds after cache download
```

## Dependencies

- **Lean 4** (v4.30.0-rc2)
- **Mathlib4** — elliptic curve library (`WeierstrassCurve`, `Affine.Point`, group law) and `lucas_primality`

## Future work

This library is designed as a building block for downstream Zcash formalizations:

- **Cycle property**: prove |Pallas(Fp)| = Fq.p and |Vesta(Fq)| = Fp.p (requires a verified point-counting algorithm or an external certificate)
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
