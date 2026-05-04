# pasta-formal

**Status:** Fully proven — zero `sorry` statements.

Lean 4 formalization of the Pasta curves (Pallas and Vesta) used in Zcash's Halo 2 proving system.

## What's formalized

Both curves share the equation *y*² = *x*³ + 5, defined over distinct ~254-bit prime fields 𝔽_p (Pallas) and 𝔽_q (Vesta).

- **Primality** of both field moduli, via Lucas test with hierarchical Pratt certificates (28 intermediate primes, 4 levels).
- **`IsElliptic` instances** for both curves — discriminant Δ = −10800 is a unit in both fields.
- **Cycle conjecture** (`Pasta/Cycle.lean`): `|Pallas(𝔽_p)| = q` and `|Vesta(𝔽_q)| = p` are stated as axioms. Proving these formally requires Schoof's point-counting algorithm, not yet available in Mathlib. The same result appears as `order_pallas` in [redpallas-formal](https://github.com/oxarbitrage/pasta-formal).

## Axioms

| Axiom | Justification |
|-------|--------------|
| `cycle_conjecture_pallas` | Requires Schoof's algorithm — not in Mathlib |
| `cycle_conjecture_vesta` | Same |

## Build

```shell
lake build
```

## Dependencies

Lean 4 (`v4.30.0-rc2`), [Mathlib4](https://github.com/leanprover-community/mathlib4).

## References

- [Zcash Protocol Spec §5.4.9.7](https://zips.z.cash/protocol/protocol.pdf)
- [Halo 2 book](https://zcash.github.io/halo2/)
- [pasta-hadeshash](https://github.com/zcash/pasta-hadeshash)

---

## Part of a series

Six repositories formally verifying the Zcash Orchard cryptographic stack:

| Layer | Repository |
|-------|-----------|
| Curves | [pasta-formal](https://github.com/oxarbitrage/pasta-formal) |
| Hash | [poseidon-formal](https://github.com/oxarbitrage/poseidon-formal) |
| Hash-to-curve | [sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal) |
| Signatures | [redpallas-formal](https://github.com/oxarbitrage/redpallas-formal) |
| Protocol | [orchard-formal](https://github.com/oxarbitrage/orchard-formal) |
| Proof system | [halo2-formal](https://github.com/oxarbitrage/halo2-formal) |
